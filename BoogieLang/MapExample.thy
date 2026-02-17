section \<open>Instantiation Example for MapV\<close>

theory MapExample
  imports (* Semantics *) Main HOL.Real
begin

subsection \<open>Definitions from other files\<close>

type_synonym fname = string (* function name *)
type_synonym vname = nat (* variable name, de-bruijn index *)
type_synonym pname = string (* procedure name *)

datatype lit =  LBool bool  | LInt int | LReal real

datatype binop = Eq | Neq | Add | Sub | Mul | Div | RealDiv | Mod | Lt | Le | Gt | Ge | And | Or | Imp | Iff
datatype unop = Not | UMinus | IntToReal

datatype prim_ty
 = TBool | TInt | TReal

type_synonym tcon_id = string (* type constructor id *)

datatype ty
  = TVar nat | (* type variables as de-bruijn indices *)
    TPrim prim_ty | (* primitive types *)
    TCon tcon_id "ty list" (* type constructor *) |
    TMap ty ty (* maps *)

primrec type_of_lit :: "lit \<Rightarrow> prim_ty"
  where
    "type_of_lit (LBool _) = TBool"
  | "type_of_lit (LInt _)  = TInt"
  | "type_of_lit (LReal _) = TReal"


datatype ('k, 'p) L =
  MapVal "'p \<Rightarrow> ('k, 'p) L" "ty \<times> ty" |  MapKey "'k \<Rightarrow> 'p" "ty \<times> ty"

text \<open>The values (and as a result the semantics) are parametrized by the carrier type 'a for the
abstract values (values that have a type constructed via type constructors)
TODO: explain Map Values
\<close>
datatype ('a, 'm) val = LitV lit | AbsV (the_absv: 'a)
  | MapV 'm

record ('a, 'k) map_interface =
  map_select :: "('a, 'k) val \<Rightarrow> ('a, 'k) val \<Rightarrow> ('a, 'k) val"
  map_store :: "('a, 'k) val \<Rightarrow> ('a, 'k) val \<Rightarrow> ('a, 'k) val \<Rightarrow> ('a, 'k) val"
  map_type :: "'k \<Rightarrow> ty"


type_synonym 'a absval_ty_fun = "'a \<Rightarrow> (tcon_id \<times> ty list)"

fun type_of_val :: "'a absval_ty_fun \<Rightarrow> ('a, 'k) map_interface \<Rightarrow> ('a, 'k) val \<Rightarrow> ty"
  where
   "type_of_val A _ (LitV v) = TPrim (type_of_lit v)"
 | "type_of_val A _ (AbsV v) = TCon (fst (A v)) (snd (A v))"
 | "type_of_val _ MI (MapV v) = (map_type MI) v"


subsection \<open>Type Definition\<close>
(* user needs to instantiate how many nesting levels to support *)

(* (type::((('a)val) => (closed_ty))) *)
datatype 'a val0 = LitV0 lit | AbsV0 (the_absv: 'a)

type_synonym 'a val1 = "('a val0, 'a val0) L"
type_synonym 'a val10 = "'a val1 + 'a val0"
type_synonym 'a val2 = "('a val1, 'a val10) L"
type_synonym 'a val210 = "'a val2 + 'a val1 + 'a val0"
type_synonym 'a val3 = "('a val2, 'a val210) L"
type_synonym 'a val3210 = "'a val3 + 'a val210"
type_synonym 'a valn = "('a, 'a val3 + 'a val2 + 'a val1) val"  (* do not inlcude val0! *)


subsection \<open>Examples\<close>
(* MapV examples *)
value "IntV 2 :: unit valn"

abbreviation IntV where "IntV i \<equiv> LitV0 (LInt i)"
abbreviation TT where "TT \<equiv> TPrim TInt"  (* convenience for testing purposes *)

abbreviation m11 :: "unit val1" where "m11 \<equiv> MapKey (undefined(IntV 3 := IntV 2)) (TT, TT)"
abbreviation m14 :: "unit valn" where "m14 \<equiv> MapV (Inr (Inr m11))"

abbreviation m22 :: "unit val2" where "m22 \<equiv> MapKey (undefined(m11 := Inr (IntV 4))) (TT, TT)"
abbreviation m24 :: "unit valn" where "m24 \<equiv> MapV (Inr (Inl m22))"

abbreviation m33 :: "unit val3" where "m33 \<equiv> MapKey (undefined(m22 := Inr (Inr (IntV 6)))) (TT, TT)"
abbreviation m34 :: "unit valn" where "m34 \<equiv> MapV (Inl m33)"

abbreviation mg3 :: "unit val3" where "mg3 \<equiv> MapKey (undefined(m22 := Inr (Inl  m11))) (TT, (TMap TT  (TPrim TInt)))"
abbreviation mg4 :: "unit valn" where "mg4 \<equiv> MapV (Inl mg3)"

abbreviation ms3 :: "unit val3" where "ms3 \<equiv> MapVal (undefined(Inr (Inr (IntV 3)) := m33)) (TT, (TMap TT  (TPrim TInt)))"
abbreviation ms4 :: "unit valn" where "ms4 \<equiv> MapV (Inl ms3)"


subsection \<open>Helper Functions and Lemmas\<close>

subsection \<open>Select\<close>
(* there needs to be as many additional store functions, as there are nesting levels *)
(* user needs to generate these functions (is there a way to make this cleaner, macro?) *)
fun select0 :: "'a val10 \<Rightarrow> 'a val0 \<Rightarrow> 'a val10" where
    "select0 (Inl (MapVal m _)) k = Inl (m k)"
  | "select0 (Inl (MapKey m _)) k = Inr (m k)"
  | "select0 _ _ = undefined"

fun select1 :: "'a val210  \<Rightarrow> 'a val10  \<Rightarrow> 'a val210" where
    "select1 (Inl (MapVal m _)) k = Inl (m k)"
  | "select1 (Inl (MapKey m _)) (Inl k) = Inr (m k)"
  | "select1 (Inr m) (Inr k) = Inr (select0 m k)"
  | "select1 _ _ = undefined"

fun select2 :: "'a val3210 \<Rightarrow> 'a val210 \<Rightarrow> 'a val3210" where
    "select2 (Inl (MapVal m _)) k = Inl (m k)"
  | "select2 (Inl (MapKey m _)) (Inl k) = Inr (m k)"
  | "select2 (Inr m) (Inr k) = Inr (select1 m k)"
  | "select2 _ _ = undefined"

fun toVal3210 :: "'a valn \<Rightarrow> 'a val3210" where
    "toVal3210 (LitV v) = (Inr (Inr (Inr (LitV0 v))))"
  | "toVal3210 (AbsV v) = (Inr (Inr (Inr (AbsV0 v))))"
  | "toVal3210 (MapV (Inr (Inr m))) = (Inr (Inr (Inl m)))"
  | "toVal3210 (MapV (Inr (Inl m))) = (Inr (Inl m))"
  | "toVal3210 (MapV (Inl m)) = (Inl m)"

fun val3ToValn :: "'a val3210 \<Rightarrow> 'a valn" where
    "val3ToValn (Inr (Inr (Inr (LitV0 v)))) = (LitV v)"
  | "val3ToValn (Inr (Inr (Inr (AbsV0 v)))) = (AbsV v)"
  | "val3ToValn (Inr (Inr (Inl m))) = (MapV (Inr (Inr m)))"
  | "val3ToValn (Inr (Inl m)) = (MapV (Inr (Inl m)))"
  | "val3ToValn (Inl m) = (MapV (Inl m))"

fun selectImpl' :: "'a val3210 \<Rightarrow> 'a val3210 \<Rightarrow> 'a val3210" where
    "selectImpl' m (Inl k) = undefined"
  | "selectImpl' m (Inr k) = select2 m k"

fun selectImplAux :: "'a val3210 \<Rightarrow> 'a val3210 \<Rightarrow> 'a val3210" where
    "selectImplAux (Inr (Inr (Inr (LitV0 v)))) _ = undefined"
  | "selectImplAux (Inr (Inr (Inr (AbsV0 v)))) _ = undefined"
  | "selectImplAux (Inr (Inr (Inl (MapVal m _)))) (Inr (Inr (Inr k))) = Inr (Inr (Inl (m k)))"
  | "selectImplAux (Inr (Inr (Inl (MapKey m _)))) (Inr (Inr (Inr k))) = Inr (Inr (Inr (m k)))"
  | "selectImplAux (Inr (Inl (MapVal m _))) (Inr (Inr k)) = Inr (Inl (m k))"
  | "selectImplAux (Inr (Inl (MapKey m _))) (Inr (Inr (Inl k))) = Inr (Inr (m k))"
  | "selectImplAux (Inl (MapVal m _)) (Inr k) = Inl (m k)"
  | "selectImplAux (Inl (MapKey m _)) (Inr (Inl k)) = Inr (m k)"
  | "selectImplAux _ _ = undefined"

fun selectImpl :: "'a valn \<Rightarrow> 'a valn \<Rightarrow> 'a valn" where
    "selectImpl (LitV _) _ = undefined"
  | "selectImpl (AbsV _) _ = undefined"
  | "selectImpl (MapV m) k = val3ToValn (selectImpl' (toVal3210 (MapV m)) (toVal3210 k))"

abbreviation example_map :: "('a, 'a val3 + 'a val2 + 'a val1) map_interface" where
  "example_map \<equiv> \<lparr> map_select = selectImpl, map_store = undefined, map_type = undefined \<rparr>"

lemma "(map_select example_map) mg4 m24 = (MapV (Inr (Inr (MapKey (undefined(IntV 3 := IntV 2)) (TT, TT)))))" by simp

subsection \<open>Store\<close>
(*
fun store0 :: "_ M \<Rightarrow> _ M \<Rightarrow> _ M \<rightharpoonup> _ M" where
    "store0 (MapAux m) (Up k) v = Some (MapAux (m(k \<mapsto> v)))"
  | "store0 _ _ _ = None"

fun store1 :: "_ M \<Rightarrow> _ M \<Rightarrow> _ M \<rightharpoonup> _ M" where
    "store1 (MapAux m) (Up k) v = Some (MapAux (m(k \<mapsto> v)))"
  | "store1 (Up m) (Up k) (Up v) = map_option Up (store0 m k v)"
  | "store1 _ _ _ = None"

fun store2 :: "_ M \<Rightarrow> _ M \<Rightarrow> _ M \<rightharpoonup> _ M" where
    "store2 (MapAux m) (Up k) v = Some (MapAux (m(k \<mapsto> v)))"
  | "store2 (Up m) (Up k) (Up v) = map_option Up (store1 m k v)"
  | "store2 _ _ _ = None"

primrec store_impl :: "'a valn \<Rightarrow> 'a valn \<Rightarrow> 'a valn \<rightharpoonup> 'a valn" where
    "store_impl (MapV tks tv m) k v = MtoVal (store2 m (valtoM k) (valtoM v)) (TMap tks tv)"
  | "store_impl (LitV _) _ _ = None"
  | "store_impl (AbsV _) _ _ = None"

abbreviation example_map2 :: "('a, 'a val3 + 'a val2 + 'a val1) map_interface" where
  "example_map2 \<equiv> \<lparr> map_select = selectImpl, map_store = storeImpl, map_type = undefined \<rparr>"

primrec select_option where "select_option (Some v) k = (map_select example_map2) v k"
lemma "select_option ((map_store example_map2) mg4 m24 (IntV 42)) m24 = Some (IntV 42)" by simp
*)

subsection \<open>Type Of Val\<close>

fun tyL where "tyL (MapVal _ (tk, tv)) = TMap tk tv" | "tyL (MapKey _ (tk, tv)) = TMap tk tv"

fun ty321 :: "'a val3 + 'a val2 + 'a val1 \<Rightarrow> ty" where
    "ty321 (Inr (Inr m)) = tyL m"
  | "ty321 (Inr (Inl m)) = tyL m"
  | "ty321 (Inl m) = tyL m"

abbreviation example_map_ty :: "('a, 'a val3 + 'a val2 + 'a val1) map_interface" where
  "example_map_ty \<equiv> \<lparr> map_select = selectImpl, map_store = undefined, map_type = ty321 \<rparr>"

fun key_ty where "key_ty (TMap tk _) = tk" | "key_ty _ = undefined"
fun val_ty where "val_ty (TMap _ tv) = tv" | "val_ty _ = undefined"

fun count_level_map_ty :: "ty \<Rightarrow> nat" where
    "count_level_map_ty (TMap tk tv) = max (1 + count_level_map_ty tk) (count_level_map_ty tv)"
  | "count_level_map_ty _ = 0"

fun wf_L where
    "wf_L n (MapKey _ (tk, tv)) = ((count_level_map_ty tk = n-1) \<and> (count_level_map_ty tv \<le> n-1))"
  | "wf_L n (MapVal _ (tk, tv)) = ((count_level_map_ty tk \<le> n-1) \<and> (count_level_map_ty tv = n))"

fun wf_ty :: "'a valn \<Rightarrow> bool" where
    "wf_ty (LitV v) = True"
  | "wf_ty (AbsV v) = True"
  | "wf_ty (MapV (Inr (Inr m))) = wf_L 1 m"
  | "wf_ty (MapV (Inr (Inl m))) = wf_L 2 m"
  | "wf_ty (MapV (Inl m)) = wf_L 3 m"

lemma map_level_gt_0: "count_level_map_ty (TMap tv tk) \<ge> 1" by auto

locale X =
  fixes A :: "'a absval_ty_fun"
begin
  abbreviation ty_of_val where "ty_of_val \<equiv> type_of_val A example_map_ty"
  fun wf where
    "wf m = ((wf_ty m) \<and>
    (\<forall>k. (wf_ty k \<and> ty_of_val k = key_ty (ty_of_val m)
    \<longrightarrow> ty_of_val (selectImpl m k) = val_ty (ty_of_val m))))"


subsubsection "Bijection between count_level_map_ty and sum type levels"

lemma C0Inrrr:
  assumes "count_level_map_ty (ty_of_val v) = 0"
  shows "\<exists>v'. toVal3210 v = Inr (Inr (Inr v'))"
  apply (cases v)
    apply auto
  by (metis assms map_level_gt_0 not_one_le_zero select_convs(3) ty321.elims tyL.elims
      type_of_val.simps(3))

lemma InrrrC0:
  assumes "\<exists>v'. toVal3210 v = Inr (Inr (Inr v'))"
  shows "count_level_map_ty (ty_of_val v) = 0"
  using assms count_level_map_ty.simps(4) toVal3210.elims by force

lemma InrrlC1:
  assumes "wf_ty v"
  assumes "\<exists>v'. toVal3210 v = Inr (Inr (Inl v'))"
  shows "count_level_map_ty (ty_of_val v) = 1"
  apply (cases v rule: toVal3210.cases)
  using assms apply auto
  apply (case_tac m) using assms
  by fastforce+

lemma C1Inrrl:
  assumes "wf_ty v"
  assumes "count_level_map_ty (ty_of_val v) = 1"
  shows "\<exists>v'. toVal3210 v = Inr (Inr (Inl v'))"
  apply (cases v rule: toVal3210.cases)
  using assms apply auto
  apply (case_tac m) using assms apply auto
  apply (case_tac m) using assms apply auto
done

lemma InrlC2:
  assumes "wf_ty v"
  assumes "\<exists>v'. toVal3210 v = Inr (Inl v')"
  shows "count_level_map_ty (ty_of_val v) = 2"
  apply (cases v rule: toVal3210.cases)
  using assms apply auto
  apply (case_tac m) using assms
  by fastforce+

lemma C2Inrl:
  assumes "wf_ty v"
  assumes "count_level_map_ty (ty_of_val v) = 2"
  shows "\<exists>v'. toVal3210 v = Inr (Inl v')"
  apply (cases v rule: toVal3210.cases)
  using assms apply auto
  apply (case_tac m) using assms apply auto
  apply (case_tac m) using assms apply auto
  done

lemma InlC3:
  assumes "wf_ty v"
  assumes "\<exists>v'. toVal3210 v = (Inl v')"
  shows "count_level_map_ty (ty_of_val v) = 3"
  apply (cases v rule: toVal3210.cases)
  using assms apply auto
  apply (case_tac m) using assms
  by fastforce+

lemma C3Inl:
  assumes "wf_ty v"
  assumes "count_level_map_ty (ty_of_val v) = 3"
  shows "\<exists>v'. toVal3210 v = (Inl v')"
  apply (cases v rule: toVal3210.cases)
  using assms apply auto
  apply (case_tac m) using assms apply auto
  apply (case_tac m) using assms apply auto
done


subsubsection \<open>Proving well formdness of a simple map\<close>
fun fAdd1 where "fAdd1 (IntV x) = (IntV (x+1))" | "fAdd1 _ = undefined"
abbreviation mAdd1 :: "'a val1" where "mAdd1 \<equiv> MapKey fAdd1 ((TPrim TInt), (TPrim TInt))"
abbreviation vAdd1 :: "'a valn" where "vAdd1 \<equiv> MapV (Inr (Inr mAdd1))"

lemma "wf_ty vAdd1" by simp

lemma VTAdd1: "val_ty (ty_of_val vAdd1) = (TPrim TInt)"
  using map_interface.select_convs(3) ty321.simps(1)
      tyL.simps(2) type_of_val.simps(3)
      val_ty.simps(1) by metis

lemma KTAdd1: "key_ty (ty_of_val vAdd1) = (TPrim TInt)" 
  using map_interface.select_convs(3) ty321.simps(1)
      tyL.simps(2) type_of_val.simps(3)
      key_ty.simps(1) by metis

lemma ty321TMap: "\<forall>v. \<exists>tk tv. ty321 v = TMap tk tv"
  by (metis (full_types) ty321.elims tyL.elims)

lemma ty_of_val_Int: "ty_of_val k = (TPrim TInt) \<longrightarrow> (\<exists>i. k = LitV (LInt i))"
proof (cases k)
  case (LitV x1)
  then show ?thesis
    by (metis (no_types, lifting) lit.exhaust prim_ty.distinct(1,5) ty.inject(2)
        type_of_lit.simps(1,3) type_of_val.simps(1))
next
  case (AbsV x2)
  then show ?thesis by simp
next
  case (MapV x3)
  then show ?thesis using ty321TMap
    by (metis select_convs(3) ty.simps(14) type_of_val.simps(3))
qed

lemma H2:
  assumes "wf_ty k"
  assumes "ty_of_val k = (TPrim TInt)"
  shows "ty_of_val (selectImpl vAdd1 k) = (TPrim TInt)"
  using assms ty_of_val_Int by fastforce

lemma HH: "(\<forall>k. (wf_ty k \<and> ty_of_val k = key_ty (ty_of_val vAdd1)
    \<longrightarrow> ty_of_val (selectImpl vAdd1 k) = val_ty (ty_of_val vAdd1)))"
  using VTAdd1 KTAdd1 H2 by simp

lemma "wf vAdd1" using VTAdd1 HH by auto

subsubsection \<open>Well formdness of a higher order map\<close>
fun hof where "hof (MapKey f ty) = Inl (MapKey (fAdd1 \<circ> f) ty)" | "hof _ = undefined"
abbreviation TMII where "TMII \<equiv> TMap (TPrim TInt) (TPrim TInt)"
abbreviation hom :: "'a val2" where "hom \<equiv> MapKey hof (TMII, TMII)"
abbreviation homV :: "'a valn" where "homV \<equiv> MapV (Inr (Inl hom))"

lemma "wf_ty homV" by simp

lemma "(val_ty (ty_of_val homV) = TMII)" by simp

lemma "(key_ty (ty_of_val homV) = TMII)" by simp

lemma "\<exists>k. ty_of_val k = TMII"
  by (metis select_convs(3) ty321.simps(1) tyL.simps(2) type_of_val.simps(3))

lemma "ty_of_val k = TMII \<longrightarrow> (\<exists>k'. k = MapV k')" apply (cases k) by auto

lemma kTMII:
  assumes "wf_ty k"
  assumes "ty_of_val k = TMII"
  shows "\<exists>f. k = MapV (Inr (Inr (MapKey f (TT, TT))))"
proof -
  obtain mv where MV: "k = MapV mv" apply (cases k) using assms by auto
  show ?thesis
  proof (cases mv)
    case (Inl m3)
    then show ?thesis
      using assms MV apply (cases m3) by auto
  next
    case (Inr m21)
    then have C21: "k = MapV (Inr m21)" using MV by simp
    then show ?thesis
    proof (cases m21)
      case (Inl m2)
      then show ?thesis
        using assms C21 apply (cases m2) by auto
    next
      case (Inr m1)
      have WF1: "wf_L 1 m1" using C21 assms(1) \<open>m21 = Inr m1\<close> by fastforce
      then have Ty1: "tyL m1 = TMII" using C21 assms \<open>m21 = Inr m1\<close> by fastforce
      then show ?thesis using C21 assms(1) \<open>m21 = Inr m1\<close> WF1 Ty1
      proof (cases m1)
        case (MapVal f t)
        have "t = (TT, TT)" using Ty1 \<open>m1 = MapVal f t\<close>
          using WF1 wf_L.elims(2) by fastforce
        then have "((count_level_map_ty TT \<le> 0) \<and> (count_level_map_ty TT = 1))"
          using Ty1 MapVal WF1 by force
        then show ?thesis by simp
      next
        case (MapKey f t)
        have tt: "t = (TT, TT)" using Ty1 \<open>m1 = MapKey f t\<close>
          using WF1 wf_L.elims(2) by fastforce
        then have "((count_level_map_ty TT = 0) \<and> (count_level_map_ty TT \<le> 0))"
          using Ty1 MapKey WF1 by force
        have "mv = (Inr (Inr (MapKey f t)))"
          using C21 \<open>m21 = Inr m1\<close> \<open>m1 = MapKey f t\<close> MV by force
        then show ?thesis using tt MV by blast
      qed
    qed
  qed
qed

lemma wff:
  assumes "wf_ty k \<and> ty_of_val k = TMII"
  shows "ty_of_val (selectImpl homV k) = TMII"
proof -
  obtain f where K: "k = MapV (Inr (Inr (MapKey f (TT, TT))))"
    using assms kTMII by auto
  then have "selectImpl homV k = val3ToValn (select2 (Inr (Inl hom)) (Inr (Inl (MapKey f (TT, TT)))))"
    by auto
  then have "selectImpl homV k = val3ToValn (Inr (select1 (Inl hom) (Inl (MapKey f (TT, TT)))))"
    by auto
  then have "selectImpl homV k = val3ToValn (Inr (Inr (hof (MapKey f (TT, TT)))))"
    by auto
  have "wf_L 1 (MapKey f (TT, TT))" using assms K by simp
  moreover have "ty_of_val (MapV (Inr (Inr (MapKey f (TT, TT))))) = TMII" using assms K by simp
  then show ?thesis
    using
      \<open>selectImpl homV k = val3ToValn (select2 (Inr (Inl hom)) (Inr (Inl (MapKey f (TT, TT)))))\<close>
    by fastforce
qed


lemma "wf homV" using wff by simp

lemma "wf k \<Longrightarrow> wf_ty k" by simp

subsubsection \<open>Some more general wf properties\<close>

(* conclude Isabelle type from key of a select assuming wf and typed *)
lemma
  assumes "wf (MapV (Inl (MapKey f ty)))"
  assumes "wf k"
  assumes "ty_of_val k = key_ty (ty_of_val (MapV (Inl (MapKey f ty))))"
  shows "\<exists>k'. toVal3210 k = Inr (Inl k')"
proof -
  have "count_level_map_ty (ty_of_val (MapV (Inl (MapKey f ty)))) = 3"
    using InlC3 X.wf.simps assms(1) toVal3210.simps by blast
  then have "count_level_map_ty (key_ty (ty_of_val (MapV (Inl (MapKey f ty))))) = 2"
    using assms(1) wf_L.elims(2) by fastforce
  then have "count_level_map_ty (ty_of_val k) = 2" using assms by auto
  then show ?thesis using C2Inrl using assms(2) by auto
qed

subsection \<open>Array Axiom Update\<close>
text \<open>Property to prove: (m[k] := v)[k] == v or select (store m k v) k = v\<close>
(*
lemma update0:
  assumes "store0 m k v = Some ms"
  shows "select0 ms k = Some v"
  using assms store0.elims by force

lemma update1Up:
  assumes "store1 (Up m') k v = Some ms"
  shows "select1 ms k = Some v"
proof -
  obtain k' v' where "k = Up k' \<and> v = Up v'"
    by (metis M.exhaust assms option.discI store1.simps(4,5))
  then show ?thesis using assms update0 by fastforce
qed

lemma update1Map:
  assumes "store1 (MapAux m') k v = Some ms"
  shows "select1 ms k = Some v"
proof -
  obtain k' where "k = Up k'"
    by (metis M.exhaust assms(1) option.discI store1.simps(5))
  thus ?thesis using assms by fastforce
qed

lemma update1:
  assumes "store1 m k v = Some ms"
  shows "select1 ms k = Some v"
  using M.exhaust assms update1Map update1Up by metis

lemma update2Up:
  assumes "store2 (Up m') k v = Some ms"
  shows "select2 ms k = Some v"
proof -
  obtain k' v' where "k = Up k' \<and> v = Up v'"
    by (metis M.exhaust assms(1) option.discI store2.simps(4,5))
  thus ?thesis using assms update1 by fastforce
qed

lemma update2Map:
  assumes "store2 (MapAux m') k v = Some ms"
  shows "select2 ms k = Some v"
proof -
  obtain k' where "k = Up k'"
    by (metis M.exhaust assms(1) option.discI store2.simps(5))
  thus ?thesis using assms by fastforce
qed

lemma update2:
  assumes "store2 m k v = Some ms"
  shows "select2 ms k = Some v"
  using M.exhaust assms update2Map update2Up by metis

lemma ArrayAxUpdate:
  assumes wf_v: "wf v"
  assumes "store_impl m k v = Some ms"
  assumes "m = (MapV tks tv m')"  (* should be deducible *)
  assumes "ms = (MapV tks tv ms')"  (* should be deducible *)
  assumes "select_impl ms k \<noteq> None"  (* should be deducible *)
  shows "Eq (select_impl ms k) (Some v)"
proof -
  have "Some ms' = store2 m' (valtoM k) (valtoM v)"
    by (metis assms(2-4) MtoVal.simps(7) MtoVal_inj option.exhaust option.simps(3) store_impl.simps(1))
  then have "Some (valtoM v) = select2 ms' (valtoM k)"
    by (simp add: update2)
  moreover obtain w where "Some w = MtoVal (Some (valtoM v)) tv"
    using assms(4,5) calculation by force
  ultimately show ?thesis using MtoVal_valtoM wf_v assms by fastforce
qed
*)
subsection \<open>Array Axiom Stable\<close>
text \<open>Property to prove:
  y \<noteq> x ==> (m[x] := v)[y] == m[y]
  y \<noteq> x ==> select (store m x v) y = select m y\<close>
(*
lemma stable0:
  assumes "x \<noteq> y"
  assumes "store0 m x v = Some ms"
  shows "select0 ms y = select0 m y"
proof (cases y)
  case (MapAux y')
  then show ?thesis by simp
next
  case (Up y')
  moreover obtain m' x' where "m = MapAux m' \<and> x = Up x'"
    by (metis assms(2) option.discI store0.elims)
  ultimately show ?thesis using assms by auto
qed

lemma stable1:
  assumes "x \<noteq> y"
  assumes "store1 m x v = Some ms"
  shows "select1 ms y = select1 m y"
proof (cases y)
  case (MapAux y')
  then show ?thesis by simp
next
  case (Up y')
  show ?thesis
  proof (cases m)
    case (MapAux m')
    moreover obtain x' where "x = Up x'"
      by (metis M.exhaust assms(2) option.discI store1.simps(5))
    then have "ms = MapAux (m'(x' \<mapsto> v))" using assms(2) calculation by fastforce
    then show ?thesis using Up \<open>x = Up x'\<close> assms(1) calculation by auto
  next
    case (Up m')
    obtain x' where "x = Up x'"
      by (metis M.exhaust assms(2) option.discI store1.simps(5))
    obtain v' where "v = Up v'"
      by (metis M.exhaust Up assms(2) option.discI store1.simps(4))
    obtain ms' where "Some ms' = store0 m' x' v'"
      using Up \<open>v = Up v'\<close> \<open>x = Up x'\<close> assms(2) by auto
    have "ms = Up ms'"
      using Up \<open>Some ms' = store0 m' x' v'\<close> \<open>v = Up v'\<close> \<open>x = Up x'\<close> assms(2) by force
    have "y' \<noteq> x'" using assms \<open>x = Up x'\<close> \<open>y = Up y'\<close> by simp
    then show ?thesis using \<open>ms = Up ms'\<close> \<open>m = Up m'\<close> \<open>y = Up y'\<close>
      by (metis \<open>Some ms' = store0 m' x' v'\<close> select1.simps(2) stable0)
  qed
qed

lemma stable2:
  assumes "x \<noteq> y"
  assumes "store2 m x v = Some ms"
  shows "select2 ms y = select2 m y"
proof (cases y)
  case (MapAux y')
  then show ?thesis by simp
next
  case (Up y')
  show ?thesis
  proof (cases m)
    case (MapAux m')
    moreover obtain x' where "x = Up x'"
      by (metis M.exhaust assms(2) option.discI store2.simps(5))
    then have "ms = MapAux (m'(x' \<mapsto> v))" using assms(2) calculation by fastforce
    then show ?thesis using Up \<open>x = Up x'\<close> assms(1) calculation by auto
  next
    case (Up m')
    obtain x' where "x = Up x'"
      by (metis M.exhaust assms(2) option.discI store2.simps(5))
    obtain v' where "v = Up v'"
      by (metis M.exhaust Up assms(2) option.discI store2.simps(4))
    obtain ms' where "Some ms' = store1 m' x' v'"
      using Up \<open>v = Up v'\<close> \<open>x = Up x'\<close> assms(2) by auto
    have "ms = Up ms'"
      using Up \<open>Some ms' = store1 m' x' v'\<close> \<open>v = Up v'\<close> \<open>x = Up x'\<close> assms(2) by force
    have "y' \<noteq> x'" using assms \<open>x = Up x'\<close> \<open>y = Up y'\<close> by simp
    then show ?thesis using \<open>ms = Up ms'\<close> \<open>m = Up m'\<close> \<open>y = Up y'\<close>
      by (metis \<open>Some ms' = store1 m' x' v'\<close> select2.simps(2) stable1)
  qed
qed

lemma ArrayAxStable:
  assumes wf_x: "wf x"
  assumes wf_y: "wf y"
  assumes "\<not>(Eq (Some x) (Some y))"
  assumes "store_impl m x v = Some ms"
  assumes "m = (MapV tks tv m')"  (* should be deducible *)
  assumes "ms = (MapV tks tv ms')"  (* should be deducible *)
  shows "select_impl ms y = select_impl m y"
proof -
  have "Some ms' = store2 m' (valtoM x) (valtoM v)"
    by (metis assms MtoVal.simps(7) MtoVal_inj option.exhaust option.simps(3) store_impl.simps(1))
  then have "Some (valtoM v) = select2 ms' (valtoM x)"  (* delete? *)
    by (simp add: update2)
  have "valtoM x \<noteq> valtoM y"
  proof (cases y)
    case (LitV y')
    then show ?thesis using MtoVal_valtoM assms(3) wf_x by force
  next
    case (AbsV y')
    then show ?thesis by (metis Eq.simps(4) MtoVal.simps(2) MtoVal_valtoM assms(3) valtoM.simps(3) wf_x)
  next
    case (MapV x31 x32 x33)
    then show ?thesis using assms(3) wf.elims(2) wf_x wf_y by fastforce
  qed
  then show ?thesis
    by (simp add: \<open>Some ms' = store2 m' (valtoM x) (valtoM v)\<close> assms(5,6) stable2)
qed
*)

subsection \<open>Array Axiom Extensionality\<close>
text \<open>Property to prove: (\<forall>k. m[k] == n[k]) <==> Eq m n\<close>

subsubsection \<open>Helper Injectivity Lemmas and Types of Map Functions\<close>

lemma valBij: "toVal3210 (val3ToValn x) = x"
  by (cases x rule: val3ToValn.cases; simp)

lemma toVal3210_inj:
  assumes "toVal3210 x = toVal3210 y"
  shows "x = y"
  apply (cases x rule: toVal3210.cases; cases y rule: toVal3210.cases)
  using assms by auto

lemma val3ToValn_inj:
  assumes "val3ToValn x = val3ToValn y"
  shows "x = y"
  using valBij by (metis assms)

lemma toValnOpt_inj:
  assumes "map_option val3ToValn x = map_option val3ToValn y"
  shows "x = y"
  using assms option.inj_map_strong[of x y val3ToValn val3ToValn] val3ToValn_inj
  by blast

lemma toValnInrOpt_inj:
  assumes "map_option ((val3ToValn) \<circ> Inr) x = map_option ((val3ToValn) \<circ> Inr) y"
  shows "x = y"
proof -
  have "map_option val3ToValn (map_option Inr x)
      = map_option val3ToValn (map_option Inr y)"
    by (simp add: assms option.map_comp)
  then show "x = y"
    by (metis (no_types, lifting) option.inj_map_strong sum.inject(2) toValnOpt_inj)
qed

lemma toValnInrrOpt_inj:
  assumes "map_option ((val3ToValn) \<circ> Inr \<circ> Inr) x = map_option ((val3ToValn) \<circ> Inr \<circ> Inr) y"
  shows "x = y"
proof -
  have "map_option val3ToValn (map_option Inr (map_option Inr x))
      = map_option val3ToValn (map_option Inr (map_option Inr y))"
    by (metis assms option.map_comp)
  then show "x = y"
    by (metis (no_types, lifting) option.inj_map_strong sum.inject(2) toValnOpt_inj)
qed


subsubsection \<open>Extensionality Aux\<close>
lemma extensionalityAux:
  assumes "wf (MapV m)"
  assumes "wf (MapV n)"
  assumes "selectImplAux (toVal3210 (MapV m)) = selectImplAux (toVal3210 (MapV n))"
  assumes "ty_of_val (MapV m) = ty_of_val (MapV n)"
  shows "m = n"
  proof (cases m rule: ty321.cases)
    case (1 m')
    then show ?thesis
    proof -
      have "count_level_map_ty (ty_of_val (MapV m)) = 1"
        using "1" InrrlC1 assms(1) toVal3210.simps(3) wf.elims(2) by blast
      then have "count_level_map_ty (ty_of_val (MapV n)) = 1"
        using assms(4) by argo
      then obtain n' where "n = Inr (Inr n')"
        by (metis C1Inrrl assms(2) toVal3210_inj val.inject(3) val3ToValn.simps(3) valBij
            wf.simps)
      then show ?thesis
      proof (cases m')
        case (MapVal m'' tm)
        then show ?thesis
        proof (cases n')
          case (MapVal n'' tn)
          have "tm = tn" using assms(4) 1 MapVal \<open>m' = MapVal m'' tm\<close>
            by (metis \<open>n = Inr (Inr n')\<close> key_ty.simps(1) select_convs(3) surj_pair ty321.simps(1)
                tyL.simps(1) type_of_val.simps(3) val_ty.simps(1))
          moreover have "m'' = n''"
          proof (rule ext)
            fix k show "m'' k = n'' k"
            using assms(3) 1 MapVal \<open>m' = MapVal m'' tm\<close> \<open>n' = MapVal n'' tn\<close>
            selectImplAux.simps(3) sum.inject(2) toVal3210.simps(3)
            by (metis \<open>n = Inr (Inr n')\<close> old.sum.inject(1))
          qed
          ultimately show ?thesis using 1 MapVal \<open>m' = MapVal m'' tm\<close> \<open>n' = MapVal n'' tn\<close>
            using \<open>n = Inr (Inr n')\<close> by force
        next
          case (MapKey x21 x22)
          (* This case is impossible because selectImplAux would return Inl for m and Inr for n *)
          fix f k
          have "selectImplAux (toVal3210 (MapV m)) (Inr (Inr (Inr k))) = Inr (Inr (Inl (m'' k)))"
            using 1 MapVal by simp
          moreover have "selectImplAux (toVal3210 (MapV n)) (Inr (Inr (Inr k))) = Inr (Inr (Inr (f k)))"
            using MapKey toVal3210.simps
            using MapKey \<open>n = Inr (Inr n')\<close> assms(3) calculation by force
          ultimately show ?thesis using assms(3) sum.distinct(1) by simp
        qed
      next
        case (MapKey m'' tm)
        then show ?thesis
        proof (cases n')
          case (MapKey n'' tn)
          have "tm = tn" using assms(4) 1 MapKey \<open>m' = MapKey m'' tm\<close> ty321.simps(1)
            by (metis \<open>n = Inr (Inr n')\<close> select_convs(3) surj_pair ty.inject(4) tyL.simps(2)
                type_of_val.simps(3))
          moreover have "m'' = n''"
          proof (rule ext)
            fix k show "m'' k = n'' k"
              using assms(3) 1 MapKey \<open>m' = MapKey m'' tm\<close> \<open>n' = MapKey n'' tn\<close>
              selectImplAux.simps(4) sum.inject(2) toVal3210.simps(3)
              by (metis \<open>n = Inr (Inr n')\<close>)
          qed
          ultimately show ?thesis using 1 MapKey \<open>m' = MapKey m'' tm\<close> \<open>n' = MapKey n'' tn\<close>
            using \<open>n = Inr (Inr n')\<close> by force
        next
          case (MapVal f tn)
          fix k
          have "selectImplAux (toVal3210 (MapV m)) (Inr (Inr (Inr k))) = Inr (Inr (Inr (m'' k)))" 
            using 1 MapKey by simp
          moreover have "selectImplAux (toVal3210 (MapV n)) (Inr (Inr (Inr k))) = Inr (Inr (Inl (f k)))"
            using \<open>n = Inr (Inr n')\<close> MapVal by simp
          ultimately show ?thesis using assms(3) sum.distinct(1) by auto
        qed
      qed
    qed
next
  case (2 m')
  then show ?thesis 
  proof -
    have "count_level_map_ty (ty_of_val (MapV m)) = 2"
      using "2" InrlC2 assms(1) toVal3210.simps(4) wf_ty.simps(4)
      by fastforce
    then have "count_level_map_ty (ty_of_val (MapV n)) = 2"
      using assms(4) by argo
    then obtain n' where N: "n = Inr (Inl n')"
      using C2Inrl assms(2) toVal3210_inj val.inject(3) val3ToValn.simps(4) valBij
      by (metis wf.elims(1))
    then show ?thesis 
      using assms(3,4) 2 N apply (cases m'; cases n')
      apply (auto simp: fun_eq_iff dest: spec[of _ "Inr (Inr _)"])
      apply (metis Inl_Inr_False selectImplAux.simps(5,6) sum.sel(2))
      apply (metis not_arg_cong_Inr old.sum.distinct(1) selectImplAux.simps(5,6))
      by (metis old.sum.inject(2) selectImplAux.simps(6))
  qed
next
  case (3 m')
  then show ?thesis 
  proof -
    have "count_level_map_ty (ty_of_val (MapV m)) = 3"
      using "3" InlC3 assms(1) toVal3210.simps(5) wf_ty.simps(5)
      by fastforce
    then have "count_level_map_ty (ty_of_val (MapV n)) = 3"
      using assms(4) by argo
    then obtain n' where N: "n = Inl n'"
      using C3Inl assms toVal3210_inj val.inject(3) val3ToValn.simps(5) valBij
      by (metis wf.elims(1))
    then show ?thesis 
      using assms(3,4) 3 N apply (cases m'; cases n')
      apply (auto simp: fun_eq_iff dest: spec[of _ "Inr _"])
      apply (metis old.sum.distinct(1) selectImplAux.simps(7,8))
      apply (metis selectImplAux.simps(7,8) sum.distinct(1))
      by (metis selectImplAux.simps(8) sum.sel(2))
  qed
qed

(*
subsubsection \<open>Extensionality Level 0\<close>

lemma extensional0Val:
  assumes "select0 (Inl (MapVal m t)) = select0 (Inl (MapVal n t'))"
  shows "m = n"
  by (metis (lifting) ext Inl_inject assms select0.simps(1))

lemma extensional0Key:
  assumes "select0 (Inl (MapKey m t)) = select0 (Inl (MapKey n t'))"
  shows "m = n"
  by (metis (no_types, lifting) ext assms not_arg_cong_Inr select0.simps(2))

lemma extensional0:
  assumes "select0 m = select0 n"
  assumes "\<exists>m'. m = Inl m'"
  assumes "ty_of_val (val3ToValn (Inr (Inr m))) = ty_of_val (val3ToValn (Inr (Inr n)))"
  shows "m = n"
proof (cases m)
  case (Inr m')
  then show ?thesis using assms by simp
next
  case (Inl m')
  then show ?thesis
  proof (cases m')
    case (MapVal m'' t)
    then show ?thesis
    proof (cases n)
      case (Inr n')
      then show ?thesis using assms
        by (metis (no_types, lifting) C0Inrrr Inr_inject InrrrC0 sum.distinct(1) valBij)
    next
      case (Inl n')
      then show ?thesis
      proof (cases n')
        case (MapKey n'' t')
        obtain k v where "select0 (Inl (MapVal m'' t)) k = (Inl v)"
          using \<open>m = Inl m'\<close> \<open>m' = MapVal m'' t\<close> assms by auto
        then show ?thesis
          using \<open>m = Inl m'\<close> \<open>m' = MapVal m'' t\<close> \<open>n = Inl n'\<close> \<open>n' = MapKey n'' t'\<close> assms
          by fastforce
      next
        case (MapVal n'' t')
        then have "m = Inl (MapVal m'' t) \<and> n = Inl (MapVal n'' t')"
          using \<open>m = Inl m'\<close> \<open>m' = MapVal m'' t\<close> \<open>n = Inl n'\<close> \<open>n' = MapVal n'' t'\<close> by simp
        then have "select0 (Inl (MapVal m'' t)) = select0 (Inl (MapVal n'' t'))"
          using assms by blast
        then show ?thesis
          using extensional0Val \<open>m = Inl m'\<close> \<open>m' = MapVal m'' t\<close> \<open>n = Inl n'\<close> \<open>n' = MapVal n'' t'\<close> assms
          by (metis (no_types, opaque_lifting) select_convs(3) surj_pair toVal3210.simps(3) toVal3210_inj
              ty.inject(4) ty321.simps(1) tyL.simps(1) type_of_val.simps(3) valBij)
      qed
    qed
  next
    case (MapKey m'' t)
    then show ?thesis
    proof (cases n)
      case (Inr n')
      then show ?thesis using assms(1,3)
        by (metis (no_types, lifting) C0Inrrr Inl X.InrrrC0 sum.distinct(1) sum.inject(2) valBij)
    next
      case (Inl n')
      then show ?thesis
      proof (cases n')
        case (MapVal n'' t')
        obtain k v where "select0 (Inl (MapKey m'' t)) k = (Inr v)"
          using \<open>m = Inl m'\<close> \<open>m' = MapKey m'' t\<close> assms by auto
        then show ?thesis
          using \<open>m = Inl m'\<close> \<open>m' = MapKey m'' t\<close> \<open>n = Inl n'\<close> \<open>n' = MapVal n'' t'\<close> assms
          by fastforce
      next
        case (MapKey n'' t')
        then show ?thesis
        using extensional0Key \<open>m = Inl m'\<close> \<open>m' = MapKey m'' t\<close> \<open>n = Inl n'\<close> \<open>n' = MapKey n'' t'\<close> assms
        by (metis (no_types, opaque_lifting) select_convs(3) surj_pair toVal3210.simps(3) toVal3210_inj
            ty.inject(4) ty321.simps(1) tyL.simps(2) type_of_val.simps(3) valBij)
      qed
    qed
  qed
qed


subsubsection \<open>Extensionality Level 1\<close>

lemma extensional1Val:
  assumes "select1 (Inl (MapVal m t)) = select1 (Inl (MapVal n t'))"
  shows "m = n"
  by (metis (no_types, lifting) ext assms select1.simps(1) sum.inject(1))

lemma extensional1Key:
  assumes "select1 (Inl (MapKey m t)) = select1 (Inl (MapKey n t'))"
  shows "m = n"
  by (metis (no_types, lifting) ext assms not_arg_cong_Inr select1.simps(2))

lemma extensional1Rec:
  assumes "select1 (Inr m') = select1 (Inr n')"
  assumes "\<exists>m''. m' = Inl m''"
  assumes "ty_of_val (val3ToValn (Inr (Inr m'))) = ty_of_val (val3ToValn (Inr (Inr n')))"
  shows "m' = n'" using extensional0 assms
  (* by (metis (lifting) ext not_arg_cong_Inr select1.simps(3)) *)
proof -
  have "\<forall>k. select0 m' k = select0 n' k"
  proof rule
    fix k
    have "select1 (Inr m') (Inr k) = Inr (select0 m' k)" by simp
    moreover have "select1 (Inr n') (Inr k) = Inr (select0 n' k)" by simp
    ultimately have "Inr (select0 m' k) = Inr (select0 n' k)" using assms by simp
    then show "select0 m' k = select0 n' k" by simp
  qed
  then have "select0 m' = select0 n'" by auto
  then show ?thesis using assms extensional0
    using \<open>select0 m' = select0 n'\<close>
    by blast
qed


lemma extensional1:
  assumes "select1 m = select1 n"
  assumes "ty_of_val (val3ToValn (Inr (m))) = ty_of_val (val3ToValn (Inr (n)))"
  assumes "\<exists>m'. m = Inr m' \<Longrightarrow> \<exists>m''. m = Inr (Inl m'')"
  shows "m = n"
proof (cases m)
  case (Inr m')
  then show ?thesis
  proof (cases n)
    case (Inl n')
    then show ?thesis using assms(1) [unfolded \<open>m = _\<close> \<open>n = _\<close>, simplified]
    proof -
      show ?thesis
        obtain k v where A: "select1 (Inr m') k = v" using assms(3) Inr by auto
        then obtain v' where "v = Inr v'" apply (cases k)
          apply (metis Inr_not_Inl L.exhaust \<open>select1 (Inr m') = select1 (Inl n')\<close> select1.simps(1,2,3))
          by auto
        then obtain k' where "k = Inr k'" using A apply (cases k)
          using Extraction.exE_realizer Extraction.exE_realizer'
              HOL.cnf.weakening_thm HOL.forw_subst try
        have "select1 (Inl n') (Inr k') \<noteq> Some (Inr v')"
          using \<open>v = Inr v'\<close> \<open>k = Inr k'\<close> apply (cases n') by auto
        then show ?thesis
          using Inl Inr \<open>select1 (Inr m') k = Some v\<close> \<open>v = Inr v'\<close> \<open>k = Inr k'\<close> assms(1)
          by force
    qed
  next
    case (Inr n') then show ?thesis
      using \<open>m = Inr m'\<close> \<open>n = Inr n'\<close> assms extensional1Rec by fastforce
  qed
next
  case (Inl m')
  then show ?thesis
  proof (cases m')
    case (MapVal m'' t)
    then show ?thesis
    proof (cases n)
      case (Inr n')
      then show ?thesis using assms(1,3)
        by (smt (verit) Inl option.map_disc_iff option.map_sel select1.elims
            sum.distinct(1))
    next
      case (Inl n')
      then show ?thesis
      proof (cases n')
        case (MapKey n'' t')
        obtain k v where "select1 (Inl (MapVal m'' t)) k = Some (Inl v)"
          using \<open>m = Inl m'\<close> \<open>m' = MapVal m'' t\<close> assms by auto
        then show ?thesis
          using \<open>m = Inl m'\<close> \<open>m' = MapVal m'' t\<close> \<open>n = Inl n'\<close> \<open>n' = MapKey n'' t'\<close> assms
          by (smt (verit) Inl_inject Inr_not_Inl L.distinct(1) option.map_disc_iff option.map_sel
              select1.elims)
      next
        case (MapVal n'' t')
        then show ?thesis
          using extensional1Val \<open>m = Inl m'\<close> \<open>m' = MapVal m'' t\<close> \<open>n = Inl n'\<close> \<open>n' = MapVal n'' t'\<close> assms
          by fastforce
      qed
    qed
  next
    case (MapKey m'' t)
    then show ?thesis
    proof (cases n)
      case (Inr n')
      then show ?thesis using assms(1,3)
        by (smt (verit) Inl Inl_inject L.distinct(1) MapKey select1.elims
            sum.distinct(1))
    next
      case (Inl n')
      then show ?thesis
      proof (cases n')
        case (MapVal n'' t')
        obtain k v where "select1 (Inl (MapKey m'' t)) k = Some (Inr v)"
          using \<open>m = Inl m'\<close> \<open>m' = MapKey m'' t\<close> assms
          by (smt (verit) L.distinct(1) option.collapse option.map_disc_iff option.map_sel
              select1.elims sum.inject(1))
        then show ?thesis
          using \<open>m = Inl m'\<close> \<open>m' = MapKey m'' t\<close> \<open>n = Inl n'\<close> \<open>n' = MapVal n'' t'\<close> assms
          by fastforce
      next
        case (MapKey n'' t')
        then show ?thesis
        using extensional1Key \<open>m = Inl m'\<close> \<open>m' = MapKey m'' t\<close> \<open>n = Inl n'\<close> \<open>n' = MapKey n'' t'\<close> assms
          by fastforce
      qed
    qed
  qed
qed

subsubsection \<open>Extensionality Level 2\<close>

lemma extensional2Val:
  assumes "select2 (Inl (MapVal m t)) = select2 (Inl (MapVal n t'))"
  assumes "\<exists>k. select2 (Inl (MapVal m t)) k \<noteq> None"
  shows "m = n"
proof -
  have "\<forall>k. map_option Inl (m k) = map_option Inl (n k)"
    by (metis (mono_tags, lifting) assms(1) option.inj_map_strong select2.simps(1)
        sum.inject(1))
  then have "\<forall>k. m k = n k"
    by (metis (no_types, lifting) Inl_inject[of "the (m _)" "the (n _)"]
        option.collapse[of "m _"] option.collapse[of "n _"] option.map_disc_iff[of Inl "n _"]
        option.map_disc_iff[of Inl "m _"] option.map_sel[of "m _" Inl]
        option.map_sel[of "n _" Inl])
  then show "m = n" by auto
qed

lemma extensional2Key:
  assumes "select2 (Inl (MapKey m t)) = select2 (Inl (MapKey n t'))"
  assumes "\<exists>k. select2 (Inl (MapKey m t)) k \<noteq> None"
  shows "m = n"
proof -
  have "\<forall>k. map_option Inr (m k) = map_option Inr (n k)"
    by (metis (mono_tags, lifting) assms(1) option.inj_map_strong select2.simps(2)
          sum.inject(2))
  then have "\<forall>k. m k = n k"
    by (metis (no_types, lifting) Inr_inject[of "the (m _)" "the (n _)"]
        option.collapse[of "m _"] option.collapse[of "n _"] option.map_disc_iff[of Inr "n _"]
        option.map_disc_iff[of Inr "m _"] option.map_sel[of "m _" Inr]
        option.map_sel[of "n _" Inr])
  then show "m = n" by auto
qed

fun type_of_val3210  where
    "type_of_val3210 (Inl m) = type_of_L m"
  | "type_of_val3210 (Inr v) = type_of_val210 v"

lemma extensional2Rec:
  assumes "select2 (Inr m') = select2 (Inr n')"
  assumes "type_of_val210 m' = type_of_val210 n'"
  assumes "\<exists>k. select2 (Inr m') k \<noteq> None"
  shows "m' = n'"
proof -
  have "\<forall>k. select1 m' k = select1 n' k"
  proof rule
    fix k
    have "select2 (Inr m') (Inr k) = map_option Inr (select1 m' k)"
      by simp
    moreover have "select2 (Inr n') (Inr k) = map_option Inr (select1 n' k)"
      by simp
    ultimately have "map_option Inr (select1 m' k) = map_option Inr (select1 n' k)"
      by (metis (mono_tags, lifting) assms(1) option.inj_map_strong sum.inject(2))
    then show "select1 m' k = select1 n' k"
      by (metis option.inj_map_strong sum.inject(2))
  qed
  then have "select1 m' = select1 n'" by auto
  have "\<exists>k. select1 m' k \<noteq> None"
  proof -
    obtain k where "select2 (Inr m') k \<noteq> None" using assms by auto
    obtain k' where "select2 (Inr m') k = map_option Inr (select1 m' k')"
      by (smt (verit) Inr_not_Inl \<open>select2 (Inr m') k \<noteq> None\<close> select2.elims
          sum.inject(2))
    then show ?thesis using \<open>select2 (Inr m') k \<noteq> None\<close> by auto
  qed
  have "type_of_val210 m' = type_of_val210 n'" using assms by auto
  then show ?thesis using assms extensional1
    using \<open>\<exists>k. select1 m' k \<noteq> None\<close> \<open>select1 m' = select1 n'\<close> by blast
qed

lemma extensional2:
  assumes "select2 m = select2 n"
  assumes "type_of_val3210 m = type_of_val3210 n"
  assumes "\<exists>k. select2 m k \<noteq> None"
  shows "m = n"
proof (cases m)
  case (Inr m')
  then show ?thesis
  proof (cases n)
    case (Inl n')
    then show ?thesis
      by (smt (verit) Inr assms(1,3) map_option_is_None option.map_sel select2.elims
          sum.distinct(1))
    (*proof -
      obtain k v where "select1 (Inr m') k = Some (v)" using Inr assms by auto
      have "select1 (Inl n') k \<noteq> Some (v)"
        by (smt (verit) Inr_not_Inl \<open>select1 (Inr m') k = Some v\<close> option.discI
            option.map_disc_iff option.map_sel select1.elims)
      then show ?thesis
        using Inl Inr \<open>select1 (Inr m') k = Some v\<close> assms(1) by auto
    qed*)
  next
    case (Inr n') then show ?thesis
      using \<open>m = Inr m'\<close> \<open>n = Inr n'\<close> assms extensional2Rec by fastforce
  qed
next
  case (Inl m')
  then show ?thesis
  proof (cases m')
    case (MapVal m'' t)
    then show ?thesis
    proof (cases n)
      case (Inr n')
      then show ?thesis using assms(1,3)
        by (smt (verit) Inl option.map_disc_iff option.map_sel select2.elims
            sum.distinct(1))
    next
      case (Inl n')
      then show ?thesis
      proof (cases n')
        case (MapKey n'' t')
        obtain k v where "select2 (Inl (MapVal m'' t)) k = Some (Inl v)"
          using \<open>m = Inl m'\<close> \<open>m' = MapVal m'' t\<close> assms by auto
        then show ?thesis
          using \<open>m = Inl m'\<close> \<open>m' = MapVal m'' t\<close> \<open>n = Inl n'\<close> \<open>n' = MapKey n'' t'\<close> assms
          by (smt (verit) Inl_inject Inr_not_Inl L.distinct(1) option.map_disc_iff option.map_sel
              select2.elims)
      next
        case (MapVal n'' t')
        then show ?thesis
          using extensional2Val \<open>m = Inl m'\<close> \<open>m' = MapVal m'' t\<close> \<open>n = Inl n'\<close> \<open>n' = MapVal n'' t'\<close> assms
          by fastforce
      qed
    qed
  next
    case (MapKey m'' t)
    then show ?thesis
    proof (cases n)
      case (Inr n')
      then show ?thesis using assms(1,3)
        by (smt (verit) Inl Inl_inject L.distinct(1) MapKey select2.elims
            sum.distinct(1))
    next
      case (Inl n')
      then show ?thesis
      proof (cases n')
        case (MapVal n'' t')
        obtain k v where "select2 (Inl (MapKey m'' t)) k = Some (Inr v)"
          using \<open>m = Inl m'\<close> \<open>m' = MapKey m'' t\<close> assms
          by (smt (verit) L.distinct(1) option.collapse option.map_disc_iff option.map_sel
              select2.elims sum.inject(1))
        then show ?thesis
          using \<open>m = Inl m'\<close> \<open>m' = MapKey m'' t\<close> \<open>n = Inl n'\<close> \<open>n' = MapVal n'' t'\<close> assms
          by fastforce
      next
        case (MapKey n'' t')
        then show ?thesis
        using extensional2Key \<open>m = Inl m'\<close> \<open>m' = MapKey m'' t\<close> \<open>n = Inl n'\<close> \<open>n' = MapKey n'' t'\<close> assms
          by fastforce
      qed
    qed
  qed
qed
*)

subsubsection \<open>Extensionality Impl\<close>

lemma extensionalImpl':
  assumes "selectImpl' m = selectImpl' n"
  assumes "type_of_val3210 m = type_of_val3210 n"
  assumes "\<exists>k. selectImpl' m k \<noteq> None"
  shows "m = n"
  by (metis (no_types, lifting) ext assms(1,2,3) extensional2[of n m]
      selectImpl'.elims[of m _ "selectImpl' m _"] selectImpl'.simps(2)[of n]
      selectImpl'.simps(2)[of m])

fun type_of_Impl where
    "type_of_Impl m = type_of_val3210 (toVal3210 (MapV m))"

lemma extensionalImplMapV:
  assumes "selectImpl (MapV m) = selectImpl (MapV n)"
  assumes "type_of_Impl m = type_of_Impl n"
  assumes "\<exists>k. selectImpl (MapV m) k \<noteq> None"
  shows "m = n"
proof -  
  (* injectivity of map_option val3ToValn *)
  have "\<forall>k'. map_option val3ToValn (selectImpl' (toVal3210 (MapV m)) (toVal3210 k'))
    = map_option val3ToValn (selectImpl' (toVal3210 (MapV n)) (toVal3210 k'))"
    by (metis assms(1) selectImpl.simps(3))
  then have "\<forall>k'. (selectImpl' (toVal3210 (MapV m)) (toVal3210 k'))
    = (selectImpl' (toVal3210 (MapV n)) (toVal3210 k'))"
    using toValnOpt_inj by blast
  then have "\<forall>k. (selectImpl' (toVal3210 (MapV m)) k)
    = (selectImpl' (toVal3210 (MapV n)) k)" by (metis valBij)

  (* lemma extensionalImpl' *)
  moreover have "type_of_val3210 (toVal3210 (MapV m)) = type_of_val3210 (toVal3210 (MapV n))"
    using assms(2) by auto
  moreover have "\<exists>k. selectImpl' (toVal3210 (MapV m)) k \<noteq> None"
    using assms(3) by auto
  ultimately have "(toVal3210 (MapV m)) = (toVal3210 (MapV n))"
    using assms extensionalImpl' by blast

  (* injectivity of toVal3210 *)
  then show ?thesis using toVal3210_inj by auto
qed

abbreviation example_map3 :: "('a, 'a val3 + 'a val2 + 'a val1) map_interface" where
  "example_map3 \<equiv> \<lparr> map_select = selectImpl, map_store = undefined, map_type = type_of_Impl \<rparr>"


lemma extensional:
  assumes "(map_select example_map3) m = (map_select example_map3) n"
  assumes "type_of_val A example_map3 m = type_of_val A example_map3 n"
  shows "m = n"
  by (smt (verit) assms(1,2,3) extensionalImplMapV map_interface.select_convs(1,3)
      selectImpl.elims type_of_val.simps(3))


end

end