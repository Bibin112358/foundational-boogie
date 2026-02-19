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

fun type_of_val :: "'a absval_ty_fun \<Rightarrow> ('m \<Rightarrow> (ty \<times> ty)) \<Rightarrow> ('a, 'm) val \<Rightarrow> ty"
  where
   "type_of_val A _ (LitV v) = TPrim (type_of_lit v)"
 | "type_of_val A _ (AbsV v) = TCon (fst (A v)) (snd (A v))"
 | "type_of_val _ M (MapV v) = TMap (fst (M v)) (snd (M v))"


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

abbreviation m11 :: "'a val1" where "m11 \<equiv> MapKey (undefined(IntV 3 := IntV 2)) (TT, TT)"
abbreviation m14 :: "'a valn" where "m14 \<equiv> MapV (Inr (Inr m11))"

abbreviation m22 :: "'a val2" where "m22 \<equiv> MapKey (undefined(m11 := Inr (IntV 4))) (TT, TT)"
abbreviation m24 :: "'a valn" where "m24 \<equiv> MapV (Inr (Inl m22))"

abbreviation m33 :: "'a val3" where "m33 \<equiv> MapKey (undefined(m22 := Inr (Inr (IntV 6)))) (TT, TT)"
abbreviation m34 :: "'a valn" where "m34 \<equiv> MapV (Inl m33)"

abbreviation mg3 :: "'a val3" where "mg3 \<equiv> MapKey (undefined(m22 := Inr (Inl  m11))) (TT, TT)"
abbreviation mg4 :: "'a valn" where "mg4 \<equiv> MapV (Inl mg3)"

abbreviation ms3 :: "'a val3" where "ms3 \<equiv> MapVal (undefined(Inr (Inr (IntV 3)) := m33)) (TT, (TMap TT  (TPrim TInt)))"
abbreviation ms4 :: "'a valn" where "ms4 \<equiv> MapV (Inl ms3)"

subsection \<open>Select\<close>
(* there needs to be as many additional store functions, as there are nesting levels *)
(* user needs to generate these functions (is there a way to make this cleaner, macro?) *)
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

fun selectImplAux :: "'a val3210 \<Rightarrow> 'a val3210 \<Rightarrow> 'a val3210" where
    "selectImplAux (Inr (Inr (Inr (LitV0 v)))) _ = (Inr (Inr (Inr undefined)))"
  | "selectImplAux (Inr (Inr (Inr (AbsV0 v)))) _ = (Inr (Inr (Inr undefined)))"
  | "selectImplAux (Inr (Inr (Inl (MapVal m _)))) (Inr (Inr (Inr k))) = Inr (Inr (Inl (m k)))"
  | "selectImplAux (Inr (Inr (Inl (MapKey m _)))) (Inr (Inr (Inr k))) = Inr (Inr (Inr (m k)))"
  | "selectImplAux (Inr (Inl (MapVal m _))) (Inr (Inr k)) = Inr (Inl (m k))"
  | "selectImplAux (Inr (Inl (MapKey m _))) (Inr (Inr (Inl k))) = Inr (Inr (m k))"
  | "selectImplAux (Inl (MapVal m _)) (Inr k) = Inl (m k)"
  | "selectImplAux (Inl (MapKey m _)) (Inr (Inl k)) = Inr (m k)"
  | "selectImplAux _ _ = (Inr (Inr (Inr undefined)))"

fun selectImpl :: "'a valn \<Rightarrow> 'a valn \<Rightarrow> 'a valn" where
  "selectImpl m k = val3ToValn (selectImplAux (toVal3210 m) (toVal3210 k))"

abbreviation example_map :: "('a, 'a val3 + 'a val2 + 'a val1) map_interface" where
  "example_map \<equiv> \<lparr> map_select = selectImpl, map_store = undefined, map_type = undefined \<rparr>"

lemma "(map_select example_map) mg4 m24 = (MapV (Inr (Inr (MapKey (undefined(IntV 3 := IntV 2)) (TT, TT)))))" by simp


subsection \<open>Type Of Val\<close>

fun tyL where "tyL (MapVal _ (tk, tv)) = (tk, tv)" | "tyL (MapKey _ (tk, tv)) = (tk, tv)"

fun ty321 :: "'a val3 + 'a val2 + 'a val1 \<Rightarrow> ty \<times> ty" where
    "ty321 (Inr (Inr m)) = tyL m"
  | "ty321 (Inr (Inl m)) = tyL m"
  | "ty321 (Inl m) = tyL m"

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


subsection \<open>Helper Injectivity Lemmas for toVal3210 and val3ToValn\<close>

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


subsection \<open>Theory dependent on A::"'a absval_ty_fun"\<close>

locale X =
  fixes A :: "'a absval_ty_fun"
begin
abbreviation ty_of_val where "ty_of_val \<equiv> type_of_val A ty321"


subsection \<open>Store\<close>

fun storeImplAux :: "'a val3210 \<Rightarrow> 'a val3210 \<Rightarrow> 'a val3210 \<Rightarrow> 'a val3210" where
    "storeImplAux (Inr (Inr (Inl (MapVal m t)))) (Inr (Inr (Inr k))) (Inr (Inr (Inl v)))
      = (Inr (Inr (Inl (MapVal (m(k := v)) t))))"
  | "storeImplAux (Inr (Inr (Inl (MapKey m t)))) (Inr (Inr (Inr k))) (Inr (Inr (Inr v)))
      = (Inr (Inr (Inl (MapKey (m(k := v)) t))))"
  | "storeImplAux (Inr (Inl (MapVal m t))) (Inr (Inr k)) (Inr (Inl v))
      = (Inr (Inl (MapVal (m(k := v)) t)))"
  | "storeImplAux (Inr (Inl (MapKey m t))) (Inr (Inr (Inl k))) (Inr (Inr v))
      = (Inr (Inl (MapKey (m(k := v)) t)))"
  | "storeImplAux (Inl (MapVal m t)) (Inr k) (Inl v)
      = (Inl (MapVal (m(k := v)) t))"
  | "storeImplAux (Inl (MapKey m t)) (Inr (Inl k)) (Inr v)
      = (Inl (MapKey (m(k := v)) t))"
  | "storeImplAux x _ _ = x"

fun storeImpl :: "'a valn \<Rightarrow> 'a valn \<Rightarrow> 'a valn \<Rightarrow> 'a valn" where
  "storeImpl m k v = (if ty_of_val v = val_ty (ty_of_val m)
    then val3ToValn (storeImplAux (toVal3210 m) (toVal3210 k) (toVal3210 v))
    else m)"

abbreviation example_map2 :: "('a, 'a val3 + 'a val2 + 'a val1) map_interface" where
  "example_map2 \<equiv> \<lparr> map_select = selectImpl, map_store = storeImpl, map_type = undefined \<rparr>"

lemma "ty_of_val (LitV (LInt 42)) = TT" by simp
lemma "val_ty (ty_of_val mg4) = TT" by simp
lemma "(map_select example_map2) ((map_store example_map2) mg4 m24 (LitV (LInt 42))) m24
  = (LitV (LInt 42))" by simp


subsection \<open>Well Formedness\<close>

inductive wf where
    wfLitV: "wf (LitV v)" | wfAbsV: "wf (AbsV v)" |
    wfMapV: "\<lbrakk> wf_ty m;  (\<forall>k. wf (selectImpl m k));
      (\<forall>k. wf_ty k \<and> ty_of_val k = key_ty (ty_of_val m) \<longrightarrow> ty_of_val (selectImpl m k) = val_ty (ty_of_val m))
      \<rbrakk> \<Longrightarrow> wf m"

lemma "(wf (LitV (LInt 2)))" using local.wf.wfLitV by simp
lemma wfundef: "(wf (val3ToValn (Inr (Inr (Inr undefined)))))"
  by (metis wfAbsV wfLitV val0.exhaust val3ToValn.simps(1,2))


subsubsection "Bijection between count_level_map_ty and sum type levels"

lemma C0Inrrr:
  assumes "count_level_map_ty (ty_of_val v) = 0"
  shows "\<exists>v'. toVal3210 v = Inr (Inr (Inr v'))"
  apply (cases v)
    apply auto
  by (metis assms map_level_gt_0 not_one_le_zero
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
  assumes "toVal3210 v = (Inl v')"
  shows "count_level_map_ty (ty_of_val v) = 3"
  apply (cases v rule: toVal3210.cases)
  using assms apply auto
  apply (cases v') using assms
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

lemma VTAdd1: "val_ty (ty_of_val vAdd1) = (TPrim TInt)" by simp

lemma KTAdd1: "key_ty (ty_of_val vAdd1) = (TPrim TInt)" by simp

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
  then show ?thesis by simp
qed

lemma H2:
  assumes "wf_ty k"
  assumes "ty_of_val k = (TPrim TInt)"
  shows "ty_of_val (selectImpl vAdd1 k) = (TPrim TInt)"
  using assms ty_of_val_Int by fastforce

lemma HH: "(\<forall>k. (wf_ty k \<and> ty_of_val k = key_ty (ty_of_val vAdd1)
    \<longrightarrow> ty_of_val (selectImpl vAdd1 k) = val_ty (ty_of_val vAdd1)))"
  using VTAdd1 KTAdd1 H2 by simp

lemma vAdd1wfSelect: "wf (selectImpl vAdd1 k)"
  apply (cases k rule: toVal3210.cases; simp add: wfundef)
      apply (case_tac v; simp add: wfundef)
        apply (simp add: wfLitV)
  done

lemma "wf vAdd1" using VTAdd1 HH vAdd1wfSelect
  using X.wf.simps[of A vAdd1] by auto


subsubsection \<open>Well formdness of a higher order map\<close>
(* TODO: I actually want to only assume wf (MapV (Inr (Inr (MapKey (f) ty)))) *)
fun hof where "hof (MapKey f ty) = (case wf (MapV (Inr (Inr (MapKey (fAdd1 \<circ> f) ty)))) of True \<Rightarrow> Inl (MapKey (fAdd1 \<circ> f) ty) | False \<Rightarrow> Inl mAdd1)" | "hof _ = Inl mAdd1"
abbreviation TMII where "TMII \<equiv> TMap (TPrim TInt) (TPrim TInt)"
abbreviation hom :: "'a val2" where "hom \<equiv> MapKey hof (TMII, TMII)"
abbreviation homV :: "'a valn" where "homV \<equiv> MapV (Inr (Inl hom))"

lemma "wf_ty homV" by simp

lemma "(val_ty (ty_of_val homV) = TMII)" by simp

lemma "(key_ty (ty_of_val homV) = TMII)" by simp

lemma "ty_of_val k = TMII \<longrightarrow> (\<exists>k'. k = MapV k')" apply (cases k) by auto

lemma kTMII:
  assumes "wf_ty k"
  assumes "ty_of_val k = TMII"
  shows "\<exists>f. k = MapV (Inr (Inr (MapKey f (TT, TT))))"
proof -
  have "count_level_map_ty (ty_of_val k) = 1" using assms by simp
  then obtain k' where "toVal3210 k = Inr (Inr (Inl k'))" using C1Inrrl assms by blast
  then have K: "k = MapV (Inr (Inr k'))" using toVal3210.elims by auto
  then have "wf_L 1 k'" using assms by force
  then show ?thesis
    apply (cases k')
    using K assms(2) by auto
qed

lemma wff:
  assumes "wf_ty k \<and> ty_of_val k = TMII"
  shows "ty_of_val (selectImpl homV k) = TMII"
proof -
  obtain f where K: "k = MapV (Inr (Inr (MapKey f (TT, TT))))"
    using assms kTMII by auto
  then have "selectImpl homV k = val3ToValn (Inr (Inr (hof (MapKey f (TT, TT)))))"
    by auto
  have "wf_L 1 (MapKey f (TT, TT))" using assms K by simp
  moreover have "ty_of_val (MapV (Inr (Inr (MapKey f (TT, TT))))) = TMII" using assms K by simp
  then show ?thesis
    using
      \<open>selectImpl homV k = val3ToValn (Inr (Inr (hof (MapKey f (TT, TT)))))\<close>
    by (smt (verit) X.hof.simps(1) select_convs(3) ty321.simps(1) tyL.simps(2) type_of_val.simps(3)
        val3ToValn.simps(3))
qed

lemma vhomVwfSelect: "wf (selectImpl homV k)"
  apply (cases k rule: toVal3210.cases; simp add: wfundef)
      apply (case_tac m; auto)
        using HH X.wf.simps[of A vAdd1] vAdd1wfSelect apply auto[1]
        apply (smt (verit) X.HH X.vAdd1wfSelect
            \<open>local.wf vAdd1 = ((\<exists>v. vAdd1 = LitV v) \<or> (\<exists>v. vAdd1 = AbsV v) \<or> (\<exists>m. vAdd1 = m \<and> wf_ty m \<and> (\<forall>k. local.wf (selectImpl m k)) \<and> (\<forall>k. wf_ty k \<and> ty_of_val k = key_ty (ty_of_val m) \<longrightarrow> ty_of_val (selectImpl m k) = val_ty (ty_of_val m))))\<close>
            count_level_map_ty.simps(3) diff_is_0_eq le_numeral_extra(3,4) val3ToValn.simps(3) wf_L.simps(1)
            wf_ty.simps(3))
  done

lemma "wf homV" using wff vhomVwfSelect X.wf.simps[of A homV] by simp

lemma wf_impl_wf_ty: "wf k \<Longrightarrow> wf_ty k" using wf.cases by force


subsubsection \<open>Some more general wf properties\<close>

(* conclude Isabelle type from key of a select assuming wf and typed *)
lemma
  assumes "wf (MapV (Inl (MapKey f ty)))"
  assumes "wf k"
  assumes "ty_of_val k = key_ty (ty_of_val (MapV (Inl (MapKey f ty))))"
  shows "\<exists>k'. toVal3210 k = Inr (Inl k')"
proof -
  have "count_level_map_ty (ty_of_val (MapV (Inl (MapKey f ty)))) = 3"
    using InlC3 X.wf.simps assms(1) toVal3210.simps wf_impl_wf_ty by fast
  then have "count_level_map_ty (key_ty (ty_of_val (MapV (Inl (MapKey f ty))))) = 2"
    using assms(1) wf_L.elims(2) wf_impl_wf_ty by fastforce
  then have "count_level_map_ty (ty_of_val k) = 2" using assms by auto
  then show ?thesis using C2Inrl using assms(2) wf_impl_wf_ty by auto
qed

subsection \<open>Select & Store is closed under wf\<close>
lemma selectClosedWf:
  assumes "wf m"
  (* assumes "wf k" *)  (* not needed *)
  shows "wf (selectImpl m k)"
  by (metis X.wf.cases assms(1) selectImpl.elims selectImplAux.simps(1,2) toVal3210.simps(1,2)
      wfundef)

(* (wf_ty m  \<and>  (\<forall>k. wf (selectImpl m k))  *)

lemma storeClosedWfTy:
  assumes "wf m"
  assumes "wf k"
  assumes "wf v"
  shows "wf (storeImpl m k v)"
  thm storeImplAux.cases
  apply (cases "(toVal3210 m, toVal3210 k, toVal3210 v)" rule: storeImplAux.cases; (auto simp add: assms))
  oops
qed

subsection \<open>Array Axiom Update\<close>
text \<open>Property to prove: (m[k] := v)[k] == v or select (store m k v) k = v\<close>

lemma
  assumes "M = MapV (Inr (Inr (MapKey f t)))"
  assumes "wf M"
  assumes "wf k"
  assumes "wf v"
  assumes "ty_of_val M = TMap (ty_of_val k) (ty_of_val v)"
  shows "selectImpl (storeImpl M k v) k = v"
proof -
  have "count_level_map_ty (ty_of_val k) = 0"
    using assms InrrlC1 wf_impl_wf_ty by fastforce
  then obtain k' where K: "toVal3210 k = Inr (Inr (Inr k'))"
    using C0Inrrr by blast
  have "count_level_map_ty (ty_of_val v) = 0"
    using assms wf_L.elims(2) wf_impl_wf_ty by fastforce
  then obtain v' where V: "toVal3210 v = Inr (Inr (Inr v'))"
    using C0Inrrr by blast
  have "storeImpl M k v = val3ToValn (Inr (Inr (Inl (MapKey (f(k' := v')) t))))"
    using assms K V by auto
  have "selectImpl (storeImpl M k v) k = val3ToValn (Inr (Inr (Inr ((f(k' := v')) k'))))"
    using assms K V by simp
  moreover have "val3ToValn (Inr (Inr (Inr v'))) = v" using V toVal3210.elims by force
  ultimately show ?thesis by auto
qed

lemma
  assumes "M = MapV (Inl (MapVal f t))"
  assumes "wf M"
  assumes "wf k"
  assumes "wf v"
  assumes "ty_of_val M = TMap (ty_of_val k) (ty_of_val v)"
  shows "selectImpl (storeImpl M k v) k = v"
proof -
  obtain tk tv where "t = (tk, tv)" by fastforce
  have "wf_L 3 (MapVal f t)" using assms
    using wf_impl_wf_ty wf_ty.simps(5) by blast
  then have "count_level_map_ty (ty_of_val k) \<le> 2" using assms \<open>t = (tk, tv)\<close> by simp
  then obtain k' where K: "toVal3210 k = Inr k'"
    by (metis Suc_n_not_le_n X.InlC3 X.wf_impl_wf_ty assms(3) numeral_2_eq_2 numeral_3_eq_3
        sumE)
  have "count_level_map_ty (ty_of_val v) = 3"
    using assms wf_L.elims(2) wf_impl_wf_ty by fastforce
  then obtain v' where V: "toVal3210 v = Inl v'"
    using C3Inl assms wf_impl_wf_ty by blast
  have "storeImpl M k v = val3ToValn (Inl (MapVal (f(k' := v')) t))"
    using assms K V by auto
  have "selectImpl (storeImpl M k v) k = val3ToValn (Inl ((f(k' := v')) k'))"
    using assms K V by simp
  moreover have "val3ToValn (Inl v') = v" using V toVal3210.elims by force
  ultimately show ?thesis by auto
qed

lemma
  assumes "M = LitV l"
  assumes "wf M"
  assumes "wf k"
  assumes "wf v"
  assumes "ty_of_val M = TMap (ty_of_val k) (ty_of_val v)"
  shows "selectImpl (storeImpl M k v) k = v"
  using assms(1,5) by force


lemma
  assumes "wf M \<and> wf k \<and> wf v"
  assumes "ty_of_val M = TMap (ty_of_val k) (ty_of_val v)"
  assumes "toVal3210 M = Inl (MapKey f t)"
  shows "(\<exists>k'. toVal3210 k = Inr (Inl k')) \<and> (\<exists>v'. toVal3210 v = Inr v')"
proof -
  have MVT: "M = MapV (Inl (MapKey f t))" using assms by (simp add: toVal3210_inj)
  obtain tv tk where "t = (tv, tk)" by fastforce
  then have T: "t = ((ty_of_val k), (ty_of_val v))" using assms MVT by fastforce
  have KL: "count_level_map_ty (ty_of_val k) = 2" using assms MVT wf_impl_wf_ty T  by force
  have VL: "count_level_map_ty (ty_of_val v) \<le> 2" using assms MVT wf_impl_wf_ty T  by force
  then show ?thesis using assms MVT wf_impl_wf_ty KL VL C2Inrl C1Inrrl C0Inrrr
    by (cases v rule: toVal3210.cases; force)
qed

lemma
  assumes "wf M \<and> wf k \<and> wf v"
  assumes "ty_of_val M = TMap (ty_of_val k) (ty_of_val v)"
  assumes "toVal3210 M = Inl (MapVal f (tv, tk))"
  shows "(\<exists>k'. toVal3210 k = Inr k') \<and> (\<exists>v'. toVal3210 v = Inl v')"
proof -
  have MVT: "M = MapV (Inl (MapVal f (tv, tk)))" using assms by (simp add: toVal3210_inj)
  then have T: "(tv, tk) = ((ty_of_val k), (ty_of_val v))" using assms MVT by fastforce
  have KL: "count_level_map_ty (ty_of_val k) \<le> 2" using assms MVT wf_impl_wf_ty T  by force
  have VL: "count_level_map_ty (ty_of_val v) = 3" using assms MVT wf_impl_wf_ty T  by force
  then show ?thesis using assms MVT wf_impl_wf_ty KL VL InlC3 C3Inl C2Inrl C1Inrrl C0Inrrr
    by (cases "toVal3210 k" rule: val3ToValn.cases; simp)
qed
  

thm val3ToValn.cases
lemma ValnCases:
"(\<And>v. x = LitV v \<Longrightarrow> P) \<Longrightarrow>
(\<And>v. x = AbsV v \<Longrightarrow> P) \<Longrightarrow>
(\<And>f tk tv. x = MapV (Inr (Inr (MapKey f (tk, tv)))) \<Longrightarrow> P) \<Longrightarrow>
(\<And>f tk tv. x = MapV (Inr (Inr (MapVal f (tk, tv)))) \<Longrightarrow> P) \<Longrightarrow>
(\<And>f tk tv. x = MapV (Inr (Inl (MapKey f (tk, tv)))) \<Longrightarrow> P) \<Longrightarrow>
(\<And>f tk tv. x = MapV (Inr (Inl (MapVal f (tk, tv)))) \<Longrightarrow> P) \<Longrightarrow>
(\<And>f tk tv. x = MapV (Inl (MapKey f (tk, tv))) \<Longrightarrow> P) \<Longrightarrow>
(\<And>f tk tv. x = MapV (Inl (MapVal f (tk, tv))) \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis L.exhaust sumE surj_pair val.exhaust_sel)


lemma ArrayAxUpdate:
  assumes "wf M"
  assumes "wf k"
  assumes "wf v"
  assumes "ty_of_val M = TMap (ty_of_val k) (ty_of_val v)"
  shows "selectImpl (storeImpl M k v) k = v"
proof (cases M rule: ValnCases)
  case (1 v)
  then show ?thesis using assms by force
next
  case (2 v)
  then show ?thesis using assms by force
next
  case (3 f tk tv)  (* M = MapV (Inr (Inr (MapKey f (tk, tv))))  *)
  then have T: "(tk, tv) = ((ty_of_val k), (ty_of_val v))" using assms by auto
  have "count_level_map_ty (ty_of_val k) = 0" using assms wf_impl_wf_ty T "3" by fastforce
  then obtain k' where K: "toVal3210 k = Inr (Inr (Inr k'))" using C0Inrrr by auto
  have "count_level_map_ty (ty_of_val v) \<le> 0" using assms wf_impl_wf_ty T "3" by force
  then obtain v' where V: "toVal3210 v = Inr (Inr (Inr v'))" using C0Inrrr by auto
  show ?thesis using assms wf_impl_wf_ty K V "3"
    by (cases v; force)
next
  case (4 f tk tv)  (* M = MapV (Inr (Inr (MapVal f (tk, tv)))) *)
  then have T: "(tk, tv) = ((ty_of_val k), (ty_of_val v))" using assms by auto
  have "count_level_map_ty (ty_of_val k) \<le> 0" using assms wf_impl_wf_ty T "4" by fastforce
  then obtain k' where K: "toVal3210 k = Inr (Inr (Inr k'))" using C0Inrrr by auto
  have "count_level_map_ty (ty_of_val v) = 1" using assms wf_impl_wf_ty T "4" by force
  then obtain v' where V: "toVal3210 v = Inr (Inr (Inl v'))" using assms wf_impl_wf_ty C1Inrrl by blast
  show ?thesis using assms wf_impl_wf_ty K V "4" by (simp add: toVal3210_inj)
next
  case (5 f tk tv)
  then have T: "(tk, tv) = ((ty_of_val k), (ty_of_val v))" using assms by auto
  have "count_level_map_ty (ty_of_val k) = 1" using assms wf_impl_wf_ty T "5" by fastforce
  then obtain k' where K: "toVal3210 k = Inr (Inr (Inl k'))" using assms C1Inrrl wf_impl_wf_ty by blast
  have "count_level_map_ty (ty_of_val v) \<le> 1" using assms wf_impl_wf_ty T "5" by force
  then obtain v' where V: "toVal3210 v = Inr (Inr v')" using assms wf_impl_wf_ty C1Inrrl
    by (cases v; fastforce)
  show ?thesis using assms wf_impl_wf_ty K V "5" by (simp add: toVal3210_inj valBij)
next
  case (6 f tk tv)
  then have T: "(tk, tv) = ((ty_of_val k), (ty_of_val v))" using assms by auto
  have "count_level_map_ty (ty_of_val k) \<le> 1" using assms wf_impl_wf_ty T "6" by fastforce
  then obtain k' where K: "toVal3210 k = Inr (Inr k')" using assms wf_impl_wf_ty C1Inrrl
    by (cases k; fastforce)
  have "count_level_map_ty (ty_of_val v) = 2" using assms wf_impl_wf_ty T "6" by force
  then obtain v' where V: "toVal3210 v = Inr (Inl v')" using assms wf_impl_wf_ty C2Inrl
    by (cases v; fastforce)
  show ?thesis using assms wf_impl_wf_ty K V "6" by (simp add: toVal3210_inj valBij)
next
  case (7 f tk tv)
  then have T: "(tk, tv) = ((ty_of_val k), (ty_of_val v))" using assms by auto
  have "count_level_map_ty (ty_of_val k) = 2" using assms wf_impl_wf_ty T "7" by fastforce
  then obtain k' where K: "toVal3210 k = Inr (Inl k')" using assms wf_impl_wf_ty C2Inrl
    by (cases k; fastforce)
  have "count_level_map_ty (ty_of_val v) \<le> 2" using assms wf_impl_wf_ty T "7" by force
  then obtain v' where V: "toVal3210 v = Inr v'" using assms wf_impl_wf_ty C2Inrl C1Inrrl
    apply (cases v; simp) by fastforce
  show ?thesis using assms wf_impl_wf_ty K V "7" by (simp add: toVal3210_inj valBij)
next
  case (8 f tk tv)
  then have T: "(tk, tv) = ((ty_of_val k), (ty_of_val v))" using assms by auto
  have "count_level_map_ty (ty_of_val k) \<le> 2" using assms wf_impl_wf_ty T "8" by fastforce
  then obtain k' where K: "toVal3210 k = Inr k'" using assms wf_impl_wf_ty C2Inrl C1Inrrl
    apply (cases k; simp) by fastforce
  have "count_level_map_ty (ty_of_val v) = 3" using assms wf_impl_wf_ty T "8" by force
  then obtain v' where V: "toVal3210 v = Inl v'" using assms wf_impl_wf_ty C3Inl
    apply (cases v; simp) by fastforce
  show ?thesis using assms wf_impl_wf_ty K V "8" by (simp add: toVal3210_inj valBij)
qed


subsection \<open>Array Axiom Stable\<close>
text \<open>Property to prove:
  y \<noteq> x ==> (m[x] := v)[y] == m[y]
  y \<noteq> x ==> select (store m x v) y = select m y\<close>

lemma ArrayAxStable1Val:
  assumes "M = MapV (Inr (Inr (MapVal f t)))"
  assumes "wf M"
  assumes "wf x"
  assumes "wf y"
  assumes "wf v"
  assumes "x \<noteq> y"
  shows "selectImpl (storeImpl M x v) y = selectImpl M y"
  apply (cases "(toVal3210 M, toVal3210 x, toVal3210 v)" rule: storeImplAux.cases; (simp add: assms))
  apply (cases y rule: toVal3210.cases; simp)
   apply (metis assms(6) toVal3210.simps(1) toVal3210_inj)
  by (metis assms(6) toVal3210.simps(2) toVal3210_inj)

lemma ArrayAxStable3Key:
  assumes "M = MapV (Inl (MapVal f t))"
  assumes "wf M"
  assumes "wf x"
  assumes "wf y"
  assumes "wf v"
  assumes "x \<noteq> y"
  shows "selectImpl (storeImpl M x v) y = selectImpl M y"
  apply (cases "(toVal3210 M, toVal3210 x, toVal3210 v)" rule: storeImplAux.cases; (simp add: assms))
  apply (cases y rule: toVal3210.cases; simp)
     apply (metis assms(6) toVal3210.simps(1) toVal3210_inj)
     apply (metis assms(6) toVal3210.simps(2) toVal3210_inj)
     apply (metis assms(6) toVal3210.simps(3) toVal3210_inj)
     apply (metis assms(6) toVal3210.simps(4) toVal3210_inj)
done

lemma ArrayAxStableLitV: "selectImpl (storeImpl (LitV l) x v) y = selectImpl (LitV l) y"
  by auto

lemma ArrayAxStable:
  assumes "wf M"
  assumes "wf x"
  assumes "wf y"
  assumes "wf v"
  assumes "x \<noteq> y"
  shows "selectImpl (storeImpl M x v) y = selectImpl M y"
  apply (cases "(toVal3210 M, toVal3210 x, toVal3210 v)" rule: storeImplAux.cases; (simp add: assms);
      cases y rule: toVal3210.cases; (simp add: valBij))
     apply (metis assms(5) toVal3210.simps toVal3210_inj)+
  done


subsection \<open>Array Axiom Extensionality\<close>
text \<open>Property to prove: (\<forall>k. m[k] == n[k]) <==> Eq m n\<close>

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
        using "1" InrrlC1 assms(1) toVal3210.simps(3) wf_impl_wf_ty by blast
      then have "count_level_map_ty (ty_of_val (MapV n)) = 1"
        using assms(4) by argo
      then obtain n' where "n = Inr (Inr n')"
        using C1Inrrl assms(2) toVal3210_inj val.inject(3) val3ToValn.simps(3) valBij
            wf.simps wf_impl_wf_ty by metis
      then show ?thesis
      proof (cases m')
        case (MapVal m'' tm)
        then show ?thesis
        proof (cases n')
          case (MapVal n'' tn)
          have "tm = tn" using assms(4) 1 MapVal \<open>m' = MapVal m'' tm\<close>
            by (metis \<open>n = Inr (Inr n')\<close> prod.collapse ty.inject(4) ty321.simps(1) tyL.simps(1)
                type_of_val.simps(3))
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
            by (metis \<open>n = Inr (Inr n')\<close> prod.collapse ty.inject(4) tyL.simps(2) type_of_val.simps(3))
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
      using "2" InrlC2 assms(1) toVal3210.simps(4) wf_ty.simps(4) wf_impl_wf_ty
      by fastforce
    then have "count_level_map_ty (ty_of_val (MapV n)) = 2"
      using assms(4) by argo
    then obtain n' where N: "n = Inr (Inl n')"
      using C2Inrl assms(2) toVal3210_inj val.inject(3) val3ToValn.simps(4) valBij
      by (metis wf_impl_wf_ty)
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
      using "3" InlC3 assms(1) toVal3210.simps(5) wf_ty.simps(5) wf_impl_wf_ty by blast
    then have "count_level_map_ty (ty_of_val (MapV n)) = 3"
      using assms(4) by argo
    then obtain n' where N: "n = Inl n'"
      using C3Inl assms toVal3210_inj val.inject(3) val3ToValn.simps(5) valBij
      by (metis wf_impl_wf_ty)
    then show ?thesis 
      using assms(3,4) 3 N apply (cases m'; cases n')
      apply (auto simp: fun_eq_iff dest: spec[of _ "Inr _"])
      apply (metis old.sum.distinct(1) selectImplAux.simps(7,8))
      apply (metis selectImplAux.simps(7,8) sum.distinct(1))
      by (metis selectImplAux.simps(8) sum.sel(2))
  qed
qed


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