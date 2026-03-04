section \<open>Instantiation Example for MapV\<close>

theory MapExample
  imports Semantics
begin

subsection \<open>Type Definition\<close>

datatype ('k, 'p) L =
  MapVal "'p \<Rightarrow> ('k, 'p) L" "ty \<times> ty" |  MapKey "'k \<Rightarrow> 'p" "ty \<times> ty"

(* user needs to instantiate how many nesting levels to support *)

(* (type::((('a)val) => (closed_ty))) *)
datatype 'a val0 = LitV0 lit | AbsV0 (the_absv: 'a)

type_synonym 'a val1 = "('a val0, 'a val0) L"
type_synonym 'a val10 = "'a val1 + 'a val0"
type_synonym 'a val2 = "('a val1, 'a val10) L"
type_synonym 'a val210 = "'a val2 + 'a val1 + 'a val0"
type_synonym 'a val3 = "('a val2, 'a val210) L"
type_synonym 'a val3210 = "'a val3 + 'a val210"
type_synonym 'a val321 = "'a val3 + 'a val2 + 'a val1"
type_synonym 'a valn = "('a, 'a val321) val"  (* do not inlcude val0! *)


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

abbreviation mg3 :: "'a val3" where "mg3 \<equiv> MapKey (undefined(m22 := Inr (Inl  m11))) (TMap TT TT, TT)"
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

lemma "selectImpl mg4 m24 = (MapV (Inr (Inr (MapKey (undefined(IntV 3 := IntV 2)) (TT, TT)))))" by simp


subsection \<open>Helper Case Distinction\<close>
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


subsection \<open>Type Of Val\<close>

fun tyL where "tyL (MapVal _ (tk, tv)) = (tk, tv)" | "tyL (MapKey _ (tk, tv)) = (tk, tv)"

fun ty321 :: "'a val3 + 'a val2 + 'a val1 \<Rightarrow> ty \<times> ty" where
    "ty321 (Inr (Inr m)) = tyL m"
  | "ty321 (Inr (Inl m)) = tyL m"
  | "ty321 (Inl m) = tyL m"

instantiation L :: (type, type) mapval begin
  fun mapval_ty_L where "mapval_ty_L x = tyL x"
  instance .. end

instantiation sum :: (mapval, mapval) mapval begin
  primrec mapval_ty_sum :: "'a + 'b \<Rightarrow> ty \<times> ty" where
      "mapval_ty_sum (Inl x) = mapval_ty x"
    | "mapval_ty_sum (Inr x) = mapval_ty x"
  instance .. end

lemma mapval_ty_eq_ty321: "mapval_ty = ty321"
  apply (rule, rename_tac x)
  by (case_tac x rule: ty321.cases; simp)

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


subsection \<open>Store\<close>

(* takes long time to proof, 20s *)
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

fun storeImpl :: "'a::absval valn \<Rightarrow> 'a valn \<Rightarrow> 'a valn \<Rightarrow> 'a valn" where
  "storeImpl m k v = (if type_of_val m = TMap (type_of_val k) (type_of_val v)
    then val3ToValn (storeImplAux (toVal3210 m) (toVal3210 k) (toVal3210 v))
    else m)"

(* examples *)
lemma "type_of_val (LitV (LInt 42)) = TT" by simp
lemma "val_ty (type_of_val mg4) = TT" by simp
lemma "selectImpl (storeImpl mg4 m24 (LitV (LInt 42))) m24
  = (LitV (LInt 42))" by simp


subsection \<open>Well Formedness\<close>

(* TODO: default_value:
(\<forall>k. wf k \<or> (selectImpl m k) = default_of_ty (val_ty (type_of_val m))); *)
inductive wf where
    wfLitV: "wf (LitV v)" | wfAbsV: "wf (AbsV v)" |
    wfMapV: "\<lbrakk> wf_ty m;  (\<forall>k. wf (selectImpl m k));
      (\<forall>k. wf_ty k \<and> type_of_val k = key_ty (type_of_val m) \<longrightarrow> type_of_val (selectImpl m k) = val_ty (type_of_val m))
      \<rbrakk> \<Longrightarrow> wf m"


text \<open>Lemma for return value of invalid select\<close>
lemma wfundef: "(wf (val3ToValn (Inr (Inr (Inr undefined)))))"
  by (metis wfAbsV wfLitV val0.exhaust val3ToValn.simps(1,2))


subsubsection "Bijection between count_level_map_ty and sum type levels"

lemma C0Inrrr:
  assumes "count_level_map_ty (type_of_val v) = 0"
  shows "\<exists>v'. toVal3210 v = Inr (Inr (Inr v'))"
  apply (cases v)
    apply auto
  by (metis assms map_level_gt_0 not_one_le_zero
      type_of_val.simps(3))

lemma InrrrC0:
  assumes "toVal3210 v = Inr (Inr (Inr v'))"
  shows "count_level_map_ty (type_of_val v) = 0"
  using assms count_level_map_ty.simps(4) toVal3210.elims by force

lemma InrrlC1:
  assumes "wf_ty v"
  assumes "toVal3210 v = Inr (Inr (Inl v'))"
  shows "count_level_map_ty (type_of_val v) = 1"
  apply (cases v rule: toVal3210.cases)
  using assms apply auto
  apply (cases v') using assms
  by fastforce+

lemma C1Inrrl:
  assumes "wf_ty v"
  assumes "count_level_map_ty (type_of_val v) = 1"
  shows "\<exists>v'. toVal3210 v = Inr (Inr (Inl v'))"
  apply (cases v rule: toVal3210.cases)
  using assms apply auto
  apply (case_tac m) using assms apply auto
  apply (case_tac m) using assms apply auto
done

lemma InrlC2:
  assumes "wf_ty v"
  assumes "toVal3210 v = Inr (Inl v')"
  shows "count_level_map_ty (type_of_val v) = 2"
  apply (cases v rule: toVal3210.cases)
  using assms apply auto
  apply (cases v') using assms
  by fastforce+

lemma C2Inrl:
  assumes "wf_ty v"
  assumes "count_level_map_ty (type_of_val v) = 2"
  shows "\<exists>v'. toVal3210 v = Inr (Inl v')"
  apply (cases v rule: toVal3210.cases)
  using assms apply auto
  apply (case_tac m) using assms apply auto
  apply (case_tac m) using assms apply auto
  done

lemma InlC3:
  assumes "wf_ty v"
  assumes "toVal3210 v = (Inl v')"
  shows "count_level_map_ty (type_of_val v) = 3"
  apply (cases v rule: toVal3210.cases)
  using assms apply auto
  apply (cases v') using assms
  by fastforce+

lemma C3Inl:
  assumes "wf_ty v"
  assumes "count_level_map_ty (type_of_val v) = 3"
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

lemma VTAdd1: "val_ty (type_of_val vAdd1) = (TPrim TInt)" by simp

lemma KTAdd1: "key_ty (type_of_val vAdd1) = (TPrim TInt)" by simp

lemma type_of_val_Int: "type_of_val k = (TPrim TInt) \<longrightarrow> (\<exists>i. k = LitV (LInt i))"
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
  assumes "type_of_val k = (TPrim TInt)"
  shows "type_of_val (selectImpl vAdd1 k) = (TPrim TInt)"
  using assms type_of_val_Int by fastforce

lemma HH: "(\<forall>k. (wf_ty k \<and> type_of_val k = key_ty (type_of_val vAdd1)
    \<longrightarrow> type_of_val (selectImpl vAdd1 k) = val_ty (type_of_val vAdd1)))"
  using VTAdd1 KTAdd1 H2 by auto

lemma vAdd1wfSelect: "wf (selectImpl vAdd1 k)"
  apply (cases k rule: toVal3210.cases; simp add: wfundef)
      apply (case_tac v; simp add: wfundef)
        apply (simp add: wfLitV)
  done

lemma wf_vAdd1: "wf vAdd1" using VTAdd1 HH vAdd1wfSelect
  using wfMapV[of vAdd1] by force


subsubsection \<open>Well formdness of a higher order map\<close>
(* TODO: I actually want to only assume wf (MapV (Inr (Inr (MapKey (f) ty)))) *)
fun hof where "hof (MapKey f ty) = (case wf (MapV (Inr (Inr (MapKey (fAdd1 \<circ> f) ty)))) of True \<Rightarrow> Inl (MapKey (fAdd1 \<circ> f) ty) | False \<Rightarrow> Inl mAdd1)" | "hof _ = Inl mAdd1"
abbreviation TMII where "TMII \<equiv> TMap (TPrim TInt) (TPrim TInt)"
abbreviation hom :: "'a::absval val2" where "hom \<equiv> MapKey hof (TMII, TMII)"
abbreviation homV :: "'a::absval valn" where "homV \<equiv> MapV (Inr (Inl hom))"

lemma "wf_ty homV" by auto

lemma "(val_ty (type_of_val homV) = TMII)" by simp

lemma "(key_ty (type_of_val homV) = TMII)" by simp

lemma "type_of_val k = TMII \<longrightarrow> (\<exists>k'. k = MapV k')" apply (cases k) by auto

lemma kTMII:
  assumes "wf_ty k"
  assumes "type_of_val k = TMII"
  shows "\<exists>f. k = MapV (Inr (Inr (MapKey f (TT, TT))))"
proof -
  have "count_level_map_ty (type_of_val k) = 1" using assms by simp
  then obtain k' where "toVal3210 k = Inr (Inr (Inl k'))" using C1Inrrl assms by blast
  then have K: "k = MapV (Inr (Inr k'))" using toVal3210.elims by auto
  then have "wf_L 1 k'" using assms by force
  then show ?thesis
    apply (cases k')
    using K assms(2) by auto
qed

lemma wff:
  assumes "wf_ty k \<and> type_of_val k = TMII"
  shows "type_of_val (selectImpl homV k) = TMII"
proof -
  obtain f where K: "k = MapV (Inr (Inr (MapKey f (TT, TT))))"
    using assms kTMII by auto
  then have S: "selectImpl homV k = val3ToValn (Inr (Inr (hof (MapKey f (TT, TT)))))"
    by auto
  have "wf_L 1 (MapKey f (TT, TT))" using assms K by simp
  moreover have "type_of_val (MapV (Inr (Inr (MapKey f (TT, TT))))) = TMII" using assms K by simp
  then show ?thesis
    using S
    apply (cases "wf (MapV (Inr (Inr (MapKey (fAdd1 \<circ> f) (TT, TT)))))")
    by auto
qed

lemma vhomVwfSelect: "wf (selectImpl homV k)"
  apply (cases k rule: toVal3210.cases; simp add: wfundef)
      apply (case_tac m; auto)
  using H2 vAdd1wfSelect wf.simps apply force
  apply (smt (z3) H2 KTAdd1 One_nat_def VTAdd1 add_diff_cancel_left'
      count_level_map_ty.simps(3) le_numeral_extra(3) plus_1_eq_Suc vAdd1wfSelect
      val3ToValn.simps(3) wfMapV wf_L.simps(1) wf_ty.simps(3))
  done

lemma "wf homV" using wff vhomVwfSelect wf.simps[of homV] by auto

lemma wf_impl_wf_ty: "wf k \<Longrightarrow> wf_ty k" using wf.cases by force


subsubsection \<open>Some more general wf properties\<close>

(* conclude Isabelle type from key of a select assuming wf and typed *)
lemma
  assumes "wf (MapV (Inl (MapKey f ty)))"
  assumes "wf k"
  assumes "type_of_val k = key_ty (type_of_val (MapV (Inl (MapKey f ty))))"
  shows "\<exists>k'. toVal3210 k = Inr (Inl k')"
proof -
  have "count_level_map_ty (type_of_val (MapV (Inl (MapKey f ty)))) = 3"
    using InlC3 wf.simps assms(1) toVal3210.simps wf_impl_wf_ty by force
  then have "count_level_map_ty (key_ty (type_of_val (MapV (Inl (MapKey f ty))))) = 2"
    using assms(1) wf_L.elims(2) wf_impl_wf_ty by fastforce
  then have "count_level_map_ty (type_of_val k) = 2" using assms by auto
  then show ?thesis using C2Inrl using assms(2) wf_impl_wf_ty by auto
qed


subsection \<open>Array Axiom Update\<close>
text \<open>Property to prove: (m[k] := v)[k] == v or select (store m k v) k = v\<close>

lemma ArrayAxUpdate:
  assumes "wf M"
  assumes "wf k"
  assumes "wf v"
  assumes "type_of_val M = TMap (type_of_val k) (type_of_val v)"
  shows "selectImpl (storeImpl M k v) k = v"
proof (cases M rule: ValnCases)
  case (1 v)
  then show ?thesis using assms by force
next
  case (2 v)
  then show ?thesis using assms by force
next
  case (3 f tk tv)  (* M = MapV (Inr (Inr (MapKey f (tk, tv))))  *)
  have C: "count_level_map_ty (type_of_val k) = 0  \<and>  count_level_map_ty (type_of_val v) \<le> 0"
    using assms wf_impl_wf_ty "3" by fastforce
  obtain k' where K: "toVal3210 k = Inr (Inr (Inr k'))"
    using assms wf_impl_wf_ty C3Inl C2Inrl C1Inrrl C0Inrrr C
    by (cases k; simp)
  obtain v' where V: "toVal3210 v = Inr (Inr (Inr v'))"
    using assms wf_impl_wf_ty C3Inl C2Inrl C1Inrrl C0Inrrr C
    by (cases v; simp)
  show ?thesis using assms wf_impl_wf_ty K V "3" by (simp add: toVal3210_inj valBij)
next
  case (4 f tk tv)  (* M = MapV (Inr (Inr (MapVal f (tk, tv)))) *)
  have C: "count_level_map_ty (type_of_val k) \<le> 0  \<and>  count_level_map_ty (type_of_val v) = 1"
    using assms wf_impl_wf_ty "4" by fastforce
  obtain k' where K: "toVal3210 k = Inr (Inr (Inr k'))"
    using assms wf_impl_wf_ty C3Inl C2Inrl C1Inrrl C0Inrrr C
    by (cases k; simp)
  obtain v' where V: "toVal3210 v = Inr (Inr (Inl v'))"
    using assms wf_impl_wf_ty C3Inl C2Inrl C1Inrrl C0Inrrr C
    apply (cases v; simp) by fastforce
  show ?thesis using assms wf_impl_wf_ty K V "4" by (simp add: toVal3210_inj valBij)
next
  case (5 f tk tv)
  have C: "count_level_map_ty (type_of_val k) = 1  \<and>  count_level_map_ty (type_of_val v) \<le> 1"
    using assms wf_impl_wf_ty "5" by fastforce
  obtain k' where K: "toVal3210 k = Inr (Inr (Inl k'))"
    using assms wf_impl_wf_ty C3Inl C2Inrl C1Inrrl C0Inrrr C
    apply (cases k; simp) by fastforce
  obtain v' where V: "toVal3210 v = Inr (Inr v')"
    using assms wf_impl_wf_ty C3Inl C2Inrl C1Inrrl C0Inrrr C
    apply (cases v; simp) by fastforce
  show ?thesis using assms wf_impl_wf_ty K V "5" by (simp add: toVal3210_inj valBij)
next
  case (6 f tk tv)
  have C: "count_level_map_ty (type_of_val k) \<le> 1  \<and>  count_level_map_ty (type_of_val v) = 2"
    using assms wf_impl_wf_ty "6" by fastforce
  obtain k' where K: "toVal3210 k = Inr (Inr k')"
    using assms wf_impl_wf_ty C3Inl C2Inrl C1Inrrl C0Inrrr C
    apply (cases k; simp) by fastforce
  obtain v' where V: "toVal3210 v = Inr (Inl v')"
    using assms wf_impl_wf_ty C3Inl C2Inrl C1Inrrl C0Inrrr C
    apply (cases v; simp) by fastforce
  show ?thesis using assms wf_impl_wf_ty K V "6" by (simp add: toVal3210_inj valBij)
next
  case (7 f tk tv)
  have C: "count_level_map_ty (type_of_val k) = 2  \<and>  count_level_map_ty (type_of_val v) \<le> 2"
    using assms wf_impl_wf_ty "7" by fastforce
  obtain k' where K: "toVal3210 k = Inr (Inl k')"
    using assms wf_impl_wf_ty C3Inl C2Inrl C1Inrrl C0Inrrr C
    apply (cases k; simp) by fastforce
  obtain v' where V: "toVal3210 v = Inr v'"
    using assms wf_impl_wf_ty C3Inl C2Inrl C1Inrrl C0Inrrr C
    apply (cases v; simp) by fastforce
  show ?thesis using assms wf_impl_wf_ty K V "7" by (simp add: toVal3210_inj valBij)
next
  case (8 f tk tv)
  have C: "count_level_map_ty (type_of_val k) \<le> 2  \<and>  count_level_map_ty (type_of_val v) = 3"
    using assms wf_impl_wf_ty "8" by fastforce
  obtain k' where K: "toVal3210 k = Inr k'"
    using assms wf_impl_wf_ty C3Inl C2Inrl C1Inrrl C0Inrrr C
    apply (cases k; simp) by fastforce
  obtain v' where V: "toVal3210 v = Inl v'"
    using assms wf_impl_wf_ty C3Inl C2Inrl C1Inrrl C0Inrrr C
    apply (cases v; simp) by fastforce
  show ?thesis using assms wf_impl_wf_ty K V "8" by (simp add: toVal3210_inj valBij)
qed


subsection \<open>Array Axiom Stable\<close>
text \<open>Property to prove:
  y \<noteq> x ==> (m[x] := v)[y] == m[y]
  y \<noteq> x ==> select (store m x v) y = select m y\<close>

lemma ArrayAxStable:
(*  apparently not needed
  assumes "wf M"
  assumes "wf x"
  assumes "wf y"
  assumes "wf v"
*)
  assumes "x \<noteq> y"
  shows "selectImpl (storeImpl M x v) y = selectImpl M y"
  apply (cases "(toVal3210 M, toVal3210 x, toVal3210 v)" rule: storeImplAux.cases; (simp add: assms);
      cases y rule: toVal3210.cases; (simp add: valBij))
     apply (metis assms toVal3210.simps toVal3210_inj)+
  done


subsection \<open>Array Axiom Extensionality\<close>
text \<open>Property to prove: (\<forall>k. m[k] == n[k]) <==> Eq m n\<close>

subsubsection \<open>Extensionality\<close>
lemma extensionalityAux:
  assumes "wf (MapV m)"
  assumes "wf (MapV n)"
  assumes "selectImplAux (toVal3210 (MapV m)) = selectImplAux (toVal3210 (MapV n))"
  assumes "type_of_val (MapV m) = type_of_val (MapV n)"
  shows "m = n"
  proof (cases m rule: ty321.cases)
    case (1 m')
    then show ?thesis
    proof -
      have "count_level_map_ty (type_of_val (MapV m)) = 1"
        using "1" InrrlC1 assms(1) toVal3210.simps(3) wf_impl_wf_ty by fastforce
      then have "count_level_map_ty (type_of_val (MapV n)) = 1"
        using assms(4) by simp
      then obtain n' where "n = Inr (Inr n')"
        using C1Inrrl assms(2) toVal3210_inj val.inject(3) val3ToValn.simps(3) valBij
            wf_impl_wf_ty by metis
      then show ?thesis
      proof (cases m')
        case (MapVal m'' tm)
        then show ?thesis
        proof (cases n')
          case (MapVal n'' tn)
          have "tm = tn" using assms(4) 1 MapVal \<open>m' = MapVal m'' tm\<close>
            by (metis \<open>n = Inr (Inr n')\<close> prod.collapse ty.inject(4) ty321.simps(1) tyL.simps(1)
                type_of_val.simps(3) mapval_ty_eq_ty321)
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
            by (metis \<open>n = Inr (Inr n')\<close> prod.collapse ty.inject(4) tyL.simps(2) type_of_val.simps(3) mapval_ty_eq_ty321)
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
    have "count_level_map_ty (type_of_val (MapV m)) = 2"
      using "2" InrlC2 assms(1) toVal3210.simps(4) wf_ty.simps(4) wf_impl_wf_ty
      by fastforce
    then have "count_level_map_ty (type_of_val (MapV n)) = 2"
      using assms(4) by simp
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
    have "count_level_map_ty (type_of_val (MapV m)) = 3"
      using "3" InlC3 assms(1) toVal3210.simps(5) wf_ty.simps(5) wf_impl_wf_ty by fastforce
    then have "count_level_map_ty (type_of_val (MapV n)) = 3"
      using assms(4) by simp
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


lemma extensionalityMapV:
  assumes "wf (MapV m)"
  assumes "wf (MapV n)"
  assumes "type_of_val (MapV m) = type_of_val (MapV n)"
  assumes "selectImpl (MapV m) = selectImpl (MapV n)"
  shows "m = n"
  by (metis (no_types, lifting) ext extensionalityAux assms(1,2,3,4) selectImpl.simps
      valBij)

lemma extensionalityMapV:
  assumes "wf (MapV m)"
  assumes "wf (MapV n)"
  assumes "type_of_val (MapV m) = type_of_val (MapV n)"
  assumes "\<forall>k. (wf k \<longrightarrow> selectImpl (MapV m) k = selectImpl (MapV n) k)"
  shows "m = n" oops  (* actually what we want, but not true *)


subsection \<open>Select & Store is closed under wf\<close>

lemma selectClosedWf:
  assumes "wf m"
  (* assumes "wf k" *)  (* not needed *)
  shows "wf (selectImpl m k)"
  by (metis wf.cases assms(1) selectImpl.elims selectImplAux.simps(1,2) toVal3210.simps(1,2)
      wfundef)


lemma storePreserveTy:
  assumes "wf m" "wf k" "wf v"
  assumes "type_of_val m = TMap (type_of_val k) (type_of_val v)"
  shows "type_of_val m = type_of_val (storeImpl m k v)"
  by (cases m rule: ValnCases;
      (simp add: assms);
      cases "((toVal3210 m), (toVal3210 k), (toVal3210 v))" rule: storeImplAux.cases;
      (simp add: assms))

lemma storeClosedWf3:
  assumes "wf m" "wf k" "wf v"
  assumes "type_of_val m = TMap (type_of_val k) (type_of_val v)"
  assumes "wf_ty x" "type_of_val x  = key_ty (type_of_val (storeImpl m k v))"
  shows "type_of_val (selectImpl (storeImpl m k v) x) = val_ty (type_of_val (storeImpl m k v))"
proof -
  have "type_of_val x = key_ty (type_of_val m)" using storePreserveTy assms by metis
  then show "type_of_val (selectImpl (storeImpl m k v) x) = val_ty (type_of_val (storeImpl m k v))"
    apply (cases "x = k")
     apply (simp add: assms(4))
    using storePreserveTy ArrayAxUpdate assms apply simp
    apply (smt (z3) ArrayAxUpdate selectImpl.simps storeImpl.simps storePreserveTy
        val_ty.simps(1))
    by (metis (no_types, opaque_lifting) ArrayAxStable InrrrC0 assms(1,2,3,4,5)
        count_level_map_ty.simps(3) map_level_gt_0 not_one_le_zero storePreserveTy
        toVal3210.simps(2) type_of_val.simps(1) wf.cases)
qed

lemma storeClosedWf2:
  assumes "wf m" "wf k" "wf v"
  assumes "type_of_val m = TMap (type_of_val k) (type_of_val v)"
  shows "(\<forall>k'. wf (selectImpl (storeImpl m k v) k'))"
  by (metis ArrayAxStable ArrayAxUpdate assms(1,2,3,4) selectClosedWf)

lemma storeClosedWf1:
  assumes "wf m" "wf k" "wf v"
  assumes "type_of_val m = TMap (type_of_val k) (type_of_val v)"
  shows "wf_ty (storeImpl m k v)"
  using assms wf_impl_wf_ty apply simp
  (* slow proof, takes 10s *)
  by (cases m rule: ValnCases; simp;
     cases "(toVal3210 k)" rule: val3ToValn.cases;
     cases "(toVal3210 v)" rule: val3ToValn.cases; fastforce)

lemma storeClosedWf:
  assumes "wf m"
  assumes "wf k"
  assumes "wf v"
  shows "wf (storeImpl m k v)"
  using  storeClosedWf1 storeClosedWf2 storeClosedWf3 wfMapV assms
  by (smt (verit) storeImpl.simps)


subsection \<open>Defining well formed type\<close>

text \<open>set for well formed inner map values\<close>
definition wf_map_set :: "'a::absval val321 set" where
  "wf_map_set = {m. wf (MapV m)}"

(* useful bijection lemma between inner and outer wf *)
lemma wf_map_bij: "wf v \<longleftrightarrow> (\<exists>v'. v = LitV v') \<or> (\<exists>v'. v = AbsV v')
  \<or> (\<exists>m'. v = MapV m' \<and> m' \<in> wf_map_set)"
  apply (case_tac v)
  apply (simp add: wfLitV)
  apply (simp add: wfAbsV)
  by (simp add: wf_map_set_def)

text \<open>typdef for well formed inner map values\<close>
(* (overloaded) keyword to allow dependency on avtf *)
typedef (overloaded) 'a::absval wf_maps = "wf_map_set :: 'a::absval val321 set"
proof
  show "(Inr (Inr mAdd1)) \<in> wf_map_set"  (* vAdd1, from earlier, as non-emptiness witness *)
    unfolding wf_map_set_def using wf_vAdd1 by simp
qed

text \<open>wf maps are mapval\<close>
instantiation wf_maps :: (type) mapval begin
  fun mapval_ty_wf_maps where "mapval_ty_wf_maps x = mapval_ty (Rep_wf_maps x)"
  instance .. end

(* see if it works *)
lemma "mapval_ty (Abs_wf_maps (Inr (Inr mAdd1))) = (TT, TT)"
  by (simp add: Abs_wf_maps_inverse wf_map_set_def wf_vAdd1)

text \<open>type for well formed values\<close>
type_synonym 'a wf_val = "('a, 'a wf_maps) val"

text \<open>lift selectImpl & storeImpl\<close>
setup_lifting type_definition_wf_maps

lift_definition wf_select :: "'a::absval wf_val \<Rightarrow> 'a wf_val \<Rightarrow> 'a wf_val"
  is selectImpl
  using selectClosedWf wf_map_bij
  by (metis top1I val.exhaust
      val.pred_inject(2)[of top "\<lambda>uu. uu \<in> wf_map_set"]
      val.pred_inject(3)[of top "\<lambda>uu. uu \<in> wf_map_set"]
      val.pred_rel[of top "\<lambda>uu. uu \<in> wf_map_set" "LitV _"]
      val.rel_inject(1)[of "eq_onp top"
        "eq_onp (\<lambda>uu. uu \<in> wf_map_set)"])

lift_definition wf_store :: "'a::absval wf_val \<Rightarrow> 'a wf_val \<Rightarrow> 'a wf_val \<Rightarrow> 'a wf_val"
  is storeImpl
  using storeClosedWf wf_map_bij
  by (metis top1I val.exhaust
      val.pred_inject(2)[of top "\<lambda>uu. uu \<in> wf_map_set"]
      val.pred_inject(3)[of top "\<lambda>uu. uu \<in> wf_map_set"]
      val.pred_rel[of top "\<lambda>uu. uu \<in> wf_map_set" "LitV _"]
      val.rel_inject(1)[of "eq_onp top"
        "eq_onp (\<lambda>uu. uu \<in> wf_map_set)"])

lift_definition wf_wf :: "'a::absval wf_val \<Rightarrow> bool"
  is wf .

lift_definition type_of_wf_val :: "'a::absval wf_val \<Rightarrow> ty"
  is type_of_val .


subsection \<open>Leammas hold for the new select & store\<close>

lemma wf_wf_val: "wf_wf x"
  apply (cases x)
  apply (simp add: wfLitV wf_wf.rep_eq)
  apply (simp add: wfAbsV wf_wf.rep_eq)
  by (simp add: Rep_wf_maps wf_map_bij wf_wf.rep_eq)


(* Gemini Magic *)

(*
(* 1. Use the .simps fact since you used 'fun' in your instantiation *)
lemma mapval_ty_wf_maps_transfer [transfer_rule]:
  "rel_fun cr_wf_maps (=) mapval_ty mapval_ty"
  unfolding rel_fun_def cr_wf_maps_def
  by (auto simp: mapval_ty_wf_maps.simps)
*)

(* 2. This bridges type_of_val across the lift *)
lemma type_of_val_transfer [transfer_rule]:
  "rel_fun (rel_val (=) cr_wf_maps) (=) type_of_val type_of_val"
  unfolding rel_fun_def cr_wf_maps_def
  apply (rule, rename_tac v_raw, rule, rename_tac v_lift)
  by (case_tac v_raw; case_tac v_lift; auto)

(*
(* 3. THE MISSING LINK: Tell Isabelle that the relation guarantees well-formedness *)
lemma rel_val_cr_wf_implies_wf:
  assumes "rel_val (=) cr_wf_maps raw lift"
  shows "wf raw"
  using assms unfolding cr_wf_maps_def
  using assms rel_funD wf_wf.transfer wf_wf_val by fastforce
*)

(* 4. The Final Proofs *)
lemma Ax1:
  fixes m::"'a::absval wf_val"
  assumes "type_of_val m = TMap (type_of_val k) (type_of_val v)"
  shows "wf_select (wf_store m k v) k = v"
  using assms
  apply transfer
  using ArrayAxUpdate wf_wf_val
  by (metis eq_onp_top_eq_eq val.pred_rel wf_wf.abs_eq)

lemma Ex:
  assumes "m = MapV m' \<and> n = MapV n'"
  assumes "type_of_val m = type_of_val n"
  assumes "wf_select m = wf_select n"
  shows "m = n"
  using assms
  apply transfer
  apply auto[1]
  using extensionalityMapV wf_wf_val
  oops (* not true *)

lemma Ax2_wf_val:
  shows "x = y \<or> wf_select (wf_store m x v) y = wf_select m y"
  by (smt (verit, del_insts) ArrayAxStable Rep_wf_maps_inject id_apply
      map_fun_apply val.inj_map_strong wf_select_def wf_store.rep_eq)


subsection \<open>Using wf type\<close>

(* the absval_ty_fun using class seems to be fixed to the class *)
instantiation unit :: absval begin
  fun absval_ty_unit :: "unit \<Rightarrow> (tcon_id \<times> ty list)" where
    "absval_ty_unit x = (''int_con'', [])"
  instance .. end

lemma "absval_ty () = (''int_con'', [])" by simp

term red_expr
interpretation semantics wf_select wf_store .
term red_expr

end
