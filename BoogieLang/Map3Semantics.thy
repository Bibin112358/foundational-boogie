section \<open>Instantiation Example for MapV with 3 domain nesting levels\<close>

theory Map3Semantics
  imports Semantics VCExprHelper
begin

subsection \<open>Type Definition\<close>

(* A helper datatype that takes a domain as a type parameter and provides
  a function from the domain to the function space itself and the domain*)
datatype 'd L = FunL "'d \<Rightarrow> 'd L + 'd" ty ty

(* user needs to instantiate how many nesting levels to support *)
datatype 'a val0 = LitV0 lit | AbsV0 'a
type_synonym 'a val1 = "'a val0 L"
type_synonym 'a val2 = "('a val1 + 'a val0) L"
type_synonym 'a val3 = "('a val2 + 'a val1 + 'a val0) L"
type_synonym 'a val3210 = "'a val3 + 'a val2 + 'a val1 + 'a val0"
type_synonym 'a val321 = "'a val3 + 'a val2 + 'a val1"
type_synonym 'a valn = "('a, 'a val321) val"  (* do not inlcude val0! *)

(* convenient abbreviations *)
abbreviation InV0 :: "'a val0 \<Rightarrow> 'a val3210" where "InV0 x \<equiv> Inr (Inr (Inr x))"
abbreviation InV1 :: "'a val1 \<Rightarrow> 'a val3210" where "InV1 x \<equiv> Inr (Inr (Inl x))"
abbreviation InV2 :: "'a val2 \<Rightarrow> 'a val3210" where "InV2 x \<equiv> Inr (Inl x)"
abbreviation InV3 :: "'a val3 \<Rightarrow> 'a val3210" where "InV3 x \<equiv> Inl x"
abbreviation InM1 :: "'a val1 \<Rightarrow> 'a val321"  where "InM1 x \<equiv> Inr (Inr x)"
abbreviation InM2 :: "'a val2 \<Rightarrow> 'a val321"  where "InM2 x \<equiv> Inr (Inl x)"
abbreviation InM3 :: "'a val3 \<Rightarrow> 'a val321"  where "InM3 x \<equiv> Inl x"
abbreviation InV10 :: "'a val1 + 'a val0 \<Rightarrow> 'a val3210"
  where "InV10 x \<equiv> Inr (Inr x)"
abbreviation InV210 :: "'a val2 + 'a val1 + 'a val0 \<Rightarrow> 'a val3210"
  where "InV210 x \<equiv> Inr x"


subsection \<open>Type Of Val\<close>

primrec tyL where "tyL (FunL f tk tv) = (tk, tv)"

fun ty321 :: "'a val321 \<Rightarrow> ty \<times> ty" where
    "ty321 (InM1 m) = tyL m"
  | "ty321 (InM2 m) = tyL m"
  | "ty321 (InM3 m) = tyL m"

instantiation L :: (type) mapval begin
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

primrec wf_L where
  "wf_L n (FunL _ tk tv) = (
    (tmap_lvl tk \<le> n-1) \<and> (tmap_lvl tv \<le> n) \<and>
    ((tmap_lvl tk = n-1) \<or> (tmap_lvl tv = n)))"
  (* guarantee highest domain or range on this level *)

fun wf_ty :: "'a valn \<Rightarrow> bool" where
    "wf_ty (LitV v) = True"
  | "wf_ty (AbsV v) = True"
  | "wf_ty (MapV (InM1 m)) = wf_L 1 m"
  | "wf_ty (MapV (InM2 m)) = wf_L 2 m"
  | "wf_ty (MapV (InM3 m)) = wf_L 3 m"

fun dom_ty where "dom_ty m = TMapInv0 (type_of_val m)"
fun ran_ty where "ran_ty m = TMapInv1 (type_of_val m)"

lemma map_level_gt_0: "tmap_lvl (TMap tv tk) \<ge> 1" by auto

subsection \<open>Select\<close>
(* there needs to be as many additional store functions, as there are nesting levels *)
(* user needs to generate these functions (is there a way to make this cleaner, macro?) *)
fun ofValn :: "'a valn \<Rightarrow> 'a val3210" where
    "ofValn (LitV v) = (InV0 (LitV0 v))"
  | "ofValn (AbsV v) = (InV0 (AbsV0 v))"
  | "ofValn (MapV (InM1 m)) = (InV1 m)"
  | "ofValn (MapV (InM2 m)) = (InV2 m)"
  | "ofValn (MapV (InM3 m)) = (InV3 m)"

fun valnOf :: "'a val3210 \<Rightarrow> 'a valn" where
    "valnOf (InV0 (LitV0 v)) = (LitV v)"
  | "valnOf (InV0 (AbsV0 v)) = (AbsV v)"
  | "valnOf (InV1 m) = (MapV (InM1 m))"
  | "valnOf (InV2 m) = (MapV (InM2 m))"
  | "valnOf (InV3 m) = (MapV (InM3 m))"

fun selectImplAux :: "'a::absval val3210 \<Rightarrow> 'a val3210 \<Rightarrow> 'a val3210" where
    "selectImplAux (InV0 (LitV0 v)) _ = (InV0 undefined)"
  | "selectImplAux (InV0 (AbsV0 v)) _ = (InV0 undefined)"
  | "selectImplAux (InV1 (FunL m _ _)) (InV0 k) = InV10 (m k)"
  | "selectImplAux (InV2 (FunL m _ _)) (InV10 k) = InV210 (m k)"
  | "selectImplAux (InV3 (FunL m _ _)) (InV210 k) = (m k)"
  | "selectImplAux m _ = ofValn (val_of_type (dom_ty (valnOf m)))"

fun selectImpl :: "'a::absval valn \<Rightarrow> 'a valn \<Rightarrow> 'a valn" where
  "selectImpl m k = valnOf (selectImplAux (ofValn m) (ofValn k))"


subsection \<open>Helper Case Distinction\<close>
thm valnOf.cases
lemma ValnCases:
"(\<And>v. x = LitV v \<Longrightarrow> P) \<Longrightarrow>
(\<And>v. x = AbsV v \<Longrightarrow> P) \<Longrightarrow>
(\<And>f tk tv. x = MapV (InM1 (FunL f tk tv)) \<Longrightarrow> P) \<Longrightarrow>
(\<And>f tk tv. x = MapV (InM2 (FunL f tk tv)) \<Longrightarrow> P) \<Longrightarrow>
(\<And>f tk tv. x = MapV (InM3 (FunL f tk tv)) \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis L.exhaust sum.collapse val.exhaust)


subsection \<open>Helper Injectivity Lemmas for ofValn and valnOf\<close>

lemma valBij: "ofValn (valnOf x) = x"
  by (cases x rule: valnOf.cases; simp)

lemma valBij2: "valnOf (ofValn x) = x"
  by (cases x rule: ofValn.cases; simp)

lemma ofValn_inj:
  assumes "ofValn x = ofValn y"
  shows "x = y"
  apply (cases x rule: ofValn.cases; cases y rule: ofValn.cases)
  using assms by auto


subsection \<open>Store\<close>

fun storeImplAux :: "'a val3210 \<Rightarrow> 'a val3210 \<Rightarrow> 'a val3210 \<Rightarrow> 'a val3210" where
    "storeImplAux (InV1 (FunL m tk tv)) (InV0 k) (InV10 v)
      = (InV1 (FunL (m(k := v)) tk tv))"
  | "storeImplAux (InV2 (FunL m tk tv)) (InV10 k) (InV210 v)
      = (InV2 (FunL (m(k := v)) tk tv))"
  | "storeImplAux (InV3 (FunL m tk tv)) (InV210 k) (v)
      = (InV3 (FunL (m(k := v)) tk tv))"
  | "storeImplAux x _ _ = x"

fun storeImpl :: "'a::absval valn \<Rightarrow> 'a valn \<Rightarrow> 'a valn \<Rightarrow> 'a valn" where
  "storeImpl m k v = (if type_of_val m = TMap (type_of_val k) (type_of_val v)
    then valnOf (storeImplAux (ofValn m) (ofValn k) (ofValn v))
    else m)"


subsection \<open>Well Formedness\<close>

inductive wf where
    wfLitV: "wf (LitV v)" | wfAbsV: "wf (AbsV v)" |
    wfMapV: "\<lbrakk> wf_ty m;  (\<forall>k. wf (selectImpl m k));
      (\<forall>k. (\<not>wf k \<or> type_of_val k \<noteq> dom_ty m)
        \<longrightarrow> (selectImpl m k) = val_of_type (ran_ty m));
      (\<forall>k. type_of_val (selectImpl m k) = ran_ty m)
      \<rbrakk> \<Longrightarrow> wf m"

subsubsection \<open>Bijection between tmaplvl and sum type levels\<close>

lemma wf_impl_wf_ty: "wf k \<Longrightarrow> wf_ty k" using wf.cases by force

lemma C0Inrrr:
  assumes "tmap_lvl (type_of_val v) = 0"
  shows "\<exists>v'. ofValn v = Inr (Inr (Inr v'))"
  apply (cases v)
    apply auto
  by (metis assms map_level_gt_0 not_one_le_zero
      type_of_val.simps(3))

lemma InrrrC0:
  assumes "ofValn v = Inr (Inr (Inr v'))"
  shows "tmap_lvl (type_of_val v) = 0"
  using assms tmap_lvl.simps(4) ofValn.elims by force

lemma InrrlC1:
  assumes "wf_ty v"
  assumes "ofValn v = Inr (Inr (Inl v'))"
  shows "tmap_lvl (type_of_val v) = 1"
  apply (cases v rule: ofValn.cases)
  using assms apply auto
  apply (cases v') using assms
  by fastforce+

lemma C1Inrrl:
  assumes "wf_ty v"
  assumes "tmap_lvl (type_of_val v) = 1"
  shows "\<exists>v'. ofValn v = Inr (Inr (Inl v'))"
  apply (cases v rule: ofValn.cases)
  using assms apply auto
  apply (case_tac m) using assms apply auto
  apply (case_tac m) using assms apply auto
done

lemma InrlC2:
  assumes "wf_ty v"
  assumes "ofValn v = Inr (Inl v')"
  shows "tmap_lvl (type_of_val v) = 2"
  apply (cases v rule: ofValn.cases)
  using assms apply auto
  apply (cases v') using assms
  by fastforce+

lemma C2Inrl:
  assumes "wf_ty v"
  assumes "tmap_lvl (type_of_val v) = 2"
  shows "\<exists>v'. ofValn v = Inr (Inl v')"
  apply (cases v rule: ofValn.cases)
  using assms apply auto
  apply (case_tac m) using assms apply auto
  apply (case_tac m) using assms apply auto
  done

lemma InlC3:
  assumes "wf_ty v"
  assumes "ofValn v = (Inl v')"
  shows "tmap_lvl (type_of_val v) = 3"
  apply (cases v rule: ofValn.cases)
  using assms apply auto
  apply (cases v') using assms
  by fastforce+

lemma C3Inl:
  assumes "wf_ty v"
  assumes "tmap_lvl (type_of_val v) = 3"
  shows "\<exists>v'. ofValn v = (Inl v')"
  apply (cases v rule: ofValn.cases)
  using assms apply auto
  apply (case_tac m) using assms apply auto
  apply (case_tac m) using assms apply auto
done


subsubsection \<open>Proving well formdness of a simple map\<close>
fun toVal0 :: "'a valn \<Rightarrow> 'a val0" where "toVal0 (LitV l) = LitV0 l" | "toVal0 _ = undefined"
fun fAdd1 where "fAdd1 (LitV0 (LInt x)) = Inr  (LitV0 (LInt (x+1)))" | "fAdd1 _ = Inr (toVal0 (val_of_type ((TPrim TInt))))"
abbreviation mAdd1 :: "'a::absval val1" where "mAdd1 \<equiv> FunL fAdd1 (TPrim TInt) (TPrim TInt)"
abbreviation vAdd1 :: "'a::absval valn" where "vAdd1 \<equiv> MapV (Inr (Inr mAdd1))"

lemma wfvotTT: "(type_of_val ((val_of_type (TPrim TInt))::'a::absval valn) = (TPrim TInt) \<and> wf ((val_of_type (TPrim TInt))::'a::absval valn))"
  by (metis (mono_tags, lifting) someI_ex tint_intv type_of_lit.simps(2) type_of_val.simps(1)
      val_of_type.simps wfLitV)

lemma mAdd1Typesafe:
  shows "type_of_val (selectImpl vAdd1 k) = (TPrim TInt)"
  apply (cases k rule: ofValn.cases)
  apply (metis (no_types, lifting) fAdd1.elims int_inverse_3 selectImpl.simps selectImplAux.simps(3)
      toVal0.simps(1) ofValn.simps(1,3) type_of_lit.simps(2) type_of_val.simps(1) valnOf.simps(1)
      wfvotTT)
  using wfvotTT tint_intv
  apply (metis (no_types, opaque_lifting) fAdd1.simps(4) selectImpl.simps selectImplAux.simps(3)
      toVal0.simps(1) ofValn.simps(1,3) valnOf.simps(2) valBij valBij2)
  apply (metis dom_ty.elims fst_conv mapval_ty_eq_ty321 selectImpl.simps selectImplAux.simps(11)
      ofValn.simps(3) ty.sel(5) ty321.simps(1) tyL.simps type_of_val.simps(3) valBij2 wfvotTT)
  apply (metis dom_ty.elims fst_conv mapval_ty_eq_ty321 selectImpl.simps selectImplAux.simps(10)
      ofValn.simps(3,4) ty.sel(5) ty321.simps(1) tyL.simps type_of_val.simps(3) valBij2 wfvotTT)
  apply (metis dom_ty.elims fst_conv mapval_ty_eq_ty321 selectImpl.simps selectImplAux.simps(09)
      ofValn.simps(3,5) ty.sel(5) ty321.simps(1) tyL.simps type_of_val.simps(3) valBij2 wfvotTT)
  done

lemma votTTpreserved: "valnOf (Inr (Inr (Inr (toVal0 (val_of_type ((TPrim TInt))))))) = (val_of_type ((TPrim TInt)))"
  by (metis int_inverse_3 toVal0.simps(1) valnOf.simps(1) wfvotTT)

lemma vAdd1defualt: "(\<not>wf k \<or> type_of_val k \<noteq> dom_ty vAdd1) \<Longrightarrow> (selectImpl vAdd1 k) = val_of_type (ran_ty vAdd1)"
  apply (cases "k" rule: ofValn.cases; cases "type_of_val k"; simp) 
      apply (rename_tac v t, case_tac v; simp) using votTTpreserved apply fastforce
  using wfLitV wfAbsV ofValn_inj valBij apply blast
  using votTTpreserved apply auto[1]
  using votTTpreserved apply auto[1]
  using wfLitV wfAbsV ofValn_inj valBij apply blast+
  done

lemma vAdd1wfSelect: "wf (selectImpl vAdd1 k)"
  using mAdd1Typesafe tint_intv wf.simps by blast

lemma wf_vAdd1: "wf vAdd1"
  using vAdd1wfSelect vAdd1defualt mAdd1Typesafe wfMapV[of vAdd1] by auto


subsection \<open>Array Axiom Update\<close>
text \<open>Property to prove: (m[k] := v)[k] == v or select (store m k v) k = v\<close>

lemma ArrayAxUpdate:
  assumes "wf M" "wf k" "wf v"
  assumes "type_of_val M = TMap (type_of_val k) (type_of_val v)"
  shows "selectImpl (storeImpl M k v) k = v"
proof (cases M rule: ValnCases)
  case (1 v)
  then show ?thesis using assms by force
next
  case (2 v)
  then show ?thesis using assms by force
next
  case (3 f tk tv)
  then show ?thesis proof (cases "(tmap_lvl tv \<le> 0)")
    case True
    then have C: "tmap_lvl (type_of_val k) = 0  \<and>  tmap_lvl (type_of_val v) \<le> 0"
      using assms wf_impl_wf_ty "3" by fastforce
    obtain k' where K: "ofValn k = Inr (Inr (Inr k'))"
      using assms wf_impl_wf_ty C3Inl C2Inrl C1Inrrl C0Inrrr C
      by (cases k; simp)
    obtain v' where V: "ofValn v = Inr (Inr (Inr v'))"
      using assms wf_impl_wf_ty C3Inl C2Inrl C1Inrrl C0Inrrr C
      by (cases v; simp)
    show ?thesis using assms wf_impl_wf_ty K V "3" by (simp add: ofValn_inj valBij)
  next
    case False
    then have C: "tmap_lvl (type_of_val k) \<le> 0  \<and>  tmap_lvl (type_of_val v) = 1"
      using assms wf_impl_wf_ty "3" by fastforce
    obtain k' where K: "ofValn k = Inr (Inr (Inr k'))"
      using assms wf_impl_wf_ty C3Inl C2Inrl C1Inrrl C0Inrrr C
      by (cases k; simp)
    obtain v' where V: "ofValn v = Inr (Inr (Inl v'))"
      using assms wf_impl_wf_ty C3Inl C2Inrl C1Inrrl C0Inrrr C
      apply (cases v; simp) by fastforce
    show ?thesis using assms wf_impl_wf_ty K V "3" by (simp add: ofValn_inj valBij)
  qed
next
  case (4 f tk tv)
  then show ?thesis proof (cases "(tmap_lvl tv \<le> 1)")
    case True
    then have C: "tmap_lvl (type_of_val k) = 1  \<and>  tmap_lvl (type_of_val v) \<le> 1"
      using assms wf_impl_wf_ty "4" by fastforce
    obtain k' where K: "ofValn k = Inr (Inr (Inl k'))"
      using assms wf_impl_wf_ty C3Inl C2Inrl C1Inrrl C0Inrrr C
      apply (cases k; simp) by fastforce
    obtain v' where V: "ofValn v = Inr (Inr v')"
      using assms wf_impl_wf_ty C3Inl C2Inrl C1Inrrl C0Inrrr C
      apply (cases v; simp) by fastforce
    show ?thesis using assms wf_impl_wf_ty K V "4" by (simp add: ofValn_inj valBij)
  next
    case False
    then have C: "tmap_lvl (type_of_val k) \<le> 1  \<and>  tmap_lvl (type_of_val v) = 2"
      using assms wf_impl_wf_ty "4" by fastforce
    obtain k' where K: "ofValn k = Inr (Inr k')"
      using assms wf_impl_wf_ty C3Inl C2Inrl C1Inrrl C0Inrrr C
      apply (cases k; simp) by fastforce
    obtain v' where V: "ofValn v = Inr (Inl v')"
      using assms wf_impl_wf_ty C3Inl C2Inrl C1Inrrl C0Inrrr C
      apply (cases v; simp) by fastforce
    show ?thesis using assms wf_impl_wf_ty K V "4" by (simp add: ofValn_inj valBij)
  qed
next
  case (5 f tk tv)
  then show ?thesis proof (cases "(tmap_lvl tv \<le> 2)")
    case True
    then have C: "tmap_lvl (type_of_val k) = 2  \<and>  tmap_lvl (type_of_val v) \<le> 2"
      using assms wf_impl_wf_ty "5" by fastforce
    obtain k' where K: "ofValn k = Inr (Inl k')"
      using assms wf_impl_wf_ty C3Inl C2Inrl C1Inrrl C0Inrrr C
      apply (cases k; simp) by fastforce
    obtain v' where V: "ofValn v = Inr v'"
      using assms wf_impl_wf_ty C3Inl C2Inrl C1Inrrl C0Inrrr C
      apply (cases v; simp) by fastforce
    show ?thesis using assms wf_impl_wf_ty K V "5" by (simp add: ofValn_inj valBij)
  next
    case False
    then have C: "tmap_lvl (type_of_val k) \<le> 2  \<and>  tmap_lvl (type_of_val v) = 3"
      using assms wf_impl_wf_ty "5" by fastforce
    obtain k' where K: "ofValn k = Inr k'"
      using assms wf_impl_wf_ty C3Inl C2Inrl C1Inrrl C0Inrrr C
      apply (cases k; simp) by fastforce
    obtain v' where V: "ofValn v = Inl v'"
      using assms wf_impl_wf_ty C3Inl C2Inrl C1Inrrl C0Inrrr C
      apply (cases v; simp) by fastforce
    show ?thesis using assms wf_impl_wf_ty K V "5" by (simp add: ofValn_inj valBij)
  qed
qed


subsection \<open>Array Axiom Stable\<close>
(*text \<open>Property to prove:
  y \<noteq> x ==> (m[x] := v)[y] == m[y]
  y \<noteq> x ==> select (store m x v) y = select m y\<close>*)

lemma ArrayAxStable:
(*  apparently not needed
  assumes "wf M"
  assumes "wf x"
  assumes "wf y"
  assumes "wf v"
*)
  assumes "x \<noteq> y"
  shows "selectImpl (storeImpl M x v) y = selectImpl M y"
  apply (cases "(ofValn M, ofValn x, ofValn v)" rule: storeImplAux.cases; (simp add: assms);
     cases y rule: ofValn.cases; (simp add: valBij); auto)
     apply (metis assms ofValn.simps ofValn_inj)+
  done


subsection \<open>Array Axiom Extensionality\<close>
(*text \<open>Property to prove: (\<forall>k. m[k] == n[k]) <==> Eq m n\<close>*)

subsubsection \<open>Extensionality\<close>
lemma extensionalityAux:
  assumes "wf (MapV m)" "wf (MapV n)"
  assumes "selectImplAux (ofValn (MapV m)) = selectImplAux (ofValn (MapV n))"
  assumes "type_of_val (MapV m) = type_of_val (MapV n)"
  shows "m = n"
  proof (cases m rule: ty321.cases)
    case (1 m')
    then show ?thesis
    proof -
      have "tmap_lvl (type_of_val (MapV m)) = 1"
        using "1" InrrlC1 assms(1) ofValn.simps(3) wf_impl_wf_ty by fastforce
      then have "tmap_lvl (type_of_val (MapV n)) = 1"
        using assms(4) by simp
      then obtain n' where "n = Inr (Inr n')"
        using C1Inrrl assms(2) ofValn_inj val.inject(3) valnOf.simps(3) valBij
            wf_impl_wf_ty by metis
      then show ?thesis
      proof (cases m')
        case (FunL m'' tmk tmv)
        then show ?thesis
        proof (cases n')
          case (FunL n'' tnk tnv)
          have "(tmk, tmv) = (tnk, tnv)" using assms(4) 1 FunL \<open>m' = FunL m'' tmk tmv\<close>
            by (metis \<open>n = Inr (Inr n')\<close> prod.collapse ty.inject(4) ty321.simps(1) tyL.simps(1)
                type_of_val.simps(3) mapval_ty_eq_ty321)
          moreover have "m'' = n''"
          proof (rule ext)
            fix k show "m'' k = n'' k"
            using assms(3) 1 FunL \<open>m' = FunL m'' tmk tmv\<close> \<open>n' = FunL n'' tnk tnv\<close>
            selectImplAux.simps(3) sum.inject(2) ofValn.simps(3)
            by (metis \<open>n = Inr (Inr n')\<close>)
          qed
          ultimately show ?thesis using 1 FunL \<open>m' = FunL m'' tmk tmv\<close> \<open>n' = FunL n'' tnk tnv\<close>
            using \<open>n = Inr (Inr n')\<close> by force
        qed
      qed
    qed
next
  case (2 m')
  then show ?thesis 
  proof -
    have "tmap_lvl (type_of_val (MapV m)) = 2"
      using "2" InrlC2 assms(1) ofValn.simps(4) wf_ty.simps(4) wf_impl_wf_ty
      by fastforce
    then have "tmap_lvl (type_of_val (MapV n)) = 2"
      using assms(4) by simp
    then obtain n' where N: "n = Inr (Inl n')"
      using C2Inrl assms(2) ofValn_inj val.inject(3) valnOf.simps(4) valBij
      by (metis wf_impl_wf_ty)
    then show ?thesis 
      using assms(3,4) 2 N apply (cases m'; cases n')
      by (auto simp: fun_eq_iff dest: spec[of _ "Inr (Inr _)"])
  qed
next
  case (3 m')
  then show ?thesis 
  proof -
    have "tmap_lvl (type_of_val (MapV m)) = 3"
      using "3" InlC3 assms(1) ofValn.simps(5) wf_ty.simps(5) wf_impl_wf_ty by fastforce
    then have "tmap_lvl (type_of_val (MapV n)) = 3"
      using assms(4) by simp
    then obtain n' where N: "n = Inl n'"
      using C3Inl assms ofValn_inj val.inject(3) valnOf.simps(5) valBij
      by (metis wf_impl_wf_ty)
    then show ?thesis 
      using assms(3,4) 3 N apply (cases m'; cases n')
      by (auto simp: fun_eq_iff dest: spec[of _ "Inr _"])
  qed
qed


lemma extensionalityMapVWeak:
  assumes "wf (MapV m)" "wf (MapV n)"
  assumes "type_of_val (MapV m) = type_of_val (MapV n)"
  assumes "selectImpl (MapV m) = selectImpl (MapV n)"
  shows "m = n"
  by (metis (no_types, lifting) ext extensionalityAux assms(1,2,3,4) selectImpl.simps
      valBij)


lemma extensionalityMapV:
  assumes "wf (MapV m)" "wf (MapV n)"
  assumes "type_of_val (MapV m) = type_of_val (MapV n)"
  assumes "\<forall>k. (wf k \<and> type_of_val k = dom_ty (MapV m)) \<longrightarrow> selectImpl (MapV m) k = selectImpl (MapV n) k"
  shows "m = n"
proof -
  have "\<And>k. selectImpl (MapV m) k = selectImpl (MapV n) k"
  proof -
    fix k show "selectImpl (MapV m) k = selectImpl (MapV n) k"
    proof (cases "(wf k \<and> type_of_val k = dom_ty (MapV m))")
      case True
      then show ?thesis using assms(4) by force
    next
      case False
      then have PM: "(\<not>wf k \<or> type_of_val k \<noteq> dom_ty (MapV m))" by simp
      then have M: "(selectImpl (MapV m) k) = val_of_type (ran_ty (MapV m))"
        using assms(1) wf.cases by fastforce
      have "(\<not>wf k \<or> type_of_val k \<noteq> dom_ty (MapV n))"
        using assms PM by simp
      then have N: "(selectImpl (MapV n) k) = val_of_type (ran_ty (MapV n))"
        using assms(2) wf.cases by fastforce
      then show ?thesis using M N assms by auto
    qed
  qed
  then show ?thesis using extensionalityMapVWeak using assms(1,2,3) by blast
qed


subsection \<open>Select and Store is closed under wf\<close>

text \<open>Lemma for return value of invalid select\<close>
lemma wf_undefined: "(wf (valnOf (InV0 undefined)))"
  by (metis wfAbsV wfLitV val0.exhaust valnOf.simps(1,2))

lemma selectClosedWf:
  assumes "wf m"
  (* assumes "wf k" *)  (* not needed *)
  shows "wf (selectImpl m k)"
  by (metis wf.cases assms(1) selectImpl.elims selectImplAux.simps(1,2) ofValn.simps(1,2) wf_undefined)

lemma storePreserveTy:
  shows "type_of_val m = type_of_val (storeImpl m k v)"
  by (cases m rule: ValnCases;
      (simp);
      cases "((ofValn m), (ofValn k), (ofValn v))" rule: storeImplAux.cases;
      (simp))

lemma storeClosedWf3:
  assumes "wf m" "wf k" "wf v"
  assumes "type_of_val m = TMap (type_of_val k) (type_of_val v)"
  shows "type_of_val (selectImpl (storeImpl m k v) x) = ran_ty (storeImpl m k v)"
  using assms
  apply (cases "x = k"; simp)
  apply (metis ArrayAxUpdate selectImpl.elims storeImpl.elims storePreserveTy ty.sel(6))
  by (metis (no_types, lifting) ArrayAxStable ran_ty.simps selectImpl.simps storeImpl.simps
      storePreserveTy ty.distinct(9) ty.simps(16) type_of_val.simps(1,2) wf.simps)

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
  (* slow proof, takes 5s *)
  by (cases m rule: ValnCases; simp;
     cases "(ofValn k)" rule: valnOf.cases; simp;
     cases "(ofValn v)" rule: valnOf.cases; fastforce)


lemma storeClosedWfDef:
  assumes "wf m" "wf k'" "wf v"
  assumes "type_of_val m = TMap (type_of_val k') (type_of_val v)"
  shows "(\<forall>k. (\<not>wf k \<or> type_of_val k \<noteq> dom_ty (storeImpl m k' v)) \<longrightarrow> (selectImpl (storeImpl m k' v) k) = val_of_type (ran_ty (storeImpl m k' v)))"
  by (metis (no_types, lifting) ArrayAxStable assms(1,2,4) dom_ty.elims ran_ty.simps storePreserveTy
      ty.distinct(11,9) ty.sel(5) type_of_val.simps(1,2) wf.simps)


lemma storeClosedWf:
  assumes "wf m" "wf k" "wf v"
  shows "wf (storeImpl m k v)"
  using  storeClosedWf1 storeClosedWf2 storeClosedWf3 storeClosedWfDef wfMapV assms
  by (smt (verit) One_nat_def add_diff_cancel_left' tmap_lvl.simps(3,4)
      diff_diff_cancel diff_is_0_eq map_level_gt_0 mapval_ty_eq_ty321 plus_1_eq_Suc
      storeImpl.simps storePreserveTy type_of_val.simps(1,2) wf.cases wf_impl_wf_ty
      zero_neq_one)


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

text \<open>type for well formed values\<close>
type_synonym 'a wf_val = "('a, 'a wf_maps) val"

text \<open>lift selectImpl and storeImpl\<close>
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


subsection \<open>Leammas hold for the new select and store\<close>

lemma wf_wf_val: "wf_wf x"
  apply (cases x)
  apply (simp add: wfLitV wf_wf.rep_eq)
  apply (simp add: wfAbsV wf_wf.rep_eq)
  by (simp add: Rep_wf_maps wf_map_bij wf_wf.rep_eq)


(* This bridges type_of_val across the lift *)
lemma type_of_val_transfer [transfer_rule]:
  "rel_fun (rel_val (=) cr_wf_maps) (=) type_of_val type_of_val"
  unfolding rel_fun_def cr_wf_maps_def
  apply (rule, rename_tac v_raw, rule, rename_tac v_lift)
  by (case_tac v_raw; case_tac v_lift; auto)


(* The Final Proofs *)
lemma Ax1:
  assumes "type_of_val m = TMap (type_of_val k) (type_of_val v)"
  shows "wf_select (wf_store m k v) k = v"
  using assms
  apply transfer
  using ArrayAxUpdate wf_wf_val
  by (metis eq_onp_top_eq_eq val.pred_rel wf_wf.abs_eq)

lemma Ex:
  assumes "m = MapV m'" "n = MapV n'"
  assumes "type_of_val m = type_of_val n"
  assumes "\<forall>k. type_of_val k = TMapInv0 (type_of_val m) \<longrightarrow> wf_select m k = wf_select n k"
  shows "m = n"
  using assms
  apply transfer
  apply auto[1]
  using extensionalityMapV wf_wf_val apply auto
  by (smt (verit) extensionalityMapV selectImpl.simps top1I type_of_val.simps(3)
      val.pred_inject(1,2,3) wf_map_bij ArrayAxStable storePreserveTy ty.distinct(11,9)
      ty.sel(5) type_of_val.simps(1,2) wf.simps dom_ty.elims ran_ty.elims dom_ty.simps ran_ty.simps)

lemma Ax2_wf_val:
  shows "x = y \<or> wf_select (wf_store m x v) y = wf_select m y"
  by (smt (verit, del_insts) ArrayAxStable Rep_wf_maps_inject id_apply
      map_fun_apply val.inj_map_strong wf_select_def wf_store.rep_eq)


subsection \<open>Proof for VC Phase\<close>

lemma key_tyC_preserved: "\<forall>tk tv. TMapCInv0 (TMapC tk tv) = tk" by simp
lemma val_tyC_preserved: "\<forall>tk tv. TMapCInv1 (TMapC tk tv) = tv" by simp

lemma map_type_safe_wf:
  shows "type_of_val (wf_select (MapV m) k) = TMapInv1 (type_of_val (MapV m))"
  apply transfer
  using wf.simps wf_map_set_def by fastforce

lemma map_select_type_safe: "\<forall>m  k.
       let tk = vc_type_of_val k; tv = TMapCInv1 (vc_type_of_val m)
       in vc_type_of_val m = TMapC tk tv \<and> vc_type_of_val k = tk \<longrightarrow>
          vc_type_of_val (wf_select m k) = tv"
  apply (rule, case_tac m; simp) using map_type_safe_wf
  by (metis mapval_ty_wf_maps.elims ty.sel(6) type_of_val.simps(3))

lemma map_store_type_safe: "\<forall> m k v.
       let tk = vc_type_of_val k; tv = vc_type_of_val v
       in (vc_type_of_val m = TMapC tk tv \<and>
           vc_type_of_val k = tk) \<and>
          vc_type_of_val v = tv \<longrightarrow>
          vc_type_of_val (wf_store m k v) =
          TMapC tk tv"
  apply (rule, case_tac m; simp)
  apply transfer
  using storePreserveTy
  by (metis (no_types, lifting) ty_to_closed.simps(3) type_of_val.simps(3))


lemma type_of_mapval_closed:
  assumes "closed (type_of_val m)" "closed (type_of_val k)" "closed (type_of_val v)"
  assumes "vc_type_of_val m = TMapC (vc_type_of_val k) (vc_type_of_val v)"
  shows "type_of_val m = TMap (type_of_val k) (type_of_val v)"
  by (metis assms(1,2,3,4) closed_inv2 closed_to_ty.simps(3) vc_type_of_val.simps)

lemma map_update:
  assumes "\<And>v::('a::absval, 'a wf_maps) val. closed (type_of_val v)"
  shows "\<forall>(m::('a, 'a wf_maps) val) k v.
       let tk = vc_type_of_val k; tv = vc_type_of_val v
       in vc_type_of_val m = TMapC tk tv \<longrightarrow> wf_select (wf_store m k v) k = v"
  by (meson Ax1 assms type_of_mapval_closed)


subsection \<open>Proof for Locale Assumptions\<close>

lemma max_map_level:
  assumes "wf v"
  shows "tmap_lvl (type_of_val v) \<le> 3"
  apply (cases v rule: ValnCases)
  using assms wf_impl_wf_ty by fastforce+

lemma max_map_level_wf:
  shows "tmap_lvl (type_of_val (v::('a::absval, 'a wf_maps) val)) \<le> 3"
  apply transfer
  using max_map_level
  by (metis eq_onp_top_eq_eq val.pred_rel wf_wf.abs_eq wf_wf_val)


lemma locale_select: "\<And>m k tk tv. \<lbrakk>type_of_val m = TMap tk tv; type_of_val k = tk\<rbrakk>
    \<Longrightarrow> type_of_val (wf_select m k) = tv"
  by (metis map_type_safe_wf ty.simps(14,16) type_of_val.elims ty.sel(6))

lemma locale_store: "\<And>m k v tk tv. \<lbrakk>type_of_val m = TMap tk tv; type_of_val k = tk; type_of_val v = tv \<rbrakk>
    \<Longrightarrow> type_of_val (wf_store m k v) = TMap tk tv"
  apply transfer
  using storePreserveTy by metis

lemma intintmap:
  assumes "type_of_val m = TMap (TPrim TInt) (TPrim TInt)"
  shows "\<exists>j. (wf_select m (IntV i)) = IntV j"
  by (simp add: assms locale_select tint_intv)

lemma inteq:
  assumes "\<exists>i. x = IntV i" "\<exists>j. y = IntV j"
  shows "(x = y) = (convert_val_to_int x = convert_val_to_int y)"
  using assms(1,2) by force

lemma int_inverse_0: "type_of_val k = (TPrim TInt) \<Longrightarrow> (k = IntV i) = (convert_val_to_int k = i)"
  using int_inverse_3 by auto

lemmas map_helper =
  locale_select locale_store intintmap inteq 
    int_inverse_3 int_inverse_2 int_inverse_1 int_inverse_0 convert_val_to_int.simps
    bool_inverse_3 bool_inverse_2 bool_inverse_1

end
