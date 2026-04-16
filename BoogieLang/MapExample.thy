section \<open>Instantiation Example for MapV\<close>

theory MapExample
  imports Semantics VCExprHelper Map3Semantics
begin

(* MapV datatype *)
value "IntV 2 :: unit valn"

abbreviation IntV0 where "IntV0 i \<equiv> LitV0 (LInt i)"
abbreviation TT where "TT \<equiv> TPrim TInt"  (* convenience for testing purposes *)

abbreviation m11 :: "'a val1" where "m11 \<equiv> FunL (undefined(IntV0 3 := Inr (IntV0 2))) TT TT"
abbreviation m14 :: "'a valn" where "m14 \<equiv> MapV (Inr (Inr m11))"

abbreviation m22 :: "'a val2" where "m22 \<equiv> FunL (undefined(Inl m11 := Inr (Inr (IntV0 4)))) TT TT"
abbreviation m24 :: "'a valn" where "m24 \<equiv> MapV (Inr (Inl m22))"

abbreviation m33 :: "'a val3" where "m33 \<equiv> FunL (undefined(Inl m22 := Inr (Inr (Inr (IntV0 6))))) TT TT"
abbreviation m34 :: "'a valn" where "m34 \<equiv> MapV (Inl m33)"

abbreviation mg3 :: "'a val3" where "mg3 \<equiv> FunL (undefined(Inl m22 := Inr (Inr (Inl  m11)))) (TMap TT TT) TT"
abbreviation mg4 :: "'a valn" where "mg4 \<equiv> MapV (Inl mg3)"

abbreviation ms3 :: "'a val3" where "ms3 \<equiv> FunL (undefined(Inr (Inr (IntV0 3)) := Inl m33)) TT (TMap TT  (TPrim TInt))"
abbreviation ms4 :: "'a valn" where "ms4 \<equiv> MapV (Inl ms3)"

(* type *)
lemma map_level_gt_0: "tmap_lvl (TMap tv tk) \<ge> 1" by auto

(* select *)
lemma "selectImpl mg4 m24 = m14" by simp

(* store *)
lemma "type_of_val (LitV (LInt 42)) = TT" by simp
lemma "ran_ty mg4 = TT" by simp
lemma "selectImpl (storeImpl mg4 m24 (LitV (LInt 42))) m24
  = (LitV (LInt 42))" by simp


subsubsection \<open>Proving well formdness of a simple map\<close>
fun toVal0 :: "'a valn \<Rightarrow> 'a val0" where "toVal0 (LitV l) = LitV0 l" | "toVal0 _ = undefined"
fun fAdd1 where "fAdd1 (IntV0 x) = Inr (IntV0 (x+1))" | "fAdd1 _ = Inr (toVal0 (val_of_type (TT)))"
abbreviation mAdd1 :: "'a::absval val1" where "mAdd1 \<equiv> FunL fAdd1 (TPrim TInt) (TPrim TInt)"
abbreviation vAdd1 :: "'a::absval valn" where "vAdd1 \<equiv> MapV (Inr (Inr mAdd1))"

lemma wfvotTT: "(type_of_val ((val_of_type TT)::'a::absval valn) = TT \<and> wf ((val_of_type TT)::'a::absval valn))"
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

(* TODO: more general *)
lemma votTTpreserved: "valnOf (Inr (Inr (Inr (toVal0 (val_of_type (TT)))))) = (val_of_type (TT))"
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


subsubsection \<open>Well formdness of a higher order map\<close>

locale valoftype =
  assumes VOT: "\<And>t. tmap_lvl t \<le> 3 \<Longrightarrow> closed t \<Longrightarrow> (type_of_val ((val_of_type t)::'a::absval valn) = t \<and> wf ((val_of_type t)::'a::absval valn))"
begin

fun toVal1 :: "'a valn \<Rightarrow> 'a val1" where "toVal1 (MapV (Inr (Inr m))) = m" | "toVal1 _ = undefined"
fun val0Of10 :: "'a val1 + 'a val0 \<Rightarrow> 'a val0" where "val0Of10 (Inr v0) = v0" | "val0Of10 _ = undefined"
abbreviation TMII where "TMII \<equiv> TMap (TPrim TInt) (TPrim TInt)"
fun compint where 
    "compint g f (IntV0 x) =  (g (val0Of10 (f (IntV0 x))))"
    | "compint g f _ =  Inr (toVal0 (val_of_type (TT)))"
fun hof where 
  "hof (Inl (FunL f tk tv)) =
    (if (tk, tv) = (TT, TT) \<and> wf (MapV (Inr (Inr (FunL f tk tv))))
        then Inr (Inl (FunL (compint fAdd1 f) TT TT))
        else Inr (Inl (toVal1 (val_of_type (TMII)))))"
  | "hof _ = Inr (Inl (toVal1 (val_of_type (TMII))))"
abbreviation hom :: "'a::absval val2" where "hom \<equiv> FunL hof TMII TMII"
abbreviation homV :: "'a::absval valn" where "homV \<equiv> MapV (Inr (Inl hom))"

lemma "wf_ty homV" by auto

lemma "ran_ty homV = TMII" by simp

lemma "dom_ty homV = TMII" by simp

lemma "type_of_val k = TMII \<longrightarrow> (\<exists>k'. k = MapV k')" apply (cases k) by auto

lemma kTMII:
  assumes "wf_ty k"
  assumes "type_of_val k = TMII"
  shows "\<exists>f. k = MapV (Inr (Inr (FunL f TT TT)))"
proof -
  have "tmap_lvl (type_of_val k) = 1" using assms by simp
  then obtain k' where "ofValn k = Inr (Inr (Inl k'))" using C1Inrrl assms by blast
  then have K: "k = MapV (Inr (Inr k'))" using ofValn.elims by auto
  then have "wf_L 1 k'" using assms by force
  then show ?thesis
    apply (cases k')
    using K assms(2) by auto
qed

lemma validClosedTMII: "tmap_lvl (TMap TT TT) \<le> 3 \<and> closed (TMap TT TT)" by simp

lemma homvotdef: "tyL (toVal1 (val_of_type (TMap TT TT))) = (TT, TT)" using VOT
  by (metis kTMII toVal1.simps(1) tyL.simps validClosedTMII wf.simps
      wf_ty.simps(1,2))


lemma votTMIIpreserved: "valnOf (Inr (Inr (Inl (toVal1 (val_of_type (TMII)))))) = (val_of_type (TMII))"
  by (metis VOT kTMII toVal1.simps(1) valnOf.simps(3) validClosedTMII wf.simps
      wf_ty.simps(1,2))


lemma wff: "type_of_val (selectImpl homV k) = TMII"
  apply (case_tac k rule: ValnCases; (simp add: valBij2))
    using homvotdef VOT by auto

lemma compwf:
  assumes "a = (MapV (Inr (Inr (FunL f TT TT))))"
  assumes "b = (MapV (Inr (Inr (FunL (compint fAdd1 f) TT TT))))"
  assumes "wf a"
  shows "wf b"
proof -
  have wft: "wf_ty b" by (simp add: assms(2))

  have wf1: "\<forall>k. wf (selectImpl b k)"
    apply rule
    apply (case_tac k rule: ofValn.cases; (simp add: assms))
    apply (rename_tac v, case_tac v; (simp add: assms))
    apply (metis val_of_type.simps votTTpreserved wfvotTT)
    apply (metis fAdd1.elims valnOf.simps(1) votTTpreserved wfLitV wfvotTT)
    apply (metis val_of_type.simps votTTpreserved wfvotTT)
    apply (metis ofValn.simps(1) val0.exhaust valnOf.simps(2) valBij2 wfAbsV
        wfLitV)
    apply (metis valBij2 val_of_type.simps wfvotTT)+
    done
  have KTT: "dom_ty b = TT" by (simp add: assms(2))
  have wf2: "\<forall>k. (\<not>wf k \<or> type_of_val k \<noteq> dom_ty b) \<longrightarrow> (selectImpl b k) = val_of_type (ran_ty b)"
  proof (rule) fix k
    show "(\<not>wf k \<or> type_of_val k \<noteq> dom_ty b) \<longrightarrow> (selectImpl b k) = val_of_type (ran_ty b)"
    proof (cases k rule: ofValn.cases)
      case (1 v)
      then show ?thesis apply (cases v)
        using assms(2) votTTpreserved apply auto[1]
        apply (simp add: KTT wfLitV)
        using assms(2) votTTpreserved apply auto
        done
    next
      case (2 v)
      then show ?thesis
        using assms(2) votTTpreserved by auto
    qed (auto simp add: assms valBij2)
  qed
    
  have wf3: "\<forall>k. type_of_val (selectImpl b k) = ran_ty b"
    apply rule
    apply (case_tac k rule: ofValn.cases; (simp add: assms))
    apply (rename_tac v, case_tac v; simp)
    apply (metis val_of_type.simps votTTpreserved wfvotTT)
    apply (metis (no_types, lifting) fAdd1.elims type_of_lit.simps(2) type_of_val.simps(1)
        valnOf.simps(1) votTTpreserved wfvotTT)
    apply (metis val_of_type.simps votTTpreserved wfvotTT)
    apply (metis val_of_type.simps votTTpreserved wfvotTT)
    apply (metis valBij2 val_of_type.simps wfvotTT)+
    done

  have wf2: "\<forall>k. (\<not>wf k \<or> type_of_val k \<noteq> dom_ty b) \<longrightarrow> (selectImpl b k) = val_of_type (ran_ty b)"
    apply rule
    apply (case_tac k rule: ofValn.cases; (simp add: assms valBij2))
        apply (rename_tac v, case_tac v; simp)
    using votTTpreserved apply fastforce
    using wfLitV apply blast
    using votTTpreserved apply fastforce+
    done

  show ?thesis using wft wf1 wf2 wf3 wfMapV by simp
qed


lemma vhomVwfSelect: "wf (selectImpl homV k)"
  apply (cases k rule: ofValn.cases; simp)
  using VOT votTMIIpreserved apply auto[1]
  using VOT votTMIIpreserved apply auto[1]
    apply (rename_tac m, case_tac m)
    using VOT validClosedTMII val_of_type.simps
    apply (simp add: valBij2)
    using valoftype.compwf valoftype.intro votTMIIpreserved apply fastforce
    apply (metis VOT valBij2 val_of_type.simps validClosedTMII)
    apply (metis VOT valBij2 val_of_type.simps validClosedTMII)
    done

lemma homVdef:
  "(\<forall>k. (\<not>wf k \<or> type_of_val k \<noteq> dom_ty homV) \<longrightarrow> (selectImpl homV k) = val_of_type (ran_ty homV))"
proof rule
  fix k
  show "(\<not>wf k \<or> type_of_val k \<noteq> dom_ty homV) \<longrightarrow> (selectImpl homV k) = val_of_type (ran_ty homV)"
    apply simp
    apply (cases k rule: ValnCases)
    apply (simp add: valBij2)
    using votTMIIpreserved apply auto[1]
    apply (simp add: votTMIIpreserved)
    using votTMIIpreserved apply force
    using votTMIIpreserved apply force
    apply (simp add: valBij2)+
    done
qed

lemma "wf homV" using wff vhomVwfSelect wf.simps[of homV] homVdef by auto

end  (* valoftype locale *)


subsubsection \<open>Some more general wf properties\<close>

(* conclude Isabelle type from key of a select assuming wf and typed *)
lemma
  assumes "wf (MapV (Inl (FunL f tk tv)))"
  assumes "wf k"
  assumes "type_of_val k = dom_ty (MapV (Inl (FunL f tk tv)))"
  shows "\<exists>k'. ofValn k = Inr ( k')"
proof -
  have "tmap_lvl (type_of_val (MapV (Inl (FunL f tk tv)))) = 3"
    using InlC3 wf.simps assms(1) ofValn.simps wf_impl_wf_ty by force
  then have "tmap_lvl (dom_ty (MapV (Inl (FunL f tk tv)))) \<le> 2"
    by auto
  then have "tmap_lvl (type_of_val k) \<le> 2" using assms by auto
  then show ?thesis using assms(2) wf_impl_wf_ty
    by (metis InlC3 One_nat_def Suc_1 Suc_n_not_le_n numeral_3_eq_3 old.sum.exhaust)
qed


text \<open>wf maps are mapval\<close>
(* see if it works *)
lemma "mapval_ty (Abs_wf_maps (Inr (Inr mAdd1))) = (TT, TT)"
  by (simp add: Abs_wf_maps_inverse wf_map_set_def wf_vAdd1)

(* lifted mapval_ty *)
lemma "mapval_ty (Abs_wf_maps (Inr (Inr mAdd1))) = ((TPrim TInt), (TPrim TInt))"
  by (simp add: Abs_wf_maps_inverse wf_map_set_def wf_vAdd1)

end
