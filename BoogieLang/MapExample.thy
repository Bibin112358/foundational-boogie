section \<open>Instantiation Example for MapV\<close>

theory MapExample
imports Semantics
begin


subsection \<open>Type Definition\<close>
(* user needs to instantiate how many nesting levels to support *)

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
(* value "Up ( Up (Up (IntV 1))) :: unit val3" *)
value "IntV 2 :: unit valn"

abbreviation IntV where "IntV i \<equiv> LitV0 (LInt i)"
abbreviation TT where "TT \<equiv> TPrim TInt"  (* convenience for testing purposes *)

abbreviation m11 :: "unit val1" where "m11 \<equiv> MapKey [IntV 3 \<mapsto> IntV 2] TT"
abbreviation m14 :: "unit valn" where "m14 \<equiv> MapV (Inr (Inr m11))"

abbreviation m22 :: "unit val2" where "m22 \<equiv> MapKey [m11 \<mapsto> Inr (IntV 4)] TT"
abbreviation m24 :: "unit valn" where "m24 \<equiv> MapV (Inr (Inl m22))"

abbreviation m33 :: "unit val3" where "m33 \<equiv> MapKey [m22 \<mapsto> Inr (Inr (IntV 6))] TT"
abbreviation m34 :: "unit valn" where "m34 \<equiv> MapV (Inl m33)"

abbreviation mg3 :: "unit val3" where "mg3 \<equiv> MapKey [m22 \<mapsto> Inr (Inl  m11)] (TMap [] (TMap []  (TPrim TInt)))"
abbreviation mg4 :: "unit valn" where "mg4 \<equiv> MapV (Inl mg3)"

abbreviation ms3 :: "unit val3" where "ms3 \<equiv> MapVal [Inr (Inr (IntV 3)) \<mapsto> m33] (TMap [] (TMap []  (TPrim TInt)))"
abbreviation ms4 :: "unit valn" where "ms4 \<equiv> MapV (Inl ms3)"


subsection \<open>Helper Functions and Lemmas\<close>

subsection \<open>Select\<close>
(* there needs to be as many additional store functions, as there are nesting levels *)
(* user needs to generate these functions (is there a way to make this cleaner, macro?) *)
fun select0 :: "'a val10 \<Rightarrow> 'a val10 \<rightharpoonup> 'a val10" where
    "select0 (Inl (MapVal m _)) (Inr k) = map_option Inl (m k)"
  | "select0 (Inl (MapKey m _)) (Inr k) = map_option Inr (m k)"
  | "select0 _ _ = None"

fun select1 :: "'a val210  \<Rightarrow> 'a val210  \<rightharpoonup> 'a val210" where
    "select1 (Inl (MapVal m _)) (Inr k) = map_option Inl (m k)"
  | "select1 (Inl (MapKey m _)) (Inr (Inl k)) = map_option Inr (m k)"
  | "select1 (Inr m) (Inr k) = map_option Inr (select0 m k)"
  | "select1 _ _ = None"

fun select2 :: "'a val3 \<Rightarrow> ('a val2 + 'a val1 + 'a val0) \<rightharpoonup>  'a val3 + 'a val2 + 'a val1 + 'a val0" where
    "select2 (MapVal m _) k = map_option Inl (m k)"
  | "select2 (MapKey m _) (Inl k) = (case m k of (Some v) \<Rightarrow> Some (Inr v) | _ \<Rightarrow> None)"
  | "select2 (MapKey m _) (Inr k) = None"


fun toVal3210 :: "'a valn \<Rightarrow> 'a val3210" where
    "toVal3210 (LitV v) = (Inr (Inr (Inr (LitV0 v))))"
  | "toVal3210 (AbsV v) = (Inr (Inr (Inr (AbsV0 v))))"
  | "toVal3210 (MapV (Inr (Inr m))) = (Inr (Inr (Inl m)))"
  | "toVal3210 (MapV (Inr (Inl m))) = (Inr (Inl m))"
  | "toVal3210 (MapV (Inl m)) = (Inl m)"

fun toVal3210Opt :: "'a valn \<Rightarrow> 'a val3210 option" where
  "toVal3210Opt x = Some (toVal3210 x)"

fun val3ToValn :: "'a val3210 \<Rightarrow> 'a valn" where
    "val3ToValn (Inr (Inr (Inr (LitV0 v)))) = (LitV v)"
  | "val3ToValn (Inr (Inr (Inr (AbsV0 v)))) = (AbsV v)"
  | "val3ToValn (Inr (Inr (Inl m))) = (MapV (Inr (Inr m)))"
  | "val3ToValn (Inr (Inl m)) = (MapV (Inr (Inl m)))"
  | "val3ToValn (Inl m) = (MapV (Inl m))"

fun vH :: "_ \<Rightarrow> _" where "vH (Some (Inl h)) = Some h" | "vH _ = None"
fun vT :: "_ \<Rightarrow> _" where "vT (Some (Inr t)) = Some t" | "vT _ = None"

fun selectAux0 :: "('a, 'a) L \<Rightarrow> (('a, 'a) L + 'a) option \<Rightarrow> (('a, 'a) L + 'a) option"  where
    "selectAux0 (MapVal m _) (Some (Inr k)) = map_option Inl (m k)"
  | "selectAux0 (MapKey m _) (Some (Inr k)) = map_option Inr (m k)"
  | "selectAux0 _ _ = None"

fun selectAux :: "('a, 'a + 'b) L \<Rightarrow> (('a, 'a + 'b) L + 'a + 'b) option \<Rightarrow> (('a, 'a + 'b) L + 'a + 'b) option"  where
    "selectAux (MapVal m _) (Some (Inr k)) = map_option Inl (m k)"
  | "selectAux (MapKey m _) (Some (Inr (Inl k))) = map_option Inr (m k)"
  | "selectAux _ _ = None"


fun selectImpl :: "'a valn \<Rightarrow> 'a valn \<rightharpoonup> 'a valn" where
    "selectImpl (LitV _) _ = None"
  | "selectImpl (AbsV _) _ = None"
  | "selectImpl (MapV (Inr (Inr m))) k = map_option ((val3ToValn) \<circ> Inr \<circ> Inr) (selectAux0 m ((vT (vT (toVal3210Opt k)))))"
  | "selectImpl (MapV (Inr (Inl m))) k = map_option ((val3ToValn) \<circ> Inr) (selectAux m ((vT (toVal3210Opt k))))"
  | "selectImpl (MapV (Inl m)) k = map_option (val3ToValn) (selectAux m ( (toVal3210Opt k)))"

abbreviation example_map :: "('a, 'a val3 + 'a val2 + 'a val1) map_interface" where
  "example_map \<equiv> \<lparr> map_select = selectImpl, map_store = undefined \<rparr>"

lemma "(map_select example_map) mg4 m24 = Some (MapV (Inr (Inr (MapKey [IntV 3 \<mapsto> IntV 2] TT))))" by simp

subsection \<open>Store\<close>
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


fun storeAux :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _" where
    "storeAux (MapVal m) _ (Some p) _ (Some w) = Some (MapVal (m(p \<mapsto> w)))"
  | "storeAux (MapKey m) (Some k) _ (Some v) _= Some (MapKey (m(k \<mapsto> v)))"
  | "storeAux _ _ _ _ _ =  None"

fun storeImpl :: "'a valn \<Rightarrow> 'a valn \<Rightarrow> 'a valn \<rightharpoonup> 'a valn" where
    "storeImpl (LitV _) _ _ = None"
  | "storeImpl (AbsV _) _ _ = None"
  | "storeImpl (MapV _ tv (Inr (Inr m))) k v = Option.bind ( storeAux m (vT (vT (vT (toVal3210 k)))) (vT (vT (vT (toVal3210 k)))) (vT (vT (vT (toVal3210 v)))) (vH (vT (vT (toVal3210 v)))) ) ((val3ToValn tv) \<circ> Inr \<circ> Inr \<circ> Inl)"
  | "storeImpl (MapV _ tv (Inr (Inl m))) k v = Option.bind ( storeAux m (vH (vT (vT (toVal3210 k)))) (vT (vT (toVal3210 k))) (vT (vT ((toVal3210 v)))) (vH (vT ((toVal3210 v)))) ) ((val3ToValn tv) \<circ> Inr \<circ> Inl)"
  | "storeImpl (MapV _ tv (Inl m)) k v = Option.bind ( storeAux m (vH (vT (toVal3210 k))) (vT (toVal3210 k)) ((vT ((toVal3210 v)))) (vH (((toVal3210 v)))) ) ((val3ToValn tv) \<circ> Inl)"


primrec store_impl :: "'a valn \<Rightarrow> 'a valn \<Rightarrow> 'a valn \<rightharpoonup> 'a valn" where
    "store_impl (MapV tks tv m) k v = MtoVal (store2 m (valtoM k) (valtoM v)) (TMap tks tv)"
  | "store_impl (LitV _) _ _ = None"
  | "store_impl (AbsV _) _ _ = None"

abbreviation example_map2 :: "('a, 'a val3 + 'a val2 + 'a val1) map_interface" where
  "example_map2 \<equiv> \<lparr> map_select = selectImpl, map_store = storeImpl \<rparr>"

primrec select_option where "select_option (Some v) k = (map_select example_map2) v k"
lemma "select_option ((map_store example_map2) mg4 m24 (IntV 42)) m24 = Some (IntV 42)" by simp

subsection \<open>Array Axiom Update\<close>
text \<open>Property to prove: (m[k] := v)[k] == v or select (store m k v) k = v\<close>

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

subsection \<open>Array Axiom Stable\<close>
text \<open>Property to prove:
  y \<noteq> x ==> (m[x] := v)[y] == m[y]
  y \<noteq> x ==> select (store m x v) y = select m y\<close>

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


subsection \<open>Array Axiom Extensionality\<close>
text \<open>Property to prove: (\<forall>k. m[k] == n[k]) <==> Eq m n\<close>

lemma extensionalAuxVal:
  assumes "selectAux (MapVal m t) = selectAux (MapVal n t')"
  shows "m = n"
proof -
  have "\<forall>p. map_option Inl (m p) = map_option Inl (n p)"
  proof rule
    fix k
    have "selectAux (MapVal m t) (Some (Inr k)) = selectAux (MapVal n t') (Some (Inr k))"
      by (metis assms selectAux.simps(1))
    also have "selectAux (MapVal m t) (Some (Inr k)) = map_option Inl (m k)" by simp
    also have "selectAux (MapVal n t') (Some (Inr k)) = map_option Inl (n k)" by simp
    finally show "map_option Inl (m k) = map_option Inl (n k)" by (metis Inl_inject option.inj_map_strong)
  qed
  then have "\<forall>p. (m p) = (n p)"
    by (metis old.sum.inject(1) option.inj_map_strong)
  then show ?thesis
    by auto
qed

lemma extensionalAux0Val:
  assumes "selectAux0 (MapVal m t) = selectAux0 (MapVal n t')"
  shows "m = n"
proof -
  have "\<forall>p. map_option Inl (m p) = map_option Inl (n p)"
  proof rule
    fix k
    have "selectAux0 (MapVal m t) (Some (Inr k)) = selectAux0 (MapVal n t') (Some (Inr k))"
      by (metis assms selectAux.simps(1))
    also have "selectAux0 (MapVal m t) (Some (Inr k)) = map_option Inl (m k)" by simp
    also have "selectAux0 (MapVal n t') (Some (Inr k)) = map_option Inl (n k)" by simp
    finally show "map_option Inl (m k) = map_option Inl (n k)" by (metis Inl_inject option.inj_map_strong)
  qed
  then have "\<forall>p. (m p) = (n p)"
    by (metis old.sum.inject(1) option.inj_map_strong)
  then show ?thesis
    by auto
qed

lemma extensionalAuxKey:
  assumes "selectAux (MapKey m t) = selectAux (MapKey n t')"
  shows "m = n"
proof -
  have "\<forall>k. map_option Inr (m k) = map_option Inr (n k)"
  proof rule
    fix k
    have "selectAux (MapKey m t) (Some (Inr (Inl k))) = selectAux (MapKey n t') (Some (Inr (Inl k)))"
      by (metis assms selectAux.simps(2))
    also have "selectAux (MapKey m t) (Some (Inr (Inl k))) = map_option Inr (m k)" by simp
    also have "selectAux (MapKey n t') (Some (Inr (Inl k))) = map_option Inr (n k)" by simp
    finally show "map_option Inr (m k) = map_option Inr (n k)"
      by (metis option.inj_map_strong sum.inject(2))
  qed
  then have "\<forall>k. (m k) = (n k)"
    by (metis option.inj_map_strong sum.inject(2))
  then show ?thesis
    by auto
qed

lemma extensionalAux0Key:
  assumes "selectAux0 (MapKey m t) = selectAux0 (MapKey n t')"
  shows "m = n"
proof -
  have "\<forall>k. map_option Inr (m k) = map_option Inr (n k)"
  proof rule
    fix k
    have "selectAux0 (MapKey m t) (Some (Inr (k))) = selectAux0 (MapKey n t') (Some (Inr (k)))"
      by (metis assms selectAux.simps(2))
    also have "selectAux0 (MapKey m t) (Some (Inr (k))) = map_option Inr (m k)" by simp
    also have "selectAux0 (MapKey n t') (Some (Inr (k))) = map_option Inr (n k)" by simp
    finally show "map_option Inr (m k) = map_option Inr (n k)"
      by (metis option.inj_map_strong sum.inject(2))
  qed
  then have "\<forall>k. (m k) = (n k)"
    by (metis option.inj_map_strong sum.inject(2))
  then show ?thesis
    by auto
qed

primrec type_of_L where
  "type_of_L (MapKey _ t) = t" | "type_of_L (MapVal _ t) = t"


lemma extensionalAux:
  assumes "selectAux m = selectAux n"
  assumes "type_of_L m = type_of_L n"
  assumes "\<exists>k. selectAux m k \<noteq> None"
  shows "m = n"
proof (cases m)
  case (MapVal m' t)
  then show ?thesis
  proof (cases n)
    case (MapVal n' t')
    then show "m = n" using MapVal \<open>m = MapVal m' t\<close> assms extensionalAuxVal by auto
  next
    case (MapKey x21 x22)
    obtain k v where "selectAux m k = Some (Inl v)"
      using assms(3) \<open>m = MapVal m' t\<close> sorry
    then show ?thesis
      using \<open>m = MapVal m' t\<close> assms elem_set option.set_sel selectAux.simps
      sorry
  qed
next
  case (MapKey m' t)
  then show ?thesis
  proof (cases n)
    case (MapVal x11 x12)
    then show ?thesis
      using \<open>m = MapKey m' t\<close> assms(1,3) elem_set option.set_sel selectAux.simps(1,3,4)
      sorry
  next
    case (MapKey x21 x22)
    then show "m = n" using MapKey \<open>m = MapKey m' t\<close> assms extensionalAuxKey by auto
  qed
qed


lemma extensionalAux0:
  assumes "selectAux0 m = selectAux0 n"
  assumes "type_of_L m = type_of_L n"
  assumes "\<exists>k. selectAux0 m k \<noteq> None"
  shows "m = n"
proof (cases m)
  case (MapVal m' t)
  then show ?thesis
  proof (cases n)
    case (MapVal n' t')
    then show "m = n" using MapVal \<open>m = MapVal m' t\<close> assms extensionalAux0Val by auto
  next
    case (MapKey x21 x22)
    obtain k v where "selectAux0 m k = Some v" using assms(3) by blast
    then show ?thesis
      using \<open>m = MapVal m' t\<close> assms elem_set option.set_sel selectAux.simps
      sorry
  qed
next
  case (MapKey m' t)
  then show ?thesis
  proof (cases n)
    case (MapVal x11 x12)
    then show ?thesis
      using \<open>m = MapKey m' t\<close> assms(1,3) elem_set option.set_sel selectAux.simps(1,3,4)
      sorry
  next
    case (MapKey x21 x22)
    then show "m = n" using MapKey \<open>m = MapKey m' t\<close> assms extensionalAux0Key by auto
  qed
qed


lemma valSurj: "surj (\<lambda>k. (vH (vT (toVal3210Opt k))))"
proof -
  have "\<forall>y. \<exists>z. (\<lambda>k. (vH (vT (toVal3210Opt k)))) z = y"
    by (metis option.exhaust_sel toVal3210.simps(4,5) toVal3210Opt.simps vH.simps(1,2)
        vT.simps(1,3))
  then show ?thesis by (metis (mono_tags, lifting) surj_def)
qed

lemma valBij: "toVal3210 (val3ToValn x) = x"
proof (cases x)
  case (Inl x')
  then show ?thesis by simp
next
  case (Inr x')
  then show ?thesis
  proof (cases x')
    case (Inl x'')
    then show ?thesis using Inl Inr by fastforce
  next
    case (Inr x'')
    then show ?thesis
    proof (cases x'')
      case (Inl x''')
      then show ?thesis 
        using \<open>x = Inr x'\<close> \<open>x' = Inr x''\<close> \<open>x'' = Inl x'''\<close> by simp
    next
      case (Inr x''')
      then show ?thesis
      proof (cases x''')
        case (LitV0 v)
        then show ?thesis
          using \<open>x''' = LitV0 v\<close> \<open>x = Inr x'\<close> \<open>x' = Inr x''\<close> \<open>x'' = Inr x'''\<close> by simp
      next
        case (AbsV0 v)
        then show ?thesis
          using \<open>x''' = AbsV0 v\<close> \<open>x = Inr x'\<close> \<open>x' = Inr x''\<close> \<open>x'' = Inr x'''\<close> by simp
      qed
    qed
  qed
qed

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
      = map_option val3ToValn (map_option Inr (map_option Inr y))" try
    by (metis assms option.map_comp)
  then show "x = y"
    by (metis (no_types, lifting) option.inj_map_strong sum.inject(2) toValnOpt_inj)
qed


lemma extensionalMapVInl:
  assumes "selectImpl (MapV (Inl m)) = selectImpl (MapV (Inl n))"
  assumes "type_of_L m = type_of_L n"
  assumes "\<exists>k. selectImpl (MapV (Inl m)) k \<noteq> None"
  shows "m = n"
proof -
  have "\<And>kOpt. selectAux m kOpt = selectAux n kOpt"
  proof -
    fix kOpt::"'a val3210 option"
    obtain k where "kOpt = None \<or> kOpt = Some k" by fastforce
    have "\<exists>k'. Some k = toVal3210Opt k'"
      by (metis toVal3210Opt.simps valBij)
    moreover have "\<forall>k. map_option val3ToValn (selectAux m (toVal3210Opt k))
      = map_option val3ToValn (selectAux n ((toVal3210Opt k)))"
      by (metis assms(1) selectImpl.simps(5))
    ultimately have "map_option val3ToValn (selectAux m (Some k))
      = map_option val3ToValn (selectAux n (Some k))"
      by force
    moreover have "map_option val3ToValn (selectAux m None)
      = map_option val3ToValn (selectAux n None)"
      by simp
    ultimately have "map_option val3ToValn (selectAux m kOpt)
      = map_option val3ToValn (selectAux n kOpt)"
      using \<open>kOpt = None \<or> kOpt = Some k\<close> by blast
    then show "(selectAux m kOpt) = (selectAux n kOpt)"
      using toValnOpt_inj by blast
  qed
  then have "selectAux m = selectAux n" by auto
  then show "m = n" using valSurj extensionalAux
    using assms(2,3) by fastforce
qed

lemma extensionalMapVInrl:
  assumes "selectImpl (MapV (Inr (Inl m))) = selectImpl (MapV (Inr (Inl n)))"
  assumes "type_of_L m = type_of_L n"
  assumes "\<exists>k. selectImpl (MapV (Inr (Inl m))) k \<noteq> None"
  shows "m = n"
proof -
  have "\<And>kOpt. selectAux m kOpt = selectAux n kOpt"
  proof -
    fix kOpt::"'a val210 option"
    obtain k where "kOpt = (vT (toVal3210Opt k))"
      by (metis not_Some_eq toVal3210Opt.elims vT.simps(1,3) valBij)
    have "map_option ((val3ToValn) \<circ> Inr) (selectAux m kOpt)
      = map_option ((val3ToValn) \<circ> Inr) (selectAux n kOpt)"
      by (metis \<open>\<And>thesis. (\<And>k. kOpt = vT (toVal3210Opt k) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> assms(1)
          selectImpl.simps(4))
    then show "(selectAux m kOpt) = (selectAux n kOpt)"
      using toValnInrOpt_inj by blast
  qed
  then have "selectAux m = selectAux n" by auto
  then show "m = n" using valSurj extensionalAux
    using assms(2,3) by fastforce
qed

lemma extensionalMapVInrr:
  assumes "selectImpl (MapV (Inr (Inr m))) = selectImpl (MapV (Inr (Inr n)))"
  assumes "type_of_L m = type_of_L n"
  assumes "\<exists>k. selectImpl (MapV (Inr (Inr m))) k \<noteq> None"
  shows "m = n"
proof -
  have "\<And>kOpt. selectAux0 m kOpt = selectAux0 n kOpt"
  proof -
    fix kOpt::"'a val10 option"
    obtain k where "kOpt = vT (vT (toVal3210Opt k))"
      by (metis not_Some_eq toVal3210Opt.elims vT.simps(1,3) valBij)
    have "map_option ((val3ToValn) \<circ> Inr \<circ> Inr) (selectAux0 m kOpt)
      = map_option ((val3ToValn) \<circ> Inr \<circ> Inr) (selectAux0 n kOpt)"
      by (metis \<open>kOpt = vT (vT (toVal3210Opt k))\<close> assms(1) selectImpl.simps(3))
    then show "(selectAux0 m kOpt) = (selectAux0 n kOpt)"
      using toValnInrrOpt_inj by blast
  qed
  then have "selectAux0 m = selectAux0 n" by auto
  then show "m = n" using assms
    using extensionalAux0 by fastforce
qed

fun type_of_map where
    "type_of_map (Inl m) = type_of_L m"
  | "type_of_map (Inr (Inl m)) = type_of_L m"
  | "type_of_map (Inr (Inr m)) = type_of_L m"

lemma extensionalMapV:
  assumes "selectImpl (MapV m) = selectImpl (MapV n)"
  assumes "type_of_map m = type_of_map n"
  assumes "\<exists>k. selectImpl (MapV m) k \<noteq> None"
  shows "m = n"
proof (cases m)
  case (Inl m')
  then show ?thesis
  proof (cases n)
    case (Inl n')
    have "selectImpl (MapV (Inl m')) = selectImpl (MapV (Inl n'))"
      using \<open>m = Inl m'\<close> \<open>n = Inl n'\<close> assms(1) by force
    moreover have "type_of_L m' = type_of_L n'"
      using \<open>m = Inl m'\<close> \<open>n = Inl n'\<close> assms(2) by force
    moreover have "\<exists>k. selectImpl (MapV (Inl m')) k \<noteq> None"
      using \<open>m = Inl m'\<close> \<open>n = Inl n'\<close> assms(3) by force
    ultimately show ?thesis using \<open>m = Inl m'\<close> \<open>n = Inl n'\<close> assms extensionalMapVInl
      by blast
  next
    case (Inr n')
    obtain k where "selectImpl (MapV (Inl m')) k \<noteq> None"
      using \<open>m = Inl m'\<close> assms by blast
    have "selectImpl (MapV (Inr n')) k = None"
      using \<open>n = Inr n'\<close> assms oops
    then show ?thesis
      using Inl Inr \<open>selectImpl (MapV (Inl m')) k \<noteq> None\<close> assms(1) by force
  qed
  
next
  case (Inr b)
  then show ?thesis oops
qed

lemma extensional:
  assumes "selectImpl m = selectImpl n"
  assumes "\<exists>k. selectImpl m k \<noteq> None"
  assumes "type_of_val A m = type_of_val A n"
  shows "m = n"
proof (cases m)
  case (LitV x1)
  then show ?thesis using assms(2) by fastforce
next
  case (AbsV x2)
  then show ?thesis using assms(2) by fastforce
next
  case cm: (MapV mtks mty m')
  then show ?thesis
  proof (cases n)
    case (LitV x1)
    then show ?thesis using assms(1,2) by auto
  next
    case (AbsV x2)
    then show ?thesis using assms(1,2) by auto
  next
    case cn: (MapV ntks nty n')
    have "mtks = ntks" using cm cn assms by auto
    have "mty = nty" using cm cn assms by auto
  qed
qed

end