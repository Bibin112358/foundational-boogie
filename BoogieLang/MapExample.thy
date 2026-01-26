section \<open>Instantiation Example for MapV\<close>

theory MapExample
imports Semantics
begin


subsection \<open>Type Definition\<close>
(* user needs to instantiate how many nesting levels to support *)
type_synonym 'a val0 = "('a, unit) val"
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

abbreviation MapTV where "MapTV \<equiv> MapV [] (TPrim TInt)"  (* convenience for testing purposes *)

abbreviation m11 :: "unit val1" where "m11 \<equiv> MapKey [IntV 3 \<mapsto> IntV 2]"
abbreviation m14 :: "unit valn" where "m14 \<equiv> MapTV (Inr (Inr m11))"

abbreviation m22 :: "unit val2" where "m22 \<equiv> MapKey [m11 \<mapsto> Inr (IntV 4)]"
abbreviation m24 :: "unit valn" where "m24 \<equiv> MapTV (Inr (Inl m22))"

abbreviation m33 :: "unit val3" where "m33 \<equiv> MapKey [m22 \<mapsto> Inr (Inr (IntV 6))]"
abbreviation m34 :: "unit valn" where "m34 \<equiv> MapTV  (Inl m33)"

abbreviation mg3 :: "unit val3" where "mg3 \<equiv> MapKey [m22 \<mapsto> Inr (Inl  m11)]"
abbreviation mg4 :: "unit valn" where "mg4 \<equiv> MapV [] (TMap []  (TPrim TInt)) (Inl mg3)"

abbreviation ms3 :: "unit val3" where "ms3 \<equiv> MapVal [Inr (Inr (IntV 3)) \<mapsto> m33]"
abbreviation ms4 :: "unit valn" where "ms4 \<equiv> MapV [] (TMap []  (TPrim TInt)) (Inl ms3)"


subsection \<open>Helper Functions and Lemmas\<close>

primrec valtoM :: "'a valn \<Rightarrow> _ M" where
    "valtoM (MapV _ _ m) = m"
  | "valtoM (LitV v) = Up3 (LitV v)"
  | "valtoM (AbsV v) = Up3 (AbsV v)"

fun MtoVal :: " _ M option \<Rightarrow> ty \<rightharpoonup> 'a valn" where
    "MtoVal (Some (Up3 (LitV v))) _ = Some (LitV v)"
  | "MtoVal (Some (Up3 (AbsV v))) _ = Some (AbsV v)"
  | "MtoVal (Some (Up3 (MapV _ _ _))) _ = None"
  | "MtoVal (Some x) (TMap tks tv) = Some (MapV tks tv x)"
  | "MtoVal _ _ = None"

lemma MtoVal_inj:
  assumes "MtoVal (Some x) (TMap tks tv) = Some (MapV tks tv y)"
  shows "x = y"
  using MtoVal.elims assms by oops

fun Eq where "Eq (Some (MapV _ _ a)) (Some (MapV _ _ b)) = (a = b)" | "Eq a b = (a = b)"

lemma MtoVal_valtoM:
  assumes "Some x = MtoVal (Some (valtoM y)) ty"
  assumes "wf y"
  shows "Eq (Some x) (Some y)"
proof (cases y)
  case (LitV y')
  then show ?thesis by (simp add: assms(1))
next
  case (AbsV y')
  then show ?thesis by (simp add: assms(1))
next
  case (MapV tks tv y')
  have "valtoM y = y'" by (simp add: MapV)
  then obtain rhs where "MtoVal (Some y') ty = Some rhs"
    using assms(1) by fastforce
  have "\<forall> v. Some y' \<noteq> Some (Up3 (LitV v))" using MapV assms(2) by fastforce
  have "\<forall> v. Some y' \<noteq> Some (Up3 (AbsV v))" using MapV assms(2) by fastforce
  have "\<forall> tks' tv' v'. Some y' \<noteq> Some (Up3 (MapV tks' tv' v'))" using MapV assms(2) by fastforce
  have "\<And> v. Some y' \<noteq> Some (Up3 v)" using MapV assms(2) by fastforce
  have "MtoVal (Some y') ty \<noteq> None" by (metis \<open>valtoM y = y'\<close> assms(1) option.discI)
  have "\<exists> tks' tv'. MtoVal (Some y') ty = Some (MapV tks' tv' y')" sorry
  then show ?thesis using MapV assms(1) by fastforce
qed

subsection \<open>Select\<close>
(* there needs to be as many additional store functions, as there are nesting levels *)
(* user needs to generate these functions (is there a way to make this cleaner, macro?) *)
fun select0 :: "'a val10 \<Rightarrow> 'a val10 \<rightharpoonup> 'a val10" where
    "select0 (Inl (MapVal m)) (Inr k) = map_option Inl (m k)"
  | "select0 (Inl (MapKey m)) (Inr k) = map_option Inr (m k)"
  | "select0 _ _ = None"

fun select1 :: "'a val210  \<Rightarrow> 'a val210  \<rightharpoonup> 'a val210" where
    "select1 (Inl (MapVal m)) (Inr k) = map_option Inl (m k)"
  | "select1 (Inl (MapKey m)) (Inr (Inl k)) = map_option Inr (m k)"
  | "select1 (Inr m) (Inr k) = map_option Inr (select0 m k)"
  | "select1 _ _ = None"

fun select2 :: "'a val3 \<Rightarrow> ('a val2 + 'a val1 + 'a val0) \<rightharpoonup>  'a val3 + 'a val2 + 'a val1 + 'a val0" where
    "select2 (MapVal m) k = map_option Inl (m k)"
  | "select2 (MapKey m) (Inl k) = (case m k of (Some v) \<Rightarrow> Some (Inr v) | _ \<Rightarrow> None)"
  | "select2 (MapKey m) (Inr k) = None"


fun toVal3210 :: "'a valn \<Rightarrow> 'a val3210 option" where
    "toVal3210 (LitV v) = Some (Inr (Inr (Inr (LitV v))))"
  | "toVal3210 (AbsV v) = Some (Inr (Inr (Inr (AbsV v))))"
  | "toVal3210 (MapV _ _ (Inr (Inr m))) = Some (Inr (Inr (Inl m)))"
  | "toVal3210 (MapV _ _ (Inr (Inl m))) = Some (Inr (Inl m))"
  | "toVal3210 (MapV _ _ (Inl m)) = Some (Inl m)"

fun val3ToValn :: "ty \<Rightarrow> 'a val3210 \<Rightarrow> 'a valn option" where
    "val3ToValn _ (Inr (Inr (Inr (LitV v)))) = Some (LitV v)"
  | "val3ToValn _ (Inr (Inr (Inr (AbsV v)))) = Some (AbsV v)"
  | "val3ToValn (TMap tks tv) (Inr (Inr (Inl m))) = Some (MapV tks tv (Inr (Inr m)))"
  | "val3ToValn (TMap tks tv) (Inr (Inl m)) = Some (MapV tks tv (Inr (Inl m)))"
  | "val3ToValn (TMap tks tv) (Inl m) = Some (MapV tks tv (Inl m))"
  | "val3ToValn _ _ = None"

fun vH :: "_ \<Rightarrow> _" where "vH (Some (Inl h)) = Some h" | "vH _ = None"
fun vT :: "_ \<Rightarrow> _" where "vT (Some (Inr t)) = Some t" | "vT _ = None"

fun selectAux :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _" where
    "selectAux (MapVal m) _ (Some p)  = map_option Inl (m p)"
  | "selectAux (MapKey m) (Some k) _ = map_option Inr (m k)"
  | "selectAux _ _ _ =  None"

fun selectImpl :: "'a valn \<Rightarrow> 'a valn \<rightharpoonup> 'a valn" where
    "selectImpl (LitV _) _ = None"
  | "selectImpl (AbsV _) _ = None"
  | "selectImpl (MapV _ tv (Inr (Inr m))) k = Option.bind (selectAux m (vT (vT (vT (toVal3210 k)))) (vT (vT (vT (toVal3210 k))))) ((val3ToValn tv) \<circ> Inr \<circ> Inr)"
  | "selectImpl (MapV _ tv (Inr (Inl m))) k = Option.bind (selectAux m (vH (vT (vT (toVal3210 k)))) (vT (vT (toVal3210 k)))) ((val3ToValn tv) \<circ> Inr)"
  | "selectImpl (MapV _ tv (Inl m)) k = Option.bind (selectAux m (vH (vT (toVal3210 k))) (vT (toVal3210 k))) (val3ToValn tv)"

abbreviation example_map :: "('a, 'a val3 + 'a val2 + 'a val1) map_interface" where
  "example_map \<equiv> \<lparr> map_select = selectImpl, map_store = undefined \<rparr>"

lemma "(map_select example_map) mg4 m24 = Some (MapTV (Inr (Inr (MapKey [IntV 3 \<mapsto> IntV 2]))))" by simp

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
  assumes "selectAux (MapVal m) = selectAux (MapVal n)"
  shows "m = n"
proof -
  have "\<forall>p. map_option Inl (m p) = map_option Inl (n p)"
  proof rule
    fix p k
    have "selectAux (MapVal m) k (Some p) = selectAux (MapVal n) k (Some p)" using assms by auto
    also have "selectAux (MapVal m) k (Some p) = map_option Inl (m p)" by simp
    also have "selectAux (MapVal n) k (Some p) = map_option Inl (n p)" by simp
    finally show "map_option Inl (m p) = map_option Inl (n p)" by (metis Inl_inject option.inj_map_strong)
  qed
  then have "\<forall>p. (m p) = (n p)"
    by (metis old.sum.inject(1) option.inj_map_strong)
  then show ?thesis
    by auto
qed

lemma extensionalAuxKey:
  assumes "selectAux (MapKey m) = selectAux (MapKey n)"
  shows "m = n"
proof -
  have "\<forall>k. map_option Inr (m k) = map_option Inr (n k)"
  proof rule
    fix p k
    have "selectAux (MapKey m) (Some k) p = selectAux (MapKey n) (Some k) p" using assms by auto
    also have "selectAux (MapKey m) (Some k) p = map_option Inr (m k)" by simp
    also have "selectAux (MapKey n) (Some k) p = map_option Inr (n k)" by simp
    finally show "map_option Inr (m k) = map_option Inr (n k)"
      by (metis option.inj_map_strong sum.inject(2))
  qed
  then have "\<forall>k. (m k) = (n k)"
    by (metis option.inj_map_strong sum.inject(2))
  then show ?thesis
    by auto
qed



lemma extensionalAux':
  assumes "selectAux m = selectAux n"
  assumes "\<exists>k p. selectAux m k p \<noteq> None"
  shows "m = n"
proof (cases m)
  case (MapVal m')
  then show ?thesis
    by (metis L.exhaust assms extensionalAuxVal option.exhaust_sel
        selectAux.simps(1,3,4))
next
  case (MapKey m')
  then show ?thesis
    by (metis L.exhaust assms extensionalAuxKey option.exhaust_sel
        selectAux.simps(2-4))
qed


lemma extensionalMapV:
  assumes "selectImpl (MapV tks ty m) = selectImpl (MapV tks ty n)"
  assumes "\<exists>k. selectImpl (MapV tks ty m) k \<noteq> None"
  shows "m = n"
proof (cases m)
  case (Inl m')
  then show ?thesis
  proof (cases n)
    case (Inl n')
    then show ?thesis try
  next
    case (Inr b)
    then show ?thesis sorry
  qed
  
next
  case (Inr b)
  then show ?thesis sorry
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