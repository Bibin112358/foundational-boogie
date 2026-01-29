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
fun select0 :: "'a val10 \<Rightarrow> 'a val0 \<rightharpoonup> 'a val10" where
    "select0 (Inl (MapVal m _)) k = map_option Inl (m k)"
  | "select0 (Inl (MapKey m _)) k = map_option Inr (m k)"
  | "select0 _ _ = None"

fun select1 :: "'a val210  \<Rightarrow> 'a val10  \<rightharpoonup> 'a val210" where
    "select1 (Inl (MapVal m _)) k = map_option Inl (m k)"
  | "select1 (Inl (MapKey m _)) (Inl k) = map_option Inr (m k)"
  | "select1 (Inr m) (Inr k) = map_option Inr (select0 m k)"
  | "select1 _ _ = None"

fun select2 :: "'a val3210 \<Rightarrow> 'a val210 \<rightharpoonup> 'a val3210" where
    "select2 (Inl (MapVal m _)) k = map_option Inl (m k)"
  | "select2 (Inl (MapKey m _)) (Inl k) = map_option Inr (m k)"
  | "select2 (Inr m) (Inr k) = map_option Inr (select1 m k)"
  | "select2 _ _ = None"

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

fun selectImpl' :: "'a val3210 \<Rightarrow> 'a val3210 \<rightharpoonup> 'a val3210" where
    "selectImpl' m (Inl k) = None"
  | "selectImpl' m (Inr k) = select2 m k"

fun selectImpl :: "'a valn \<Rightarrow> 'a valn \<rightharpoonup> 'a valn" where
    "selectImpl m k = map_option val3ToValn (selectImpl' (toVal3210 m) (toVal3210 k))"

abbreviation example_map :: "('a, 'a val3 + 'a val2 + 'a val1) map_interface" where
  "example_map \<equiv> \<lparr> map_select = selectImpl, map_store = undefined \<rparr>"

lemma "(map_select example_map) mg4 m24 = Some (MapV (Inr (Inr (MapKey [IntV 3 \<mapsto> IntV 2] TT))))" by simp

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
  "example_map2 \<equiv> \<lparr> map_select = selectImpl, map_store = storeImpl \<rparr>"

primrec select_option where "select_option (Some v) k = (map_select example_map2) v k"
lemma "select_option ((map_store example_map2) mg4 m24 (IntV 42)) m24 = Some (IntV 42)" by simp
*)
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
      = map_option val3ToValn (map_option Inr (map_option Inr y))"
    by (metis assms option.map_comp)
  then show "x = y"
    by (metis (no_types, lifting) option.inj_map_strong sum.inject(2) toValnOpt_inj)
qed

primrec type_of_L where
  "type_of_L (MapKey _ t) = t" | "type_of_L (MapVal _ t) = t"

fun type_of_val10  where
    "type_of_val10 (Inl m) = type_of_L m"
  | "type_of_val10 (Inr v) = undefined"

subsubsection \<open>Extensionality Level 0\<close>

lemma extensional0Val:
  assumes "select0 (Inl (MapVal m t)) = select0 (Inl (MapVal n t'))"
  assumes "\<exists>k. select0 (Inl (MapVal m t)) k \<noteq> None"
  shows "m = n"
proof -
  have "\<forall>k. map_option Inl (m k) = map_option Inl (n k)"
    by (metis (mono_tags, lifting) assms(1) option.inj_map_strong select0.simps(1)
        sum.inject(1))
  then have "\<forall>k. m k = n k"
    by (metis (no_types, lifting) Inl_inject[of "the (m _)" "the (n _)"]
        option.collapse[of "m _"] option.collapse[of "n _"] option.map_disc_iff[of Inl "n _"]
        option.map_disc_iff[of Inl "m _"] option.map_sel[of "m _" Inl]
        option.map_sel[of "n _" Inl])
  then show "m = n" by auto
qed

lemma extensional0Key:
  assumes "select0 (Inl (MapKey m t)) = select0 (Inl (MapKey n t'))"
  assumes "\<exists>k. select0 (Inl (MapKey m t)) k \<noteq> None"
  shows "m = n"
proof -
  have "\<forall>k. map_option Inr (m k) = map_option Inr (n k)"
    by (metis assms(1) option.inj_map_strong select0.simps(2) sum.inject(2))
  then have "\<forall>k. m k = n k"
    by (metis (no_types, lifting) Inr_inject[of "the (m _)" "the (n _)"]
        option.collapse[of "m _"] option.collapse[of "n _"] option.map_disc_iff[of Inr "n _"]
        option.map_disc_iff[of Inr "m _"] option.map_sel[of "m _" Inr]
        option.map_sel[of "n _" Inr])
  then show "m = n" by auto
qed

lemma extensional0:
  assumes "select0 m = select0 n"
  assumes "type_of_val10 m = type_of_val10 n"
  assumes "\<exists>k. select0 m k \<noteq> None"
  shows "m = n"
proof (cases m)
  case (Inr m')
  then show ?thesis using assms(3) by auto
next
  case (Inl m')
  then show ?thesis
  proof (cases m')
    case (MapVal m'' t)
    then show ?thesis
    proof (cases n)
      case (Inr n')
      then show ?thesis using assms(1,3) by auto
    next
      case (Inl n')
      then show ?thesis
      proof (cases n')
        case (MapKey n'' t')
        obtain k v where "select0 (Inl (MapVal m'' t)) k = Some (Inl v)"
          using \<open>m = Inl m'\<close> \<open>m' = MapVal m'' t\<close> assms by auto
        then show ?thesis
          using \<open>m = Inl m'\<close> \<open>m' = MapVal m'' t\<close> \<open>n = Inl n'\<close> \<open>n' = MapKey n'' t'\<close> assms
          by fastforce
      next
        case (MapVal n'' t')
        then show ?thesis
          using extensional0Val \<open>m = Inl m'\<close> \<open>m' = MapVal m'' t\<close> \<open>n = Inl n'\<close> \<open>n' = MapVal n'' t'\<close> assms
          by fastforce
      qed
    qed
  next
    case (MapKey m'' t)
    then show ?thesis
    proof (cases n)
      case (Inr n')
      then show ?thesis using assms(1,3) by auto
    next
      case (Inl n')
      then show ?thesis
      proof (cases n')
        case (MapVal n'' t')
        obtain k v where "select0 (Inl (MapKey m'' t)) k = Some (Inr v)"
          using \<open>m = Inl m'\<close> \<open>m' = MapKey m'' t\<close> assms by auto
        then show ?thesis
          using \<open>m = Inl m'\<close> \<open>m' = MapKey m'' t\<close> \<open>n = Inl n'\<close> \<open>n' = MapVal n'' t'\<close> assms
          by fastforce
      next
        case (MapKey n'' t')
        then show ?thesis
        using extensional0Key \<open>m = Inl m'\<close> \<open>m' = MapKey m'' t\<close> \<open>n = Inl n'\<close> \<open>n' = MapKey n'' t'\<close> assms
          by fastforce
      qed
    qed
  qed
qed


subsubsection \<open>Extensionality Level 1\<close>

lemma extensional1Val:
  assumes "select1 (Inl (MapVal m t)) = select1 (Inl (MapVal n t'))"
  assumes "\<exists>k. select1 (Inl (MapVal m t)) k \<noteq> None"
  shows "m = n"
proof -
  have "\<forall>k. map_option Inl (m k) = map_option Inl (n k)"
    by (metis (mono_tags, lifting) assms(1) option.inj_map_strong select1.simps(1)
        sum.inject(1))
  then have "\<forall>k. m k = n k"
    by (metis (no_types, lifting) Inl_inject[of "the (m _)" "the (n _)"]
        option.collapse[of "m _"] option.collapse[of "n _"] option.map_disc_iff[of Inl "n _"]
        option.map_disc_iff[of Inl "m _"] option.map_sel[of "m _" Inl]
        option.map_sel[of "n _" Inl])
  then show "m = n" by auto
qed

lemma extensional1Key:
  assumes "select1 (Inl (MapKey m t)) = select1 (Inl (MapKey n t'))"
  assumes "\<exists>k. select1 (Inl (MapKey m t)) k \<noteq> None"
  shows "m = n"
proof -
  have "\<forall>k. map_option Inr (m k) = map_option Inr (n k)"
    by (metis (mono_tags, lifting) assms(1) option.inj_map_strong select1.simps(2)
          sum.inject(2))
  then have "\<forall>k. m k = n k"
    by (metis (no_types, lifting) Inr_inject[of "the (m _)" "the (n _)"]
        option.collapse[of "m _"] option.collapse[of "n _"] option.map_disc_iff[of Inr "n _"]
        option.map_disc_iff[of Inr "m _"] option.map_sel[of "m _" Inr]
        option.map_sel[of "n _" Inr])
  then show "m = n" by auto
qed

fun type_of_val210  where
    "type_of_val210 (Inl m) = type_of_L m"
  | "type_of_val210 (Inr v) = type_of_val10 v"

lemma extensional1Rec:
  assumes "select1 (Inr m') = select1 (Inr n')"
  assumes "type_of_val10 m' = type_of_val10 n'"
  assumes "\<exists>k. select1 (Inr m') k \<noteq> None"
  shows "m' = n'"
proof -
  have "\<forall>k. select0 m' k = select0 n' k"
  proof rule
    fix k
    have "select1 (Inr m') (Inr k) = map_option Inr (select0 m' k)"
      by simp
    moreover have "select1 (Inr n') (Inr k) = map_option Inr (select0 n' k)"
      by simp
    ultimately have "map_option Inr (select0 m' k) = map_option Inr (select0 n' k)"
      by (metis (mono_tags, lifting) assms(1) option.inj_map_strong sum.inject(2))
    then show "select0 m' k = select0 n' k"
      by (metis option.inj_map_strong sum.inject(2))
  qed
  then have "select0 m' = select0 n'" by auto
  have "\<exists>k. select0 m' k \<noteq> None"
  proof -
    obtain k where "select1 (Inr m') k \<noteq> None" using assms by auto
    obtain k' where "select1 (Inr m') k = map_option Inr (select0 m' k')"
      by (smt (verit) Inr_not_Inl \<open>select1 (Inr m') k \<noteq> None\<close> select1.elims
          sum.inject(2))
    then show ?thesis using \<open>select1 (Inr m') k \<noteq> None\<close> by auto
  qed
  have "type_of_val10 m' = type_of_val10 n'" using assms by auto
  then show ?thesis using assms extensional0
    using \<open>\<exists>k. select0 m' k \<noteq> None\<close> \<open>select0 m' = select0 n'\<close> by blast
qed

(*
lemma extensional1':
  assumes "select1 m = select1 n"
  assumes "type_of_val10 m = type_of_val10 n"
  assumes "\<exists>k. select1 m k \<noteq> None"
  shows "m = n"
proof (cases rule: select1.cases)
  case (1 m uu k)
  then show ?thesis sorry
next
  case (2 m uv k)
  then show ?thesis sorry
next
  case (3 m k)
  then show ?thesis sorry
next
  case ("4_1" va vb v)
  then show ?thesis sorry
next
  case ("4_2" v va)
  then show ?thesis sorry
qed
*)

lemma extensional1:
  assumes "select1 m = select1 n"
  assumes "type_of_val210 m = type_of_val210 n"
  assumes "\<exists>k. select1 m k \<noteq> None"
  shows "m = n"
proof (cases m)
  case (Inr m')
  then show ?thesis
  proof (cases n)
    case (Inl n')
    then show ?thesis using assms(1) [unfolded \<open>m = _\<close> \<open>n = _\<close>, simplified]
      proof -
        obtain k v where A: "select1 (Inr m') k = Some v" using assms(3) Inr by auto
        then obtain v' where "v = Inr v'" apply (cases k) by auto
        then obtain k' where "k = Inr k'" using A apply (cases k) by auto
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

subsubsection \<open>Extensionality Impl\<close>

fun type_of_map where
    "type_of_map (Inl m) = type_of_L m"
  | "type_of_map (Inr (Inl m)) = type_of_L m"
  | "type_of_map (Inr (Inr m)) = type_of_L m"


lemma extensionalImpl':
  assumes "selectImpl' m = selectImpl' n"
  assumes "type_of_val3210 m = type_of_val3210 n"
  assumes "\<exists>k. selectImpl' m k \<noteq> None"
  shows "m = n"
  by (metis (no_types, lifting) ext assms(1,2,3) extensional2[of n m]
      selectImpl'.elims[of m _ "selectImpl' m _"] selectImpl'.simps(2)[of n]
      selectImpl'.simps(2)[of m])

lemma extensionalImpl:
  assumes "selectImpl (MapV m) = selectImpl (MapV n)"
  assumes "type_of_map m = type_of_map n"
  assumes "\<exists>k. selectImpl (MapV m) k \<noteq> None"
  shows "m = n"
(* "selectImpl m k = map_option val3ToValn (selectImpl' (toVal3210 m) (toVal3210 k))" *)
proof -
  have "\<forall>k'. map_option val3ToValn (selectImpl' (toVal3210 (MapV m)) (toVal3210 k'))
    = map_option val3ToValn (selectImpl' (toVal3210 (MapV m)) (toVal3210 k'))" by simp
  fix k
  obtain k' where "k = toVal3210 k'" by (metis valBij)
  (* injectivity of map_option val3ToValn *)
  (* lemma extensionalImpl' *)
  (* injectivity of toVal3210 *)
  oops

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