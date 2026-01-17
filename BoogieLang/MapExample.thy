section \<open>Semantics of the Boogie Language\<close>

theory MapExample
imports Semantics
begin

(* user needs to instantiate how many nesting levels to support *)
type_synonym 'a val0 = "('a, unit)  val"
type_synonym 'a val1 = "('a val0) M"
type_synonym 'a val2 = "('a val1) M"
type_synonym 'a val3 = "('a val2) M"
type_synonym 'a valn = "('a, 'a val3) val"

(* MapV examples *)
value "Up ( Up (Up (IntV 1))) :: unit val3"
value "IntV 2 :: unit valn"
definition simple_map_example :: "(unit val3, unit valn) map" where
  "simple_map_example = [Up ( Up (Up (IntV 1))) \<mapsto> IntV 2]"

abbreviation MapTV where "MapTV \<equiv> MapV [] (TPrim TInt)"  (* convenience for testing purposes *)
abbreviation Up2 where "Up2 x \<equiv> Up (Up x)"
abbreviation Up3 where "Up3 x \<equiv> Up (Up2 x)"
abbreviation Up4 where "Up4 x \<equiv> Up (Up3 x)"

abbreviation m11 :: "unit val1" where "m11 \<equiv> MapAux [IntV 3 \<mapsto> Up (IntV 2)]"
abbreviation m14 :: "unit valn" where "m14 \<equiv> MapTV (Up2 m11)"

abbreviation m22 :: "unit val2" where "m22 \<equiv> MapAux [m11 \<mapsto> Up2 (IntV 4)]"
abbreviation m24 :: "unit valn" where "m24 \<equiv> MapTV (Up m22)"

abbreviation m33 :: "unit val3" where "m33 \<equiv> MapAux [m22 \<mapsto> Up3 (IntV 6)]"
abbreviation m34 :: "unit valn" where "m34 \<equiv> MapTV  m33"

abbreviation mg3 :: "unit val3" where "mg3 \<equiv> MapAux [m22 \<mapsto> Up2 m11]"
abbreviation mg4 :: "unit valn" where "mg4 \<equiv> MapV [] (TMap []  (TPrim TInt)) mg3"

(* there needs to be as many additional store functions, as there are nesting levels *)
(* user needs to generate these functions (is there a way to make this cleaner, macro?) *)
fun select0 :: "_ M \<Rightarrow> _ M \<rightharpoonup> _ M" where
    "select0 (MapAux m) (Up k) = m k"
  | "select0 _ _ = None"

fun select1 :: "_ M \<Rightarrow> _ M \<rightharpoonup> _ M" where
    "select1 (MapAux m) (Up k) = m k"
  | "select1 (Up m) (Up k) = map_option Up (select0 m k)"
  | "select1 _ _ = None"

fun select2 :: "_ M \<Rightarrow> _ M \<rightharpoonup> _ M" where
    "select2 (MapAux m) (Up k) = m k"
  | "select2 (Up m) (Up k) = map_option Up (select1 m k)"
  | "select2 _ _ = None"

primrec valtoM :: "'a valn \<Rightarrow> _ M" where
    "valtoM (MapV _ _ m) = m"
  | "valtoM (LitV v) = Up3 (LitV v)"
  | "valtoM (AbsV v) = Up3 (AbsV v)"


fun MtoVal :: " _ M option \<Rightarrow> ty \<rightharpoonup> 'a valn" where
    "MtoVal (Some (Up3 (LitV v))) _ = Some (LitV v)"
  | "MtoVal (Some (Up3 (AbsV v))) _ = Some (AbsV v)"
  | "MtoVal (Some x) (TMap tks tv) = Some (MapV tks tv x)"
  | "MtoVal _ _ = None"

lemma MtoVal_inj:
  assumes "MtoVal (Some x) (TMap tks tv) = Some (MapV tks tv y)"
  shows "x = y"
  sorry

fun Eq where "Eq (Some (MapV _ _ a)) (Some (MapV _ _ b)) = (a = b)" | "Eq a b = (a = b)"

fun wf :: "'a valn \<Rightarrow> bool" where
    "wf (MapV _ _ (Up (Up (Up v)))) = False"
  | "wf _ = True"

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
  have "\<forall> v. y' \<noteq> (Up3 (LitV v))" using MapV assms(2) by fastforce
  have "\<forall> v. y' \<noteq> (Up3 (AbsV v))" using MapV assms(2) by fastforce
  have "MtoVal (Some y') ty \<noteq> None" by (metis \<open>valtoM y = y'\<close> assms(1) option.discI)
  then have "\<exists> tks' tv'. MtoVal (Some y') ty = Some (MapV tks' tv' y')" sorry
  then show ?thesis using MapV assms(1) by fastforce
qed


primrec select_impl :: "'a valn \<Rightarrow> 'a valn \<rightharpoonup> 'a valn" where
    "select_impl (MapV _ tv m) k = MtoVal (select2 m (valtoM k)) tv"
  | "select_impl (LitV _) _ = None"
  | "select_impl (AbsV _) _ = None"


abbreviation example_map :: "('a, 'a val3) map_interface" where
  "example_map \<equiv> \<lparr> map_select = select_impl, map_store = undefined \<rparr>"

lemma "(map_select example_map) mg4 m24 = Some m14" by simp

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

abbreviation example_map2 :: "('a, 'a val3) map_interface" where
  "example_map2 \<equiv> \<lparr> map_select = select_impl, map_store = store_impl \<rparr>"

primrec select_option where "select_option (Some v) k = (map_select example_map2) v k"
lemma "select_option ((map_store example_map2) mg4 m24 (IntV 42)) m24 = Some (IntV 42)" by simp

lemma
  assumes store: "store_impl (MapV tks tv m) x v = Some ms"
  assumes wf: "wf v"
  assumes select: "select_impl ms x = Some w"
  shows sh: "Eq (Some w) (Some v)"
  oops

lemma update0:
  assumes "store0 m k v = Some ms"
  assumes "select0 ms k = w"
  shows "w = Some v"
  using assms(1,2) store0.elims by force

lemma update1Up:
  assumes "store1 (Up m') k v = Some ms"
  assumes "select1 ms k = Some w"
  shows "w = v"
proof -
  obtain k' v' where "k = Up k' \<and> v = Up v'"
    by (metis M.exhaust assms(1,2) option.discI select1.simps(4) store1.simps(4))
  thus "w = v"
    using assms(1,2) update0 by fastforce
qed

lemma update1Map:
  assumes "store1 (MapAux m') k v = Some ms"
  assumes "select1 ms k = Some w"
  shows "w = v"
proof -
  obtain k' where "k = Up k'" 
    by (metis M.exhaust assms(2) option.discI select1.simps(4))
  thus "w = v"
    using assms(1,2) by fastforce
qed

lemma update1:
  assumes "store1 m k v = Some ms"
  assumes "Some w = select1 ms k"
  shows "w = v"
  using M.exhaust assms(1,2) update1Map update1Up by metis

lemma update2Up:
  assumes "store2 (Up m') k v = Some ms"
  assumes "select2 ms k = Some w"
  shows "w = v"
proof -
  obtain k' v' where "k = Up k' \<and> v = Up v'"
    by (metis M.exhaust assms(1,2) option.discI select2.simps(4) store2.simps(4))
  thus "w = v"
    using assms(1,2) update1 by fastforce
qed

lemma update2Map:
  assumes "store2 (MapAux m') k v = Some ms"
  assumes "select2 ms k = Some w"
  shows "w = v"
proof -
  obtain k' where "k = Up k'"
    by (metis M.exhaust assms(2) option.discI select2.simps(4))
  thus "w = v"
    using assms(1,2) by fastforce
qed

lemma update2:
  assumes "store2 m k v = Some ms"
  assumes "Some w = select2 ms k"
  shows "w = v"
  using M.exhaust assms(1,2) update2Map update2Up by metis

lemma
  assumes store: "store_impl (MapV tks tv m) x v = Some (MapV tks tv ms)"
  assumes wfv: "wf v"
  assumes select: "select_impl (MapV tks tv ms) x = Some w"
  shows sh: "Eq (Some w) (Some v)"
proof -
  have "Some ms = store2 m (valtoM x) (valtoM v)"
    by (metis MtoVal.simps(7) MtoVal_inj option.exhaust option.simps(3) store
        store_impl.simps(1))
  then have "Some (valtoM v) = select2 ms (valtoM x)"
    by (metis MtoVal.simps(7) local.select option.discI option.exhaust select_impl.simps(1)
        update2)
  then have "Some w = MtoVal (Some (valtoM v)) tv"
    using local.select by fastforce
  then show ?thesis using MtoVal_valtoM wfv by blast
qed

end