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

fun Eq where "Eq (Some (MapV _ _ a)) (Some (MapV _ _ b)) = (a = b)" | "Eq a b = (a = b)"

fun wf :: "'a valn \<Rightarrow> bool" where
    "wf (MapV _ _ (Up (Up (Up v)))) = False"
  | "wf _ = True"



lemma
  assumes store: "store_impl (MapV tks tv m) x v = Some ms"
  assumes wf: "wf v"
  assumes select: "select_impl ms x = Some w"
  shows sh: "Eq (Some w) (Some v)"
  oops


lemma update0:
  assumes "store0 m k v = Some ms"
  assumes "select0 ms k = Some w"
  shows "w = v"  
  using assms(1,2) store0.elims by force


lemma update1Up:
  fixes ms :: "'a M M"
  assumes "store1 (Up m') k v = Some ms"
  assumes s: "Some w = select1 ms k"
  shows "w = v"
  by (smt (verit) M.distinct(1) M.inject(2) assms(1) map_option_eq_Some
      option.discI s select1.elims store1.elims update0)

(*
  by (smt (verit) M.distinct(1) M.inject(2) assms(1) map_option_eq_Some
      option.discI s select1.elims store1.elims update0)
*)

(*
lemma update1Map:
  fixes ms :: "'a M M"
  assumes "store1 (MapAux m') k v = Some ms"
  assumes s: "Some w = select1 ms k"
  shows "w = v"
  by (smt (verit) M.distinct(1) assms(1) map_upd_Some_unfold option.discI s
      select1.simps(1) store1.elims)

lemma update1:
  fixes ms :: "'a M M"
  assumes "store1 m k v = Some ms"
  assumes s: "Some w = select1 ms k"
  shows "w = v"
  by (smt (verit) M.distinct(1) assms(1) map_upd_Some_unfold option.discI s
      select1.simps(1) store1.elims)

lemma update2:
  fixes ms :: "'a M M M"
  assumes "store2 (Up m) k v = Some ms"
  assumes s: "Some w = select1 ms k"
  shows "w = v"


proof -
  apply auto


(*
lemma
  assumes store: "store_impl (MapV tks tv m) x v = Some ms"
  assumes wf: "wf v"
  assumes select: "select_impl ms x = Some w"
  shows sh: "Eq (Some w) (Some v)"
proof -
  have "Some ms = MtoVal (store2 m (valtoM x) (valtoM v)) (TMap tks tv)" using store by auto
*)

*)

end