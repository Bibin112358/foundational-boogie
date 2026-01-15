section \<open>Semantics of the Boogie Language\<close>

theory MapExample
imports Semantics
begin

(* user needs to instantiate how many nesting levels to support *)
type_synonym 'a val0 = "('a, unit)  val"
type_synonym 'a val1 = "('a, 'a val0) val"
type_synonym 'a val2 = "('a, 'a val1) val"
type_synonym 'a val3 = "('a, 'a val2) val"
type_synonym 'a val4 = "('a, 'a val3) val"

(* MapV examples *)
value "IntV 1 :: unit val3"
value "IntV 2 :: unit val4"
definition simple_map_example :: "(unit val3, unit val4) map" where "simple_map_example = [IntV 1 \<mapsto> IntV 2]"

abbreviation MapTV where "MapTV \<equiv> MapV (TPrim TInt) (TPrim TInt)"  (* convenience for testing purposes *)

fun empty where "empty _ = undefined"
abbreviation m11 :: "unit val1" where "m11 \<equiv> MapTV (empty(IntV 3 := IntV 2)) None"
abbreviation m12 :: "unit val2" where "m12 \<equiv> MapTV (empty(IntV 3 := IntV 2)) (Some m11)"
abbreviation m13 :: "unit val3" where "m13 \<equiv> MapTV (empty(IntV 3 := IntV 2)) (Some m12)"
abbreviation m14 :: "unit val4" where "m14 \<equiv> MapTV (empty(IntV 3 := IntV 2)) (Some m13)"

abbreviation m22 :: "unit val2" where "m22 \<equiv> MapTV (empty(m11 := IntV 4)) None"
abbreviation m23 :: "unit val3" where "m23 \<equiv> MapTV (empty(m12 := IntV 4)) (Some m22)"
abbreviation m24 :: "unit val4" where "m24 \<equiv> MapTV (empty(m13 := IntV 4)) (Some m23)"

abbreviation m33 :: "unit val3" where "m33 \<equiv> MapTV (empty(m22 := IntV 6)) None"
abbreviation m34 :: "unit val4" where "m34 \<equiv> MapTV (empty(m23 := IntV 6)) (Some m33)"

abbreviation mg3 :: "unit val3" where "mg3 \<equiv> MapTV (empty(m22 := m13)) None"
abbreviation mg4 :: "unit val4" where "mg4 \<equiv> MapTV (empty(m23 := m14)) (Some mg3)"


fun Up1 where "Up1 (LitV v) = LitV v"
fun UpF2 :: "('a val0 \<Rightarrow> 'a val1) \<Rightarrow> ('a val1 \<Rightarrow> 'a val2)"
and Up2 :: "'a val1 \<Rightarrow> 'a val2" where 
    "UpF2 f x = (case (down x) of (Some y) \<Rightarrow> Up2 (f y) | None \<Rightarrow> undefined)"
  | "Up2 (MapV tk tv f k) = (MapV tk tv (UpF2 f) (Some (MapV tk tv f k)))"
  | "Up2 (LitV v) = LitV v"
  | "Up2 (AbsV v) = AbsV v" 


fun Up :: "('a, _) val \<Rightarrow> ('a, _) val" where
    "UpF f x = (if x = (Up y) then Up (f y) else undefined)"

inductive wf_map :: "('a, _) val => nat \<Rightarrow>  bool" where
  "wf_map (MapV _ _ _ _) 0" 
| "wf_map (MapV _ _ (\<lambda>x. e)  k) 1 ==> wf_map (MapV _ _ (\<lambda>y. (down x) e)  k) 2"

abbreviation example_map :: "('a, 'a val3) map_interface" where
  "example_map \<equiv> \<lparr> map_select = select_impl, map_store = undefined \<rparr>"

lemma "(map_select example_map) mg4 m24 = Some m14" by simp

(* there needs to be as many additional store functions, as there are nesting levels *)
(* user needs to generate these functions (is there a way to make this cleaner, macro?) *)
fun store3 :: "('a, _) val option \<Rightarrow> ('a, _) val option \<Rightarrow> ('a, _) val option \<rightharpoonup> ('a, _) val" where
    "store3 _ _ _ = None"

fun store2 :: "('a, _) val option \<Rightarrow> ('a, _) val option \<Rightarrow> ('a, _) val option \<rightharpoonup> ('a, _) val" where
    "store2 (Some (MapV tk tv mm mk)) (Some k) (Some v) = Some (MapV tk tv (mm(k := v)) (store3 mk (down k) (down v)))"
  | "store2 _ _ _ = None"

fun store1 :: "('a, _) val option \<Rightarrow> ('a, _) val option \<Rightarrow> ('a, _) val option \<rightharpoonup> ('a, _) val" where
    "store1 (Some (MapV tk tv mm mk)) (Some k) (Some v) = Some (MapV tk tv (mm(k := v)) (store2 mk (down k) (down v)))"
  | "store1 _ _ _ = None"

fun store0 :: "('a, _) val option \<Rightarrow> ('a, _) val option \<Rightarrow> ('a, _) val option \<rightharpoonup> ('a, _) val" where
    "store0 (Some (MapV tk tv mm mk)) (Some k) (Some v) = Some (MapV tk tv (mm(k := v)) (store1 mk (down k) (down v)))"
  | "store0 _ _ _ = None"

primrec store_impl :: "'a val4 \<Rightarrow> ('a, _) val \<Rightarrow> ('a, _) val \<rightharpoonup> ('a, _) val" where
    "store_impl (MapV tk tv mm mk) k v = store0 (Some (MapV tk tv mm mk)) (down k) (Some v)"
  | "store_impl (LitV _) _ _ = None"
  | "store_impl (AbsV _) _ _ = None"


abbreviation example_map2 :: "('a, 'a val3) map_interface" where
  "example_map2 \<equiv> \<lparr> map_select = select_impl, map_store = store_impl \<rparr>"

primrec select_option where "select_option (Some v) k = (map_select example_map2) v k"
lemma "select_option ((map_store example_map2) mg4 m24 (IntV 42)) m24 = Some (IntV 42)" by simp

lemma
  assumes "(map_store example_map2) (MapV tk tv mm mk) x v = Some ms"
  shows "(map_select example_map2) ms x = Some v"
  apply auto

end