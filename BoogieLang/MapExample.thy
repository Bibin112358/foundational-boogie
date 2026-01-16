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

abbreviation MapTV where "MapTV \<equiv> MapV (TPrim TInt) (TPrim TInt)"  (* convenience for testing purposes *)
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
abbreviation mg4 :: "unit valn" where "mg4 \<equiv> MapTV  mg3"

(* there needs to be as many additional store functions, as there are nesting levels *)
(* user needs to generate these functions (is there a way to make this cleaner, macro?) *)
fun select3 :: "('a, _) val \<Rightarrow> ('a, _) val option \<rightharpoonup> ('a, _) val" where
    "select3 (MapV tk tv (Inl f)) (Some k) = f k"
  | "select3 _ _ = None"

fun select2 :: "('a, _) val \<Rightarrow> ('a, _) val option \<rightharpoonup> ('a, _) val" where
    "select2 (MapV tk tv (Inl f)) (Some k) = f k"
  | "select2 (MapV tk tv (Inr m)) (Some k) = map_option up (select3 m (down k))"
  | "select2 _ _ = None"

fun select1 :: "('a, _) val \<Rightarrow> ('a, _) val option \<rightharpoonup> ('a, _) val" where
    "select1 (MapV tk tv (Inl f)) (Some k) = f k"
  | "select1 (MapV tk tv (Inr m)) (Some k) = map_option up (select2 m (down k))"
  | "select1 _ _ = None"

fun select0 :: "_ M \<Rightarrow> _ M option \<rightharpoonup> ('a, _) val" where
    "select0 (MapAux m) (Some k) = m k"
  (*| "select0 (MapV tk tv (Inr m)) (Some k) = map_option up (select1 m (down k))"*)
  | "select0 _ _ = None"

primrec select_impl :: "'a valn \<Rightarrow> 'a valn \<rightharpoonup> 'a valn" where
    "select_impl (MapV _ _ m) (MapV _ _ k) = select0 m (down k)"
  | "select_impl (MapV _ _ m) (LitV v) = select0 m (Up3 (LitV v))"
  | "select_impl (LitV _) _ = None"
  | "select_impl (AbsV _) _ = None"


abbreviation example_map :: "('a, 'a val3) map_interface" where
  "example_map \<equiv> \<lparr> map_select = select_impl, map_store = undefined \<rparr>"

lemma "(map_select example_map) mg4 m24 = Some m14" by simp


fun store3 :: "('a, _) val \<Rightarrow> ('a, _) val option \<Rightarrow> ('a, _) val option \<rightharpoonup> ('a, _) val" where
    "store3 (MapV tk tv (Inl f)) (Some k) (Some v) = Some (MapV tk tv (Inl (f(k \<mapsto> v))))"  
  | "store3 _ _ _ = None"

fun store2 :: "('a, _) val \<Rightarrow> ('a, _) val option \<Rightarrow> ('a, _) val option \<rightharpoonup> ('a, _) val" where
    "store2 (MapV tk tv (Inl f)) (Some k) (Some v) = Some (MapV tk tv (Inl (f(k \<mapsto> v))))"
  | "store2 (MapV tk tv (Inr m)) (Some k) (Some v) = map_option up (store3 m (down k) (down v))"
  | "store2 _ _ _ = None"

fun store1 :: "('a, _) val \<Rightarrow> ('a, _) val option \<Rightarrow> ('a, _) val option \<rightharpoonup> ('a, _) val" where
    "store1 (MapV tk tv (Inl f)) (Some k) (Some v) = Some (MapV tk tv (Inl (f(k \<mapsto> v))))"
  | "store1 (MapV tk tv (Inr m)) (Some k) (Some v) = map_option up (store2 m (down k) (down v))"
  | "store1 _ _ _ = None"

fun store0 :: "('a, _) val \<Rightarrow> ('a, _) val option \<Rightarrow> ('a, _) val option \<rightharpoonup> ('a, _) val" where
    "store0 (MapV tk tv (Inl f)) (Some k) (Some v) = Some (MapV tk tv (Inl (f(k \<mapsto> v))))"
  | "store0 (MapV tk tv (Inr m)) (Some k) (Some v) = map_option up (store1 m (down k) (down v))"
  | "store0 _ _ _ = None"

primrec store_impl :: "'a val4 \<Rightarrow> ('a, _) val \<Rightarrow> ('a, _) val \<rightharpoonup> ('a, _) val" where
    "store_impl (MapV tk tv m) k v = store0 (MapV tk tv m) (down k) (Some v)"
  | "store_impl (LitV _) _ _ = None"
  | "store_impl (AbsV _) _ _ = None"


abbreviation example_map2 :: "('a, 'a val3) map_interface" where
  "example_map2 \<equiv> \<lparr> map_select = select_impl, map_store = store_impl \<rparr>"

primrec select_option where "select_option (Some v) k = (map_select example_map2) v k"
lemma "select_option ((map_store example_map2) mg4 m24 (IntV 42)) m24 = Some (IntV 42)" by simp

lemma
  assumes "(map_store example_map2) (MapV tk tv m) x v = Some ms"
  shows "(map_select example_map2) ms x = Some v"
  apply auto
  try

end