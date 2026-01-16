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

abbreviation m11 :: "unit val1" where "m11 \<equiv> MapTV (Inl [IntV 3 \<mapsto> IntV 2])"
abbreviation m12 :: "unit val2" where "m12 \<equiv> MapTV (Inr m11)"
abbreviation m13 :: "unit val3" where "m13 \<equiv> MapTV (Inr m12)"
abbreviation m14 :: "unit val4" where "m14 \<equiv> MapTV (Inr m13)"

abbreviation m22 :: "unit val2" where "m22 \<equiv> MapTV (Inl [m11 \<mapsto> IntV 4])"
abbreviation m23 :: "unit val3" where "m23 \<equiv> MapTV (Inr m22)"
abbreviation m24 :: "unit val4" where "m24 \<equiv> MapTV (Inr m23)"

abbreviation m33 :: "unit val3" where "m33 \<equiv> MapTV (Inl [m22 \<mapsto> IntV 6])"
abbreviation m34 :: "unit val4" where "m34 \<equiv> MapTV (Inr m33)"

abbreviation mg3 :: "unit val3" where "mg3 \<equiv> MapTV (Inl [m22 \<mapsto> m13])"
abbreviation mg4 :: "unit val4" where "mg4 \<equiv> MapTV (Inr mg3)"

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

fun select0 :: "('a, _) val \<Rightarrow> ('a, _) val option \<rightharpoonup> ('a, _) val" where
    "select0 (MapV tk tv (Inl f)) (Some k) = f k"
  | "select0 (MapV tk tv (Inr m)) (Some k) = map_option up (select1 m (down k))"
  | "select0 _ _ = None"

primrec select_impl :: "'a val4 \<Rightarrow> ('a, _) val \<rightharpoonup> ('a, _) val" where
    (*"select_impl (MapV _ _ m _) k = map_option m (down k)"*)
    "select_impl (MapV tk tv m) k = select0 (MapV tk tv m) (down k)"
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