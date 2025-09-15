theory Scratch
  imports Main "HOL.Rings" "HOL-Library.Finite_Map"

begin

(* Definition of weights, weighted sets and graphs*)
class ssr = linorder +
  fixes oplus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "\<oplus>" 65)
  fixes otimes :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 70)
  fixes one :: "'a"
  (*assume assoc*)

type_synonym ('a, 's) FWeighted = "('a, 's) fmap"
type_synonym ('a, 's) GraphOfFWeighted = "'a \<Rightarrow> ('a, 's) FWeighted"

(* Scaling of weighted sets *)
context includes fmap.lifting begin
lift_definition scaleFWeighted :: "'s::ssr \<Rightarrow> ('a, 's) FWeighted \<Rightarrow> ('a, 's) FWeighted" is
  "\<lambda>scalar. \<lambda>w. \<lambda>el. Option.bind (w el) (\<lambda>x. Some(x \<oplus> scalar))"
  subgoal for scalar w
    apply (auto split: if_splits simp: dom_def)
    by (simp add: bind_eq_Some_conv)
  done
end

(* EDGE SEMIRING *)
(* Graph-union, \<oplus> *)
definition unionGraph :: "('a, 's::ssr) GraphOfFWeighted \<Rightarrow> ('a, 's::ssr) GraphOfFWeighted  \<Rightarrow> ('a, 's::ssr) GraphOfFWeighted" where
  "unionGraph f g x = fmadd (f x) (g x)"

(* Empty graph, \<zero> *)
definition emptyGraph :: "('a, 's) GraphOfFWeighted" where
  "emptyGraph x = fmempty"

(* Connect-operator, \<otimes> *)
context includes fmap.lifting begin
lift_definition connectGraph :: "('a, 's::ssr) GraphOfFWeighted \<Rightarrow> ('a, 's::ssr) GraphOfFWeighted  \<Rightarrow> ('a, 's::ssr) GraphOfFWeighted" is
   "\<lambda>G1 G2 (u :: 'a) (v :: 'a). let X = {s. \<exists>(w :: 'a) s1 s2.
      G1 u w = Some s1 \<and> G2 w v = Some s2 \<and> s = s1 \<oplus> s2} in (if X = {} then None else Some (Min X))"
  subgoal for G1 G2 u
    apply (rule finite_subset[where B="\<Union>v \<in> dom (G1 u). dom (G2 v)"])
     apply (auto split: if_splits simp: dom_def)
    done
  done
end

(* Return-graph, \<one> *)
definition returnGraph :: "('a, 's::ssr) GraphOfFWeighted" where
  "returnGraph x = fmap_of_list [(x, one)]"

(* Monad implementation *)
context includes fmap.lifting begin
lift_definition bindWeighted :: "('a, 's::ssr) FWeighted \<Rightarrow> ('a \<Rightarrow> ('a, 's) FWeighted) \<Rightarrow> ('a, 's) FWeighted" is
  "\<lambda>(w :: 'a \<Rightarrow> 's option) k (el :: 'a). (
  let (X :: 's set) = {s. \<exists>x t1 t2. w x = Some t1 \<and> k x el = Some t2 \<and> s = t1 \<oplus> t2} in
  if X = {} then None else Some(Min X))"
  subgoal for w k
    apply (rule finite_subset[where B="\<Union>v \<in> dom w. dom (k v)"])
      apply (auto split: if_splits simp: dom_def)
    done
  done
end

(* Algorithms with edge semiring *)
(* Naive-star is endlessly recursive, but maybe possibly corecursive
fun naiveStar :: "('a, 's::ssr) GraphOfFWeighted \<Rightarrow> ('a, 's) GraphOfFWeighted" where
  "naiveStar g = unionGraph returnGraph (connectGraph (naiveStar g) g)"*)

fun exp :: "('a, 's::ssr) GraphOfFWeighted \<Rightarrow> nat \<Rightarrow> ('a, 's) GraphOfFWeighted" where
  "exp g 0 = returnGraph" |
  "exp g (Suc n) = connectGraph g (exp g n)"

(*context includes fmap.lifting begin
lift_definition mapGraph :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 's::linorder) FWeighted \<Rightarrow> ('b, 's) FWeighted" is
  "\<lambda>(f::'a \<Rightarrow> 'b). \<lambda>(w::'a \<Rightarrow> 's option). \<lambda>(el:: 'b). 
  (let X = {s. \<exists>x. f x = el \<and> w x = Some s} in
  if X = {} then None else Some(Min X))"
  subgoal for f w
    apply (auto split: if_splits simp: dom_def)
    apply (rule finite_subset[where B="\<Union>v \<in> dom w. {f v}"])
    sledgehammer
    done
    done
end*)

lemma finite_image_from_w:
  assumes "finite {a. \<exists>y. w a = Some y}"
  shows "finite {a. \<exists>x xa. f xa = a \<and> w xa = Some x}"
proof -
  have "{a. \<exists>x xa. f xa = a \<and> w xa = Some x} = f ` {xa. \<exists>y. w xa = Some y}"
    by auto
  then show ?thesis using assms
    by auto
qed


context includes fmap.lifting begin
lift_definition mapFWeighted :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 's::linorder) FWeighted \<Rightarrow> ('b, 's) FWeighted" is
  "\<lambda>(f::'a \<Rightarrow> 'b). \<lambda>(w::'a \<Rightarrow> 's option). \<lambda>(el:: 'b). 
  (let X = {s. \<exists>x. f x = el \<and> w x = Some s} in
  if X = {} then None else Some(Min X))"
  subgoal for f w
    apply (auto split: if_splits simp: dom_def)
    by (simp add: finite_image_from_w)
  done
end

datatype 'a list_plus = Single 'a | Snoc "'a list_plus" 'a

fun pathed :: "('a, 's) GraphOfFWeighted \<Rightarrow> ('a list_plus, 's::linorder) GraphOfFWeighted" where
  "pathed g (Snoc vs v) = mapFWeighted (\<lambda>t. Snoc (Snoc vs v) t) (g v)" |
  "pathed g (Single v) = mapFWeighted (\<lambda>t. Snoc (Single v) t) (g v)"

context includes fmap.lifting begin
lift_definition filtering :: "('a \<Rightarrow> bool) \<Rightarrow> ('a, 's::ssr) GraphOfFWeighted" is
  "\<lambda>p v el. (if p v then Some one else None)"
  subgoal for p v
    (*apply (auto split: if_splits simp: dom_def)*)
    done
end

term filtering

term fmran
term fset_of_fmap

codatatype ('s, 'a) heap = Heap 'a "(('s \<times> ('s, 'a) heap) list)"

term un_Heap1
term un_Heap2

end
