theory Scratch
  imports Main "HOL.Rings" "HOL-Library.Finite_Map"

begin

(* Definition of weights, weighted sets and graphs*)
class ssr = linorder +
  fixes oplus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "\<oplus>" 65)
  fixes otimes :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 70)
  fixes one :: "'a"
  fixes monus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<doteq>" 70)
  (*assume assoc*)

instantiation nat :: ssr begin
definition oplus_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "oplus_nat a b = min a b"
definition otimes_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "otimes_nat a b = a + b"
definition one_nat :: "nat" where "one_nat = 0"
definition monus_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "monus_nat a b = a-b"
instance proof qed end


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
  "\<lambda>p v el. (if p v \<and> v = el then Some one else None)"
  by (auto split: if_splits simp: dom_def)
end

lemma filtering_true_equals_return: "returnGraph = filtering (\<lambda>x. true)"
  sorry

(* THE VERTEX SEMIRING *)









type_synonym ('s, 'a) link = "('s \<times> 'a) option"
(*codatatype ('s, 'a) chain = Chain 'a "('s \<times> ('s, 'a) chain) option"*)
codatatype ('s, 'a) chain = Chain 'a "('s, ('s, 'a) chain) link"
codatatype ('s, 'a) heap = Heap 'a "(('s \<times> ('s, 'a) heap) list)"

fun bowtie :: "'s::ssr \<times> ('s, 'a) heap \<Rightarrow> 's \<times> ('s, 'a) heap \<Rightarrow> 's \<times> ('s, 'a) heap" where
  "bowtie (wl, hl) (wr, hr) = (
    if (wl \<le> wr) then
      (wl, Heap (un_Heap1 hl) ((monus wr wl, hr) # (un_Heap2 hl)))
    else
      (wr, Heap (un_Heap1 hr) ((monus wl wr, hl) # (un_Heap2 hr)))
  )"
notation bowtie (infixl "\<bowtie>" 65)

fun merges_plus :: "('s::ssr \<times> ('s, 'a) heap) \<Rightarrow> ('s \<times> ('s, 'a) heap) list \<Rightarrow> ('s \<times> ('s, 'a) heap)" where
  "merges_plus x [] = x" |
  "merges_plus x1 [x2] = x1 \<bowtie> x2" |
  "merges_plus x1 (x2#x3#xs) = (x1 \<bowtie> x2) \<bowtie> merges_plus x3 xs"

fun merges :: "('s::ssr \<times> ('s, 'a) heap) list \<Rightarrow> ('s, ('s, 'a) heap) link" where
  "merges [] = None" |
  "merges (x#xs) = Some (merges_plus x xs)"

definition map2 :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c \<times> 'a) \<Rightarrow> ('c \<times> 'b)" where
  "map2 f p = (let (c, a) = p in (c, f a))"

definition out :: "('s, 'a) heap \<Rightarrow> ('a \<times> (('s \<times> ('s, 'a) heap) list))" where
  "out h = (un_Heap1 h, un_Heap2 h)"

primcorec test_chain :: "'a \<Rightarrow> 's \<Rightarrow> ('s, 'a) chain" where
  "test_chain a s = Chain a (Some(s, test_chain a s))"

primcorec search::"('s::ssr, 'a) heap \<Rightarrow> ('s, 'a) chain" where
  "search h = (
  let (a, h_opt) = map_prod id merges (out h) in
  Chain a (map_option (map_prod id search) h_opt))
"

datatype Vertex = a | b | c | d
definition test_heap :: "(nat, Vertex) heap" where
  "test_heap = Heap a [(7, Heap b [(8, Heap c [(11, Heap d [])])]), (2, Heap c [(5, Heap d [])])]"

value "search test_heap"
value "(2, test_heap) \<bowtie> (1, test_heap)"

term Heap

fun list_plus_contains :: "'a list_plus \<Rightarrow> 'a \<Rightarrow> bool" where
  "list_plus_contains (Single x) y = (x = y)" |
  "list_plus_contains (Snoc xs x) y = ((x = y) \<or> list_plus_contains xs y)"

fun uniq :: "'a list_plus \<Rightarrow> bool" where
  "uniq (Single x) = True" |
  "uniq (Snoc xs x) = (\<not> list_plus_contains xs x \<and> uniq xs)"

datatype ('a, 'b) Either = Left 'a | Right 'b 
codatatype ('a, 's) fweightedinf = 
  FWeightedInf "((((('a, 's) fweightedinf, 's) FWeighted), 'a) Either)"
type_synonym ('a, 's) Forest = "(('a, 's) fweightedinf, 's) FWeighted"



(*fun dijkstra :: "'a \<Rightarrow> ('a, 's) GraphOfFWeighted \<Rightarrow> ('a list_plus) Neighbours" where
  "dijkstra s g = connectFWeighted (pathed g) (filtering uniq)"*)

end
