theory Scratch2
  imports Main "HOL.Rings" "HOL-Library.Finite_Map" "HOL-Library.BNF_Corec"

begin

subsection \<open>The type of weighted sets\<close>
 
instantiation option :: (ab_semigroup_add) comm_monoid_add begin
definition zero_option where "zero_option = None"
definition plus_option where "plus_option a b = (case (a, b) of (Some x, Some y) \<Rightarrow> Some (x + y) | (Some x, None) \<Rightarrow> Some x | (None, Some x) \<Rightarrow> Some x | _ \<Rightarrow> None)"
instance
  by standard (auto simp: zero_option_def plus_option_def ac_simps split: option.splits)
end
 
typedef ('a, 'w :: ab_semigroup_add) wset = \<open>{f :: 'a \<Rightarrow> 'w option. finite {x. f x \<noteq> None}}\<close>
  morphisms weight Abs_wset
proof
  show \<open>(\<lambda>x. None) \<in> {f. finite {x. f x \<noteq> None}}\<close>
    by simp
qed
 
setup_lifting type_definition_wset
 
lift_definition wempty :: \<open>('a, 'w :: ab_semigroup_add) wset\<close> is
  \<open>\<lambda>a. None\<close>
  by simp
 
lift_definition wsingle :: \<open>'a \<Rightarrow> 'w \<Rightarrow> ('a, 'w :: ab_semigroup_add) wset\<close> is
  \<open>\<lambda>a w b. if a = b then Some w else None\<close>
  by simp

lift_definition wset :: \<open>('a, 'w :: ab_semigroup_add) wset \<Rightarrow> 'a set\<close> is
  \<open>\<lambda>M. {x. M x \<noteq> None}\<close> .
 
lift_definition wadd :: \<open>('a, 'w :: ab_semigroup_add) wset \<Rightarrow> ('a, 'w) wset \<Rightarrow> ('a, 'w) wset\<close> is
  \<open>\<lambda>M1 M2 x. M1 x + M2 x\<close>
  by (erule (1) finite_subset[rotated, OF finite_Un[THEN iffD2, OF conjI]]) (auto simp: plus_option_def split: option.splits)
 
lift_definition image_wset :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'w :: ab_semigroup_add) wset \<Rightarrow> ('b, 'w) wset" is
  \<open>\<lambda>f M b. Finite_Set.fold (\<lambda>a b. M a + b) None ({a. M a \<noteq> None \<and> f a = b})\<close>
  subgoal for f M
    apply (erule finite_surj[of _ _ f])
    apply auto
    sorry
  done
 
fun wset_of_list :: "('a \<times> 'w) list \<Rightarrow> ('a, 'w :: ab_semigroup_add) wset" where
  "wset_of_list [] = wempty" |
  "wset_of_list ((a, w) # x) = wadd (wsingle a w) (wset_of_list x)"
 
definition rel_wset where
  "rel_wset R X Y \<longleftrightarrow> (\<exists>xs ys. wset_of_list xs = X \<and> wset_of_list ys = Y \<and> list_all2 (rel_prod R (=)) xs ys)"
 
bnf "('a, 'w :: ab_semigroup_add) wset"
  map: image_wset
  sets: wset
  bd: natLeq
  wits: "wempty"
  rel: rel_wset
  sorry

(* Definition of weights, weighted sets and graphs*)
class ssr = linorder + ab_semigroup_add +
  (*fixes oplus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "\<oplus>" 65)*)
  fixes otimes :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 70)
  fixes one :: "'a"
  fixes monus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes right_neutral: "t \<otimes> one = t"

definition returnwset :: "'a \<Rightarrow> ('a, 's::ssr) wset" where
  "returnwset el = wsingle el one"


print_classes

instantiation nat :: ssr begin
(*definition oplus_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "oplus_nat a b = min a b"*)
definition otimes_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "otimes_nat a b = a + b"
definition one_nat :: "nat" where "one_nat = 0"
definition monus_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "monus_nat a b = a-b"

instance proof 
  fix t::nat show "t \<otimes> one = t"
    unfolding one_nat_def otimes_nat_def
    by simp
qed end


type_synonym ('a, 's) GraphOfwset = "'a \<Rightarrow> ('a, 's) wset"

(* Scaling of weighted sets *)
context includes wset.lifting begin
lift_definition scalewset :: "'s::ssr \<Rightarrow> ('a, 's) wset \<Rightarrow> ('a, 's) wset" is
  "\<lambda>scalar. \<lambda>w. \<lambda>el. Option.bind (w el) (\<lambda>x. Some(x + scalar))"
  subgoal for scalar w
    apply (auto split: if_splits simp: dom_def)
    by (simp add: bind_eq_Some_conv)
  done
end

(* EDGE SEMIRING *)
(* Graph-union, \<oplus> *)
definition unionGraph :: "('a, 's::ssr) GraphOfwset \<Rightarrow> ('a, 's::ssr) GraphOfwset  \<Rightarrow> ('a, 's::ssr) GraphOfwset" where
  "unionGraph f g x = wadd (f x) (g x)"

(* Empty graph, \<zero> *)
definition emptyGraph :: "('a, 's::ssr) GraphOfwset" where
  "emptyGraph x = wempty"

(* Connect-operator, \<otimes> *)
lift_definition connectGraph :: "('a, 's::ssr) GraphOfwset \<Rightarrow> ('a, 's::ssr) GraphOfwset  \<Rightarrow> ('a, 's::ssr) GraphOfwset" is
   "\<lambda>G1 G2 (u :: 'a) (v :: 'a). let X = {s. \<exists>(w :: 'a) s1 s2.
      G1 u w = Some s1 \<and> G2 w v = Some s2 \<and> s = s1 + s2} in (if X = {} then None else Some (Min X))"
  subgoal for G1 G2 u
    apply (rule finite_subset[where B="\<Union>v \<in> dom (G1 u). dom (G2 v)"])
     apply (auto split: if_splits simp: dom_def)
    done
  done

(* Return-graph, \<one> *)
definition returnGraph :: "('a, 's::ssr) GraphOfwset" where
  "returnGraph x = wset_of_list [(x, one)]"

(* Monad implementation *)
lift_definition bindwset :: "('a, 's::ssr) wset \<Rightarrow> ('a \<Rightarrow> ('b, 's) wset) \<Rightarrow> ('b, 's) wset" is
  "\<lambda>(w :: 'a \<Rightarrow> 's option) k (el :: 'b). (
  let (X :: 's set) = {s. \<exists>x t1 t2. w x = Some t1 \<and> k x el = Some t2 \<and> s = t1 \<otimes> t2} in
  if X = {} then None else Some(Min X))"
  subgoal for w k
    apply (rule finite_subset[where B="\<Union>v \<in> dom w. dom (k v)"])
      apply (auto split: if_splits simp: dom_def)
    done
  done

(* Algorithms with edge semiring *)
(* Naive-star is endlessly recursive, but maybe possibly corecursive
fun naiveStar :: "('a, 's::ssr) GraphOfwset \<Rightarrow> ('a, 's) GraphOfwset" where
  "naiveStar g = unionGraph returnGraph (connectGraph (naiveStar g) g)"*)

fun exp :: "('a, 's::ssr) GraphOfwset \<Rightarrow> nat \<Rightarrow> ('a, 's) GraphOfwset" where
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

context includes wset.lifting begin
lift_definition mapwset :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 's::ssr) wset \<Rightarrow> ('b, 's) wset" is
  "\<lambda>(f::'a \<Rightarrow> 'b). \<lambda>(w::'a \<Rightarrow> 's option). \<lambda>(el:: 'b). 
  (let X = {s. \<exists>x. f x = el \<and> w x = Some s} in
  if X = {} then None else Some(Min X))"
  subgoal for f w
    apply (auto split: if_splits simp: dom_def)
    by (simp add: finite_image_from_w)
  done
end

datatype 'a list_plus = Single 'a | Snoc "'a list_plus" 'a

fun pathed :: "('a, 's::ssr) GraphOfwset \<Rightarrow> ('a list_plus, 's) GraphOfwset" where
  "pathed g (Snoc vs v) = mapwset (\<lambda>t. Snoc (Snoc vs v) t) (g v)" |
  "pathed g (Single v) = mapwset (\<lambda>t. Snoc (Single v) t) (g v)"

context includes wset.lifting begin
lift_definition filtering :: "('a \<Rightarrow> bool) \<Rightarrow> ('a, 's::ssr) GraphOfwset" is
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
  "bowtie (wl, Heap pl chl) (wr, Heap pr chr) = (
    if (wl \<le> wr) then
      (wl, Heap pl ((monus wr wl, Heap pr chr) # chl))
    else
      (wr, Heap pr ((monus wl wr, Heap pl chl) # chr))
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

fun outHeap :: "('s, 'a) heap \<Rightarrow> ('a \<times> (('s \<times> ('s, 'a) heap) list))" where
  "outHeap (Heap p ch) = (p, ch)"

primcorec test_chain :: "'a \<Rightarrow> 's \<Rightarrow> ('s, 'a) chain" where
  "test_chain a s = Chain a (Some(s, test_chain a s))"

primcorec search::"('s::ssr, 'a) heap \<Rightarrow> ('s, 'a) chain" where
  "search h = (
  let (a, h_opt) = map_prod id merges (outHeap h) in
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

type_synonym ('a, 's) LWeighted = "('a \<times> 's) list"

declare [[typedef_overloaded]]
codatatype ('a, 'w::ssr) wsetinf = WSetInf (outwsetinf: "('a, 'w) Forest + 'a")
and ('a ,'w) Forest = Forest "(('a, 'w) wsetinf, 'w) wset"
definition returnwsetinf :: "'a \<Rightarrow> ('a, 'w::ssr) wsetinf" where
"returnwsetinf x = WSetInf (Inr x)"

(*type_synonym ('a, 's) Forest = "(('a, 's) wsetinf, 's) wset"*)
definition returnForest :: "'a \<Rightarrow> ('a, 'w::ssr) Forest" where
"returnForest x = Forest (returnwset (returnwsetinf x))"

(*fun bindForest :: "('a, 'w::ssr) Forest \<Rightarrow> ('a \<Rightarrow> ('b, 'w) Forest) \<Rightarrow> ('b, 'w) Forest" where
"bindForest xs k = (let binder = (
    returnwset \<circ> WSetInf \<circ> Inl \<circ> ((case_sum (\<lambda>ys. bindForest ys k) k) \<circ> outwsetinf)
  ) in
  Forest (bindwset (un_Forest xs) binder))"*)

primcorec bindForest :: "('a, 'w::ssr) Forest \<Rightarrow> ('a \<Rightarrow> ('b, 'w) Forest) \<Rightarrow> ('b, 'w) Forest" 
  and bindwsetinf :: "('a \<Rightarrow> ('b, 'w) Forest) \<Rightarrow> ('a, 'w) wsetinf \<Rightarrow> ('b, 'w) wsetinf" where
  "bindForest xs k = Forest (image_wset (bindwsetinf k) (un_Forest xs))" |
  "bindwsetinf k xs = WSetInf (case outwsetinf xs of 
    Inl ys \<Rightarrow> Inl (bindForest ys k) 
  | Inr xs \<Rightarrow> Inl (k xs))"

lemma bind1[simp] : "bindwset A (f \<circ> g) = bindwset (image_wset g A) f"
  sorry

lemma bind2[simp] : "bindwset A returnwset = A"
  unfolding returnwset_def
  apply(transfer)
  apply(auto simp add: fun_eq_iff right_neutral)
  by (metis option.exhaust)

lemma awd : "bindForest xs k = (let binder = (
    returnwset \<circ> WSetInf \<circ> Inl \<circ> ((case_sum (\<lambda>ys. bindForest ys k) k) \<circ> outwsetinf)
  ) in
  Forest (bindwset (un_Forest xs) binder))"
  apply (subst bindForest.code)
  apply (auto intro!:wset.map_cong simp add:wset.map_comp bindwsetinf.code split:sum.split)
  done

type_synonym ('a, 's) GraphOfForest = "'a \<Rightarrow> ('a, 's) Forest"

definition dfse :: "('a, 's::ssr) GraphOfForest \<Rightarrow> 'a \<Rightarrow> ('a + 'a, 's) Forest" where
  "dfse g x = Forest (wadd (un_Forest (returnForest (Inr x))) (un_Forest (bindForest (g x) (\<lambda>y. returnForest (Inl y)))))"

primcorec dfsForest :: "('a, 's::ssr) GraphOfForest \<Rightarrow> 'a \<Rightarrow> ('a, 's) Forest" 
and dfswsetinf :: "('a, 's::ssr) GraphOfForest \<Rightarrow> ('a, 's) wsetinf \<Rightarrow> ('a, 's) wsetinf" where
  "dfsForest g x = Forest (image_wset (case_sum (dfswsetinf g) id) (wadd (image_wset Inl (un_Forest (g x))) (returnwset (Inr (returnwsetinf x)))))" |
  "dfswsetinf g x = WSetInf (case outwsetinf x of
    Inl el \<Rightarrow> Inl el
    | Inr el \<Rightarrow> (Inl (dfsForest g el)))" (*x is an either, need case*)

(*primcorec dfsForest :: "('a, 's::ssr) GraphOfForest \<Rightarrow> 'a \<Rightarrow> ('a, 's) Forest" and dfswsetinf :: "('a, 's::ssr) GraphOfForest \<Rightarrow> 'a \<Rightarrow> ('a, 's) wsetinf" where
  "dfsForest g x = Forest (wadd (un_Forest (returnForest x)) (un_Forest (bindForest (g x) (\<lambda>y. dfs g y))))" |
  "dfswsetinf g x = undefined"*)

lemma "dfsForest g x = Forest (wadd (un_Forest (returnForest x)) (un_Forest (bindForest (g x) (\<lambda>y. dfs g y))))"

(*fun dijkstra :: "'a \<Rightarrow> ('a, 's) GraphOfwset \<Rightarrow> ('a list_plus) Neighbours" where
  "dijkstra s g = connectwset (pathed g) (filtering uniq)"*)

end
