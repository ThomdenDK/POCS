theory DmitriyProof
  imports "HOL-Library.Finite_Map"
begin

typ "('k, 'v) fmap"
term "fset o fmdom"

term "x :: 'a :: order"

type_synonym ('a, 'w) graph = "'a \<Rightarrow> ('a, 'w) fmap"

context includes fmap.lifting begin
lift_definition connect :: "('a, nat) graph \<Rightarrow> ('a, nat) graph  \<Rightarrow> ('a, nat) graph" is
   "\<lambda>G1 G2 (u :: 'a) (v :: 'a). let X = {s::nat. \<exists>(w :: 'a) s1 s2.
      G1 u w = Some s1 \<and> G2 w v = Some s2 \<and> s = s1 + s2} in (if X = {} then None else Some (Min X))"
  subgoal for G1 G2 u
    apply (rule finite_subset[where B="\<Union>v \<in> dom (G1 u). dom (G2 v)"])
     apply (auto split: if_splits simp: dom_def)
    done
  done
end