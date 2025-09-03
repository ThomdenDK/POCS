theory Scratch
  imports Main

begin

class ssr =
  fixes oplus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "\<oplus>" 65)
  fixes otimes :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 70)
  fixes one :: "'a"

(*Since it is impossible to quantify over type constructors in Isabelle, 
we cannot make a generic set type in the GraphOf type definition, and must make a class*)
class Neighbors =
  fixes union :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

(*The ssr option is not enforced anywhere, and this enforcement is not possible in a
type synonym. Consider switching to a definition.*)
(*typedef ('a, 's::ssr) wset = "{f :: 'a \<Rightarrow> 's option. True}"*)
type_synonym ('a, 's) wset = "'a \<Rightarrow> 's::ssr option"
definition wempty :: "('a, 's) wset" where "wempty x = None"

fun wunion :: "('a, 's::ssr) wset \<Rightarrow> ('a, 's) wset \<Rightarrow> ('a, 's) wset"
  where 
    "wunion v w x = (case (v x, w x) of
        (Some a, Some b) \<Rightarrow> Some (a \<oplus> b)
      | (Some a, None)   \<Rightarrow> Some a
      | (None, Some b)   \<Rightarrow> Some b
      | (None, None)     \<Rightarrow> None)"

notation wunion (infixl "\<union>" 65)

fun wscale :: "'s::ssr \<Rightarrow> ('a, 's) wset \<Rightarrow> ('a, 's) wset"
  where 
    "wscale s v x = Option.bind (v x) (\<lambda>a. Some (s \<otimes> a))"

notation wscale (infixl "⋊" 65)

type_synonym ('a, 's) GraphOf = "'a \<Rightarrow> ('a, 's) wset"
definition empty :: "('a, 's) GraphOf" where "empty x = wempty"

fun gunion :: "('a, 's::ssr) GraphOf \<Rightarrow> ('a, 's) GraphOf \<Rightarrow> ('a, 's) GraphOf" where
  "gunion f g x = f x \<union> g x" 
(*warning about ambiguous \<union>, no problem because of type inference*)

notation gunion (infixl "⊞" 65)

definition return :: "('a, 's::ssr) GraphOf" where
  "return x = (\<lambda>y. if y = x then Some one else None)"

fun graph_invert :: "('a, 's) GraphOf \<Rightarrow> ('a, 's) GraphOf" where
  "graph_invert f x a = f a x"

definition wset_as_set :: "('a,'s) wset \<Rightarrow> ('s \<times> 'a) set" where
  "wset_as_set f = {(y,x). f x = Some y}"

(*
I ask, is d in the connect set of a?
connect asks g, is d in the g set of anything?
g says, yes it is my g set of b with a weight of 3.
connect asks f, is a in the b set of f?
f says, yes, with a weight of 1.
connect says yes, a is in the connect set of a with a weight of 3 + 1 = 4.
I can ask a node what neighbors it points to.
But how can i ask what is pointing to a node?
Since the types are potentially infinitely big, it is not possible without 
predicates which compromises computability
*)
fun connect :: "('a, 's::ssr) GraphOf \<Rightarrow> ('a, 's) GraphOf \<Rightarrow> ('a, 's) GraphOf" where
  "connect f g x y = (
    let nodes_pointed_to_from_x_via_f = {(w, v). f x = Some v} in
    let nodes_pointing_to_y_via_g = {(w, v). g v = y} in
  )"
    (*let g' = graph_invert g in 
    let gxset = wset_as_set (g' x) in
    let nodes_from_gxset = {(a,b). (a,b) \<in> gxset & b = y} in
    

*)
(*
f a = {1 > b, 2 > c}
g b = {1 > a, 3 > d}
connect f g a = {2 > a, 4 > d}
*)


codatatype ('s, 'a) heap = Heap 'a (('s \<times> ('s, 'a) heap) list)

end
