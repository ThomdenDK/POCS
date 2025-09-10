theory Scratch
  imports Main "HOL.Rings"

begin

class ssr = order +
  fixes oplus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "\<oplus>" 65)
  fixes otimes :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 70)
  fixes one :: "'a"
  (*assume assoc*)

(*Since it is impossible to quantify over type constructors in Isabelle, 
we cannot make a generic set type in the GraphOf type definition, and must make a class*)
type_synonym ('a, 's) Weighted = "('s \<times> 'a) list"

definition scaleWeighted :: "'s::ssr \<Rightarrow> ('a, 's) Weighted \<Rightarrow> ('a, 's) Weighted" where
  "scaleWeighted p = map (\<lambda>(els, ela). (els \<oplus> p, ela))"

definition returnWeighted :: "'a \<Rightarrow> ('a, 's::ssr) Weighted " where
  "returnWeighted x = [(one, x)]"

fun bindWeighted :: "('a, 's::ssr) Weighted \<Rightarrow> ('a \<Rightarrow> ('a, 's) Weighted) \<Rightarrow> ('a, 's) Weighted" where
  "bindWeighted [] k = []" |
  "bindWeighted ((p, x) # xs) k = (scaleWeighted p (k x)) @ (bindWeighted xs k)"

type_synonym ('a, 's) GraphOfWeighted = "'a \<Rightarrow> ('a, 's) Weighted"
(*typedef ('a, 's) GraphOfWeighted = "UNIV :: ('a \<Rightarrow> ('a, 's) Weighted) set"
  by auto*)

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

fun connect :: "('a, 's::ssr) GraphOf \<Rightarrow> ('a, 's) GraphOf \<Rightarrow> ('a, 's) GraphOf" where
  "connect f g node el = (
    let gnodes = {(w, x). g x el = Some w} in
    let fnodes = {w. \<exists>y w1 w2. f node y = Some w1 \<and> (w2, y) \<in> gnodes \<and> w = w1 \<oplus> w2} in
    if fnodes = {} then None
    else Some (SOME w. w \<in> fnodes \<and> (\<forall>y \<in> fnodes. y \<ge> w))
)"

fun connectWeighted :: "('a, 's::ssr) GraphOfWeighted \<Rightarrow> ('a , 's) GraphOfWeighted \<Rightarrow> ('a, 's) GraphOfWeighted" where
  "connectWeighted f g x = 
    fold (\<lambda>(els, ela) acc. (map (\<lambda>(gs, ga). (gs \<oplus> els, ga)) (g ela)) @ acc) (f x) []"

fun graphUnionWeighted :: "('a, 's::ssr) GraphOfWeighted \<Rightarrow> ('a , 's) GraphOfWeighted \<Rightarrow> ('a, 's) GraphOfWeighted" where
  "graphUnionWeighted f g x = f x @ g x"

fun naiveStar :: "('a, 's::ssr) GraphOfWeighted \<Rightarrow> ('a, 's) GraphOfWeighted" where
  "naiveStar g = graphUnionWeighted returnWeighted (connectWeighted (naiveStar g) g)"

fun exp :: "('a, 's::ssr) GraphOfWeighted \<Rightarrow> nat \<Rightarrow> ('a, 's) GraphOfWeighted" where
  "exp g 0 = returnWeighted" |
  "exp g (Suc n) = connectWeighted g (exp g n)"

(*instantiation Weighted :: "Monad"
begin
end*)

codatatype ('s, 'a) heap = Heap 'a "(('s \<times> ('s, 'a) heap) list)"

term un_Heap1
term un_Heap2

end
