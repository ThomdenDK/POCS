theory WSet
  imports Main 
    "HOL-Library.Tree"
    "HOL-Library.Multiset" 
    "HOL-ex.Sketch_and_Explore" 
    "HOL-Combinatorics.List_Permutation"
begin

subsection \<open>The type of weighted sets\<close>

instantiation option :: (ab_semigroup_add) comm_monoid_add begin
definition zero_option where "zero_option = None"
definition plus_option where "plus_option a b = (case (a, b) of (Some x, Some y) \<Rightarrow> Some (x + y) | (Some x, None) \<Rightarrow> Some x | (None, Some x) \<Rightarrow> Some x | _ \<Rightarrow> None)"
instance
  by standard (auto simp: zero_option_def plus_option_def ac_simps split: option.splits)
end

class ab_semigroup_add_test = ab_semigroup_add +
  assumes common_splitting: "(a :: 'a :: ab_semigroup_add) + b = c + d \<Longrightarrow> 
  (\<exists> (e11 :: ('a :: ab_semigroup_add) option) e12 e21 e22. Some a = e11 + e12 \<and>
    Some b = e21 + e22 \<and> Some c = e11 + e21 \<and> Some d = e12 + e22)"

lemma plus_option_simps [simp]: "a + None = a" "None + a = a" "Some a + Some b = Some (a + b)"
  unfolding add.right_neutral add.left_neutral zero_option_def[symmetric]
  unfolding plus_option_def
  by auto

instantiation option :: (ab_semigroup_add_test) ab_semigroup_add_test begin
instance
proof-
  have H: "b = c + d \<Longrightarrow> \<exists>e11 e12. Some None = e11 + e12 \<and> (\<exists>e21 e22. Some (c + d) = e21 + e22 \<and> Some c = e11 + e21 \<and> Some d = e12 + e22)" for b c d
    apply(rule exI[where x = "Some None"])
    apply(rule exI[where x = "Some None"])
    apply simp
    apply(rule exI[where x = "Some c"])
    apply(rule exI[where x = "Some d"])
    by simp
  show "OFCLASS('a option, ab_semigroup_add_test_class)"
  apply standard
    subgoal for a b c d
      apply(cases a, simp, drule H)
      subgoal
        by metis
      apply(cases b, simp, drule H)
      subgoal
        by (metis add.commute)
      apply(cases c, simp, drule sym, frule H)
      subgoal
        by (metis add.commute)
      apply(cases d, simp, drule sym, frule H)
      subgoal
        by (metis add.commute)
      subgoal for a' b' c' d'
        unfolding plus_option_def[of a] plus_option_def[of c]
        apply simp
        apply(drule common_splitting[of a' b' c' d'])
        apply(erule exE)+
        subgoal for e11 e12 e21 e22
          apply(rule exI[where x = "Some e11"])
          apply(rule exI[where x = "Some e12"])
          apply simp
          apply(rule exI[where x = "Some e21"])
          apply(rule exI[where x = "Some e22"])
          by simp
        done
      done
    done
qed
end

typedef ('a, 'w :: ab_semigroup_add_test) wset = \<open>{f :: 'a \<Rightarrow> 'w option. finite {x. f x \<noteq> None}}\<close>
  morphisms weight Abs_wset
proof
  show \<open>(\<lambda>x. None) \<in> {f. finite {x. f x \<noteq> None}}\<close>
    by simp
qed

setup_lifting type_definition_wset

lift_definition wempty :: \<open>('a, 'w :: ab_semigroup_add_test) wset\<close> is
  \<open>\<lambda>a. None\<close>
  by simp

lift_definition wsingle :: \<open>'a \<Rightarrow> 'w \<Rightarrow> ('a, 'w :: ab_semigroup_add_test) wset\<close> is
  \<open>\<lambda>a w b. if a = b then Some w else None\<close>
  by simp

lift_definition wset :: \<open>('a, 'w :: ab_semigroup_add_test) wset \<Rightarrow> 'a set\<close> is
  \<open>\<lambda>M. {x. M x \<noteq> None}\<close> .

lift_definition wadd :: \<open>('a, 'w :: ab_semigroup_add_test) wset \<Rightarrow> ('a, 'w) wset \<Rightarrow> ('a, 'w) wset\<close> is
  \<open>\<lambda>M1 M2 x. M1 x + M2 x\<close>
  by (erule (1) finite_subset[rotated, OF finite_Un[THEN iffD2, OF conjI]]) (auto simp: plus_option_def split: option.splits)

lift_definition wupdate :: \<open>('a, 'w :: ab_semigroup_add_test) wset \<Rightarrow> 'a \<Rightarrow> 'w option \<Rightarrow> ('a, 'w) wset\<close> is
  \<open>\<lambda>M x w x'. if x = x' then w else M x'\<close>
  subgoal for fun' a
    apply(drule finite_UnI[where G = "{a}"])
    subgoal by simp
    apply(erule rev_finite_subset)
    by auto
  done

lift_definition image_wset :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'w :: ab_semigroup_add_test) wset \<Rightarrow> ('b, 'w) wset" is
  \<open>\<lambda>f M b. Finite_Set.fold (\<lambda>x y. M x + y) None {a. M a \<noteq> None \<and> f a = b}\<close>
  subgoal for f M
    apply (erule finite_surj[of _ _ f])
    apply safe
    subgoal for b w
      unfolding image_def
      apply simp
      apply(cases "{} = {a. (\<exists>y. M a = Some y) \<and> f a = b}")
      by auto
    done
  done

instantiation wset :: (type, type) size
begin

definition size_wset where
  size_wset_overloaded_def: "size_wset M = card (wset M)"
instance ..

end

lemma w_finite_fold: "finite {x. \<exists>y. Finite_Set.fold h None {a. (\<exists>y. weight g a = Some y) \<and> f a = x} = Some y}"
  apply(rule rev_finite_subset[where B = "{x. \<exists>xa y. f xa = x \<and> weight g xa = Some y}"])
  subgoal
    using weight[where x = g]
    apply simp
    apply(drule finite_imageI[where h = f])
    unfolding image_def
    by (smt (verit, ccfv_SIG) Collect_cong mem_Collect_eq)
  subgoal
    apply safe
    by (smt (verit) UNIV_def empty_Collect_eq empty_def finite_def fold_empty image_id map_fun_id option.distinct(1) wset_def)
  done

fun wset_of_list :: "('a \<times> 'w) list \<Rightarrow> ('a, 'w :: ab_semigroup_add_test) wset" where
  "wset_of_list [] = wempty" |
  "wset_of_list ((a, w) # x) = wadd (wsingle a w) (wset_of_list x)"

definition rel_wset where
  "rel_wset R X Y \<longleftrightarrow> (\<exists>xs ys. wset_of_list xs = X \<and> wset_of_list ys = Y \<and> list_all2 (rel_prod R (=)) xs ys)"


lemma Abs_wset_inverse_help: " weight (Abs_wset y) x = z \<Longrightarrow> y \<in> {f. finite {x. f x \<noteq> None}} \<Longrightarrow> y x = z"
  using Abs_wset_inverse by force

lemma Abs_wset_inverse_help'': "y \<in> {f. finite {x. f x \<noteq> None}} \<Longrightarrow> \<exists> z. y x = Some z \<Longrightarrow> \<exists> z. weight (Abs_wset y) x = Some z"
  using Abs_wset_inverse
  by fastforce

lemma finite_set_fold_some': "Finite_Set.fold (+) None s = Some w \<Longrightarrow> finite s \<Longrightarrow> \<exists>w'. Some w' \<in> s"
  apply(cases "s = {}"; simp?)
  apply(cases "s = {None}"; simp?)
  by (metis insertI1 is_singletonI' is_singleton_some_elem not_None_eq)

lemma finite_set_fold_some: "finite s \<Longrightarrow> w' \<in> s \<Longrightarrow> weight g w' \<noteq> None \<Longrightarrow> \<exists>w. Finite_Set.fold (\<lambda>x. (+) (weight g x)) None s = Some w"
  using comp_fun_commute_on.fold_rec[where f = "(\<lambda>x. (+) (weight g x))" and S = s and A = s and x = "w'" and z = None]
  apply -
  apply safe
  apply simp
  apply(drule impI)
  apply(erule impE)
  subgoal
    using add.left_commute
    unfolding comp_fun_commute_on_def
    by fastforce
  subgoal for w
    apply(rule exI[where x = "case Finite_Set.fold (\<lambda>x. (+) (weight g x)) None (s - {w'}) of None \<Rightarrow> w | Some w'' \<Rightarrow> w + w''"])
    apply(cases "Finite_Set.fold (\<lambda>w. (+) (weight g w)) None (s - {w'})")
    unfolding plus_option_def
    by auto
  done

lemma finite_set_fold_eq: "\<forall> x. Finite_Set.fold eq1 None (s1 x) = Finite_Set.fold eq2 None (s2 x) \<Longrightarrow> (\<lambda>x. Finite_Set.fold eq1 None (s1 x)) = (\<lambda>x. Finite_Set.fold eq2 None (s2 x))"
  by simp

abbreviation fold' where
  "fold' l \<equiv> foldl (+) (hd l) (tl l)"

abbreviation mf where
  "mf l a \<equiv> map snd (filter (\<lambda> (x,w). x = a) l)"

lemma wadd_wsingle_wempty: "wadd (wsingle a b) M \<noteq> wempty"
  apply(rule notI)
  apply(drule arg_cong[where f = weight])
  apply(simp add: wempty.rep_eq wadd.rep_eq wsingle.rep_eq plus_option_def)
  apply(drule fun_cong[where x = a])
  apply(cases "weight M a")
  by auto

inductive list_split :: "('a\<times>'w :: ab_semigroup_add_test) list \<Rightarrow> ('a\<times>'w) list \<Rightarrow> bool" where
  Base: "list_split [] []"
| Split: "list_split xs'' ys \<Longrightarrow> xs = xs' @ xs'' \<Longrightarrow> w = fold' (map snd xs') \<Longrightarrow> xs' \<noteq> [] \<Longrightarrow> list_all (\<lambda> (a,b). a = y) xs' \<Longrightarrow> list_split xs ((y,w) # ys)"

inductive list_split' :: "((('w :: ab_semigroup_add_test) option) list) list \<Rightarrow> ('w option) list \<Rightarrow> bool" where
  Base': "list_split' [] []"
| Split': "list_split' xss ys \<Longrightarrow> y = fold' xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> list_split' (xs # xss) (y # ys)"

lemma list_split'_length: "list_split' xs ys \<Longrightarrow> length xs = length ys"
  apply(induction xs arbitrary: ys)
  by(auto elim: list_split'.cases)+

lemma wset_of_list_weight: "wset_of_list xs = wset_of_list [(y,w)] \<Longrightarrow> \<forall>x. x \<noteq> y \<longrightarrow> weight (wset_of_list xs) x = None"
  proof (induction xs arbitrary: y w)
    case Nil
    then show ?case
      by(simp add: weight_inject[symmetric] wempty.rep_eq wadd.rep_eq wsingle.rep_eq)
  next
    fix a :: "'a \<times> 'b"
      and xs :: "('a \<times> 'b) list"
      and y :: 'a
      and w :: 'b
    assume ind: "\<And>y w. wset_of_list xs = wset_of_list [(y, w)] \<Longrightarrow> \<forall>x. x \<noteq> y \<longrightarrow> weight (wset_of_list xs) x = None"
      and eq: "wset_of_list (a # xs) = wset_of_list [(y, w)]"
    obtain x' w' where a_def: "a = (x',w')"
      by fastforce
    show "\<forall>x. x \<noteq> y \<longrightarrow> weight (wset_of_list (a # xs)) x = None"
      using eq ind
      unfolding a_def
      by(auto simp add: wempty.rep_eq wadd.rep_eq wsingle.rep_eq)
  qed

lemma list_split_all_same: 
  assumes H: "wset_of_list xs = wset_of_list [(y,w)]"
  shows "list_all (\<lambda> (a,b). a = y) xs"
proof -
  have H2: "(\<forall>x. x \<noteq> y \<longrightarrow> weight (wset_of_list xs) x = None) \<Longrightarrow> list_all (\<lambda> (a,b). a = y) xs"
  proof (induction xs arbitrary: y)
    case Nil
    then show ?case
      by auto
  next
    fix a :: "'a \<times> 'b"
      and xs :: "('a \<times> 'b) list"
      and y :: 'a
    assume ind: "\<And>y. \<forall>x. x \<noteq> y \<longrightarrow> weight (wset_of_list xs) x = None \<Longrightarrow> list_all (\<lambda>(a, b). a = y) xs"
      and eq: "\<forall>x. x \<noteq> y \<longrightarrow> weight (wset_of_list (a # xs)) x = None"
    obtain x' w' where a_def: "a = (x',w')"
      by fastforce
    have x'_def: "x' = y"
      using eq
      unfolding a_def
      by(cases "weight (wset_of_list xs) x'"; auto simp add: wadd.rep_eq wsingle.rep_eq wempty.rep_eq plus_option_def)
    show "list_all (\<lambda>(a, b). a = y) (a # xs)"
      using eq
      unfolding a_def x'_def
      apply simp
      apply(rule ind[of y])
      by(auto intro: simp add: wadd.rep_eq wsingle.rep_eq wempty.rep_eq)
  qed
  show ?thesis
    using H wset_of_list_weight H2
    by fast
qed

lemma foldl_assoc: "(\<And>a b c. f (f a b) c = f a  (f b c)) \<Longrightarrow> f z (foldl f y xs) = foldl f (f z y) xs"
  by(induction xs arbitrary: z y; auto)

lemma wset_of_list_fold: 
  "wset_of_list xs = wset_of_list [(y,w)] \<Longrightarrow> w = fold' (map snd xs)"
proof (induction xs arbitrary: y w)
  case Nil
  then show ?case
    apply(simp add: weight_inject[symmetric] wempty.rep_eq wadd.rep_eq wsingle.rep_eq)
    by(drule fun_cong[where x = y]; simp)
next
  fix a :: "'a \<times> 'b"
    and xs :: "('a \<times> 'b) list"
    and y :: 'a
    and w :: 'b
  assume ind: "\<And>y w. wset_of_list xs = wset_of_list [(y, w)] \<Longrightarrow> w = fold' (map snd xs)"
    and eq: "wset_of_list (a # xs) = wset_of_list [(y, w)]"
  obtain x' w' where a_def: "a = (x',w')"
    by fastforce
  have x'_def: "x' = y"
    using list_split_all_same[where y = y and w = w and xs = "(a # xs)"] eq
    unfolding a_def
    by simp
  have Nil: "weight (wset_of_list xs) y = None \<Longrightarrow> xs = []"
    apply(cases xs; simp)
    subgoal for a' xs'
      apply(cases a')
      subgoal for a1' a2'
        using eq
        apply -
        apply(drule list_split_all_same)
        unfolding a_def
        by(cases "weight (wset_of_list xs') y"; auto simp add: wadd.rep_eq wempty.rep_eq wsingle.rep_eq plus_option_def)
      done
    done
  have App: "\<And>w''. weight (wset_of_list xs) y = Some w'' \<Longrightarrow> wset_of_list xs = wset_of_list [(y, w'')]"
    subgoal for w''
      apply(simp add: weight_inject[symmetric] fun_eq_iff)
      apply(rule allI)
      subgoal for x
        using eq
        unfolding a_def x'_def
        apply - 
        apply(drule wset_of_list_weight)
        apply(erule allE[where x = x])
        by(cases "x = y"; (simp add: wsingle.rep_eq wadd.rep_eq wempty.rep_eq))
      done
    done
  show "w = fold' (map snd (a # xs))"
    using eq
    unfolding a_def x'_def
    apply(simp only: weight_inject[symmetric])
    apply(drule fun_cong[where x = y])
    apply(simp add: wadd.rep_eq wempty.rep_eq wsingle.rep_eq)
    apply(cases "weight (wset_of_list xs) y =  None")
    subgoal
      using Nil
      by auto
    subgoal
      apply safe
      subgoal for w''
        apply(simp add: plus_option_def)
        apply(cases xs)
        subgoal
          by(simp add: wempty.rep_eq)
        apply(drule App)
        apply(drule ind)
        by (simp add: add.assoc foldl_assoc)
      done
    done
qed

lemma wset_of_list_one: "wset_of_list xs = wset_of_list [(y,w)] \<Longrightarrow> list_split xs ((y,w) # [])"
  apply(rule list_split.intros(2)[where xs'' = "[]" and xs' = xs])
  subgoal
    by(auto intro: list_split.intros)
  subgoal
    by simp
  subgoal
    using wset_of_list_fold
    by simp
  subgoal
    apply(cases xs; simp)
    apply(simp add: weight_inject[symmetric] wempty.rep_eq wadd.rep_eq wsingle.rep_eq)
    by(drule fun_cong[where x = y]; simp)
  subgoal
    using list_split_all_same
    by simp
  done

lemma list_split_empty: "\<forall>a. list_split (mf xs a) [] \<Longrightarrow> xs = []"
  apply(cases xs; safe)
  subgoal for x' w
    apply(erule allE[where x = x'])
    by(auto elim: list_split.cases)
  done

lemma list_split_refl: "list_split xs xs"
proof(induction xs)
  case Nil
  then show ?case
    by(auto intro: list_split.intros)
next
  case (Cons x xs)
  then show ?case
    apply(cases x)
    subgoal for x1 x2
      by(auto intro: list_split.intros)
    done
qed

lemma list_split'_empty: "\<forall>a. list_split' (mf xs a) [] \<Longrightarrow> xs = []"
  apply(cases xs; safe)
  subgoal for x' x'' xs'
    apply(erule allE[where x = x'])
    by(force elim: list_split'.cases)
  done

lemma list_split'_refl: "list_split' (map (\<lambda>x. [x]) xs) xs"
proof(induction xs)
  case Nil
  then show ?case
    by(auto intro: list_split'.intros)
next
  case (Cons x xs)
  then show ?case
    by(auto intro: list_split'.intros)
qed

lemma wset_of_list_Mem: "weight (wset_of_list xs) x \<noteq> None = (\<exists> w. ListMem (x, w) xs)"
proof(induction xs)
  case Nil
  then show ?case
    by(auto simp add: wempty.rep_eq elim: ListMem.cases)
next
  case (Cons a xs)
  then show ?case
    apply(cases a)
    by(auto simp add: wadd.rep_eq wsingle.rep_eq plus_option_def intro: ListMem.insert ListMem.elem elim: ListMem.cases)
qed

fun option_list :: "('a option) list \<Rightarrow> 'a list" where
  "option_list [] = []" |
  "option_list (None # l) = option_list l" |
  "option_list (Some a # l) = a # option_list l"

lemma fold_option_not_none: "Some a = fold' l \<Longrightarrow> l \<noteq> [] \<Longrightarrow> (option_list l) \<noteq> []"
  apply(induction l arbitrary: a)
  subgoal
    by simp
  subgoal for a l aa
    apply(cases a; cases l)
    by auto
  done

lemma fold_option: "Some a = fold' l \<Longrightarrow> l \<noteq> [] \<Longrightarrow> a = fold' (option_list l)"
proof -
  have H: "\<And> x x' l. Some x = foldl (+) (Some x') l \<Longrightarrow> x = foldl (+) x' (option_list l)"
    subgoal for x x' l
      apply(induction l arbitrary: x x'; simp)
      subgoal for a l x x'
        apply(cases a)
        by(auto simp add: plus_option_def split: option.split)
      done
    done
  show "Some a = fold' l \<Longrightarrow> l \<noteq> [] \<Longrightarrow> a = fold' (option_list l)"
    apply(induction l arbitrary: a)
    subgoal
      by simp
    subgoal for a l aa
      apply(cases a)
      subgoal
        apply(cases l)
        by auto
      subgoal for a'
        using H[of aa a' l]
        by simp
      done
    done
qed

fun create_split :: "('a \<times> 'w) list \<Rightarrow> ('a \<Rightarrow> (('w option) list) list) \<Rightarrow> ('a \<times> 'w) list" where
  "create_split [] als = []" |
  "create_split ((a,_) # l) als =  map (\<lambda>x. (a,x)) (option_list (hd (als a))) @ (create_split l (als(a := tl(als a))))"

fun create_sum_tree :: "('w :: ab_semigroup_add) list \<Rightarrow> 'w tree" where
  "create_sum_tree [] = \<langle>\<rangle>" |
  "create_sum_tree [x] = \<langle>\<langle>\<rangle>, x, \<langle>\<rangle>\<rangle>" |
  "create_sum_tree (x # xs) = \<langle>\<langle>\<langle>\<rangle>, x, \<langle>\<rangle>\<rangle>, fold (+) xs x , create_sum_tree xs\<rangle>"

lemma list_split'_exist: 
  "((xs \<noteq> [] \<and> ys \<noteq> []) \<longrightarrow> fold' (xs :: (('w :: ab_semigroup_add_test) option) list) = fold' ys) \<Longrightarrow>
    ((xs = []) = (ys = [])) \<Longrightarrow>
  (\<exists>zs zs'. list_split' zs xs \<and> list_split' zs' ys \<and> (\<forall>n m. n < length xs \<longrightarrow> m < length ys \<longrightarrow> zs ! n ! m = zs' ! m ! n) \<and> 
    list_all (\<lambda> l. length l = length ys) zs \<and> list_all (\<lambda> l. length l = length xs) zs')"
proof (induction "length xs + length ys" arbitrary: xs ys rule: nat_less_induct)
  fix xs :: "('w option) list"
    and ys :: "('w option) list"
  assume ind: "\<forall>m<length (xs :: (('w :: ab_semigroup_add_test) option) list) + length ys.
          \<forall>(x :: (('w :: ab_semigroup_add_test) option) list) xa.
             m = length x + length xa \<longrightarrow>
             (x \<noteq> [] \<and> xa \<noteq> [] \<longrightarrow> fold' x = fold' xa) \<longrightarrow>
             (x = []) = (xa = []) \<longrightarrow>
             (\<exists>zs zs'.
                 list_split' zs x \<and> list_split' zs' xa \<and> (\<forall>n m. n < length x \<longrightarrow> m < length xa \<longrightarrow> zs ! n ! m = zs' ! m ! n) \<and> list_all (\<lambda>l. length l = length xa) zs \<and> list_all (\<lambda>l. length l = length x) zs')"
    and eq_app: "(xs \<noteq> [] \<and> ys \<noteq> []) \<longrightarrow> fold' (xs :: (('w :: ab_semigroup_add_test) option) list) = fold' ys"
    and eq_nil: "(xs = []) = (ys = [])"
  have ind: "\<And>(x :: (('w :: ab_semigroup_add_test) option) list) xa.
             length x + length xa < length xs + length ys \<Longrightarrow>
             (x \<noteq> [] \<and> xa \<noteq> [] \<longrightarrow> fold' x = fold' xa) \<Longrightarrow>
             (x = []) = (xa = []) \<Longrightarrow>
             (\<exists>zs zs'.
                 list_split' zs x \<and> list_split' zs' xa \<and> (\<forall>n m. n < length x \<longrightarrow> m < length xa \<longrightarrow> zs ! n ! m = zs' ! m ! n) \<and> list_all (\<lambda>l. length l = length xa) zs \<and> list_all (\<lambda>l. length l = length x) zs')"
    using ind by auto
  have gt3_cases: "\<And>(xs :: 'w option list) ys. ((xs = []) = (ys = [])) \<Longrightarrow>
            ((xs \<noteq> [] \<and> ys \<noteq> []) \<longrightarrow> fold' (xs :: (('w :: ab_semigroup_add_test) option) list) = fold' ys) \<Longrightarrow>
            (\<And>(x :: (('w :: ab_semigroup_add_test) option) list) xa.
             length x + length xa < length xs + length ys \<Longrightarrow>
             (x \<noteq> [] \<and> xa \<noteq> [] \<longrightarrow> fold' x = fold' xa) \<Longrightarrow>
             (x = []) = (xa = []) \<Longrightarrow>
             (\<exists>zs zs'.
                 list_split' zs x \<and> list_split' zs' xa \<and> (\<forall>n m. n < length x \<longrightarrow> m < length xa \<longrightarrow> zs ! n ! m = zs' ! m ! n) \<and> list_all (\<lambda>l. length l = length xa) zs \<and> list_all (\<lambda>l. length l = length x) zs')) \<Longrightarrow>
2 < length xs \<Longrightarrow> \<exists>zs zs'.
       list_split' zs xs \<and>
       list_split' zs' ys \<and>
       (\<forall>n m. n < length xs \<longrightarrow> m < length ys \<longrightarrow> zs ! n ! m = zs' ! m ! n) \<and>
       list_all (\<lambda>l. length l = length ys) zs \<and> list_all (\<lambda>l. length l = length xs) zs'"
    subgoal for xs ys
    proof -
      assume len: "2 < length xs"
        and eq_nil: "(xs = []) = (ys = [])"
        and eq_app: "(xs \<noteq> [] \<and> ys \<noteq> []) \<longrightarrow> fold' (xs :: (('w :: ab_semigroup_add_test) option) list) = fold' ys"
        and ind: "\<And>(x :: (('w :: ab_semigroup_add_test) option) list) xa.
             length x + length xa < length xs + length ys \<Longrightarrow>
             (x \<noteq> [] \<and> xa \<noteq> [] \<longrightarrow> fold' x = fold' xa) \<Longrightarrow>
             (x = []) = (xa = []) \<Longrightarrow>
             (\<exists>zs zs'.
                 list_split' zs x \<and> list_split' zs' xa \<and> (\<forall>n m. n < length x \<longrightarrow> m < length xa \<longrightarrow> zs ! n ! m = zs' ! m ! n) \<and> list_all (\<lambda>l. length l = length xa) zs \<and> list_all (\<lambda>l. length l = length x) zs')"
      obtain x x' xs' where xs_def: "xs = x # x' # xs'" and xs'_nil: "xs' \<noteq> []"
        using len
        by (metis One_nat_def Suc_1 Suc_eq_plus1 length_0_conv length_Cons less_nat_zero_code list.exhaust not_add_less1 verit_comp_simplify1(1))
      have "\<exists> zs zs'. list_split' zs ((x + x') # xs') \<and>
       list_split' zs' ys \<and>
       (\<forall>n m. n < length ((x + x') # xs') \<longrightarrow> m < length ys \<longrightarrow> zs ! n ! m = zs' ! m ! n) \<and>
       list_all (\<lambda>l. length l = length ys) zs \<and> list_all (\<lambda>l. length l = length ((x + x') # xs')) zs'"
        using ind[of "(x + x') # xs'" ys] eq_app eq_nil
        unfolding xs_def
        by auto
      obtain zs zs' where ind1: "list_split' zs ((x + x') # xs') \<and>
       list_split' zs' ys \<and>
       (\<forall>n m. n < length ((x + x') # xs') \<longrightarrow> m < length ys \<longrightarrow> zs ! n ! m = zs' ! m ! n) \<and>
       list_all (\<lambda>l. length l = length ys) zs \<and> list_all (\<lambda>l. length l = length ((x + x') # xs')) zs'"
        using ind[of "(x + x') # xs'" ys] eq_app eq_nil
        unfolding xs_def
        by auto
      have "\<exists>zsa zs'.
     list_split' zsa [x, x'] \<and>
     list_split' zs' (hd zs) \<and>
     (\<forall>n m. n < length [x, x'] \<longrightarrow> m < length (hd zs) \<longrightarrow> zsa ! n ! m = zs' ! m ! n) \<and> list_all (\<lambda>l. length l = length (hd zs)) zsa \<and> list_all (\<lambda>l. length l = length [x, x']) zs'"
        apply(rule ind[of "[x, x']" "hd zs"])
        subgoal
          using len eq_nil ind1
          apply(cases zs)
          by(auto elim: list_split'.cases simp add: less_eq_Suc_le)
        subgoal
          using len eq_nil ind1
          by(auto elim: list_split'.cases simp add: ab_semigroup_add_class.add.commute)
        subgoal
          using len eq_nil ind1
          by(auto elim: list_split'.cases simp add: ab_semigroup_add_class.add.commute)
        done
      then obtain zs1 zs1' where ind2: "list_split' zs1 [x, x'] \<and> list_split' zs1' (hd zs) \<and>
     (\<forall>n m. n < length [x, x'] \<longrightarrow> m < length (hd zs) \<longrightarrow> zs1 ! n ! m = zs1' ! m ! n) \<and> list_all (\<lambda>l. length l = length (hd zs)) zs1 \<and> list_all (\<lambda>l. length l = length [x, x']) zs1'"
        by blast
      have H1: "list_split' (zs1 ! 0 # zs1 ! 1 # tl zs) xs"
        using ind1 ind2
        unfolding xs_def
        apply(cases zs1)
        subgoal
          by(auto elim: list_split'.cases)
        subgoal for e zss1
          apply(cases zss1)
          by(auto intro!: list_split'.intros elim: list_split'.cases)
        done
      have "\<And>m n. m < length ys \<longrightarrow> zs ! 0 ! m = zs' ! m ! 0" "list_split' zs' ys" "list_split' zs1' (hd zs)" "list_all (\<lambda>l. length l = length [x, x']) zs1'" "list_all (\<lambda>l. length l = length ys) zs"
        using ind1 ind2 by auto
      also have len_zs1': "length zs1' = length ys" 
        using ind1 ind2 list_split'_length
        by (metis (mono_tags, lifting) hd_conv_nth length_greater_0_conv list.distinct(1) list_all_length)
      moreover have "ys \<noteq> [] \<Longrightarrow> zs \<noteq> []"
        using ind1 
        by (auto elim: list_split'.cases)
      ultimately have H2: "list_split' (map2 (\<lambda>l l'. (l' ! 0) # (l' ! 1) # (tl l)) zs' zs1') ys"
        sketch(induction ys arbitrary: zs zs' zs1')
      proof (induction ys arbitrary: zs zs' zs1')
        case Nil
        then show ?case
          by(auto intro: list_split'.intros dest: list_split'.cases)
      next
        fix y :: "'w option"
          and ys :: "'w option list"
          and zs :: "'w option list list"
          and zs' :: "'w option list list"
          and zs1' :: "'w option list list"
        assume ind: "\<And>zs zs' zs1'. (\<And>m. m < length ys \<longrightarrow> zs ! 0 ! m = zs' ! m ! 0) \<Longrightarrow> list_split' zs' ys \<Longrightarrow> list_split' zs1' (hd zs) \<Longrightarrow> list_all (\<lambda>l. length l = length [x, x']) zs1' \<Longrightarrow> list_all (\<lambda>l. length l = length ys) zs  \<Longrightarrow> length zs1' = length ys \<Longrightarrow> (ys \<noteq> [] \<Longrightarrow> zs \<noteq> []) \<Longrightarrow> list_split' (map2 (\<lambda>x y. y ! 0 # y ! 1 # tl x) zs' zs1') ys"
          and trans: "\<And>m. m < length (y # ys) \<longrightarrow> (zs ! 0 ! m::'w option) = zs' ! m ! 0"
          and zs'_ys: "list_split' zs' (y # ys)"
          and zs1'_zs: "list_split' zs1' (hd zs::'w option list)"
          and len: "list_all (\<lambda>l. length (l::'w option list) = length [x, x']) zs1'"
          and len_zs: "list_all (\<lambda>l. length l = length (y # ys)) zs"
          and len': "length zs1' = length (y # ys)"
          and zs_Nil: "(y # ys) \<noteq> [] \<Longrightarrow> zs \<noteq> []"
        have trans': "zs ! 0 ! 0 = zs' ! 0 ! 0"
          using trans by auto
        have zs_Nil: "zs \<noteq> []"
          using zs_Nil by simp
        obtain z zss' where zs'_def: "zs' = z # zss'" and y_fold: "y = fold' z" and zss'_ys: "list_split' zss' ys" and z_Nil: "z \<noteq> []"
          using zs'_ys
          by(auto elim: list_split'.cases)
        obtain ze zl where z_app: "z = ze # zl"
          using z_Nil 
          by (meson list.exhaust)
        have ze_def: "ze = zs ! 0 ! 0"
          using trans'
          unfolding zs'_def z_app
          by simp
        obtain zse zsl where zs_def: "zs = zse # zsl"
          using zs_Nil
          using list.exhaust by auto
        have "\<exists> zs1'e1 zs1'e2 zs1'l. zs1' = [zs1'e1, zs1'e2] # zs1'l \<and> zs1'e1 + zs1'e2 = ze"
          using len ze_def zs1'_zs zs_def
          apply -
          apply(erule list_split'.cases)
          subgoal
            using len' zs1'_zs
            by auto
          subgoal for xss ys y xs
            apply simp
            by (smt (verit, ccfv_SIG) Suc_length_conv foldl_Cons foldl_Nil length_0_conv list.exhaust_sel list.inject list.exhaust)
          done
        then obtain zs1'e1 zs1'e2 zs1'l where zs1'_def: "zs1' = [zs1'e1, zs1'e2] # zs1'l \<and> zs1'e1 + zs1'e2 = ze"
          by auto
        show "list_split' (map2 (\<lambda>x y. y ! 0 # y ! 1 # tl x) zs' zs1') (y # ys)"
          using zs1'_def zs'_ys
          unfolding zs'_def ze_def trans'
          apply simp
          apply(rule list_split'.intros)
          subgoal
            apply(erule HOL.cnf.weakening_thm)+
            unfolding One_nat_def[symmetric]
            apply(rule ind[of "map tl zs"])
            subgoal for m
              using trans[of "Suc m"] zs_def zs'_def len_zs nth_tl[of m zse]
              by simp
            subgoal
              using zss'_ys
              by simp
            subgoal
              using zs1'_zs zs1'_def zs_def
              by(auto elim: list_split'.cases)
            subgoal
              using len zs1'_def
              by simp
            subgoal
              using len_zs
              by(induction zs; simp)
            subgoal
              using len' zs1'_def
              by simp
            subgoal
              unfolding zs_def
              by simp
            done
          subgoal
            using z_Nil
            by(auto elim: list_split'.cases simp add: hd_conv_nth)
          subgoal
            by simp
          done
      qed
      have Heq: "length zs' = length zs1'"
        using ind1 ind2
        apply safe
        apply(drule list_split'_length)+
        by(cases zs; simp)
      have "\<And> m. length zs' = length zs1' \<Longrightarrow> map2 (\<lambda>x y. y ! 0 # y ! Suc 0 # tl x) zs' zs1' ! m ! 0 = zs1' ! m ! 0"
        subgoal for m
          apply(induction m arbitrary: zs' zs1')
          subgoal for zs' zs1'
            by(cases zs'; cases zs1'; auto)
          subgoal for m zs' zs1'
            by(cases zs';  cases zs1'; auto)
          done
        done
      then have H3_1: "\<And> m. map2 (\<lambda>x y. y ! 0 # y ! Suc 0 # tl x) zs' zs1' ! m ! 0 = zs1' ! m ! 0"
        using Heq
        by blast
      have "\<And> m. length zs' = length zs1' \<Longrightarrow> map2 (\<lambda>x y. y ! 0 # y ! Suc 0 # tl x) zs' zs1' ! m ! Suc 0 = zs1' ! m ! Suc 0"
        subgoal for m
          apply(induction m arbitrary: zs' zs1')
          subgoal for zs' zs1'
            by(cases zs'; cases zs1'; auto)
          subgoal for m zs' zs1'
            by(cases zs';  cases zs1'; auto)
          done
        done
      then have H3_2: "\<And> m. map2 (\<lambda>x y. y ! 0 # y ! Suc 0 # tl x) zs' zs1' ! m ! Suc 0 = zs1' ! m ! Suc 0"
        using Heq
        by blast
      have H3_3: "\<And> n m. n \<ge> 2 \<Longrightarrow> m < length zs' \<Longrightarrow> length zs' = length zs1' \<Longrightarrow> n \<le> length (zs' ! m) \<Longrightarrow> map2 (\<lambda>x y. y ! 0 # y ! Suc 0 # tl x) zs' zs1' ! m ! n = zs' ! m ! (n - 1)"
        subgoal for n m
          apply(induction m arbitrary: zs' zs1')
          subgoal for zs' zs1'
            apply(cases zs'; cases zs1'; simp)
            subgoal for a list aa lista
              by(cases a; auto)
            done
          subgoal for m zs' zs1'
            by(cases zs';  cases zs1'; auto)
          done
        done
      have H3_help: "\<And>n m xs zs. n < length xs \<Longrightarrow> m < length zs \<Longrightarrow> list_all (\<lambda>l. length l = Suc (length xs)) zs \<Longrightarrow> Suc (Suc n) \<le> length (zs ! m)"
        subgoal for n m xs zs
          apply(induction zs arbitrary: n m xs; simp)
          subgoal for z zs n m xs
            by(cases m; simp)
          done
        done
      have H3: "\<forall>n m. n < length xs \<longrightarrow> m < length ys \<longrightarrow> (zs1 ! 0 # zs1 ! 1 # tl zs) ! n ! m = map2 (\<lambda>zs' y. y ! 0 # y ! 1 # tl zs') zs' zs1' ! m ! n"
        apply auto
        subgoal for n m
          apply(cases n; simp)
          subgoal
            using ind2 len_zs1'
            unfolding H3_1
            by(auto dest: list_split'_length)+
          subgoal for n'
            apply(cases n'; simp)
            subgoal
              using ind2 len_zs1'
              unfolding H3_2
              by(auto dest: list_split'_length)+
            subgoal for n''
              apply(rule sym)
              apply(rule trans)
              apply(rule H3_3[where n1 = "Suc (Suc n'')" and m1 = m])
              subgoal
                by simp
              subgoal
                using ind1 list_split'_length
                by metis
              subgoal
                using Heq by simp
              subgoal
                using ind1 xs_def
                by(fastforce intro: H3_help dest!: list_split'_length)
              subgoal
                using ind1 nth_tl[of n'' zs]
                unfolding xs_def
                by(fastforce dest: list_split'_length)
              done
            done
          done
        done
        have H4: "list_all (\<lambda>l. length l = length ys) (zs1 ! 0 # zs1 ! 1 # tl zs)"
        using ind1 ind2
        unfolding xs_def
        apply(cases zs1)
        subgoal
          by(auto elim: list_split'.cases)
        subgoal for e zss1
          apply(cases zss1)
          by(auto intro!: list_split'.intros elim: list_split'.cases)
        done
      have "list_all (\<lambda>l. length l = length ((x + x') # xs')) zs'" "length zs' = length zs1'"
        using ind1 Heq by auto
      then have H5: "list_all (\<lambda>l. length l = length xs) (map2 (\<lambda>zs' y. y ! 0 # y ! Suc 0 # tl zs') zs' zs1')"
        unfolding xs_def
        apply(induction zs' arbitrary: zs1')
        subgoal
          by simp
        subgoal for z zs' zs1'
          by(cases zs1'; simp)
        done
      show ?thesis
        apply(rule exI[where x = "zs1 ! 0 # zs1 ! 1 # tl zs"])
        apply(rule exI[where x = "map2 (\<lambda>l l'. (l' ! 0) # (l' ! 1) # (tl l)) zs' zs1'"])
        using H1 H2 H3 H4 H5
        by simp
    qed
    done
  have list_all_len_1: "\<And>ys. list_all (\<lambda>l. length l = Suc 0) (map (\<lambda>y. [y]) ys)"
    subgoal for ys
      by(induction ys; simp)
    done
  consider "length xs \<le> 1" | "length ys \<le> 1" | "length xs = 2 \<and> length ys = 2" | "length xs > 2" | "length ys > 2"
    by linarith
  then show "\<exists>zs zs'. list_split' zs xs \<and> list_split' zs' ys \<and> (\<forall>n m. n < length xs \<longrightarrow> m < length ys \<longrightarrow> zs ! n ! m = zs' ! m ! n) \<and> 
        list_all (\<lambda> l. length l = length ys) zs \<and> list_all (\<lambda> l. length l = length xs) zs'"
    proof (cases, goal_cases "leq1" "leq1'" "eq2" "gt3" "gt3'")
      case leq1
      then show ?case
        using eq_nil eq_app
        apply(cases xs)
        subgoal
         by(rule exI[where x = "[]"], rule exI[where x = "[]"], cases ys, auto intro: list_split'.intros simp add: wadd_wsingle_wempty[symmetric])
        subgoal for x xs'
          apply(rule exI[where x = "[ys]"])
          apply(rule exI[where x = "map (\<lambda>y. [y]) ys"])
          by(auto simp add: wadd_wsingle_wempty list_split'.intros list_split'_refl list_all_len_1)
        done
    next
      case leq1'
      then show ?case
        using eq_nil eq_app
        apply(cases ys)
        subgoal
         by(rule exI[where x = "[]"], cases xs, auto intro: list_split'.intros simp add: wadd_wsingle_wempty)
        subgoal for y ys'
          apply(rule exI[where x = "map (\<lambda>x. [x]) xs"])
          apply(rule exI[where x = "[xs]"])
          by(auto simp add: wadd_wsingle_wempty list_split'.intros list_split'_refl list_all_len_1)
        done
    next
      case eq2
      then show ?case
        apply(cases xs; cases ys; simp)
        subgoal for x xs' y ys'
          apply(cases xs'; cases ys'; simp)
          subgoal for x' xs'' y'
            using eq_app
            apply simp
            using common_splitting
            apply -
            apply(drule common_splitting[of x x' y y'])
            apply safe
            subgoal for e11 e12 e21 e22
              apply(rule exI[where x = "[case (e11, e12) of (Some e11', Some e12') \<Rightarrow> [e11', e12'] | (Some e11', None) \<Rightarrow> [e11', None] | (None, Some e12') \<Rightarrow> [None, e12'],
                                         case (e21, e22) of (Some e21', Some e22') \<Rightarrow> [e21', e22'] | (Some e21', None) \<Rightarrow> [e21', None] | (None, Some e22') \<Rightarrow> [None, e22']]"])
              apply safe
              subgoal
                by(cases e11; cases e12; cases e21; cases e22; auto intro!: list_split'.intros simp add: ab_semigroup_add_class.add.commute; auto simp add: plus_option_def)
              subgoal
                apply(rule exI[where x = "[case (e11, e21) of (Some e11', Some e21') \<Rightarrow> [e11', e21'] | (Some e11', None) \<Rightarrow> [e11', None] | (None, Some e21') \<Rightarrow> [None, e21'],
                                           case (e12, e22) of (Some e12', Some e22') \<Rightarrow> [e12', e22'] | (Some e12', None) \<Rightarrow> [e12', None] | (None, Some e22') \<Rightarrow> [None, e22']]"])
                apply(rule conjI)
                subgoal
                  by(cases e11; cases e12; cases e21; cases e22; auto intro!: list_split'.intros simp add: ab_semigroup_add_class.add.commute; auto simp add: plus_option_def)
                apply(cases e11; cases e12; cases e21; cases e22; auto intro!: list_split'.intros simp add: ab_semigroup_add_class.add.commute)
                by (metis less_Suc0 less_antisym nth_Cons_0 nth_Cons_Suc)+
            done
          done
        done
      done
  next
      case gt3
      assume len: "2 < length xs"
      show ?case
        using gt3_cases len ind eq_app eq_nil
        by presburger
    next
      case gt3'
      assume len: "2 < length ys"
      have "(ys = []) = (xs = [])"
        using eq_nil by simp
      moreover have "ys \<noteq> [] \<and> xs \<noteq> [] \<longrightarrow> fold' ys = fold' xs"
        using eq_app by simp
      moreover have "\<And>(x :: 'w option list) xa.
        length x + length xa < length ys + length xs \<Longrightarrow>
        x \<noteq> [] \<and> xa \<noteq> [] \<longrightarrow> fold' x = fold' xa \<Longrightarrow>
        (x = []) = (xa = []) \<Longrightarrow>
        \<exists>zs zs'.
           list_split' zs x \<and>
           list_split' zs' xa \<and>
           (\<forall>n m. n < length x \<longrightarrow> m < length xa \<longrightarrow> zs ! n ! m = zs' ! m ! n) \<and>
           list_all (\<lambda>l. length l = length xa) zs \<and> list_all (\<lambda>l. length l = length x) zs'"
        subgoal for x xa
          using ind[of x xa]
          by auto
        done
      ultimately show ?case
        using len gt3_cases[of ys xs]
        apply simp
        by metis
    qed
qed


lemma list_split_exist: 
  assumes wset_eq: "(wset_of_list xs :: ('a, 'w :: ab_semigroup_add_test) wset) = wset_of_list ys"
  shows "\<exists>zs zs'. list_split zs xs \<and> list_split zs' ys \<and> mset zs = mset zs'"
proof -
  have foldl_eq: "\<And>x2 b zs. Some x2 + foldl (+) (Some b) (map (\<lambda>x. Some (snd x)) zs) = foldl (+) (Some x2 + Some b) (map (\<lambda>x. Some (snd x)) zs)"
    subgoal for x2 b zs
      apply(induction zs arbitrary: x2 b)
      subgoal for xs b
        by simp
      subgoal for z zs xs b
        by(auto simp add: plus_option_def add.left_commute add.assoc)
      done
    done
  have filter_eq: "\<And>xs a. filter (\<lambda>(x, _). a = x) xs = [] = (weight (wset_of_list xs) a = None)"
    subgoal for xs a
      apply(induction xs)
      subgoal
        by(auto simp add: wempty.rep_eq)
      subgoal for x xs
        apply(cases x)
        subgoal for x1 x2
          by(auto simp add:  wadd.rep_eq wsingle.rep_eq plus_option_def)
        done
      done
    done
  have weight_wset_eq: "\<And>xs a. filter (\<lambda>(x, _). a = x) xs \<noteq> [] \<Longrightarrow> weight (wset_of_list xs) a = fold' (map (\<lambda>x. Some (snd x)) (filter (\<lambda>(x, _). a = x) xs))"
    subgoal for xs a
      apply(induction xs)
      subgoal
        by simp
      subgoal for x xs
        apply(cases x)
        subgoal for x1 x2
          apply(auto simp add:  wadd.rep_eq wsingle.rep_eq)
          apply(cases "filter (\<lambda>(x, _). a = x) xs \<noteq> []")
          subgoal
            by(cases "(map (\<lambda>x. Some (snd x)) (filter (\<lambda>(x, _). a = x) xs))"; auto simp add: foldl_eq)
          subgoal
            apply simp
            by(simp add: filter_eq plus_option_def)
          done
        done
      done
    done
  have ind_help: "\<And>(zs :: (('w option) list) list) zs'. \<forall>n<length zs. \<forall>m<length zs'. zs ! n ! m = zs' ! m ! n \<Longrightarrow>
    list_all (\<lambda>l. length l = length zs') zs \<Longrightarrow> list_all (\<lambda>l. length l = length zs) zs' \<Longrightarrow> mset (concat zs) = mset (concat zs')"
    subgoal for zs zs'
  proof (induction zs arbitrary: zs')
    case Nil
    then show ?case
      by(induction zs'; simp)
  next
    fix z :: "('w option) list"
      and zs :: "('w option) list list"
      and zs' :: "('w option) list list"
    assume ind: "\<And>zs'. \<forall>n<length zs. \<forall>m<length zs'. (zs ! n ! m::('w option)) = zs' ! m ! n \<Longrightarrow> list_all (\<lambda>l. length l = length zs') zs \<Longrightarrow> list_all (\<lambda>l. length l = length zs) zs' \<Longrightarrow> mset (concat zs) = mset (concat zs')"
      and trans: "\<forall>n<length (z # zs). \<forall>m<length zs'. (z # zs) ! n ! m = (zs' ! m ! n::('w option))"
      and len1: "list_all (\<lambda>l. length (l::('w option) list) = length (zs'::('w option) list list)) (z # zs)"
      and len2: "list_all (\<lambda>l. length (l::('w option) list) = length ((z::('w option) list) # zs)) zs'"
    have trans': "\<And>n m. n<length (z # zs) \<Longrightarrow>  m<length zs' \<Longrightarrow> (z # zs) ! n ! m = (zs' ! m ! n::('w option))"
      using trans by force
    have G1: "mset (concat zs') = mset (map hd zs') + mset (concat (map tl zs'))"
      using len2
      unfolding mset_append[symmetric]
      apply(induction zs'; simp)
      subgoal for z zs'
        by(cases z; simp)
      done
    have "length z = length zs'" using len1 by auto
    then have G2: "mset z = image_mset hd (mset zs')"
      using trans'[of 0] len2
      apply simp
      apply(induction zs' arbitrary: z; simp)
      subgoal for z' zs' z
        apply(cases z; cases z'; simp)
        by fastforce
      done
    have G3: "mset (concat zs) = mset (concat (map tl zs'))"
      apply(rule ind)
      subgoal
        apply safe
        subgoal for n m
          using trans'[of "Suc n" m] len2
          by(auto simp add: nth_tl list_all_length)
        done
      subgoal
        using len1
        by simp
      subgoal
        using len2
        apply simp
        by(induction zs' arbitrary: zs; simp)
      done
    show "mset (concat ((z::('w option) list) # zs)) = mset (concat zs')"
      using G1 G2 G3
      by simp
  qed
  done
  have "\<forall> a. \<exists>zs zs'.
     list_split' zs (map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) xs)) \<and>
     list_split' zs' (map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) ys)) \<and>
     (\<forall>n m. n < length (map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) xs)) \<longrightarrow> m < length (map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) ys)) \<longrightarrow> zs ! n ! m = zs' ! m ! n) \<and>
     list_all (\<lambda>l. length l = length (map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) ys))) zs \<and>
     list_all (\<lambda>l. length l = length (map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) xs))) zs'"
    using wset_eq
    apply -
    apply(rule allI)
    subgoal for a
      apply(rule list_split'_exist[where xs = "(map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) xs))" and ys = "(map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) ys))"])
      subgoal
        by(auto simp add: weight_inject[symmetric] comp_def dest!: weight_wset_eq)
      subgoal
        by(auto simp add: comp_def filter_eq)
      done
    done
  then have "\<forall> a. \<exists>zs zs'. list_split' zs (map (Some \<circ> snd) (filter (\<lambda>(x,_). a = x) xs)) \<and> list_split' zs' (map (Some \<circ> snd) (filter (\<lambda>(x,_). a = x) ys)) \<and> mset (concat zs) = mset (concat zs')"
    apply safe
    subgoal for a
      apply(erule allE[where x = a])
      apply safe
      subgoal for zs zs'
        apply(rule exI[where x = zs])
        apply(rule exI[where x = zs'])
        apply safe
        apply(drule list_split'_length)+
        using ind_help
        by simp
      done
    done
  then obtain zs zs' where L1: "\<And> a. list_split' (zs a) (map (Some \<circ> snd) (filter (\<lambda>(x,_). a = x) xs))" and 
      L2: "\<And> a. list_split' (zs' a) (map (Some \<circ> snd) (filter (\<lambda>(x,_). a = x) ys))" and L3: "\<And> a. mset (concat (zs a)) = mset (concat (zs' a))"
    by metis
  have G: "\<And>(zs :: 'a \<Rightarrow> 'w option list list) xs. (\<forall> a. list_split' (zs a) (map (Some \<circ> snd) (filter (\<lambda>(x,_). a = x) xs))) \<Longrightarrow> list_split (create_split xs zs) xs"
    subgoal for zs xs
  proof (induction xs arbitrary: zs)
    fix zs :: "'a \<Rightarrow> 'w option list list"
    assume "\<forall>a. list_split' (zs (a::'a)) (map (Some \<circ> snd) (filter (\<lambda>(x, y). ((\<lambda>_. a = x)::'w \<Rightarrow> bool) y) []))"
    show "list_split (create_split [] zs) []"
        by(auto intro: list_split.intros)
  next
    fix x :: "'a \<times> 'w"
      and xs :: "('a \<times> 'w) list"
      and zs :: "'a \<Rightarrow> 'w option list list"
    assume ind1: "\<And>zs. (\<forall>a. list_split' (zs a) (map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) xs))) \<Longrightarrow> list_split (create_split xs zs) xs"
      and ind2: "\<forall>a. list_split' (zs a) (map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) (x # xs)))"
    have ind1: "\<And>zs. (\<And>a. list_split' (zs a) (map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) xs))) \<Longrightarrow> list_split (create_split xs zs) xs"
      and ind2: "\<And>a. list_split' (zs a) (map (Some \<circ> snd) (filter (\<lambda>(x, _). a = x) (x # xs)))"
      using ind1 ind2 by auto
    obtain x1 x2 where x_def: "x = (x1,x2)"
      by fastforce
    have H1: "list_split (create_split xs (zs(x1 := tl (zs x1)))) xs"
      apply(rule ind1)
      subgoal for x'
        using ind2[of x']
        unfolding x_def
        by(auto elim: list_split'.cases)
      done
    have H2: "create_split ((x1, x2) # xs) zs = map (Pair x1) (option_list (hd (zs x1))) @ create_split xs (zs(x1 := tl (zs x1)))"
      by simp
    have H3: "x2 = fold' (map snd (map (Pair x1) (option_list (hd (zs x1)))))"
      using ind2[of x1]
      unfolding x_def
      apply -
      apply(cases "zs x1")
      subgoal
        using list_split'.cases by fastforce
      apply(erule list_split'.cases; simp)
      unfolding comp_def
      by(auto elim: list_split'.cases simp add: fold_option)
    have H4: "map (Pair x1) (option_list (hd (zs x1))) \<noteq> []"
      using ind2[of x1]
      unfolding x_def
      apply -
      apply(cases "zs x1")
      subgoal
        using list_split'.cases by fastforce
      by(auto elim: list_split'.cases simp add: fold_option_not_none)
    have "\<And> l. list_all (\<lambda>(a, b). a = x1) (map (Pair x1) (option_list l))"
      subgoal for l
        apply(induction l; simp?)
        subgoal for a l
          apply(cases a)
          by auto
        done
      done
    then have H5: "list_all (\<lambda>(a, b). a = x1) (map (Pair x1) (option_list (hd (zs x1))))"
      by auto
    show "list_split (create_split (x # xs) zs) (x # xs)"
      using H1 H2 H3 H4 H5 Split
      unfolding x_def
      by fast
    qed
    done
  have G3': "\<And>zs a (xs :: ('a \<times> 'w) list) w. length (zs a) = length (filter (\<lambda>(x, _). a = x) xs) \<Longrightarrow> count (mset (concat (zs a))) (Some w) = count (mset (create_split xs zs)) (a, w)"
    subgoal for zs a xs w
    proof (induction xs arbitrary: zs)
      case Nil
      then show ?case by simp
    next
      fix x :: "'a \<times> 'w"
        and xs :: "('a \<times> 'w) list"
        and zs :: "'a \<Rightarrow> 'w option list list"
      assume ind: "\<And>zs. length (zs a) = length (filter (\<lambda>(x, _). a = x) xs) \<Longrightarrow> count (mset (concat (zs a))) (Some w) = count (mset (create_split xs zs)) (a, w)"
        and len: "length (zs a::'w option list list) = length (filter (\<lambda>(x, _). a = x) (x # xs))"
      obtain x1 x2 where x_def: "x = (x1, x2)"
        by fastforce
      consider "a = x1" | "a \<noteq> x1" by auto
      then show "count (mset (concat (zs a))) (Some w) = count (mset (create_split (x # xs) zs)) (a, w)"
      proof (cases, goal_cases "eq" "neq")
        case eq
        obtain z zsa where zs_def: "zs x1 = z # zsa"
          using len eq
          unfolding x_def
          by(cases "zs a"; simp)
        have "count (mset z) (Some w) = count (image_mset (Pair x1) (mset (option_list z))) (x1, w)"
          apply(induction z)
          subgoal
            by simp
          subgoal for z1 z2
            by(cases z1; simp)
          done
        also have "count (mset (concat zsa)) (Some w) = count (mset (create_split xs (zs(x1 := zsa)))) (x1, w)"
          using ind[of "zs(x1 := zsa)"] len
          unfolding eq x_def zs_def
          by simp
        ultimately show ?case
          using zs_def
          unfolding x_def eq
          by simp
      next
        case neq
        have "\<And>m. count (image_mset (Pair x1) m) (a, w) = 0"
          using neq prod.inject by fastforce
        also have "length (zs a) = length (filter (\<lambda>(x, _). a = x) xs)"
          using len neq
          unfolding x_def
          by simp
        ultimately show ?case
          using ind[of "(zs(x1 := tl (zs x1)))"] neq
          unfolding x_def
          by simp
      qed
    qed
    done
  have G3: "mset (create_split xs zs) = mset (create_split ys zs')"
    apply(simp add: count_inject[symmetric] fun_eq_iff)
    by (metis (no_types, lifting) length_map L1 L2 L3 G3' list_split'_length)
  show ?thesis
    using G L1 L2 G3
    by blast
qed

lemma w_size_eq_Suc_imp_eq_union:
  assumes H: "size M = Suc n"
  shows "\<exists>x w N. M = wupdate N x (Some w) \<and> weight N x = None"
  using H
  apply(simp add: weight_inject[symmetric] fun_eq_iff)
  apply(cases "\<exists>x w. weight M x = Some w")
  subgoal
    apply(erule exE)+
    subgoal for x w
      apply(rule exI[where x = x])
      apply(rule exI[where x = w])
      apply(rule exI[where x = "wupdate M x None"])
      by(simp add: wupdate.rep_eq)
    done
  subgoal
    unfolding size_wset_overloaded_def wset_def
    by auto
  done

lemma size_wupdate: "Suc k = size (wupdate N x (Some w)) \<Longrightarrow> weight N x = None \<Longrightarrow> k = size N"
  unfolding size_wset_overloaded_def  wset_def
  apply(simp add: wupdate.rep_eq)
  apply(cases "{xa. \<exists>y. (if x = xa then Some w else weight N xa) = Some y} = 
      {x. \<exists>y. weight N x = Some y} \<union> {x}")
  subgoal
    apply(simp only: )
    apply simp
    by (smt (verit, best) card.infinite card_insert_disjoint finite_insert mem_Collect_eq nat.distinct(1) nat.inject
        option.discI)
  subgoal
    apply(rule FalseE)
    apply(erule notE[where P = "{xa. \<exists>y. (if x = xa then Some w else weight N xa) = Some y} = {x. \<exists>y. weight N x = Some y} \<union> {x}"])
    apply(simp only: Un_def)
    apply(rule Collect_cong)
    subgoal for xa
      by simp
    done
  done

theorem wset_induct [case_names empty add, induct type: multiset]:
  assumes empty: "\<And> M. (\<And> x. weight M x = None) \<Longrightarrow> P M"
  assumes add: "\<And>x w M. P M \<Longrightarrow> weight M x = None \<Longrightarrow> P (wupdate M x (Some w))"
  shows "P M"
proof (induct "size M" arbitrary: M)
  case 0 thus "P M"
    by (metis (mono_tags, lifting) "0.hyps" empty card_0_eq empty_iff eq_onp_live_step mem_Collect_eq size_wset_overloaded_def
        weight weight_inverse wset.abs_eq)
next
  fix k :: nat
    and M :: "('a, 'b) wset"
  assume ind: "\<And>M. k = size M \<Longrightarrow> P M"
    and size: "Suc k = size M"
  obtain N x w where M_def: "M = wupdate N x (Some w)" and weight_N: "weight N x = None"
    using size[symmetric] w_size_eq_Suc_imp_eq_union
    by blast
  show "P M"
    using size weight_N ind[of N] size_wupdate add
    unfolding M_def
    by metis
qed

lemma w_image_update: "weight M x = None \<Longrightarrow> image_wset f (wupdate M x (Some w)) = wadd (wsingle (f x) w) (image_wset f M)"
  unfolding wadd_def
  apply(simp add: wsingle.rep_eq image_wset.rep_eq)
  unfolding image_wset_def
  apply(simp add: wupdate.rep_eq)
  apply(rule arg_cong[where f = "Abs_wset"])
  apply(simp only: fun_eq_iff)
  apply(cases "{a. x \<noteq> a \<longrightarrow> (\<exists>y. weight M a = Some y) \<and> f a = f x} = insert x {a. (\<exists>y. weight M a = Some y) \<and> f a = f x}")
  subgoal
    apply simp
    apply safe
    apply simp
    subgoal
      apply(rule verit_eq_transitive, rule comp_fun_commute_on.fold_insert[where S = "(insert x {a. (\<exists>y. weight M a = Some y) \<and> f a = f x})"])
      subgoal
        by (auto intro!: comp_fun_commute_on.intro simp add: add.left_commute comp_def)
      subgoal
        by auto
      subgoal
        using wset.weight[where x = M]
        by auto
      subgoal
        by auto
      subgoal
        apply(cases "Finite_Set.fold (\<lambda>xa. (+) (if x = xa then Some w else weight M xa)) None {a. (\<exists>y. weight M a = Some y) \<and> f a = f x} = Finite_Set.fold (\<lambda>x. (+) (weight M x)) None {a. (\<exists>y. weight M a = Some y) \<and> f a = f x}")
        by(auto intro!: fold_closed_eq[where A = "{a. (\<exists>y. weight M a = Some y) \<and> f a = f x}" and B = UNIV])
      done
    subgoal for z
      apply(cases "{a. (x = a \<longrightarrow> f a = z) \<and> (x \<noteq> a \<longrightarrow> (\<exists>y. weight M a = Some y) \<and> f a = z)} = {a. (\<exists>y. weight M a = Some y) \<and> f a = z}")
      by(auto intro!: fold_closed_eq[where A = "{a. (\<exists>y. weight M a = Some y) \<and> f a = z}" and B = UNIV])
    done
  subgoal
    by auto
  done

lemma wimage_empty: "image_wset f wempty = wempty"
  unfolding image_wset_def
  apply (simp add: wempty.rep_eq)
  unfolding wempty_def
  by simp

lemma wimage_wadd_wsingle: "image_wset f (wadd (wsingle x w) ws) = wadd (wsingle (f x) w) (image_wset f ws)"
proof -
  have "\<And>x'. weight (image_wset f (wadd (wsingle x w) ws)) x' = weight (wadd (wsingle (f x) w) (image_wset f ws)) x'"
  proof -
    fix x'
    consider "f x = x'" | "f x \<noteq> x'"
      by auto
    then show "weight (image_wset f (wadd (wsingle x w) ws)) x' = weight (wadd (wsingle (f x) w) (image_wset f ws)) x'"
    proof(cases, goal_cases "eq" "neq")
      case eq
      have set_eq: "{a. (x = a \<longrightarrow> (\<exists>y. Some w + weight ws a = Some y) \<and> f a = x') \<and> (x \<noteq> a \<longrightarrow> (\<exists>y. weight ws a = Some y) \<and> f a = x')} = 
                    insert x {a. (\<exists>y. weight ws a = Some y) \<and> f a = x'}"
        using eq
        by(cases "weight ws x"; auto simp add: plus_option_def)
      consider "weight ws x = None" | "weight ws x \<noteq> None"
        by auto
      then show ?case
      proof(cases, goal_cases "eq_None" "neq_None")
        case eq_None
        show ?case
          apply(simp add: eq_None eq weight_inject[symmetric] image_wset.rep_eq wadd.rep_eq wsingle.rep_eq set_eq)
          apply(rule trans, rule comp_fun_commute_on.fold_insert_remove[of UNIV])
          subgoal
            unfolding comp_fun_commute_on_def
            by(auto simp add: add.assoc add.left_commute)
          subgoal
            by simp
          subgoal
            using weight[of ws]
            by simp
          subgoal
            apply(auto simp add: eq_None)
            apply(rule arg_cong[where f = "\<lambda>y. Some w + y"])
            apply(rule Finite_Set.fold_closed_eq[where B = UNIV])
            by(auto simp add: eq_None)
          done
      next
        case neq_None
        obtain w' where ws_weight: "weight ws x = Some w'"
          using neq_None
          by fast
        have "{a. (\<exists>y. weight ws a = Some y) \<and> f a = x'} = insert x ({a. (\<exists>y. weight ws a = Some y) \<and> f a = x'})"
          using ws_weight eq
          by fast
        then have set_eq': "Finite_Set.fold (\<lambda>x. (+) (weight ws x)) None {a. (\<exists>y. weight ws a = Some y) \<and> f a = x'} =
              Finite_Set.fold (\<lambda>x. (+) (weight ws x)) None (insert x ({a. (\<exists>y. weight ws a = Some y) \<and> f a = x'}))"
          by presburger
        show ?case
          apply(simp add: ws_weight eq weight_inject[symmetric] image_wset.rep_eq wadd.rep_eq wsingle.rep_eq set_eq set_eq')
          apply(rule trans, rule comp_fun_commute_on.fold_insert_remove[of UNIV])
          subgoal
            unfolding comp_fun_commute_on_def
            by(auto simp add: add.assoc add.left_commute)
          subgoal
            by simp
          subgoal
            using weight[of ws]
            by simp
          subgoal
            apply simp
            unfolding add.assoc
            apply(rule arg_cong[where f = "\<lambda>y. Some w + y"])
            apply(rule sym)
            apply(rule trans, rule comp_fun_commute_on.fold_insert_remove[of UNIV])
            subgoal
              unfolding comp_fun_commute_on_def
              by(auto simp add: add.assoc add.left_commute)
            subgoal
              by simp
            subgoal
              using weight[of ws]
              by simp
            subgoal
            apply(rule arg_cong[where f = "\<lambda>y. weight ws x + y"])
            apply(rule Finite_Set.fold_closed_eq[where B = UNIV])
            by(auto simp add: neq_None)
          done
        done
    qed
    next
      case neq
      have set_eq: "{a. (x = a \<longrightarrow> (\<exists>y. Some w + weight ws a = Some y) \<and> f a = x') \<and> (x \<noteq> a \<longrightarrow> (\<exists>y. weight ws a = Some y) \<and> f a = x')} = 
                    {a. (\<exists>y. weight ws a = Some y) \<and> f a = x'}"
        using neq
        by auto
      then show ?case
        apply(simp add: neq weight_inject[symmetric] image_wset.rep_eq wadd.rep_eq wsingle.rep_eq set_eq)
        apply(rule Finite_Set.fold_closed_eq[where B = UNIV])
        using neq
        by auto
    qed
  qed
  then show ?thesis
    by(simp add: weight_inject[symmetric] fun_eq_iff)
qed

lemma image_wset_list: "image_wset f (wset_of_list l) = wset_of_list (map (\<lambda>(a,b). (f a, b)) l)"
  by(induction l, auto simp add: wimage_wadd_wsingle wimage_empty split: prod.split)

lemma wset_of_list_eq: " wset_of_list xs' = wset_of_list xs \<Longrightarrow>
    ListMem (x, w) xs' \<Longrightarrow> \<exists> w'. ListMem(x, w') xs"
  using wset_of_list_Mem
  by metis

lemma wset_eq_iff: "M = N \<longleftrightarrow> (\<forall>a. weight M a = weight N a)"
  by (simp only: weight_inject [symmetric] fun_eq_iff)

lemma wset_eqI: "(\<And>x. weight A x = weight B x) \<Longrightarrow> A = B"
  using wset_eq_iff by auto

lemma wadd_assoc: "wadd x (wadd y z) = wadd (wadd x y) z"
  by(simp add: weight_inject[symmetric] wadd.rep_eq add.assoc)

lemma wadd_commute: "wadd x y = wadd y x"
  by(simp add: weight_inject[symmetric] wadd.rep_eq add.commute)

lemma wadd_wsingles: "wadd (wsingle x w1) (wadd (wsingle x w2) z) = wadd (wsingle x (w1 + w2)) z"
  apply(simp add: weight_inject[symmetric] wadd.rep_eq wsingle.rep_eq fun_eq_iff add.assoc[symmetric])
  by(auto simp add: plus_option_def)

lemma w_list_all2_reorder_left_invariance:
  "list_all2 (rel_prod R (=)) xs ys \<Longrightarrow> list_split xs' xs \<Longrightarrow>
  \<exists>ys'. list_all2 (rel_prod R (=)) xs' ys' \<and> wset_of_list ys' = wset_of_list ys"
proof (induction "length xs" arbitrary: xs ys xs')
  fix xs :: "('a \<times> 'b) list"
  and ys :: "('c \<times> 'b) list"
  and xs' :: "('a \<times> 'b) list"
  assume "0 = length xs"
    and "list_all2 (rel_prod R (=)) xs ys"
    and "list_split xs' xs"
  then show "\<exists>ys'. list_all2 (rel_prod R (=)) xs' ys' \<and> wset_of_list ys' = wset_of_list ys"
    by(auto elim: list_split.cases)
next
  fix n :: nat
    and xs :: "('a \<times> 'b) list"
    and ys :: "('c \<times> 'b) list"
    and xs' :: "('a \<times> 'b) list"
  assume ind: "\<And>xs ys (xs' :: ('a \<times> 'b) list). n = length xs \<Longrightarrow> list_all2 (rel_prod R (=)) xs ys \<Longrightarrow> list_split xs' xs \<Longrightarrow> \<exists>ys'. list_all2 (rel_prod R (=)) xs' ys' \<and> wset_of_list ys' = wset_of_list ys"
    and len_xs: "Suc n = length xs"
    and list2_all': "list_all2 (rel_prod R (=)) xs ys"
    and list_split': "list_split xs' xs"
  show "\<exists>ys'. list_all2 (rel_prod R (=)) xs' ys' \<and> wset_of_list ys' = wset_of_list ys"
  proof (cases xs ; cases ys ; safe)
    assume "xs = []"
      and "ys = []"
    then show "\<exists>ys'. list_all2 (rel_prod R (=)) xs' ys' \<and> wset_of_list ys' = wset_of_list []"
      using list_split'
      by(auto elim: list_split.cases)
  next
    fix y' :: 'c
      and wy :: 'b
      and yss :: "('c \<times> 'b) list"
    assume "xs = []"
      and "ys = (y', wy) # yss"
    then show "\<exists>ys'. list_all2 (rel_prod R (=)) xs' ys' \<and> wset_of_list ys' = wset_of_list ((y', wy) # yss)"
      using list2_all'
      by blast
  next
    fix x' :: 'a
      and wx :: 'b
      and xss :: "('a \<times> 'b) list"
    assume "xs = (x', wx) # xss"
      and "ys = []"
    then show "\<exists>ys'. list_all2 (rel_prod R (=)) xs' ys' \<and> wset_of_list ys' = wset_of_list []"
      using list2_all'
      by blast
  next
    fix x' :: 'a
      and wx :: 'b
      and xss :: "('a \<times> 'b) list"
      and y' :: 'c
      and wy :: 'b
      and yss :: "('c \<times> 'b) list"
    assume xs_def: "xs = (x', wx) # xss"
      and ys_def: "ys = (y', wy) # yss"
    have wx_def: "wx = wy"
      using list2_all' xs_def ys_def
      by fastforce
    have R_x_y: "R x' y'"
      using list2_all' xs_def ys_def
      by simp
    obtain exs exs' where list_split': "list_split exs' xss" and xs'_def: "xs' = exs @ exs'" and 
        wy_fold: "wy = fold' (map snd exs)" and exs_nonempty: "exs \<noteq> []" and list_all_exs: "list_all (\<lambda> (a,b). a = x') exs"
      using list_split' xs_def wx_def
      by(auto elim: list_split.cases)
    obtain eys' where ind_e: "list_all2 (rel_prod R (=)) exs' eys'" and wset_yss: "wset_of_list yss = wset_of_list eys'"
      using len_xs list2_all' list_split' xs_def ys_def ind
      by fastforce
    show "\<exists>ys'. list_all2 (rel_prod R (=)) xs' ys' \<and> wset_of_list ys' = wset_of_list ((y', wy) # yss)"
      apply(rule exI[where x = "(map (\<lambda> (_,w). (y',w)) exs) @ eys'"])
      apply(rule conjI)
      subgoal
        unfolding xs'_def
        using R_x_y list_all_exs
        apply -
        apply(rule list_all2_appendI; simp?)
        subgoal
          apply(induction exs)
          by auto
        subgoal
          using ind_e
          by simp
        done
      subgoal
        using exs_nonempty
        apply(simp add: wset_yss wx_def wy_fold)
        apply(induction exs; simp, safe?)
        subgoal for a b axs
          by(cases axs; auto simp add: wadd_wsingles foldl_assoc add.assoc)
      done
    done
  qed
qed

lemma w_list_all2_reorder_right_invariance:
  "list_all2 (rel_prod R (=)) xs ys \<Longrightarrow> list_split ys' ys \<Longrightarrow>
  \<exists>xs'. list_all2 (rel_prod R (=)) xs' ys' \<and> wset_of_list xs' = wset_of_list xs"
  using w_list_all2_reorder_left_invariance list.rel_flip
  by (metis conversep_eq prod.rel_conversep)

lemma wadd_remove1: "ListMem (y,w) ys \<Longrightarrow> wadd (wsingle y w) (wset_of_list (remove1 (y,w) ys)) = wset_of_list ys"
proof(induction "length ys" arbitrary: y w ys)
  case 0
  then show ?case 
    by(auto elim: ListMem.cases)
next
  case (Suc n)
  then show ?case 
    apply(cases ys; safe)
    subgoal
      by auto
    subgoal for y'' w' ys'
      apply simp
      using wadd_assoc wadd_commute ListMem.cases list.inject prod.inject
      by metis
    done
qed

lemma wset_mset_list:
  "mset (xs :: ('a \<times> 'w :: ab_semigroup_add_test) list) = mset ys \<Longrightarrow>
  wset_of_list xs = wset_of_list ys"
proof (induction "xs" arbitrary: ys)
  fix ys :: "('a \<times> 'w) list"
  assume "mset [] = mset ys"
  then show "wset_of_list [] = wset_of_list ys"
    by force
next
  fix x :: "'a \<times> 'w"
    and xs :: "('a \<times> 'w) list"
    and ys :: "('a \<times> 'w) list"
  obtain x' w where x_def: "x = (x', w)"
    by force
  assume ind: "\<And>ys. mset xs = mset ys \<Longrightarrow> wset_of_list xs = wset_of_list ys"
    and mset_eq: "mset (x # xs) = mset ys"
  have "ListMem (x', w) ys"
    using mset_eq
    by (metis ListMem_iff list.set_intros(1) set_mset_mset x_def)
  then have wset_ys: "wset_of_list ys = wadd (wsingle x' w) (wset_of_list (remove1 (x', w) ys))"
    by(rule wadd_remove1[symmetric])
  have wset_xs: "(wset_of_list xs) = (wset_of_list (remove1 (x', w) ys))"
    using ind mset_eq
    by (metis mset_remove1 remove1.simps(2) x_def)
  show "wset_of_list (x # xs) = wset_of_list ys"
    by(auto simp add: wset_ys wset_xs x_def)
qed

lemma weight_plus: "(\<lambda> x. (weight f x + weight g x)) = weight (wadd f g)"
  unfolding wadd_def map_fun_def comp_def
  using weight
  apply -
  apply(rule Abs_wset_inverse[symmetric])
  apply simp
  apply(rule rev_finite_subset[where B = "{x. \<exists>y. weight f x = Some y} \<union> {x. \<exists>y. weight g x = Some y}"])
  by auto

lemma set_wset_wset[simp]: "wset (wset_of_list xs) = set (map fst xs)"
proof(induct xs)
  case Nil
  then show ?case
    apply simp
    unfolding wempty_def
    using wset.abs_eq[where x = "(\<lambda>a. None)"]
    using wempty.rsp by fastforce 
next
  case (Cons a xs)
  then show ?case
    apply(cases a)
    subgoal for aa ab
      apply simp
      unfolding wset_def comp_def map_def
      apply(simp add: wadd.rep_eq wsingle.rep_eq)
      by(cases "weight (wset_of_list xs) aa"; auto simp add: plus_option_def)
    done
qed

bnf "('a, 'w :: ab_semigroup_add_test) wset"
  map: image_wset
  sets: wset
  bd: natLeq
  wits: "wempty"
  rel: rel_wset
proof -
  show "image_wset id = id"
  proof -
    have H: "\<forall> f z. weight (Abs_wset f) = f \<longrightarrow>  (\<lambda>b. Finite_Set.fold (\<lambda>xa. (+) (weight (Abs_wset f) xa)) None {a. a = b \<and> (\<exists>y. weight (Abs_wset f) a = Some y)}) z = f z"
      unfolding image_def
      apply safe
      subgoal for f z
        apply(cases "f z")
        subgoal
          apply(cases "{a. a = z \<and> (\<exists>y. f a = Some y)} = {}")
           apply (simp only:)
          by auto
        subgoal for a
          apply(cases "{a. a = z \<and> (\<exists>y. f a = Some y)} = {z}")
          by auto
        done
      done
    show ?thesis
    unfolding eq_id_iff[symmetric] image_wset_def
    apply(rule allI)
    subgoal for z
      apply(cases z)
      apply simp
      apply(rule arg_cong[where f = "Abs_wset"])
      using H  Abs_wset_inverse
      by auto
    done
  qed                                        
  show "image_wset (g \<circ> f) = image_wset g \<circ> image_wset f" for f g
  proof -
    have "(image_wset (g \<circ> f)) h = (image_wset g \<circ> image_wset f) h" for h
      apply(induction h)
      subgoal for h
        unfolding image_wset_def
        apply auto
        proof -
          have "\<forall>ga h. (\<forall>i. weight (Abs_wset (\<lambda>h. None)) h \<noteq> Some (i::'i)) \<or> g h \<noteq> ga"
            by (metis (full_types) not_None_eq wempty.rep_eq wempty_def)
          then have "\<forall>ga. {} = {h. (\<exists>i. weight (Abs_wset (\<lambda>h. None)) h = Some (i::'i)) \<and> g h = ga}"
            by auto
          then show "Abs_wset (\<lambda>g. None) = Abs_wset (\<lambda>ga. Finite_Set.fold (\<lambda>h. (+) (weight (Abs_wset (\<lambda>h. None)) h)) None {h. (\<exists>i. weight (Abs_wset (\<lambda>h. None)) h = Some (i::'i)) \<and> g h = ga})"
            by (metis (no_types) fold_empty)
        qed
        subgoal for x w M
          unfolding comp_def
          apply(cases "weight M x = None")
          apply(drule w_image_update[where f = f and w = w])
          by(auto dest: w_image_update[where f = "(\<lambda>a. g (f a))" and w = w] simp add: wimage_wadd_wsingle)
        done
  then show ?thesis
    by fast
  qed
  show "(\<And>z. z \<in> wset X \<Longrightarrow> f z = g z) \<Longrightarrow> image_wset f X = image_wset g X" for f g X
    apply (induct X)
    subgoal for M
      unfolding image_wset_def
      by(auto)
    subgoal for x w M
      unfolding wset_def
      by(auto simp add: wupdate.rep_eq w_image_update)
    done
  show "card_order natLeq"
    by (rule natLeq_card_order)
  show "BNF_Cardinal_Arithmetic.cinfinite natLeq"
    by (rule natLeq_cinfinite)
  show "regularCard natLeq"
    by (rule regularCard_natLeq)
  show "ordLess2 (card_of (wset X)) natLeq" for X
    by transfer
      (auto simp: finite_iff_ordLess_natLeq[symmetric])
  show "rel_wset R OO rel_wset S \<le> rel_wset (R OO S)" for R S
    unfolding rel_wset_def[abs_def] OO_def
    apply simp
    apply safe
    apply(drule list_split_exist)
    apply safe
    subgoal for _ _ _ xs xs' ys ys' zs zs'
      apply -
      apply(drule WSet.w_list_all2_reorder_right_invariance[where ys = ys], assumption)
      apply(drule WSet.w_list_all2_reorder_left_invariance[where ys = ys'], assumption)
      apply safe
      apply(drule list_all2_reorder_left_invariance, assumption)
      apply safe
      subgoal for ex ey ez
        apply(rule exI[where x = "ex"])
        apply(rule conjI, simp)
        apply(rule exI[where x = "ez"])
        apply(rule conjI)
        subgoal
          by (metis wset_mset_list)
        apply(rule list_all2_trans[of "(rel_prod R (=))"]; simp?)
        by auto
      done
    done
  show "rel_wset R =
    (\<lambda>x y. \<exists>z. wset z \<subseteq> {(x, y). R x y} \<and>
    image_wset fst z = x \<and> image_wset snd z = y)" for R
    unfolding rel_wset_def[abs_def]
    apply(simp only: fun_eq_iff)
    apply(safe; simp)
    subgoal for xs ys
      apply(rule exI[where x = "wset_of_list (map (\<lambda>((a,b),(c,_)). ((a,c),b)) (zip xs ys))"])
      apply safe
      subgoal for e1 e2
        by(auto simp add: list_all2_iff)
      subgoal
        apply(simp only: image_wset_list map_map)
        apply(induction xs arbitrary: ys)
        subgoal for ys
          by auto
        subgoal for v vs ys
          apply(cases ys; simp)
          by(auto split: prod.split list.split)
        done
      subgoal
        apply(simp only: image_wset_list map_map)
        apply(induction ys arbitrary: xs)
        subgoal for xs
          by auto
        subgoal for v vs xs
          apply(cases xs)
          by(auto split: prod.split list.split)
        done
      done
    subgoal for z
      apply(induction z)
      subgoal for M
        apply safe
        apply(rule exI[where x = "[]"]; simp)
        unfolding image_wset_def wempty_def
        by(cases "weight M = (\<lambda> _. None)"; auto)
      subgoal for z w M
        unfolding wset_def
        apply(drule impI; erule impE)
        subgoal
          by(auto simp add: wupdate.rep_eq map_fun_def comp_def id_def Collect_mono_iff)
        apply safe
        subgoal for xs zs
          apply(rule exI[where x = "(fst z,w) # xs"]; simp)
          by(auto intro!: exI[where x = "(snd z,w) # zs"] simp add: wupdate.rep_eq w_image_update)
        done
      done
    done
  show "wset \<circ> image_wset f = (`) f \<circ> wset" for f
  proof -
    have "(wset \<circ> image_wset f) g = ((`) f \<circ> wset) g" for g
      unfolding image_def comp_def image_wset_def wset_def
      apply simp
      apply safe
      subgoal for x y
        apply(drule Abs_wset_inverse_help)
        subgoal
          by(simp add: w_finite_fold)
        subgoal
          apply(cases "{a. (\<exists>y. weight g a = Some y) \<and> f a = x} = {}")
          by auto
        done
      subgoal for x y
        using weight[where x = g]
        by(auto intro!: Abs_wset_inverse_help'' finite_set_fold_some simp add: w_finite_fold )
      done
    then show ?thesis
      by blast
  qed
  show "\<And>b. b \<in> wset wempty \<Longrightarrow> False"
    unfolding wempty_def
    using Abs_wset_inverse
    using wempty.rsp wset.abs_eq by fastforce
qed

unused_thms

declare [[typedef_overloaded]]
codatatype ('a, 'w) wsetinf = WSetInf "(('a, 'w) wsetinf + 'a, 'w :: ab_semigroup_add_test) wset"
