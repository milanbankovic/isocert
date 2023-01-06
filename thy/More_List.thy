section\<open>Additions to standard library\<close>

text\<open>In this section we define some additional functions and prove some
 additional lemmas about lists and multisets.\<close>

subsection \<open>Additions to the List library\<close>

theory More_List
  imports Main "HOL-Library.Product_Lexorder"
begin

text \<open>@{text rev}\<close>

lemma nth_rev: "n < length xs \<Longrightarrow> rev xs ! n = xs ! (length xs - 1 - n)"
  using rev_nth by simp

text \<open>@{text takeWhile}\<close>

lemma length_takeWhile:
  assumes "i < length l" "\<forall> i' < i. P (l ! i')" "\<not> P (l ! i)" 
  shows "length (takeWhile P l) = i"
  using assms
proof (induction l arbitrary: i)
  case Nil
  thus ?case
    by simp
next
  case (Cons x l)
  show ?case
  proof (cases "i = 0")
    case True
    thus ?thesis
      using Cons(4)
      by simp
  next
    case False
    hence "length (takeWhile P l) = i - 1"
      using Cons(1)[of "i-1"] Cons(2) Cons(3) Cons(4)
      by (auto simp add: nth_Cons) (metis Cons.prems(2) Cons.prems(3) Suc_less_SucD diff_Suc_Suc gr0_implies_Suc less_Suc_eq_0_disj minus_nat.diff_0 nth_Cons old.nat.simps(5))
    thus ?thesis
      using Cons(3)[rule_format, of 0] `i \<noteq> 0`
      by simp
  qed
qed

lemma length_takeWhile':
  assumes "length (takeWhile P xs) = n"
  shows "(\<forall> i < n. P (xs ! i)) \<and> ((n < length xs \<and> \<not> P (xs ! n)) \<or> n = length xs)"
  using assms
  by (metis length_takeWhile_le nat_less_le nth_length_takeWhile nth_mem set_takeWhileD takeWhile_nth)

text \<open>@{text min_list}\<close>

lemma min_list_map_iff:
  fixes f :: "'a \<Rightarrow> 'b::linorder"
  assumes "ps \<noteq> []"
  shows "((\<exists> i \<in> set ps. s = f i) \<and> list_all (\<lambda>p. s \<le> f p) ps) \<longleftrightarrow> 
          (min_list (map (\<lambda>p. f p) ps) = s)"
  using assms
  unfolding list_all_iff
proof safe
  fix i
  assume "\<forall>p\<in>set ps. f i \<le> f p" "i \<in> set ps"
  thus "min_list (map f ps) = f i"
    using `ps \<noteq> []` min_list_Min[of  "map f ps"] eq_Min_iff[of "set (map f ps)" "f i"]
    by auto
next
  show "\<exists>i\<in>set ps. min_list (map f ps) = f i"
    using `ps \<noteq> []` min_list_Min[of  "map f ps"] eq_Min_iff[of "set (map f ps)"]
    by auto
next
  fix p
  assume "p \<in> set ps"
  thus "min_list (map f ps) \<le> f p"
    using `ps \<noteq> []` min_list_Min[of  "map f ps"] eq_Min_iff[of "set (map f ps)"]
    by auto
qed

lemma P_min_list:
  fixes l :: "'a::{linorder} list"
  assumes "l \<noteq> []" "\<forall> x \<in> set l. P x" 
  shows "P (min_list l)"
  using assms
  using min_list_Min[of l] Min_in[of "set l"]
  by simp

lemma min_list_map_is_min:
  fixes f :: "'a \<Rightarrow> 'b::linorder"
  assumes "ps \<noteq> []"
  shows "list_all (\<lambda>p. min_list (map (\<lambda>p. f p) ps) \<le> f p) ps"
  using assms
  unfolding list_all_iff
  by (simp add: min_list_Min)

text \<open>@{text max_list}\<close>

fun max_list where
  "max_list (x#xs) = fold max xs x"

lemma max_list_ubound:
  assumes "xs \<noteq> []" "\<forall> x \<in> set xs. x \<le> n"
  shows "max_list xs \<le> n"
proof-
  from assms obtain x xs' where "xs = x # xs'"
    by (cases xs) auto
  hence "x \<le> n" "\<forall> x \<in> set xs'. x \<le> n"
    using assms
    by auto
  hence "fold max xs' x \<le> n"
    by (induction xs' rule: rev_induct) (auto simp add: max_def)
  thus ?thesis
    using `xs = x # xs'`
    by auto
qed

lemma max_list_max:
  fixes xs :: "('a :: linorder) list"
  shows "\<forall> x \<in> set xs. max_list xs \<ge> x"
proof (cases xs)
  case (Cons x xs)
  have "x \<le> fold max xs x"
    by (induction xs) (auto, smt List.finite_set Max.in_idem Max.set_eq_fold insertCI list.set(2) max.assoc max.commute max_def)
  moreover
  have "\<forall>x'\<in>set xs. x' \<le> fold max xs x"
    by (induction xs, auto,
        smt List.finite_set Max.in_idem Max.set_eq_fold list.set_intros(1) max.assoc max_def min.orderI min_def,
        metis List.finite_set Max.in_idem Max.set_eq_fold insertCI list.set(2) max.commute max.orderI)
  ultimately
  show ?thesis
    using Cons
    by simp
qed simp
 
lemma max_list_is_nth:
  assumes "l \<noteq> []"
  shows "\<exists> i. i < length l \<and> l ! i = max_list l"
  using assms
proof-
  from assms obtain a l' where "l = a # l'"
    by (cases l) auto
  have "\<exists>i. i < length (a # l') \<and> (a # l') ! i = fold max l' a"
  proof (induction l' rule: rev_induct)
    case Nil
    then show ?case 
      by (rule_tac x=0 in exI, simp)
  next
    case (snoc x xs)
    show ?case
    proof (cases "x \<le> (fold max xs a)")
      case True
      obtain i where i: "i < length (a # xs)" "(a # xs) ! i = fold max xs a"
        using snoc
        by auto
      have "(a # xs @ [x]) ! i = (a # xs) ! i"
        using `i < length (a # xs)`
        by (metis (mono_tags, lifting) append_Cons butlast_snoc nth_butlast)
      moreover
      have "fold max (xs @ [x]) a = fold max xs a"
        using True
        by (simp add: max_def)
      ultimately
      show ?thesis
        using i
        by (rule_tac x=i in exI, simp)
    next
      case False
      hence "fold max (xs @ [x]) a = x"
        by (simp add: max_def)
      moreover
      have "(a # xs @ [x]) ! (length (a # xs)) = x"
        by (simp add: nth_append)
      ultimately
      show ?thesis
        by (rule_tac x="length (a # xs)" in exI, simp)
    qed
  qed
  thus ?thesis
    using `l = a # l'`
    by simp
qed

text \<open>@{text index_of}\<close>

definition index_of where
  "index_of xs x = snd (hd (filter (\<lambda> (a, b). a = x) (zip xs [0..<length xs])))"

lemma index_of_in_set:
  assumes "x \<in> set xs"
  shows "index_of xs x < length xs \<and> xs ! index_of xs x = x"
proof-
  obtain i where "x = xs ! i" "i < length xs"
    using assms in_set_conv_nth[of x xs]
    by auto
  hence "(x, i) \<in> set (zip xs [0..<length xs])"
    using assms
    by (auto simp add: set_zip)
  hence "filter (\<lambda>(a, b). a = x) (zip xs [0..<length xs]) \<noteq> []"
    by (metis (mono_tags, lifting) filter_empty_conv old.prod.case)
  thus ?thesis
    unfolding index_of_def
    using hd_in_set[of "(filter (\<lambda>(a, b). a = x) (zip xs [0..<length xs]))"]
    by (auto split: prod.split_asm simp add: set_zip)
qed

lemma singleton_list_iff: 
  "xs = [x] \<longleftrightarrow> set xs = {x} \<and> distinct xs"
  by auto (metis distinct.simps(2) distinct_length_2_or_more insert_not_empty  neq_Nil_conv set_empty2 singletonD)

lemma index_of_list_element:
  assumes "p < length xs" "distinct xs"
  shows "index_of xs (xs ! p) = p"
proof-
  have "(xs ! p, p) \<in> set (zip xs [0..<length xs])"
    using assms
    by (auto simp add: set_zip)
  moreover
  hence "\<forall> p'. (xs ! p, p') \<in> set (zip xs [0..<length xs]) \<longrightarrow> p = p'"
    using `distinct xs` `p < length xs`
    by (auto simp add: set_zip nth_eq_iff_index_eq)
  ultimately
  have "set (filter (\<lambda>(a, b). a = xs ! p) (zip xs [0..<length xs])) = {(xs ! p, p)}"
    by auto
  moreover
  have "distinct (filter (\<lambda>(a, b). a = xs ! p) (zip xs [0..<length xs]))"
    by  (rule distinct_filter, rule distinct_zipI2, simp)
  ultimately
  have "filter (\<lambda>(a, b). a = xs ! p) (zip xs [0..<length xs]) = [(xs ! p, p)]"
    by (simp add: singleton_list_iff)
  thus ?thesis
    unfolding index_of_def
    by auto
qed

text \<open>@{text sum_list}\<close>

lemma sum_list_ge_eq:
  fixes xs ys :: "nat list"
  assumes "length xs = length ys" "\<forall> i < length xs. xs ! i \<ge> ys ! i" "sum_list xs = sum_list ys"
  shows "\<forall> i < length xs. xs ! i = ys ! i"
  using assms
proof safe
  fix i
  assume "i < length xs" 
  show "xs ! i = ys ! i"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    hence "xs ! i > ys ! i"
      using assms `i < length xs`
      by auto
    moreover
    have "xs = take i xs @ [xs ! i] @ drop (i + 1) xs"
         "ys = take i ys @ [ys ! i] @ drop (i + 1) ys"
      using `i < length xs` `length xs = length ys`
      by (metis One_nat_def add.right_neutral add_Suc_right append.assoc append_take_drop_id hd_drop_conv_nth take_hd_drop)+
    hence "sum_list (take i xs) + xs ! i + sum_list (drop (i + 1) xs) =
           sum_list (take i ys) + ys ! i + sum_list (drop (i + 1) ys)"
      using `sum_list xs = sum_list ys`
      by (metis (mono_tags, lifting) add.assoc add.right_neutral sum_list.Cons sum_list.Nil sum_list.append)
    moreover
    have "sum_list (take i xs) \<ge> sum_list (take i ys)"
    proof-
      have "map ((!) xs) [0..<i] = take i xs"  "map ((!) ys) [0..<i] = take i ys"       
        using  `i < length xs` `length xs = length ys`
        by (auto intro: nth_equalityI)+
      thus ?thesis
        using sum_list_mono[of "[0..<i]" "(!) ys" "(!) xs"] assms `i < length xs`
        by auto
    qed
    moreover
    have "sum_list (drop (i+1) xs) \<ge> sum_list (drop (i+1) ys)"
    proof-
      have "map ((!) xs) [i+1..<length xs] = drop (i+1) xs"  "map ((!) ys) [i+1..<length ys] = drop (i+1) ys"       
        using  `i < length xs` `length xs = length ys`
        by (auto intro: nth_equalityI)+
      thus ?thesis
        using sum_list_mono[of "[i+1..<length xs]" "(!) ys" "(!) xs"] assms `i < length xs`
        by auto
    qed
    ultimately
    show False
      by simp
  qed
qed                                                     

lemma sum_list_const:
  assumes "\<forall> x \<in> set L. f x = y"
  shows "sum_list (map f L) = y * length L"
  using assms
  by (induction L) auto

lemma sum_list_replicate [simp]:
  fixes x :: nat
  shows "sum_list (replicate n x) = n * x"
  by (induction n) auto

lemma sum_list_nonempty_gt:
  fixes xs :: "nat list"
  assumes "x \<in> set xs" "x > 1" "\<forall> x \<in> set xs. x \<ge> 1"
  shows "sum_list xs > List.length xs"
proof-
  obtain i where "i < List.length xs" "xs ! i = x"
    by (meson assms(1) in_set_conv_nth)
  then have "xs = (take i xs) @ [x] @ (drop (i + 1) xs)" (is "?l = ?l1 @ ?x @ ?l2")
    using id_take_nth_drop by auto
  then have "sum_list xs = sum_list ?l1 + sum_list [x] + sum_list ?l2"
    by (metis append.assoc sum_list_append)
  moreover
  have "sum_list ?l1 \<ge> i"
    using sum_list_mono[of "take i xs" "\<lambda> x. 1" "\<lambda> x. x"]
    by (metis \<open>i < List.length xs\<close> assms(3) in_set_takeD lambda_one length_take less_or_eq_imp_le map_ident min.bounded_iff order_antisym_conv sum_list_const take_map)
  moreover
  have "sum_list ?l2 \<ge> List.length xs - 1 - i"
    using sum_list_mono[of "drop (i + 1) xs" "\<lambda> x. 1" "\<lambda> x. x"]
    by (metis assms(3) drop_drop in_set_dropD lambda_one length_drop map_ident sum_list_const)
  moreover
  have "sum_list ?x > 1"
    using \<open>1 < x\<close>
    by fastforce
  ultimately
  show ?thesis
    using `i < List.length xs`
    by auto
qed

text \<open>@{text insort}\<close>

lemma insort_middle:
  "\<exists> p s. xs = p @ s \<and> insort x xs = p @ [x] @ s"
  by (induct xs) (auto, meson Cons_eq_appendI)

lemma insort_append:
   "(\<exists> p s. l1 = p @ s \<and> insort x (l1 @ l2) = p @ [x] @ s @ l2) \<or>
    (\<exists> p s. l2 = p @ s \<and> insort x (l1 @ l2) = l1 @ p @ [x] @ s)"
proof-
  obtain p s where "l1 @ l2 = p @ s" and ps: "insort x (l1 @ l2) = p @ [x] @ s"
    using insort_middle[of "l1 @ l2" x]
    by auto
  then obtain us where "l1 = p @ us \<and> us @ l2 = s \<or> l1 @ us = p \<and> l2 = us @ s"
    by (subst (asm) append_eq_append_conv2) auto
  thus ?thesis
  proof
    assume "l1 = p @ us \<and> us @ l2 = s"
    thus ?thesis
      using ps
      by blast
  next
    assume "l1 @ us = p \<and> l2 = us @ s"
    thus ?thesis
      using ps
      by - (rule disjI2, rule_tac x=us in exI, rule_tac x=s in exI, simp)
  qed
qed

lemma insort_append_skip_first:
  assumes "\<forall> b \<in> set xs. b < a"
  shows "insort a (xs @ ys) = xs @ insort a ys"
  using assms
  by (induction xs) auto

text \<open>@{text sort}\<close>

lemma sort_snoc [simp]:
  shows "sort (xs @ [a]) = insort a (sort xs)"
by (induction xs) (auto simp add: insort_left_comm)

lemma sort_rev [simp]:
  shows "sort (rev s) = sort s"
  by (induction s, auto)

lemma sort_append_swapped:
  assumes "\<forall> A \<in> set xs. \<forall> B \<in> set ys. A > B"
  shows "sort (xs @ ys) = sort ys @ sort xs"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    using insort_append_skip_first[of "sort ys"]
    by (auto simp add: sorted_append)
qed

text \<open>@{text sorted}\<close>

lemma sorted_rev_cons:
  assumes "sorted (rev xs)" "x \<ge> hd xs" 
  shows "sorted (rev (x # xs))"
proof (cases "xs = []")
  case True
  thus ?thesis
    by simp
next
  case False
  hence "last (rev xs) = hd xs"
    by (simp add: last_rev)
  moreover
  have  "\<forall> x' \<in> set xs. x' \<le> last (rev xs)"
    using `sorted (rev xs)`
    using last_conv_nth[OF `xs \<noteq> []`]
    by (metis False calculation hd_conv_nth in_set_conv_nth le0 sorted_rev_nth_mono)
  ultimately
  show ?thesis
    using assms
    by (auto simp add: sorted_append)
qed

lemma sorted_filter [simp]:
  assumes "sorted xs"
  shows  "sorted (filter P xs)"
  using assms
  by (induction xs) auto

lemma sorted_rev_tl:
  assumes "sorted (rev l)"
  shows "sorted (rev (tl l))"                                                            
  using assms
  using sorted_butlast 
  by (cases "l = []") force+

lemma sorted_hd:
  assumes "x \<in> set xs" "sorted xs"
  shows "hd xs \<le> x"
  using assms
  by (metis dual_order.eq_iff empty_set equals0D list.exhaust_sel set_ConsD sorted_simps(2))

lemma sorted_last_Max:
  assumes "sorted xs" "set xs \<noteq> {}"
  shows "last xs = Max (set xs)"
  using assms
proof (induction rule: rev_induct)
  case Nil
  then show ?case 
    by simp
next
  case (snoc x xs)
  then show ?case
    by (cases "xs = []") (auto simp add: sorted_append max_def antisym)
qed

lemma sorted_map_mono:
  assumes "sorted xs" "\<forall> x \<in> set xs. \<forall> y \<in> set xs. x \<le> y \<longrightarrow> f x \<le> f y" 
  shows "sorted (map f xs)"
  using assms
  by (metis (no_types, lifting) sorted_map sorted_wrt_mono_rel)

lemma sorted_map_rev:
  assumes "sorted xs"
  assumes "\<forall> x y. x \<in> set xs \<and> y \<in> set xs \<and> x < y \<longrightarrow> f x > f y"
  shows "sorted (map f (rev xs))"
  using assms
  by (induction xs, simp, auto simp add: sorted_append less_imp_le antisym_conv2)
     (metis antisym_conv2 eq_iff less_imp_le)

lemma distinct_last_not_in_butlast:
  assumes "distinct xs" "xs \<noteq> []"
  shows "last xs \<notin> set (butlast xs)"
  using assms
  by (metis append_butlast_last_id distinct_butlast not_distinct_conv_prefix)

text \<open>@{text sorted_list_of_set}\<close>

lemma sorted_list_of_set_remove_Max:
  assumes "A \<noteq> {}" "finite A"
  shows "sorted_list_of_set (A - {Max A}) = butlast (sorted_list_of_set A)" (is "?lhs = ?rhs")
proof (rule sorted_distinct_set_unique)
  show "sorted ?lhs" "distinct ?lhs"
    using assms
    by auto
next
  show "sorted ?rhs" "distinct ?rhs"
    using assms
    by (auto simp add: sorted_butlast distinct_butlast)
next
  let ?A = "sorted_list_of_set A" 
  let ?B = "butlast ?A"
  have "A = set ?B \<union> {Max A}"
    using assms append_butlast_last_id[of "sorted_list_of_set A"]
    using sorted_last_Max[of "sorted_list_of_set A"]
    by (metis empty_set list.simps(15) set_append set_sorted_list_of_set sorted_sorted_list_of_set)
  moreover
  have "Max A \<notin> set ?B"
    using sorted_last_Max[of "sorted_list_of_set A"]
    using distinct_last_not_in_butlast[of ?A] assms
    by auto
  moreover
  have "Max A \<in> A"
    using assms
    by auto
  ultimately
  show "set ?lhs = set ?rhs"
    using assms 
    by (auto simp add: sorted_list_of_set_remove)
qed

lemma sorted_list_of_set_insert_Max [simp]:
  assumes "finite F" "\<forall> s' \<in> F. s' < s" 
  shows "sorted_list_of_set (insert s F) = sorted_list_of_set F @ [s]" (is "?lhs = ?rhs @ [s]")
proof-
  have "s \<notin> F"
    using assms
    by auto

  have s1Max: "Max (insert s F) = s"
    using assms
    apply (cases "F = {}")
    apply simp
    apply (metis (no_types, lifting) Max_gr_iff Max_in Un_insert_right finite_insert infinite_growing insert_iff sup_bot.comm_neutral)
    done

  hence "butlast ?lhs = ?rhs"
    using assms sorted_list_of_set_remove_Max[of "insert s F"] `s \<notin> F`
    by simp

  moreover

  have "last ?lhs = s"
    using s1Max sorted_last_Max[of "sorted_list_of_set (insert s F)"]
    using assms  \<open>s \<notin> F\<close>
    by (metis Un_insert_right finite_insert insert_iff set_sorted_list_of_set sorted_sorted_list_of_set sup_bot.comm_neutral)

  ultimately

  show ?thesis
    using assms append_butlast_last_id[of "?lhs"]
    by auto
qed

lemma sorted_list_of_set_inj:
  assumes "finite x" "finite y" "sorted_list_of_set x = sorted_list_of_set y"
  shows "x = y"
  using assms
  using set_sorted_list_of_set by fastforce

lemma sorted_list_of_set_union:
  assumes "\<forall> x \<in> p. \<forall> y \<in> s. x \<le> y" "p \<inter> s = {}" "finite p" "finite s"
  shows "sorted_list_of_set (p \<union> s) = sorted_list_of_set p @ sorted_list_of_set s" (is "?lhs = ?rhs")
  by (rule sorted_distinct_set_unique) (auto simp add: assms sorted_append)

lemma sorted_list_of_set_image_rev:
  assumes "\<forall> x y. x \<in> A \<and> y \<in> A \<and> x < y \<longrightarrow> f x > f y" "inj_on f A" "finite A"
  shows "sorted_list_of_set (f ` A) = rev (map f (sorted_list_of_set A))" (is "?lhs = ?rhs")
proof (rule sorted_distinct_set_unique)
  show "sorted ?lhs" "distinct ?lhs"
    using assms
    by auto
next
  show "sorted ?rhs"
    using assms
    by (simp add: rev_map sorted_map_rev)
next
  show "distinct ?rhs"
    using assms
    by (simp add: distinct_map inj_on_def)
next
  show "set ?lhs = set ?rhs"
    using assms
    by auto
qed

text \<open>@{text map2}\<close>

lemma map2_map:
   "map2 f (map g xs) xs = map (\<lambda> k. f (g k) k) xs"
  by (induction xs) auto

text \<open>@{text replicate}\<close>

lemma list_eq_replicate:
  assumes "\<forall> x \<in> set l. x = a" 
  shows "l = replicate (length l) a"
proof (rule nth_equalityI)
  show "length l = length (replicate (length l) a)"
    by simp
next
  fix i
  assume "i < length l"
  thus "l ! i = replicate (length l) a ! i"
    using assms in_set_conv_nth[of "l ! i" l]
    by auto
qed

text \<open>@{text concat}\<close>

lemma concat_nth:
  assumes "\<forall> x \<in> set M. length x = n" "i < n * length M"
  shows "concat M ! i = M ! (i div n) ! (i mod n)"
  using assms
proof (induction M rule: rev_induct)
  case Nil
  then show ?case 
    by simp
next
  case (snoc a M)
  show ?case
  proof (cases "i < n * length M")
    case True
    hence "i div n < length M"
      by (simp add: Groups.mult_ac(2) less_mult_imp_div_less)
    moreover
    have "length (concat M) = n * length M"
      using snoc(2)
      by (induction M) auto
    ultimately
    show ?thesis
      using snoc True
      by (simp add: nth_append)
  next
    case False
    hence "i div n \<ge> length M"
      by (metis assms(2) div_le_mono le_less_linear mult_is_0 nonzero_mult_div_cancel_left)
    moreover
    have "length (concat M) = n * length M"
      using snoc(2)
      by (induction M) auto
    moreover
    have "i div n = length M"
      using snoc(3) False div_nat_eqI
      by auto
    moreover
    have "i - n * length M = i mod n"
      using False
      by (metis `i div n = length M` minus_mult_div_eq_mod)
    ultimately
    show ?thesis
      using False
      by(simp add: nth_append)
  qed
qed

lemma drop_concat:
  assumes "\<forall> x \<in> set M. length x = n" "i < length M"
  shows "drop (i * n) (concat M) = (concat (drop i M))"
  using assms 
proof (induct M rule: rev_induct)
  case Nil
  then show ?case 
    by simp
next
  case (snoc x xs)
  show ?case
  proof (cases "i < length xs")
    case True
    then show ?thesis
      using snoc
      using length_concat[of xs]
      using sum_list_const[of xs length n]
      by auto
  next
    case False
    hence "i = length xs"
      using snoc(3)
      by simp
    then show ?thesis
      using snoc(2)
      using length_concat[of xs]
      using sum_list_const[of xs length n]
      by simp
  qed
qed

lemma take_concat:
  assumes "length (hd M) = n" "M \<noteq> []"
  shows "take n (concat M) = hd M"
  using assms
  by (metis append_eq_conv_conj concat.simps(2) hd_Cons_tl)

lemma take_drop_concat:
  assumes "\<forall> x \<in> set M. length x = n" "i < length M"
  shows "take n (drop (i * n) (concat M)) = M ! i"
  using assms
  using drop_concat[OF assms]
  using take_concat[of "drop i M" n]
  by (simp add: hd_drop_conv_nth)

lemma hd_concat [simp]:
  assumes "xs \<noteq> []" "hd xs \<noteq> []"
  shows "hd (concat xs) = hd (hd xs)"
  using assms
  by (induction xs, auto)

lemma concat_filter_empty:
  shows "concat xs = concat (filter (\<lambda> x. x \<noteq> []) xs)"
  by (induction xs) auto

lemma sorted_concat:
  assumes "\<forall> xs \<in> set xss. sorted xs"
          "\<forall> i j. i < j \<and> j < length xss \<longrightarrow> (\<forall> x \<in> set (xss ! i). \<forall> y \<in> set (xss ! j). x \<le> y)"
 shows "sorted (concat xss)"
  using assms
proof (induction xss)
  case Nil
  then show ?case
    by simp
next
  case (Cons a xss)
  have "sorted a"
    using Cons(2)
    by simp
  moreover
  have "sorted (concat xss)"
  proof (rule Cons(1))
    show "\<forall> a \<in> set xss. sorted a"
      using Cons(2)
      by simp
  next
    show "\<forall>i j. i < j \<and> j < length xss \<longrightarrow> (\<forall>x\<in>set (xss ! i). \<forall>a\<in>set (xss ! j). x \<le> a)"
    proof safe                                                                                  
      fix i j x y
      assume "x \<in> set (xss ! i)" "y \<in> set (xss ! j)" "i < j" "j < length xss"
      thus "x \<le> y"
        using Cons(3)[rule_format, of "i+1" "j+1" x y]
        by simp
    qed
  qed

  moreover
  have "\<forall> x \<in> set a. \<forall> y \<in> set xss. \<forall>z\<in>set y. x \<le> z"
  proof safe
    fix x y z
    assume *: "x \<in> set a" "y \<in> set xss" "z \<in> set y"
    then obtain j where "j < length xss" "xss ! j = y"
      using in_set_conv_nth[of y xss]
      by auto
    thus "x \<le> z" 
      using Cons(3)[rule_format, of 0 "j+1" x z] *
      by simp
  qed

  ultimately

  show ?case 
    by (simp add: sorted_append)
qed

lemma concat_nonempty_singletons:
  assumes "List.length (concat xs) = List.length xs" "\<forall> x \<in> set xs. x \<noteq> []" "x \<in> set xs"
  shows "List.length x = 1"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then have "List.length x > 1"
    using assms(2-3)
    using antisym_conv3 by auto
  moreover
  have "\<forall> x \<in> set xs. List.length x \<ge> 1"
    using assms(2)
    by (simp add: Suc_leI)
  ultimately
  have "sum_list (map List.length xs) > List.length xs"
    using sum_list_nonempty_gt[of "List.length x" "map List.length xs"] `x \<in> set xs`
    by auto
  then show False
    using assms(1)
    by (simp add: length_concat)
qed


definition concat_prefix_length :: "'a list list \<Rightarrow> nat \<Rightarrow> nat" where 
  "concat_prefix_length xs n = sum_list (map length (take n xs))"

lemma concat_prefix_length_Suc [simp]:
  assumes "n < List.length xs"
  shows "concat_prefix_length xs (n + 1) = concat_prefix_length xs n  + length (xs ! n)"
proof-
  have "take (n + 1) xs = take n xs @ [xs ! n]"
    using assms
    using take_Suc_conv_app_nth by auto
  then show ?thesis
    unfolding concat_prefix_length_def
    by auto
qed

lemma concat_prefix_length_ub:
  shows "concat_prefix_length xs n \<le> length (concat xs)"
  unfolding concat_prefix_length_def
  by (metis append_take_drop_id concat_append length_append length_concat linorder_not_less not_add_less1)

lemma length_prefix_mono:
  assumes "n1 \<le> n2"
  shows "concat_prefix_length xs n1 \<le> concat_prefix_length xs n2"
proof-
  obtain ys where "take n2 xs = take n1 xs @ ys"
    by (metis assms nat_le_iff_add take_add)
  then have "sum_list (map List.length (take n2 xs)) = sum_list (map List.length (take n1 xs)) + sum_list (map List.length ys)"
    by auto
  moreover have "sum_list (map List.length ys) \<ge> 0"
    by auto
  ultimately show ?thesis
    unfolding concat_prefix_length_def
    by auto
qed

lemma concat_in_nth_list:
  assumes "j < length xs" "k < length (xs ! j)"
  assumes "x = (xs ! j ! k)" "i = concat_prefix_length xs j + k"
  shows "(concat xs) ! i = x"
proof-
  let ?p = "take j xs"
  let ?s = "drop (j+1) xs"
  have "xs = ?p @ [xs ! j] @ ?s"
    by (metis add.commute append_assoc append_take_drop_id assms(1) hd_drop_conv_nth plus_1_eq_Suc take_hd_drop)
  then have "concat xs = concat ?p @ (xs ! j) @ concat ?s"
    by (metis append.right_neutral concat.simps(1) concat.simps(2) concat_append)
  moreover have "length (concat ?p) = sum_list (map length ?p)"
    by (rule length_concat)
  ultimately have "concat xs ! i = ((xs ! j) @ concat ?s) ! k"
    using `i = concat_prefix_length xs j + k`
    by (metis nth_append_length_plus concat_prefix_length_def)
  also have "... = (xs ! j) ! k"
    using `k < length (xs ! j)`
    thm nth_append
    by (simp add: nth_append)
  finally show ?thesis
    using `x = (xs ! j) ! k`
    by simp
qed

text \<open>@{text positions}\<close>

definition positions :: "bool list \<Rightarrow> nat list" where
  "positions xs = map snd (filter (\<lambda> (x, p). x) (zip xs [0..<length xs]))"

lemma sorted_positions:
  shows "sorted (positions xs)"
  unfolding positions_def
  by (induction xs rule: rev_induct) (auto simp add: sorted_append set_zip)

lemma distinct_positions:
  shows "distinct (positions xs)"
  unfolding positions_def
  by (induction xs rule: rev_induct) (auto simp add: set_zip)

lemma set_positions:
  shows "set (positions xs) = {p. p < length xs \<and> xs ! p}"
  unfolding positions_def
  by (induction xs rule: rev_induct) (auto simp add: nth_append)

lemma positions_sorted_list_of_set:
  shows "positions xs = sorted_list_of_set {p. p < length xs \<and> xs ! p}"
  using sorted_distinct_set_unique[of "positions xs" "sorted_list_of_set {p. p < length xs \<and> xs ! p}"]
  by (simp add: sorted_positions distinct_positions set_positions)

text \<open>@{text of_positions}\<close>

definition of_positions where
  "of_positions n xs = map (\<lambda> k. k \<in> set xs) [0..<n]"

lemma of_positions_positions: 
  shows "of_positions (length xs) (positions xs) = xs"
proof-
  have "map (\<lambda>k. k < length xs \<and> xs ! k) [0..<length xs] = map (\<lambda> k. xs ! k) [0..<length xs]"
    by simp
  thus ?thesis
    using map_nth[of xs]
    unfolding of_positions_def
    by (simp add: set_positions)
qed

lemma positions_of_positions:
  assumes "set ps \<subseteq> {0..<n}" "distinct ps" "sorted ps"
  shows "positions (of_positions n ps) = ps"
proof-
  let ?A = "{k. k < length (of_positions n ps) \<and> of_positions n ps ! k}"
  have "set ps = ?A"
    using `set ps \<subseteq> {0..<n}`
    unfolding of_positions_def
    by auto
  hence "ps = sorted_list_of_set ?A"
    using `sorted ps` `distinct ps`
    using sorted_distinct_set_unique[of ps "sorted_list_of_set ?A"]
    by simp
  thus ?thesis
    using positions_sorted_list_of_set[of "of_positions n ps"]
    by simp
qed


definition max_by_prop :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b::linorder) \<Rightarrow> 'a set" where 
  "max_by_prop A f = (
    let max = Max (f ` A)
     in {x \<in> A. f x = max}
  )"

lemma max_by_prop_nonempty [simp]:
  assumes "finite A" "A \<noteq> {}"
  shows "max_by_prop A f \<noteq> {}"
  using assms Max_in[of "f ` A"]
  unfolding max_by_prop_def Let_def
  by fastforce

lemma max_by_prop_finite [simp]:
  assumes "finite A" 
  shows "finite (max_by_prop A f)"
  using assms
  unfolding max_by_prop_def Let_def
  by auto

lemma max_by_prop_subseteq:
  shows "max_by_prop A f \<subseteq> A"
  unfolding max_by_prop_def
  by auto

lemma max_by_prop_max_prop:
  assumes "finite A" "x \<in> max_by_prop A f" "x' \<in> A"
  shows "f x \<ge> f x'"
  using assms
  unfolding max_by_prop_def Let_def
  by simp

lemma max_by_prop_max_prop_eq:
  assumes "finite A" "x \<in> max_by_prop A f" "x' \<in> max_by_prop A f"
  shows "f x = f x'"
  using assms
  unfolding max_by_prop_def Let_def
  by simp

lemma max_by_prop_max_prop_gt:
  assumes "finite A" "x \<in> max_by_prop A f" "x' \<in> A" "x' \<notin> max_by_prop A f"
  shows "f x > f x'"
  using assms
  unfolding max_by_prop_def Let_def
  by (simp add: order_less_le)

lemma max_by_prop_iff:
  assumes "finite A" "A \<noteq> {}"
  shows "x \<in> max_by_prop A f \<longleftrightarrow> x \<in> A \<and> (\<forall> x' \<in> A. f x' \<le> f x)"
  unfolding max_by_prop_def Let_def
  by (smt (verit, best) Max.coboundedI Max_in assms(1) assms(2) finite_has_maximal2 finite_imageI imageE image_eqI image_is_empty mem_Collect_eq)


lemma max_by_prop_pair:
  assumes "finite A" "A \<noteq> {}"
  shows "max_by_prop (max_by_prop A f1) f2 = max_by_prop A (\<lambda> x. (f1 x, f2 x))" (is "?lhs = ?rhs")
proof-
  have "\<forall> x. x \<in> ?lhs \<longleftrightarrow> x \<in> ?rhs"
  proof
    fix x
    have "x \<in> ?lhs \<longleftrightarrow> x \<in> max_by_prop A f1 \<and> (\<forall> x' \<in> max_by_prop A f1. f2 x \<ge> f2 x')"
      using assms max_by_prop_iff
      by (metis max_by_prop_finite max_by_prop_nonempty)
    also have "... \<longleftrightarrow> x \<in> A \<and> (\<forall> x' \<in> A. f1 x' \<le> f1 x) \<and> (\<forall> x' \<in> A. (\<forall> x'' \<in> A. f1 x'' \<le> f1 x') \<longrightarrow> f2 x \<ge> f2 x')"
      using assms max_by_prop_iff
      by metis
    also have "... \<longleftrightarrow> x \<in> ?rhs"
      by (subst max_by_prop_iff[OF assms]) (force simp add: less_eq_prod_def nless_le)
    finally show "x \<in> ?lhs \<longleftrightarrow> x \<in> ?rhs"
      .
  qed
  then show ?thesis
    by blast
qed

lemma max_by_prop_cong:
  assumes "finite A" "A \<noteq> {}"
  assumes "\<forall> x1 \<in> A. \<forall> x2 \<in> A. f1 x1 < f1 x2 \<longleftrightarrow> f2 x1 < f2 x2"
  shows "max_by_prop A f1 = max_by_prop A f2"
  using assms
  unfolding max_by_prop_def
  by (smt (verit, ccfv_SIG) Collect_cong Max_ge Max_in finite_imageI imageE image_eqI image_is_empty linorder_not_less not_less_iff_gr_or_eq) 


definition split_by_prop :: "'a set => ('a => 'b) => 'a set set" where
  "split_by_prop A f = { {y \<in> A. f y = x} | x. x \<in> f ` A}" 

lemma split_by_prop_finite [simp]:
  assumes "finite A"
  shows "finite (split_by_prop A f)"
  unfolding split_by_prop_def
  using assms
  by auto

lemma split_by_prop_nonempty [simp]:
  shows "{} \<notin> split_by_prop A f"
  unfolding split_by_prop_def
  by auto

lemma split_by_prop_set [simp]:
  shows "\<Union> (split_by_prop A f) = A"
  unfolding split_by_prop_def
  by auto

lemma split_by_prop_disjoint:
  assumes "x \<in> split_by_prop A f" "y \<in> split_by_prop A f"
  shows "x = y \<or> x \<inter> y = {}"
  using assms
  unfolding split_by_prop_def
  by auto

definition is_split_by_prop where
  "is_split_by_prop cs f \<longleftrightarrow> 
    (\<forall> cl \<in> cs. \<forall> v1 \<in> cl. \<forall> v2 \<in> cl. f v1 = f v2) \<and> 
    (\<forall> cl1 \<in> cs. \<forall> cl2 \<in> cs. cl1 \<noteq> cl2  \<longrightarrow> (\<forall> v1 \<in> cl1. \<forall> v2 \<in> cl2. f v1 \<noteq> f v2)) \<and>
    (\<forall> cl \<in> cs. cl \<noteq> {})"

lemma split_by_prop_is_split_by_prop [simp]:
  shows "is_split_by_prop (split_by_prop A f) f"
  unfolding is_split_by_prop_def split_by_prop_def
  by auto

lemma split_by_prop_singleton:
  assumes "A \<noteq> {}"
  shows "split_by_prop A f = {A} \<longleftrightarrow> (\<forall> x \<in> A. \<forall> y \<in> A. f x = f y)"
proof
  assume "split_by_prop A f = {A}"
  then show "\<forall> x \<in> A. \<forall> y \<in> A. f x = f y"
    by (metis is_split_by_prop_def singletonI split_by_prop_is_split_by_prop)
next
  assume *: "\<forall> x \<in> A. \<forall> y \<in> A. f x = f y"
  from assms obtain x where "x \<in> A"
    by auto
  then have "\<forall> x' \<in> A. f x' = f x"
    using *
    by blast
  then have "f ` A = {f x}"
    using \<open>x \<in> A\<close> by blast
  then have "{{y \<in> A. f y = x} |x. x \<in> f ` A} = {{y \<in> A. f y = f x}}"
    by auto
  then show "split_by_prop A f = {A}"
    unfolding split_by_prop_def
    using *
    by blast
qed

end
