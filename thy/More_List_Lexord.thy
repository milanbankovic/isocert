theory More_List_Lexord
  imports Main "HOL-Library.List_Lexorder" More_List
begin

subsection \<open>Additional lemmas about list lexorder\<close>

lemma lexord_right_append:
  assumes "(xs, ys) \<in> lexord R" "length xs = length ys"
  shows "(xs @ xs', ys @ ys') \<in> lexord R"
  using assms
  unfolding lexord_def
  by auto blast+

lemma list_less_right_append:
  assumes "length xs = length ys" "xs < ys"
  shows "xs @ xs' < ys @ ys'"
  using assms
  by (simp add: list_less_def lexord_right_append)

lemma lexord_prefix_same_length:
  assumes "(xs1 @ ys1, xs2 @ ys2) \<in> lexord R" "length xs1 = length xs2"
  shows "(xs1, xs2) \<in> lexord R \<or> xs1 = xs2"
  using assms
  by (induct xs1 arbitrary: xs2 ys1 ys2) (auto, smt Suc_length_conv append_Cons lexord_cons_cons)

lemma list_prefix_same_length:
  assumes "xs1 @ ys1 < xs2 @ ys2" "length xs1 = length xs2"
  shows "xs1 \<le> xs2"
  using assms
  by (simp add: list_less_def list_le_def lexord_prefix_same_length)

lemma list_less_append:
  assumes "ys1 < ys2"
  shows "xs @ ys1 < xs @ ys2"
  using assms
  unfolding list_less_def lexord_def
  by (smt append_assoc case_prodD case_prodI mem_Collect_eq)

lemma map_mono:
  assumes "length a = length b"
    "\<forall> x \<in> set a \<union> set b. \<forall> y \<in> set a \<union> set b. x < y \<longleftrightarrow> f x < f y"
    "\<forall> x \<in> set a \<union> set b. \<forall> y \<in> set a \<union> set b. f x = f y \<longrightarrow> x = y"
  shows "a < b \<longleftrightarrow> map f a < map f b"
proof
  assume "a < b"
  then obtain u xa xb va vb where *: "a = u @ xa # va" "b = u @ xb # vb" "xa < xb"
    using `length a = length b`
    unfolding list_less_def lexord_def
    by auto
  hence "map f a = map f u @ f xa # map f va" "map f b = map f u @ f xb # map f vb" "f xa < f xb"
    using assms(1-2)
    by auto
  thus "map f a < map f b"
    unfolding list_less_def lexord_def
    by blast
next
  have "length (map f a) = length (map f b)"
    using assms
    by auto
  assume "map f a < map f b"
  then obtain u xa xb va vb where *: "map f a = u @ xa # va" "map f b = u @ xb # vb" "xa < xb"
    unfolding list_less_def lexord_def
    using \<open>length (map f a) = length (map f b)\<close> case_prodD lexord_take_index_conv mem_Collect_eq min_less_iff_conj
    by fastforce
  hence "xa = f (a ! (length u))" "xb = f (b ! (length u))" 
    by (metis One_nat_def add_diff_cancel_left' diff_is_0_eq' length_append length_map less_or_eq_imp_le list.size(4) not_le not_one_le_zero nth_append_length nth_map zero_eq_add_iff_both_eq_0)+
  hence "a ! length u < b ! length u"
    using `xa < xb` assms(2)[rule_format, of "a ! length u" "b ! length u"]
    by (metis "*"(1) One_nat_def Un_iff \<open>length (map f a) = length (map f b)\<close> add_diff_cancel_left' diff_is_0_eq' length_append length_map less_or_eq_imp_le list.size(4) not_le not_one_le_zero nth_mem zero_eq_add_iff_both_eq_0)
  moreover
  have "take (length u) a = take (length u) b"
  proof (rule nth_equalityI)
    show "length (take (length u) a) = length (take (length u) b)"
      using * assms(1)
      by simp
  next
    fix i
    assume **: "i < length (take (length u) a)"
    hence "map f a ! i = map f b ! i"
      using *
      by (simp add: nth_append)
    hence "f (a ! i) = f (b ! i)"
      using * **
      by (metis assms(1) length_take min_less_iff_conj nth_map)
    hence "a ! i = b ! i"
      using assms(3)[rule_format, of "a ! i" "b ! i"]
      using "**" assms(1) by auto
    thus "take (length u) a ! i = take (length u) b ! i"
      using * **
      by simp
  qed
  ultimately 
  show "a < b"
    using * assms(1)
    unfolding list_less_def lexord_def
    by (smt add_diff_cancel_left' case_prodI diff_is_0_eq' id_take_nth_drop length_append length_map list.size(4) mem_Collect_eq nat.simps(3) not_le zero_eq_add_iff_both_eq_0)
qed

lemma map_mono':
  assumes "length a = length b"
    "\<forall> x \<in> set a \<union> set b. \<forall> y \<in> set a \<union> set b. x < y \<longleftrightarrow> f x > f y"
    "\<forall> x \<in> set a \<union> set b. \<forall> y \<in> set a \<union> set b. f x = f y \<longrightarrow> x = y"
  shows "a < b \<longleftrightarrow> map f a > map f b"
proof
  assume "a < b"
  then obtain u xa xb va vb where *: "a = u @ xa # va" "b = u @ xb # vb" "xa < xb"
    using `length a = length b`
    unfolding list_less_def lexord_def
    by auto
  hence "map f a = map f u @ f xa # map f va" "map f b = map f u @ f xb # map f vb" "f xa > f xb"
    using assms(1-2)
    by auto
  thus "map f a > map f b"
    unfolding list_less_def lexord_def
    by blast
next
  have "length (map f a) = length (map f b)"
    using assms
    by auto
  assume "map f b < map f a"
  then obtain u xa xb va vb where *: "map f a = u @ xa # va" "map f b = u @ xb # vb" "xa > xb"
    unfolding list_less_def lexord_def
    using \<open>length (map f a) = length (map f b)\<close> case_prodD lexord_take_index_conv mem_Collect_eq min_less_iff_conj
    by fastforce
  hence "xa = f (a ! (length u))" "xb = f (b ! (length u))" 
    by (metis One_nat_def add_diff_cancel_left' diff_is_0_eq' length_append length_map less_or_eq_imp_le list.size(4) not_le not_one_le_zero nth_append_length nth_map zero_eq_add_iff_both_eq_0)+
  hence "a ! length u < b ! length u"
    using `xa > xb` assms(2)[rule_format, of "a ! length u" "b ! length u"]
    by (metis "*"(1) One_nat_def Un_iff \<open>length (map f a) = length (map f b)\<close> add_diff_cancel_left' diff_is_0_eq' length_append length_map less_or_eq_imp_le list.size(4) not_le not_one_le_zero nth_mem zero_eq_add_iff_both_eq_0)
  moreover
  have "take (length u) a = take (length u) b"
  proof (rule nth_equalityI)
    show "length (take (length u) a) = length (take (length u) b)"
      using * assms(1)
      by simp
  next
    fix i
    assume **: "i < length (take (length u) a)"
    hence "map f a ! i = map f b ! i"
      using *
      by (simp add: nth_append)
    hence "f (a ! i) = f (b ! i)"
      using * **
      by (metis assms(1) length_take min_less_iff_conj nth_map)
    hence "a ! i = b ! i"
      using assms(3)[rule_format, of "a ! i" "b ! i"]
      using "**" assms(1) by auto
    thus "take (length u) a ! i = take (length u) b ! i"
      using * **
      by simp
  qed
  ultimately 
  show "a < b"
    using * assms(1)
    unfolding list_less_def lexord_def
    by (smt add_diff_cancel_left' case_prodI diff_is_0_eq' id_take_nth_drop length_append length_map list.size(4) mem_Collect_eq nat.simps(3) not_le zero_eq_add_iff_both_eq_0)
qed

lemma map_filter_less_list:
  assumes "length (filter P1 [0..<n]) = length (filter P2 [0..<n])"
  shows "rev (map P1 [0..<n]) < rev (map P2 [0..<n]) \<longleftrightarrow> 
         rev (filter P1 [0..<n]) < rev (filter P2 [0..<n])" (is "?lhs \<longleftrightarrow> ?rhs")
proof 
  assume ?lhs
  then obtain u v w
    where uvw: "rev (map P1 [0..<n]) = u @ False # v" "rev (map P2 [0..<n]) = u @ True # w"
    unfolding list_less_def lexord_def
    by auto

  moreover
  hence *: "length u + 1 + length v = n" "length u + 1 + length w = n"
    by (metis One_nat_def add.assoc add.commute diff_zero length_append length_map length_rev length_upt list.size(4))+

  moreover

  let ?F = "\<lambda> l1 l2. map snd (filter fst (zip l1 l2))"

  have P1: "filter P1 [0..<n] = ?F (map P1 [0..<n]) [0..<n]"
    by (induction n, auto)
  moreover
  have P2: "filter P2 [0..<n] = ?F (map P2 [0..<n]) [0..<n]"
    by (induction n, auto)
  moreover

  let ?i1 = "take (length u) (rev [0..<n])"
  let ?i = "rev [0..<n] ! length u"
  let ?i2 = "drop (length u + 1) (rev [0..<n])"

  have ii: "rev [0..<n] = ?i1 @ [?i] @ ?i2"
    by (metis One_nat_def add.right_neutral add_Suc_right add_diff_cancel_left' append_Cons append_Nil calculation(1) calculation(3) diff_is_0_eq' diff_zero id_take_nth_drop length_append length_map length_rev length_upt less_add_one linorder_not_le not_add_less1)

  have "zip (u @ False # v) (rev [0..<n]) = zip u ?i1 @ [(False, ?i)] @ zip v ?i2"
    using ii
    by (metis append_Cons append_Nil append_take_drop_id same_append_eq zip_Cons_Cons zip_append1)

  moreover

  have z2: "zip (u @ True # w) (rev [0..<n]) = zip u ?i1 @ [(True, ?i)] @ zip w ?i2"
    using ii
    by (metis append_Cons append_Nil append_take_drop_id same_append_eq zip_Cons_Cons zip_append1)

  ultimately
  have rf: "rev (filter P1 [0..<n]) = ?F u ?i1 @ ?F v ?i2 "
           "rev (filter P2 [0..<n]) = ?F u ?i1 @ [?i] @ ?F w ?i2 "
    using zip_rev[of "map P1 [0..<n]" "[0..<n]", symmetric]
    using zip_rev[of "map P2 [0..<n]" "[0..<n]", symmetric]
    by (auto simp add: rev_map rev_filter)

  moreover

  have "?F v ?i2 < ?i # ?F w ?i2"
  proof-
    have "length (?F v ?i2) = length (?i # ?F w ?i2)"
      using rf assms
      by (smt add_left_cancel append_Cons append_Nil length_append length_rev)
    hence "?F v ?i2 \<noteq> []"
      by auto
    moreover
    have "\<forall> x \<in> set (?F v ?i2). x < ?i"
      using *
      by (auto simp add: set_zip nth_rev)
    ultimately
    show ?thesis
      by (metis (no_types, hide_lams) Cons_less_Cons One_nat_def add.commute add.right_neutral add_Suc_right list.set_intros(1) max_list.cases)
  qed
  ultimately
  show ?rhs
    using zip_rev[of "map P1 [0..<n]" "[0..<n]", symmetric]
    using zip_rev[of "map P2 [0..<n]" "[0..<n]", symmetric]
    by (simp add: rev_map rev_filter nth_rev list_less_append)
next
  assume ?rhs
  then obtain u a b v w
    where *: "a < b"  "rev (filter P1 [0..<n]) = u @ a # v" "rev (filter P2 [0..<n]) = u @ b # w"
    using assms
    unfolding list_less_def lexord_def
    by auto (metis append_Cons append_assoc append_eq_append_conv assms length_rev list.discI)

  hence **: "filter P1 [0..<n] = rev (u @ a # v)" "filter P2 [0..<n] = rev (u @ b # w)"
    by (metis rev_rev_ident)+

  have "sorted (filter P1 [0..<n])" "sorted (filter P2 [0..<n])"
       "distinct (filter P1 [0..<n])" "distinct (filter P2 [0..<n])"
    by auto
  hence "sorted (rev (u @ a # v))"  "sorted (rev (u @ b # w))"
        "distinct (rev (u @ a # v))"  "distinct (rev (u @ b # w))"
    using **
    by auto

  have "\<forall> i. i \<in> set u \<longleftrightarrow> b < i \<and> i < n \<and> P1 i"
  proof safe
    fix i
    assume "i \<in> set u" 
    thus "b < i"
      using `sorted (rev (u @ b # w))` `distinct (rev (u @ b # w))`
      by (metis distinct_append distinct_rev le_neq_implies_less list.set_intros(1) not_distinct_conv_prefix rev_append set_rev sorted_append)
  next
    fix i
    assume "i \<in> set u"
    hence "i \<in> set (filter P1 [0..<n])"
      using **
      by simp
    thus "i < n" "P1 i"
      by auto
  next
    fix i
    assume "b < i" "i < n" "P1 i"
    hence "i \<in> set (filter P1 [0..<n])"
      by auto
    hence "i \<in> set (rev (u @ a # v))"
      using **
      by simp
    thus "i \<in> set u"
      using `a < b` `b < i` `sorted (rev (u @ a # v))`
      by (auto simp add: sorted_append)
  qed

  moreover

  have "\<forall> i. i \<in> set u \<longleftrightarrow> b < i \<and> i < n \<and> P2 i"
  proof safe
    fix i
    assume "i \<in> set u" 
    thus "b < i"
      using `sorted (rev (u @ b # w))` `distinct (rev (u @ b # w))`
      by (metis distinct_append distinct_rev le_neq_implies_less list.set_intros(1) not_distinct_conv_prefix rev_append set_rev sorted_append)
  next
    fix i
    assume "i \<in> set u"
    hence "i \<in> set (filter P2 [0..<n])"
      using **
      by simp
    thus "i < n" "P2 i"
      by auto
  next
    fix i
    assume "b < i" "i < n" "P2 i"
    hence "i \<in> set (filter P2 [0..<n])"
      by auto
    hence "i \<in> set (rev (u @ b # w))"
      using **
      by simp
    thus "i \<in> set u"
      using `b < i` `sorted (rev (u @ b # w))` 
      by (auto simp add: sorted_append)
  qed

  ultimately

  have "\<forall> i. b < i \<and> i < n \<longrightarrow> P1 i \<longleftrightarrow> P2 i"
    by auto
  hence "rev (map P1 [b+1..<n]) = rev (map P2 [b+1..<n]) "
    by auto
  moreover
  have "b \<in> set (filter P2 [0..<n])"
    using **
    by simp
  hence "P2 b" "b < n"
    by simp_all

  moreover

  have "b \<notin> set (filter P1 [0..<n])"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    hence "b \<in> set (rev (u @ a # v))"
      using **
      by simp
    thus False
      using `sorted (rev (u @ a # v))` `a < b` `distinct (rev (u @ b # w))`
      by (auto simp add: sorted_append)
  qed
  hence "\<not> P1 b"
    using `b < n`
    by auto

  moreover
  have "[0..<n] = [0..<b] @ [b] @ [b+1..<n]"
    using `b < n`
    by (metis One_nat_def add.right_neutral add_Suc_right append_Cons append_Nil less_imp_add_positive upt_add_eq_append upt_conv_Cons zero_le)
  hence "rev (map P1 [0..<n]) = rev (map P1 [b+1..<n]) @ [P1 b] @ rev (map P1 [0..<b])"
        "rev (map P2 [0..<n]) = rev (map P2 [b+1..<n]) @ [P2 b] @ rev (map P2 [0..<b])"
    by auto
  ultimately
  show ?lhs
    unfolding list_less_def lexord_def
    by fastforce
qed

lemma map_less:
  shows "map f1 I < map f2 I \<longleftrightarrow> (\<exists> i < length I. f1 (I ! i) < f2 (I ! i) \<and> (\<forall> j < i. f1 (I ! j) = f2 (I ! j)))" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then obtain a b u v w where *: "a < b" "map f1 I = u @ a # v" "map f2 I = u @ b # w"
    unfolding list_less_def lexord_def
    by auto
  let ?i = "length u"
  have "?i < length I"
    using *
    by (metis One_nat_def add_diff_cancel_left' diff_is_0_eq' le_eq_less_or_eq length_append length_map linorder_neqE_nat list.size(4) not_one_le_zero zero_eq_add_iff_both_eq_0)
  moreover
  have "map f1 I ! ?i = a" "map f2 I ! ?i = b"
    using *
    by auto
  hence "f1 (I ! ?i) < f2 (I ! ?i)"
    using `a < b` `?i < length I`
    by simp
  moreover
  have "\<forall> j < ?i. map f1 I ! j = map f2 I ! j"
    using * `?i < length I`
    by (auto simp add: nth_append)
  hence "\<forall> j < ?i. f1 (I ! j) = f2 (I ! j)"
    using `?i < length I`
    by simp
  ultimately
  show ?rhs
    using *
    by (rule_tac x="?i" in exI) auto
next
  assume ?rhs
  then obtain i where
    i: "i<length I" "f1 (I ! i) < f2 (I ! i)" "(\<forall>j<i. f1 (I ! j) = f2 (I ! j))"
    by auto
  hence "take i (map f2 I) =  take i (map f1 I)"
    by (simp add: i(1) less_imp_le less_le_trans nth_take_lemma)
  hence "\<exists>u a b. a < b \<and> (\<exists>v. map f1 I = u @ a # v) \<and> (\<exists>w. map f2 I = u @ b # w)"
    using i
    apply (rule_tac x="take i (map f1 I)" in exI, rule_tac x="f1 (I ! i)" in exI, rule_tac x="f2 (I ! i)" in exI)
    apply auto
    apply (metis id_take_nth_drop length_map nth_map)
    apply (metis id_take_nth_drop length_map nth_map)
    done    
  thus ?lhs
    unfolding list_less_def lexord_def
    by auto    
qed

end
