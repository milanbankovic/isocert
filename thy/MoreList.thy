theory MoreList
imports Main
begin
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

end