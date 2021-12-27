theory Option_Lexord
imports Main
begin

instantiation option :: (ord) ord
begin

definition "x \<le> y \<longleftrightarrow>
  (case y of                             
      None \<Rightarrow> True 
    | Some y' \<Rightarrow>
          (case x of 
            None \<Rightarrow> False
          | Some x' \<Rightarrow> x' \<le> y')
      )"

definition  
  "(x :: _ option) < y \<longleftrightarrow> x \<le> y \<and> x \<noteq> y"

instance
  ..
end

instantiation option :: (linorder) linorder
begin

instance
proof
  fix x :: "'a option" 
  show "x \<le> x"
    unfolding less_eq_option_def
    by (cases x, auto)
next
  fix x y :: "'a option"
  show "x \<le> y \<or> y \<le> x"
    unfolding less_eq_option_def
    by (metis le_cases option.case_eq_if)
next
  fix x y :: "'a option"
  assume "x \<le> y" "y \<le> x"
  then show "x = y"
    unfolding less_eq_option_def
    by (smt (z3) antisym case_optionE option.simps(5))
next
  fix x y z :: "'a option"
  assume "x \<le> y" "y \<le> z"
  then show "x \<le> z"
    unfolding less_eq_option_def         
    by (metis dual_order.trans option.case_eq_if)
next
  fix x y :: "'a option"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    unfolding less_eq_option_def less_option_def
    by (smt (z3) case_optionE dual_order.antisym option.case_eq_if option.simps(5))
qed

end


end