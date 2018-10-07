theory mult
  imports Main soma
begin
primrec mult::"nat \<Rightarrow> nat \<Rightarrow> nat" where
multeq1:"mult x 0 = 0"|
multeq2:"mult x (Suc y) = soma x (mult x y)"

thm nat.induct
print_statement nat.induct

value "mult 1 0"
value "mult 1 1"
value "mult 1 2"
value "mult 2 2"
value "mult 2 3"

theorem mult1:"\<forall>x. mult x y = x * y"
proof (induct y)
  show "\<forall>x. mult x 0 = x * 0"
  proof (rule allI)
    fix x0::nat
    have "mult x0 0 = 0" by (simp only:multeq1)
    also have "... = x0 * 0" by simp
    finally show "mult x0 0 = x0 * 0" by simp
  qed
next
  fix y0::nat
  assume HI:"\<forall>x. mult x y0 = x * y0"
  show "\<forall>x. mult x (Suc y0) = x * (Suc y0)"
  proof (rule allI)
    fix x0::nat
    have "mult x0 (Suc y0) = soma x0 (mult x0 y0)" by (simp only:multeq2)
    also have "... = soma x0 (x0 * y0)" by (simp only:HI)
    also have "... = soma (x0 * y0) x0" by (simp only:soma2)
    also have "... = (x0 * y0) + x0" by (simp only:soma1)
    also have "... = x0 * (Suc y0) + 0" by simp
    also have "... = soma (x0 * (Suc y0)) 0" by (simp only:soma1)
    also have "... = x0 * (Suc y0)" by (simp only:somaeq1)
    finally show "mult x0 (Suc y0) = x0 * (Suc y0)" by simp
  qed
qed

theorem mult2:"\<forall>x. mult x y = mult y x"
proof (induct y)
  show "\<forall>x. mult x 0 = mult 0 x"
  proof (rule allI)
    fix x0::nat
    have "mult x0 0 = 0" by (simp only:multeq1)
    also have "... = 0*x0" by simp
    also have "... = 0*x0 + 0" by simp
    also have "... = (mult 0 x0) + 0" by (simp only:mult1)
    also have "... = soma (mult 0 x0) 0" by (simp only:soma1)
    also have "... = mult 0 x0" by (simp only:somaeq1)
    finally show "mult x0 0 = mult 0 x0" by simp
  qed
next
  fix y0::nat
  assume HI: "\<forall>x. mult x y0 = mult y0 x"
  show "\<forall>x. mult x (Suc y0) = mult (Suc y0) x"
  proof (rule allI)
    fix x0::nat
    have "mult x0 (Suc y0) = soma x0 (mult x0 y0)" by (simp only:multeq2)
    also have "... = soma x0 (mult y0 x0)" by (simp only:HI)
    also have "... = soma x0 (y0 * x0)" by (simp only:mult1)
    also have "... = soma (y0 * x0) x0" by (simp only:soma2)
    also have "... = (y0 * x0) + x0" by (simp only:soma1)
    also have "... = (Suc y0) * x0 + 0" by simp
    also have "... = soma ((Suc y0) * x0) 0" by (simp only:soma1)
    also have "... = (Suc y0) * x0" by (simp only:somaeq1)
    also have "... = mult (Suc y0) x0" by (simp only:mult1)
    finally show "mult x0 (Suc y0) = mult (Suc y0) x0" by simp
  qed
qed
