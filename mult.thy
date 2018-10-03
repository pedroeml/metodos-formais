theory mult
  imports Main soma
begin
primrec mult::"nat \<Rightarrow> nat \<Rightarrow> nat" where
multeq1:"mult x 0 = 0"|
multeq2:"mult x (Suc y) = soma x (mult x y)"

value "mult 1 0"
value "mult 1 1"
value "mult 1 2"
value "mult 2 2"

theorem mult1:"mult x y = x * y"
proof (induct y)
  show "mult x 0 = x * 0"
  proof -
    have "mult x 0 = 0" by (simp only:multeq1)
    also have "... = x * 0" by simp
    finally show "mult x 0 = x * 0" by simp
  qed
next
  fix y::nat
  assume HI:"mult x y = x * y"
  show "mult x (Suc y) = x * (Suc y)"
  proof -
    have "mult x (Suc y) = soma x (mult x y)" by (simp only:multeq2)
    also have "... = soma (mult x y) x" by (simp only:soma2)
    also have "... = soma (x*y) x" by (simp only:HI)
    also have "... = mult "
  qed
qed
