theory soma
  imports Main
begin
primrec soma::"nat \<Rightarrow> nat \<Rightarrow> nat" where
somaeq1:"soma x 0 = x"|
somaeq2:"soma x (Suc y) = Suc (soma x y)"

value "soma 1 0"
value "soma 1 1"

theorem soma1:"soma x y = x + y"
proof (induct y)
  show "soma x 0 = x + 0"
  proof -
    have "soma x 0 = x" by (simp only:somaeq1)
    also have "... = x + 0" by simp
    finally show "soma x 0 = x + 0" by simp
  qed
next
  fix y::nat
  assume HI:"soma x y = x + y"
  show "soma x (Suc y) = x + (Suc y)"
  proof - 
    have "soma x (Suc y) = Suc (soma x y)" by (simp only:somaeq2)
    also have "... = Suc (x + y)" by (simp only:HI)
    finally show "soma x (Suc y) = x + (Suc y)" by simp
  qed
qed

theorem soma2:"soma x y = soma y x"
proof (induct y)
  show "soma x 0 = soma 0 x"
  proof - 
    have "soma x 0 = x" by (simp only:somaeq1)
    also have "... = 0 + x" by simp
    also have "... = soma 0 x" by (simp only:soma1)
    finally show "soma x 0 = soma 0 x" by simp
  qed
next
  fix y::nat
  assume HI:"soma x y = soma y x"
  show "soma x (Suc y) = soma (Suc y) x"
  proof -
    have "soma x (Suc y) = Suc (soma x y)" by (simp only:somaeq2)
    also have "... = Suc (soma y x)" by (simp only:HI)
    also  have "... = soma (Suc y) x" by (simp only:soma1)
    finally show "soma x (Suc y) = soma (Suc y) x" by simp
  qed
qed

theorem soma3:"soma x (Suc y) = soma (Suc x) y"
proof (induct y)
  show "soma x (Suc 0) = soma (Suc x) 0"
  proof -
    have "soma x (Suc 0) = Suc (soma x 0)" by (simp only:somaeq2)
    also have "... = Suc (x)" by (simp only:somaeq1)
    also have "... = soma (Suc x) 0" by (simp only:soma1)
    finally show "soma x (Suc 0) = soma (Suc x) 0" by simp
  qed
next
  fix y::nat
  assume HI:"soma x (Suc y) = soma (Suc x) y"
  show "soma x (Suc (Suc y)) = soma (Suc x) (Suc y)"
  proof -
    have "soma x (Suc (Suc y)) = Suc (soma x (Suc y))" by (simp only:somaeq2)
    also have "... = Suc (soma (Suc x) y)" by (simp only:HI)
    also have "... = soma (Suc x) (Suc y)" by (simp only:soma1)
    finally show "soma x (Suc (Suc y)) = soma (Suc x) (Suc y)" by simp
  qed
qed

end
