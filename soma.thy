theory soma
  imports Main
begin
primrec soma::"nat \<Rightarrow> nat \<Rightarrow> nat" where
somaeq1:"soma x 0 = x"|
somaeq2:"soma x (Suc y) = Suc (soma x y)"

thm nat.induct
print_statement nat.induct

value "soma 1 0"
value "soma 1 1"

theorem soma1:"\<forall>x. soma x y = x + y"
proof (induct y)
  show "\<forall>x. soma x 0 = x + 0"
  proof (rule allI)
    fix x0::nat
    have "soma x0 0 = x0" by (simp only:somaeq1)
    also have "... = x0 + 0" by simp
    finally show "soma x0 0 = x0 + 0" by simp
  qed
next
  fix y0::nat
  assume HI:"\<forall>x. soma x y0 = x + y0"
  show "\<forall>x. soma x (Suc y0) = x + (Suc y0)"
  proof (rule allI)
    fix x0::nat
    have "soma x0 (Suc y0) = Suc (soma x0 y0)" by (simp only:somaeq2)
    also have "... = Suc (x0 + y0)" by (simp only:HI)
    also have "... = x0 + (Suc y0)" by simp
    finally show "soma x0 (Suc y0) = x0 + (Suc y0)" by simp
  qed
qed

theorem soma2:"\<forall>x. soma x y = soma y x"
proof (induct y)
  show "\<forall>x. soma x 0 = soma 0 x"
  proof (rule allI)
    fix x0::nat
    have "soma x0 0 = x0" by (simp only:somaeq1)
    also have "... = 0 + x0" by simp
    also have "... = soma 0 x0" by (simp only:soma1)
    finally show "soma x0 0 = soma 0 x0" by simp
  qed
next
  fix y0::nat
  assume HI:"\<forall>x. soma x y0 = soma y0 x"
  show "\<forall>x. soma x (Suc y0) = soma (Suc y0) x"
  proof (rule allI)
    fix x0::nat
    have "soma x0 (Suc y0) = Suc (soma x0 y0)" by (simp only:somaeq2)
    also have "... = Suc (soma y0 x0)" by (simp only:HI)
    also  have "... = soma (Suc y0) x0" by (simp only:soma1)
    finally show "soma x0 (Suc y0) = soma (Suc y0) x0" by simp
  qed
qed

theorem soma3:"\<forall>x. soma x (Suc y) = soma (Suc x) y"
proof (induct y)
  show "\<forall>x. soma x (Suc 0) = soma (Suc x) 0"
  proof (rule allI)
    fix x0::nat
    have "soma x0 (Suc 0) = Suc (soma x0 0)" by (simp only:somaeq2)
    also have "... = Suc (x0)" by (simp only:somaeq1)
    also have "... = soma (Suc x0) 0" by (simp only:soma1)
    finally show "soma x0 (Suc 0) = soma (Suc x0) 0" by simp
  qed
next
  fix y0::nat
  assume HI:"\<forall>x. soma x (Suc y0) = soma (Suc x) y0"
  show "\<forall>x. soma x (Suc (Suc y0)) = soma (Suc x) (Suc y0)"
  proof (rule allI)
    fix x0::nat
    have "soma x0 (Suc (Suc y0)) = Suc (soma x0 (Suc y0))" by (simp only:somaeq2)
    also have "... = Suc (soma (Suc x0) y0)" by (simp only:HI)
    also have "... = soma (Suc x0) (Suc y0)" by (simp only:soma1)
    finally show "soma x0 (Suc (Suc y0)) = soma (Suc x0) (Suc y0)" by simp
  qed
qed

end
