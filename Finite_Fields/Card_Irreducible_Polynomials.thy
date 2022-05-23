theory Card_Irreducible_Polynomials
  imports "Dirichlet_Series.Moebius_Mu" "Theorem_2"
begin

theorem (in field)
  assumes "n > 0"
  assumes "finite (carrier R)"
  shows "n * card ({f. monic_irreducible_poly R f \<and> degree f = n}) = 
    (\<Sum>d | d dvd n. moebius_mu d * (card (carrier R)^(n div d)))" (is "?lhs = ?rhs")
proof -
  have "?lhs = dirichlet_prod moebius_mu (\<lambda>x. int (card (carrier R) ^ x)) n"
    using corrolary_1[OF field_axioms assms(2)] unfolding Coset.order_def
    by (intro moebius_inversion assms, simp)
  also have "... = ?rhs"
    by (simp add:dirichlet_prod_def)
  finally show ?thesis by simp
qed

end
