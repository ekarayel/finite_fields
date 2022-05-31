theory SimpleFields
  imports "HOL-Algebra.Ring_Divisibility" "HOL-Algebra.IntRing" "HOL-Computational_Algebra.Factorial_Ring"
begin

locale finite_field = field +
  assumes finite_carrier: "finite (carrier R)"
begin

lemma finite_field_min_order:
  "order R > 1"
proof (rule ccontr)
  assume a:"\<not>(1 < order R)"
  have "{\<zero>\<^bsub>R\<^esub>,\<one>\<^bsub>R\<^esub>} \<subseteq> carrier R" by auto
  hence "card {\<zero>\<^bsub>R\<^esub>,\<one>\<^bsub>R\<^esub>} \<le> card (carrier R)"
    using card_mono finite_carrier by blast
  also have "... \<le> 1" using a by (simp add:order_def)
  finally have "card {\<zero>\<^bsub>R\<^esub>,\<one>\<^bsub>R\<^esub>} \<le> 1" by blast
  thus "False" by simp
qed

end

lemma finite_fieldI:
  assumes "field R"
  assumes "finite (carrier R)"
  shows "finite_field R"
  using assms unfolding finite_field_def finite_field_axioms_def by auto

lemma (in domain) finite_domain_units:
  assumes "finite (carrier R)"
  shows "Units R = carrier R - {\<zero>}" (is "?lhs = ?rhs")
proof 
  have "Units R \<subseteq> carrier R" by (simp add:Units_def) 
  moreover have "\<zero> \<notin> Units R"
    by (meson zero_is_prime(1) primeE)
  ultimately show "Units R \<subseteq> carrier R - {\<zero>}" by blast
next
  have "x \<in> Units R" if a: "x \<in> carrier R - {\<zero>}" for x
  proof -
    have x_carr: "x \<in> carrier R" using a by blast
    define f where "f = (\<lambda>y. y \<otimes>\<^bsub>R\<^esub> x)"
    have "inj_on f (carrier R)" unfolding f_def
      by (rule inj_onI, metis DiffD1 DiffD2 a m_rcancel insertI1)
    hence "card (carrier R) = card (f ` carrier R)"
      by (metis card_image)
    moreover have "f ` carrier R \<subseteq> carrier R" unfolding f_def
      by (rule image_subsetI, simp add: ring.ring_simprules x_carr)
    ultimately have "f ` carrier R = carrier R"
      using card_subset_eq assms by metis
    moreover have "\<one>\<^bsub>R\<^esub> \<in> carrier R" by simp
    ultimately have "\<exists>y \<in> carrier R. f y = \<one>\<^bsub>R\<^esub>" 
      by (metis image_iff)
    then obtain y where y_carrier: "y \<in> carrier R" and y_left_inv: "y \<otimes>\<^bsub>R\<^esub> x = \<one>\<^bsub>R\<^esub>" 
      using f_def by blast
    hence  y_right_inv: "x \<otimes>\<^bsub>R\<^esub> y = \<one>\<^bsub>R\<^esub>"
      by (metis DiffD1 a cring_simprules(14))
    show "x \<in> Units R" using y_carrier y_left_inv y_right_inv
      by (metis DiffD1 a divides_one factor_def)
  qed
  thus "?rhs \<subseteq> ?lhs" by auto
qed

lemma finite_domains_are_fields:
  assumes "domain R"
  assumes "finite (carrier R)"
  shows "finite_field R"
proof -
  interpret domain R using assms by auto
  have "Units R = carrier R - {\<zero>\<^bsub>R\<^esub>}" using finite_domain_units[OF assms(2)] by simp
  then have "field R" by (simp add: assms(1) field.intro field_axioms.intro)
  thus ?thesis  using assms(2) finite_fieldI by auto 
qed

lemma 
  assumes "p > 0"
  shows card_zfact_carr: "card (carrier (ZFact (int p))) = p"
    and fin_zfact: "finite (carrier (ZFact (int p)))"
  sorry

lemma zfact_prime_is_finite_field:
  assumes "Factorial_Ring.prime p"
  shows "finite_field (ZFact (int p))"
proof -
  have p_gt_0: "p > 0" using assms(1) prime_gt_0_nat by simp
  have "Factorial_Ring.prime (int p)" 
    using assms by simp
  moreover have "finite (carrier (ZFact (int p)))" 
    using fin_zfact[OF p_gt_0] by simp
  ultimately show ?thesis
    by (intro finite_domains_are_fields ZFact_prime_is_domain, auto)
qed

end