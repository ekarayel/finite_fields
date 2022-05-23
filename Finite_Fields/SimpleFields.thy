theory SimpleFields
  imports "HOL-Algebra.Ring_Divisibility"
begin

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
  shows "field R"
proof -
  interpret domain R using assms by auto
  have "Units R = carrier R - {\<zero>\<^bsub>R\<^esub>}" using finite_domain_units[OF assms(2)] by simp
  then show "field R" by (simp add: assms(1) field.intro field_axioms.intro)
qed

end