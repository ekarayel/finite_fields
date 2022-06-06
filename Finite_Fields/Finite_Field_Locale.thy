theory Finite_Field_Locale
  imports 
    "Finite_Fields_Preliminary_Results"
    "HOL-Algebra.IntRing" 
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

lemma (in finite_field) order_pow_eq_self:
  assumes "x \<in> carrier R"
  shows "x [^] (order R) = x"
proof (cases "x = \<zero>")
  case True
  have "order R > 0"
    using assms(1) order_gt_0_iff_finite finite_carrier by simp
  then obtain n where n_def:"order R = Suc n" 
    using lessE by blast
  have "x [^] (order R) = \<zero>" 
    unfolding n_def using True by (subst nat_pow_Suc, simp)
  thus ?thesis using True by simp
next
  case False
  have x_carr:"x \<in> carrier (mult_of R)"
    using False assms by simp

  have carr_non_empty: "card (carrier R) > 0" 
    using order_gt_0_iff_finite finite_carrier unfolding order_def by simp
  have "x [^] (order R) = x [^]\<^bsub>mult_of R\<^esub> (order R)"
    by (simp add:nat_pow_mult_of)
  also have "... = x [^]\<^bsub>mult_of R\<^esub> (order (mult_of R)+1)"
    using carr_non_empty unfolding order_def
    by (intro arg_cong[where f="\<lambda>t. x [^]\<^bsub>mult_of R\<^esub> t"]) (simp)
  also have "... = x"
    using x_carr
    by (simp add:mult_of.pow_order_eq_1)
  finally show "x [^] (order R) = x"
    by simp
qed

lemma (in finite_field) order_pow_eq_self':
  assumes "x \<in> carrier R"
  shows "x [^] (order R ^ d) = x"
proof (induction d)
  case 0
  then show ?case using assms by simp
next
  case (Suc d)
  have "x [^] order R ^ (Suc d) = x [^] (order R ^ d * order R)"
    by (simp add:mult.commute)
  also have "... = (x [^] (order R ^ d)) [^] order R"
    using assms by (simp add: nat_pow_pow)
  also have "... = (x [^] (order R ^ d))"
    using order_pow_eq_self assms by simp
  also have "... = x"
    using Suc by simp
  finally show ?case by simp
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

definition zfact_iso :: "nat \<Rightarrow> nat \<Rightarrow> int set" where
  "zfact_iso p k = Idl\<^bsub>\<Z>\<^esub> {int p} +>\<^bsub>\<Z>\<^esub> (int k)"

context
  fixes n :: nat
  assumes n_gt_0: "n > 0"
begin

private abbreviation I where "I \<equiv> Idl\<^bsub>\<Z>\<^esub> {int n}"

private lemma ideal_I: "ideal I \<Z>"
  by (simp add: int.genideal_ideal)

lemma int_cosetI:
  assumes "u mod (int n) = v mod (int n)"
  shows "Idl\<^bsub>\<Z>\<^esub> {int n} +>\<^bsub>\<Z>\<^esub> u = Idl\<^bsub>\<Z>\<^esub> {int n} +>\<^bsub>\<Z>\<^esub> v"
proof -
  have "u - v \<in> I"
    by (metis Idl_subset_eq_dvd assms int_Idl_subset_ideal mod_eq_dvd_iff)
  thus ?thesis
    using ideal_I int.quotient_eq_iff_same_a_r_cos by simp
qed

lemma zfact_iso_inj:
  "inj_on (zfact_iso n) {..<n}"
proof (rule inj_onI)
  fix x y
  assume a:"x \<in> {..<n}" "y \<in> {..<n}"
  assume "zfact_iso n x = zfact_iso n y"
  hence "I +>\<^bsub>\<Z>\<^esub> (int x) = I +>\<^bsub>\<Z>\<^esub> (int y)"
    by (simp add:zfact_iso_def)
  hence "int x - int y \<in> I"
    by (subst int.quotient_eq_iff_same_a_r_cos[OF ideal_I], auto)
  hence "int x mod int n = int y mod int n"
    by (meson Idl_subset_eq_dvd int_Idl_subset_ideal mod_eq_dvd_iff)
  thus "x = y"
    using a by simp
qed

lemma zfact_iso_ran:
  "zfact_iso n ` {..<n} = carrier (ZFact (int n))"
proof -
  have "zfact_iso n ` {..<n} \<subseteq> carrier (ZFact (int n))"
    unfolding zfact_iso_def ZFact_def FactRing_simps 
    using int.a_rcosetsI by auto
  moreover have "\<And>x. x \<in> carrier (ZFact (int n)) \<Longrightarrow> x \<in> zfact_iso n ` {..<n}"
  proof -
    fix x
    assume "x \<in> carrier (ZFact (int n))"
    then obtain y where y_def: "x = I  +>\<^bsub>\<Z>\<^esub> y"
      unfolding ZFact_def FactRing_simps by auto
    obtain z where z_def: "(int z) mod (int n) = y mod (int n)" "z < n"
      by (metis Euclidean_Division.pos_mod_sign mod_mod_trivial n_gt_0 nonneg_int_cases
          of_nat_0_less_iff of_nat_mod unique_euclidean_semiring_numeral_class.pos_mod_bound)
    have "x = I  +>\<^bsub>\<Z>\<^esub> y"
      by (simp add:y_def)
    also have "... = I +>\<^bsub>\<Z>\<^esub> (int z)"
      by (intro int_cosetI, simp add:z_def)
    also have "... = zfact_iso n z"
      by (simp add:zfact_iso_def)
    finally have "x = zfact_iso n z"
      by simp
    thus "x \<in> zfact_iso n ` {..<n}"
      using z_def(2) by blast
  qed
  ultimately show ?thesis by auto
qed

lemma zfact_iso_bij:
  "bij_betw (zfact_iso n) {..<n} (carrier (ZFact (int n)))"
  using  bij_betw_def zfact_iso_inj zfact_iso_ran by blast

lemma card_zfact_carr: "card (carrier (ZFact (int n))) = n"
  using bij_betw_same_card[OF zfact_iso_bij] by simp

lemma fin_zfact: "finite (carrier (ZFact (int n)))"
  using card_zfact_carr n_gt_0 card_ge_0_finite by force

end

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
