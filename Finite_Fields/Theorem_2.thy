theory Theorem_2
imports 
  "Lemma_2_3" "Formal_Differentiation" "Ring_Characteristic"
begin

lemma sum'_subtractf_nat:
  fixes f :: "'a \<Rightarrow> nat"
  assumes "finite {i \<in> A. f i \<noteq> 0}"
  assumes "finite {i \<in> A. g i \<noteq> 0}"
  assumes "\<And>i. i \<in> A \<Longrightarrow> g i \<le> f i"
  shows "sum' (\<lambda>i. f i - g i) A = sum' f A - sum' g A" (is "?lhs = ?rhs")
proof -
  let ?B = "{i \<in> A. f i \<noteq> 0 \<or> g i \<noteq> 0}"

  have b:"?B = {i \<in> A. f i \<noteq> 0} \<union> {i \<in> A. g i \<noteq> 0}"
    by (auto simp add:set_eq_iff)
  have a:"finite ?B"
    using assms(1,2) by (subst b, simp)
  have "?lhs = sum' (\<lambda>i. f i - g i) ?B"
    by (intro sum.mono_neutral_cong_right', simp_all)
  also have "... = sum (\<lambda>i. f i - g i) ?B"
    by (intro sum.eq_sum a) 
  also have "... = sum f ?B - sum g ?B"
    using assms(3) by (subst sum_subtractf_nat, auto)
  also have "... = sum' f ?B - sum' g ?B"
    by (intro arg_cong2[where f="(-)"] sum.eq_sum[symmetric] a)
  also have "... = ?rhs"
    by (intro arg_cong2[where f="(-)"] sum.mono_neutral_cong_left', simp_all)
  finally show ?thesis
    by simp
qed

lemma sum'_nat_eq_0_iff:
  fixes f :: "'a \<Rightarrow> nat"
  assumes "finite {i \<in> A. f i \<noteq> 0}"
  assumes "sum' f A = 0"
  shows "\<And>i. i \<in> A \<Longrightarrow> f i = 0"
proof -
  let ?B = "{i \<in> A. f i \<noteq> 0}"

  have "sum f ?B = sum' f ?B"
    by (intro sum.eq_sum[symmetric] assms(1))
  also have "... = sum' f A"
    by (intro sum.non_neutral')
  also have "... = 0" using assms(2) by simp
  finally have a:"sum f ?B = 0" by simp
  have "\<And>i. i \<in> ?B \<Longrightarrow> f i = 0"
    using sum_nonneg_0[OF assms(1) _ a] by blast
  thus "\<And>i. i \<in> A \<Longrightarrow> f i = 0"
    by blast
qed

lemma sum'_eq_iff:
  fixes f :: "'a \<Rightarrow> nat"
  assumes "finite {i \<in> A. f i \<noteq> 0}"
  assumes "\<And>i. i \<in> A \<Longrightarrow> f i \<ge> g i"
  assumes "sum' f A \<le> sum' g A"
  shows "\<forall>i \<in> A. f i = g i"
proof -
  have "{i \<in> A. g i \<noteq> 0} \<subseteq> {i \<in> A. f i \<noteq> 0}"
    using assms(2) order_less_le_trans
    by (intro subsetI, auto) 
  hence a:"finite {i \<in> A. g i \<noteq> 0}"
    by (rule finite_subset, intro assms(1))
  have " {i \<in> A. f i - g i \<noteq> 0} \<subseteq> {i \<in> A. f i \<noteq> 0}" 
    by (intro subsetI, simp_all)
  hence b: "finite {i \<in> A. f i - g i \<noteq> 0}" 
    by (rule finite_subset, intro assms(1))
  have "sum' (\<lambda>i. f i - g i) A = sum' f A - sum' g A"
    using assms(1,2) a by (subst sum'_subtractf_nat, auto) 
  also have "... = 0"
    using assms(3) by simp
  finally have "sum' (\<lambda>i. f i - g i) A = 0" by simp
  hence "\<And>i. i \<in> A \<Longrightarrow> f i - g i = 0"
    using sum'_nat_eq_0_iff[OF b] by simp
  thus ?thesis
    using assms(2) diff_is_0_eq' diffs0_imp_equal by blast
qed

lemma (in ring) poly_of_const_inj:
  "inj poly_of_const"
proof -
  have "coeff (poly_of_const x) 0 = x" for x 
    unfolding poly_of_const_def normalize_coeff[symmetric]
    by simp
  thus ?thesis by (metis injI)
qed

lemma (in domain) rupture_order:
  assumes "subfield K R"
  assumes "f \<in> carrier (K[X])" "degree f > 0"
  shows "order (Rupt K f) = card K^degree f"
proof -
  interpret p:principal_domain "(K[X])"
    using univ_poly_is_principal[OF assms(1)] by simp

  interpret I: ideal "PIdl\<^bsub>K[X]\<^esub> f" "K[X]"
    using p.cgenideal_ideal[OF assms(2)] by simp

  interpret d:ring "Rupt K f"
    unfolding rupture_def using I.quotient_is_ring by simp

  have e:"subring K R"
    using assms(1) subfieldE(1) by auto

  interpret h:ring_hom_ring "R \<lparr> carrier := K \<rparr>" "Rupt K f" "rupture_surj K f \<circ> poly_of_const"
    using rupture_surj_norm_is_hom[OF e assms(2)] ring_hom_ringI2 subring_is_ring d.is_ring e 
    by blast

  have "field (R \<lparr>carrier := K\<rparr>)"
    using assms(1) subfield_iff(2) by simp
  hence "subfield K (R\<lparr>carrier := K\<rparr>)" 
    using ring.subfield_iff[OF subring_is_ring[OF e]] by simp
  hence b: "subfield (rupture_surj K f ` poly_of_const ` K) (Rupt K f)"
    unfolding image_image comp_def[symmetric]
    by (intro h.img_is_subfield rupture_one_not_zero assms, simp)

  have "inj_on poly_of_const K" using poly_of_const_inj inj_on_subset by auto
  moreover have "poly_of_const ` K \<subseteq> ((\<lambda>q. q pmod f) ` carrier (K [X]))"
  proof (rule image_subsetI)
    fix x assume "x \<in> K"
    hence f:"poly_of_const x \<in> carrier (K[X])" "degree (poly_of_const x) = 0" 
      using poly_of_const_over_subfield[OF assms(1)] by auto
    moreover 
    have "degree (poly_of_const x) < degree f"
      using f(2) assms by simp
    hence "poly_of_const x pmod f = poly_of_const x"
      by (intro pmod_const(2)[OF assms(1)] f assms(2), simp)
    ultimately show "poly_of_const x \<in> ((\<lambda>q. q pmod f) ` carrier (K [X]))"
      by force
  qed  
  hence "inj_on (rupture_surj K f) (poly_of_const ` K)"
    using rupture_surj_inj_on[OF assms(1,2)] inj_on_subset by blast
  ultimately have d: "inj_on (rupture_surj K f \<circ> poly_of_const) K"
    using comp_inj_on by auto

  have a:"d.dimension (degree f) (rupture_surj K f ` poly_of_const ` K) (carrier (Rupt K f))"
    using rupture_dimension[OF assms(1-3)] by auto
  then obtain base where base_def:
    "set base \<subseteq> carrier (Rupt K f)"
    "d.independent (rupture_surj K f ` poly_of_const ` K) base"
    "length base = degree f" 
    "d.Span (rupture_surj K f ` poly_of_const ` K) base = carrier (Rupt K f)" 
    using d.exists_base[OF b a] by auto
  have "order (Rupt K f) = card (d.Span (rupture_surj K f ` poly_of_const ` K) base)"
    unfolding order_def base_def(4) by simp
  also have "... = card (rupture_surj K f ` poly_of_const ` K) ^ length base"
    using d.card_span[OF b base_def(2,1)] by simp
  also have "... = card ((rupture_surj K f \<circ> poly_of_const) ` K) ^ degree f"
    using base_def(3) image_image unfolding comp_def by metis
  also have "... = card K^degree f"
    by (subst card_image[OF d], simp)
  finally show ?thesis by simp
qed


context 
  fixes R
  assumes field_R:"field R"
  assumes fin_carr: "finite (carrier R)"
begin

private abbreviation P where "P \<equiv> poly_ring R"
private abbreviation M where "M \<equiv> mult_of (poly_ring R)"

interpretation field "R" using field_R by simp
interpretation p:principal_domain "poly_ring R"
  by (simp add: carrier_is_subfield univ_poly_is_principal)


lemma order_min:
  "order R > 1"
  using finite_field_min_order[OF fin_carr] by simp

lemma div_gauss_poly_iff:
  assumes "n > 0"
  assumes "monic_irreducible_poly R f"
  shows "f pdivides\<^bsub>R\<^esub> gauss_poly R (order R^n) \<longleftrightarrow> degree f dvd n"
proof -
  have f_carr: "f \<in> carrier P" 
    using assms(2) unfolding monic_irreducible_poly_def monic_poly_def by simp
  have f_deg: "degree f > 0" 
    using assms(2) monic_poly_min_degree[OF field_axioms] by fastforce

  define K where "K = Rupt\<^bsub>R\<^esub> (carrier R) f"
  have field_K: "field K"
    using assms(2) unfolding K_def monic_irreducible_poly_def monic_poly_def
    by (subst rupture_is_field_iff_pirreducible[OF carrier_is_subfield])  auto
  have a: "order K = order R^degree f" 
    using rupture_order[OF carrier_is_subfield] f_carr f_deg
    unfolding K_def order_def by simp
  hence "card (carrier K) > 0"
    using f_deg order_min unfolding order_def by simp
  hence d: "finite (carrier K)" using card_ge_0_finite by auto
  interpret f: field "K" using field_K by simp
  define \<phi> where "\<phi> = rupture_surj (carrier R) f"
  interpret h:ring_hom_ring "P" "K" "\<phi>"
    unfolding K_def \<phi>_def using f_carr rupture_surj_hom[OF carrier_is_subring] by simp

  interpret r:ring_hom_ring "R" "P" "poly_of_const"
    using canonical_embedding_ring_hom[OF carrier_is_subring] by simp

  interpret q:ring_hom_cring "K" "K" "\<lambda>x. x [^]\<^bsub>K\<^esub> order R^n"
    apply (intro f.frobenius_hom) sorry

  have o1: "order R^degree f > 1" sorry
  have o11: "order R^degree f > 0" sorry
  have o2: "order R^n > 1" sorry
  have o21: "order R^n > 0" sorry
  let ?g1 = "gauss_poly K (order R^degree f)"
  let ?g2 = "gauss_poly K (order R^n)"

  have c:"x [^]\<^bsub>K\<^esub> (order R^degree f) = x" if b:"x \<in> carrier K" for x
    using b d
    apply (subst a[symmetric])
    by (intro f.x_pow_n_eq_x, auto)

  have k_cycle: "\<phi> (poly_of_const x) [^]\<^bsub>K\<^esub> (order R^n) = \<phi>(poly_of_const x)" 
    if k_cycle_1: "x \<in> carrier R" for x
  proof -
    have "\<phi> (poly_of_const x) [^]\<^bsub>K\<^esub> (order R^n) = \<phi> (poly_of_const (x [^]\<^bsub>R\<^esub> (order R^n)))"
      using k_cycle_1 by (simp add: h.hom_nat_pow r.hom_nat_pow)
    also have "... = \<phi> (poly_of_const x)"
      using x_pow_n_eq_x'[OF fin_carr] k_cycle_1 by simp
    finally show ?thesis by simp
  qed
  
  have roots_g1: "pmult\<^bsub>K\<^esub> d ?g1 \<ge> 1" if z1: "degree d = 1" "monic_irreducible_poly K d" for d
  proof -
    obtain x where x_def: "x \<in> carrier K" "d = [\<one>\<^bsub>K\<^esub>, \<ominus>\<^bsub>K\<^esub> x]"
      using degree_one_monic_poly[OF field_K] z1 by auto
    interpret x:ring_hom_cring "poly_ring K" "K" "(\<lambda>p. f.eval p x)"
      by (intro f.eval_cring_hom[OF f.carrier_is_subring] x_def)
    have "ring.eval K ?g1 x = \<zero>\<^bsub>K\<^esub>"
      unfolding gauss_poly_def a_minus_def
      using f.var_closed[OF f.carrier_is_subring] f.eval_var x_def c
      by (simp, algebra)
    hence "f.is_root ?g1 x"
      using x_def gauss_poly_not_zero[OF field_K o11]
      unfolding f.is_root_def univ_poly_zero by simp
    hence "[\<one>\<^bsub>K\<^esub>, \<ominus>\<^bsub>K\<^esub> x] pdivides\<^bsub>K\<^esub> ?g1"
      using f.is_root_imp_pdivides gauss_poly_carr[OF field_K] by simp
    hence "d pdivides\<^bsub>K\<^esub> ?g1" by (simp add:x_def)
    thus "pmult\<^bsub>K\<^esub> d ?g1 \<ge> 1"
      using z1
      by (subst multiplicity_ge_1_iff_pdivides[OF field_K], simp_all)
  qed

  show ?thesis
  proof
    assume f:"f pdivides\<^bsub>R\<^esub> gauss_poly R (order R^n)"
    have "(\<phi> X\<^bsub>R\<^esub>) [^]\<^bsub>K\<^esub> (order R^n) \<ominus>\<^bsub>K\<^esub> (\<phi> X\<^bsub>R\<^esub>) = \<phi> (gauss_poly R (order R^n))"
      unfolding gauss_poly_def a_minus_def using var_closed[OF carrier_is_subring]
      by (simp add: h.hom_nat_pow)
    also have "... = \<zero>\<^bsub>K\<^esub>" 
      unfolding K_def \<phi>_def using f_carr gauss_poly_carr[OF field_axioms] f
      by (subst rupture_eq_0_iff[OF carrier_is_subfield], simp_all) 
    finally have "(\<phi> X\<^bsub>R\<^esub>) [^]\<^bsub>K\<^esub> (order R^n) \<ominus>\<^bsub>K\<^esub> (\<phi> X\<^bsub>R\<^esub>) = \<zero>\<^bsub>K\<^esub>" by simp
    hence g:"(\<phi> X\<^bsub>R\<^esub>) [^]\<^bsub>K\<^esub> (order R^n) = (\<phi> X\<^bsub>R\<^esub>)"
      using var_closed[OF carrier_is_subring] 
      by simp

    have roots_g2: "pmult\<^bsub>K\<^esub> d ?g2 \<ge> 1" if z1: "degree d = 1" "monic_irreducible_poly K d" for d
    proof -
      obtain y where y_def: "y \<in> carrier K" "d = [\<one>\<^bsub>K\<^esub>, \<ominus>\<^bsub>K\<^esub> y]"
        using degree_one_monic_poly[OF field_K] z1 by auto

      interpret x:ring_hom_cring "poly_ring K" "K" "(\<lambda>p. f.eval p y)"
        by (intro f.eval_cring_hom[OF f.carrier_is_subring] y_def)
      obtain x where x_def: "x \<in> carrier P" "y = \<phi> x"
        using y_def unfolding \<phi>_def K_def rupture_def FactRing_def A_RCOSETS_def' by auto
      let ?\<tau>  = "\<lambda>i. poly_of_const (coeff x i)"
      have test: "?\<tau> i \<in> carrier P" for i sorry
      have test_2: "coeff x i \<in> carrier R" for i sorry

      have "(\<phi> x) [^]\<^bsub>K\<^esub> (order R^n) = 
        \<phi> (\<Oplus>\<^bsub>P\<^esub>i \<in> {..<length x}. ?\<tau> i \<otimes>\<^bsub>P\<^esub> X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> i) [^]\<^bsub>K\<^esub> (order R^n)"
        by (subst split_poly_in_finsum[OF carrier_is_subring x_def(1)], simp)
      also have "... = (finsum K (\<phi> \<circ> (\<lambda>i.  ?\<tau> i \<otimes>\<^bsub>P\<^esub> X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> i)) {..<length x}) [^]\<^bsub>K\<^esub> (order R^n)"
        using var_pow_closed[OF carrier_is_subring] test
        by (subst h.hom_finsum, simp add:Pi_def, simp)
      also have "... = (\<Oplus>\<^bsub>K\<^esub>i \<in> {..<length x}. \<phi> (?\<tau> i) \<otimes>\<^bsub>K\<^esub> \<phi> (X\<^bsub>R\<^esub>) [^]\<^bsub>K\<^esub> i) [^]\<^bsub>K\<^esub> (order R^n)"
        using var_closed[OF carrier_is_subring] test
        by (simp add:comp_def h.hom_nat_pow)
      also have "... = (\<Oplus>\<^bsub>K\<^esub>i \<in> {..<length x}. \<phi> (?\<tau> i) \<otimes>\<^bsub>K\<^esub> (\<phi> (X\<^bsub>R\<^esub>) [^]\<^bsub>K\<^esub> i) [^]\<^bsub>K\<^esub> (order R^n))"
        using var_closed[OF carrier_is_subring] test test_2
        apply (subst q.hom_finsum, simp, simp add:comp_def)
        by (subst k_cycle, simp_all)
      also have "... = (\<Oplus>\<^bsub>K\<^esub>i \<in> {..<length x}. \<phi> (?\<tau> i) \<otimes>\<^bsub>K\<^esub> (\<phi> (X\<^bsub>R\<^esub>) [^]\<^bsub>K\<^esub> (order R^n)) [^]\<^bsub>K\<^esub> i)"
        using var_closed[OF carrier_is_subring] test
        by (simp add: f.nat_pow_pow mult.commute)
      also have "... = (\<Oplus>\<^bsub>K\<^esub>i \<in> {..<length x}. \<phi> (?\<tau> i) \<otimes>\<^bsub>K\<^esub> \<phi> (X\<^bsub>R\<^esub>) [^]\<^bsub>K\<^esub> i)"
        by (subst g, simp)
      also have "... = finsum K (\<phi> \<circ> (\<lambda>i.  ?\<tau> i \<otimes>\<^bsub>P\<^esub> X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> i)) {..<length x}"
        using var_closed[OF carrier_is_subring] test
        by (simp add:comp_def h.hom_nat_pow)
      also have "... = \<phi> (\<Oplus>\<^bsub>P\<^esub>i \<in> {..<length x}. ?\<tau> i \<otimes>\<^bsub>P\<^esub> X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> i)"
        using var_pow_closed[OF carrier_is_subring] test
        by (subst h.hom_finsum, simp add:Pi_def, simp)
      also have "... = \<phi> x"
        by (subst split_poly_in_finsum[OF carrier_is_subring x_def(1)], simp)
      finally have "\<phi> x [^]\<^bsub>K\<^esub> order R ^ n = \<phi> x" by simp
      
      hence "y [^]\<^bsub>K\<^esub> (order R^n) = y" using x_def by simp
      hence "ring.eval K ?g2 y = \<zero>\<^bsub>K\<^esub>"
        unfolding gauss_poly_def a_minus_def
        using f.var_closed[OF f.carrier_is_subring] f.eval_var y_def
        by (simp, algebra)
      hence "f.is_root ?g2 y"
        using y_def gauss_poly_not_zero[OF field_K o21]
        unfolding f.is_root_def univ_poly_zero by simp
      hence "d pdivides\<^bsub>K\<^esub> ?g2"
        unfolding y_def
        by (intro f.is_root_imp_pdivides gauss_poly_carr[OF field_K], simp)
      thus "pmult\<^bsub>K\<^esub> d ?g2 \<ge> 1"
        using z1
        by (subst multiplicity_ge_1_iff_pdivides[OF field_K], auto)
    qed

    have "sum' (\<lambda>d. pmult\<^bsub>K\<^esub> d ?g1 * degree d) {d. monic_irreducible_poly K d} = degree ?g1"
      using gauss_poly_monic[OF field_K] o1
      by (subst degree_monic_poly'[OF field_K], simp_all)
    also have "... = order K"
      using gauss_poly_degree[OF field_K] o1 a by simp
    also have "... = card ((\<lambda>k. [\<one>\<^bsub>K\<^esub>, \<ominus>\<^bsub>K\<^esub> k]) ` carrier K)"
      unfolding order_def 
      by (intro card_image[symmetric] inj_onI, simp_all, metis f.minus_minus) 
    also have "... = card {d. monic_irreducible_poly K d \<and> degree d = 1}"
      using degree_one_monic_poly[OF field_K]
      by (intro arg_cong[where f="card"], simp add:set_eq_iff image_iff) 
    also have "... = sum (\<lambda>d. 1) {d. monic_irreducible_poly K d \<and> degree d = 1}" 
      by simp
    also have "... = sum' (\<lambda>d. 1) {d. monic_irreducible_poly K d \<and> degree d = 1}" 
      apply (intro sum.eq_sum[symmetric]) sorry
    also have "... = sum' (\<lambda>d. of_bool (degree d = 1)) {d. monic_irreducible_poly K d}" 
      by (intro sum.mono_neutral_cong_left' subsetI, simp_all)
    also have "... \<le> sum' (\<lambda>d. of_bool (degree d = 1)) {d. monic_irreducible_poly K d}"
      by simp
    finally have 
      " sum' (\<lambda>d. pmult\<^bsub>K\<^esub> d ?g1 * degree d) {d. monic_irreducible_poly K d}
      \<le> sum' (\<lambda>d. of_bool (degree d = 1)) {d. monic_irreducible_poly K d}"
      by simp
    moreover have "pmult\<^bsub>K\<^esub> d ?g1 * degree d \<ge> of_bool (degree d = 1)" 
      if v:"monic_irreducible_poly K d" for d
    proof (cases "degree d = 1")
      case True
      then obtain x where "x \<in> carrier K" "d = [\<one>\<^bsub>K\<^esub>, \<ominus>\<^bsub>K\<^esub> x]"
        using degree_one_monic_poly[OF field_K] v by auto
      hence "pmult\<^bsub>K\<^esub> d ?g1 \<ge> 1"
        using roots_g1 v by simp
      then show ?thesis using True by simp
    next
      case False
      then show ?thesis by simp
    qed
    moreover have "finite {d. monic_irreducible_poly K d \<and> pmult\<^bsub>K\<^esub> d ?g1 * degree d > 0}"
      sorry
    ultimately have v2:"\<forall>d \<in> {d. monic_irreducible_poly K d}. pmult\<^bsub>K\<^esub> d ?g1 * degree d = 
      of_bool (degree d = 1)" 
      by (intro sum'_eq_iff, simp_all add:not_le)
    have "pmult\<^bsub>K\<^esub> d ?g1 \<le> pmult\<^bsub>K\<^esub> d ?g2" if v1: "monic_irreducible_poly K d" for d
    proof (cases "degree d = 1")
      case True
      hence "pmult\<^bsub>K\<^esub> d ?g1 = 1" using v2 v1 by simp
      also have "... \<le> pmult\<^bsub>K\<^esub> d ?g2" 
        by (intro roots_g2 True v1)
      finally show ?thesis by simp
    next
      case False
      hence "degree d > 1" using monic_poly_min_degree[OF field_K v1] by simp
      hence "pmult\<^bsub>K\<^esub> d ?g1 = 0" using v2 v1 by auto
      then show ?thesis by simp
    qed
    hence "?g1 pdivides\<^bsub>K\<^esub> ?g2"
      using o1 o2 divides_monic_poly[OF field_K] gauss_poly_monic[OF field_K] by simp
    thus "degree f dvd n"
      by (subst (asm) div_gauss_poly_iff_1[OF field_K assms(1)], simp) 
  next
    have d:"\<phi> X\<^bsub>R\<^esub> \<in> carrier K"
      by (intro h.hom_closed var_closed[OF carrier_is_subring])

    have "\<phi> (gauss_poly R (order R^degree f)) = (\<phi> X\<^bsub>R\<^esub>) [^]\<^bsub>K\<^esub> (order R^degree f) \<ominus>\<^bsub>K\<^esub> (\<phi> X\<^bsub>R\<^esub>)"
      unfolding gauss_poly_def a_minus_def using var_closed[OF carrier_is_subring]
      by (simp add: h.hom_nat_pow)
    also have "... = \<zero>\<^bsub>K\<^esub>"
      using c d by simp
    finally have "\<phi> (gauss_poly R (order R^degree f)) = \<zero>\<^bsub>K\<^esub>" by simp
    hence "f pdivides\<^bsub>R\<^esub> gauss_poly R (order R^degree f)"
      unfolding K_def \<phi>_def using f_carr gauss_poly_carr[OF field_axioms]
      by (subst (asm) rupture_eq_0_iff[OF carrier_is_subfield], simp_all) 
    moreover assume "degree f dvd n"
    
    hence "gauss_poly R (order R^degree f) pdivides\<^bsub>R\<^esub> (gauss_poly R (order R^n))"
      using div_gauss_poly_iff_1[OF field_axioms assms(1)] by simp
    ultimately show "f pdivides\<^bsub>R\<^esub> gauss_poly R (order R^n)"
      using f_carr a p.divides_trans unfolding pdivides_def by blast
  qed
qed

lemma multiplicity_of_factor_of_gauss_poly:
  assumes "n > 0"
  assumes "monic_irreducible_poly R f"
  shows "pmult\<^bsub>R\<^esub> f (gauss_poly R (order R^n)) = of_bool (degree f dvd n)"
proof (cases "degree f dvd n")
  case True
  let ?g = "gauss_poly R (order R^n)"
  have f_carr: "f \<in> carrier P" "f \<noteq> []"
    using assms(2) unfolding monic_irreducible_poly_def monic_poly_def
    by auto

  have o21: "order R^n > 0" 
    using finite_field_min_order assms fin_carr by simp

  obtain d :: nat where order_dim: "order R = char R ^ d" "d > 0"
    using finite_field_order[OF fin_carr] by blast
  have "d * n > 0" using order_dim assms by simp
  hence char_dvd_order: "int (char R) dvd int (order R ^ n)"
    unfolding order_dim using finite_carr_imp_char_ge_0[OF fin_carr]
    by (simp add:power_mult[symmetric])

  interpret h: ring_hom_ring  "R" "P" "poly_of_const"
    using canonical_embedding_ring_hom[OF carrier_is_subring] by simp

  have "f pdivides\<^bsub>R\<^esub> ?g"
    using True div_gauss_poly_iff[OF assms] by simp
  hence "pmult\<^bsub>R\<^esub> f ?g \<ge> 1"
    using multiplicity_ge_1_iff_pdivides[OF field_axioms assms(2)] by auto
  moreover have "pmult\<^bsub>R\<^esub> f ?g < 2"
  proof (rule ccontr)
    assume "\<not> pmult\<^bsub>R\<^esub> f ?g < 2"
    hence "pmult\<^bsub>R\<^esub> f ?g \<ge> 2" by simp
    hence "(f [^]\<^bsub>P\<^esub> (2::nat)) pdivides\<^bsub>R\<^esub> ?g"
      by (subst (asm) multiplicity_ge_iff[OF field_axioms assms(2), where k="2"], simp) 
    hence "(f [^]\<^bsub>P\<^esub> (2::nat)) divides\<^bsub>mult_of P\<^esub> ?g"
      unfolding pdivides_def 
      using f_carr gauss_poly_not_zero[OF field_axioms] o21 gauss_poly_carr[OF field_axioms]
      by (intro p.divides_imp_divides_mult) simp_all
    then obtain h where h_def: "h \<in> carrier (mult_of P)" "?g = f [^]\<^bsub>P\<^esub> (2::nat) \<otimes>\<^bsub>P\<^esub> h"
      using dividesD by auto
    have "\<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub> = int_embed P (order R ^ n) \<otimes>\<^bsub>P\<^esub> (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> (order R ^ n-1)) \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>"
      using var_closed[OF carrier_is_subring]
      apply (subst int_embed_consistent_with_poly_of_const[OF carrier_is_subring])
      by(subst iffD2[OF embed_char_eq_0_iff char_dvd_order], simp add:a_minus_def)
    also have "... = pderiv\<^bsub>R\<^esub> (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> order R ^ n) \<ominus>\<^bsub>P\<^esub> pderiv\<^bsub>R\<^esub> X\<^bsub>R\<^esub>"
      using pderiv_var
      by (subst pderiv_var_pow[OF o21 carrier_is_subring], simp)
    also have "... = pderiv\<^bsub>R\<^esub> ?g" 
      unfolding gauss_poly_def a_minus_def using var_closed[OF carrier_is_subring]
      by (subst pderiv_add[OF carrier_is_subring], simp_all add:pderiv_inv[OF carrier_is_subring])
    also have "... = pderiv\<^bsub>R\<^esub> (f [^]\<^bsub>P\<^esub> (2::nat) \<otimes>\<^bsub>P\<^esub> h)"
      using h_def(2) by simp
    also have "... = pderiv\<^bsub>R\<^esub> (f [^]\<^bsub>P\<^esub> (2::nat)) \<otimes>\<^bsub>P\<^esub> h \<oplus>\<^bsub>P\<^esub> (f [^]\<^bsub>P\<^esub> (2::nat)) \<otimes>\<^bsub>P\<^esub> pderiv\<^bsub>R\<^esub> h"
      using f_carr h_def
      by (intro pderiv_mult[OF carrier_is_subring], simp_all)
    also have "... = int_embed P 2 \<otimes>\<^bsub>P\<^esub> f  \<otimes>\<^bsub>P\<^esub> pderiv\<^bsub>R\<^esub> f \<otimes>\<^bsub>P\<^esub> h \<oplus>\<^bsub>P\<^esub> f \<otimes>\<^bsub>P\<^esub> f \<otimes>\<^bsub>P\<^esub> pderiv\<^bsub>R\<^esub> h"
      using f_carr
      by (subst pderiv_pow[OF _ carrier_is_subring], simp_all add:numeral_eq_Suc)
    also have "... = f \<otimes>\<^bsub>P\<^esub> (int_embed P 2 \<otimes>\<^bsub>P\<^esub> pderiv\<^bsub>R\<^esub> f \<otimes>\<^bsub>P\<^esub> h) \<oplus>\<^bsub>P\<^esub> f \<otimes>\<^bsub>P\<^esub> (f \<otimes>\<^bsub>P\<^esub> pderiv\<^bsub>R\<^esub> h)"
      using f_carr pderiv_carr[OF carrier_is_subring] h_def poly_of_const_carr p.int_embed_closed
      apply (intro arg_cong2[where f="(\<oplus>\<^bsub>P\<^esub>)"]) 
      by (subst p.m_comm, simp_all add:p.m_assoc)
    also have "... = f \<otimes>\<^bsub>P\<^esub> (int_embed P 2 \<otimes>\<^bsub>P\<^esub> pderiv\<^bsub>R\<^esub> f \<otimes>\<^bsub>P\<^esub> h \<oplus>\<^bsub>P\<^esub> f \<otimes>\<^bsub>P\<^esub> pderiv\<^bsub>R\<^esub> h)"
      using f_carr pderiv_carr[OF carrier_is_subring] h_def poly_of_const_carr p.int_embed_closed
      by (subst p.r_distr, simp_all)
    finally have "\<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub> = f \<otimes>\<^bsub>P\<^esub> (int_embed P 2 \<otimes>\<^bsub>P\<^esub> pderiv\<^bsub>R\<^esub> f \<otimes>\<^bsub>P\<^esub> h \<oplus>\<^bsub>P\<^esub> f \<otimes>\<^bsub>P\<^esub> pderiv\<^bsub>R\<^esub> h)" 
      (is "_ = f \<otimes>\<^bsub>P\<^esub> ?q")
      by simp

    hence "f pdivides\<^bsub>R\<^esub> \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>"
      unfolding factor_def pdivides_def using f_carr pderiv_carr[OF carrier_is_subring] 
        h_def poly_of_const_carr p.int_embed_closed
      by auto
    moreover have "\<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub> \<noteq> \<zero>\<^bsub>P\<^esub>" by simp
    ultimately have  "degree f \<le> degree (\<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>)"
      using f_carr 
      by (intro pdivides_imp_degree_le[OF carrier_is_subring], simp_all add:univ_poly_zero)
    also have "... = 0"
      by (subst univ_poly_a_inv_degree[OF carrier_is_subring], simp)
       (simp add:univ_poly_one)
    finally have "degree f = 0" by simp
       
    then show "False" 
      using pirreducible_degree[OF carrier_is_subfield] assms(2)
      unfolding monic_irreducible_poly_def monic_poly_def 
      by fastforce
  qed
  ultimately have "pmult\<^bsub>R\<^esub> f ?g = 1" by simp
  then show ?thesis using True by simp
next
  case False
  hence "\<not>(f pdivides\<^bsub>R\<^esub> gauss_poly R (order R^n))"
    using div_gauss_poly_iff[OF assms] by simp
  hence "pmult\<^bsub>R\<^esub> f (gauss_poly R (order R^n)) = 0"
    using multiplicity_ge_1_iff_pdivides[OF field_axioms assms(2)] 
    by (meson leI less_one)
  then show ?thesis using False by simp
qed

lemma corrolary_1:
  assumes "n > 0"
  shows "order R^n = (\<Sum>d | d dvd n. d * card {f. monic_irreducible_poly R f \<and> degree f = d})"
  (is "?lhs = ?rhs")
proof -
  let ?G = "{f. monic_irreducible_poly R f \<and> degree f dvd n}"
  
  let ?D = "{f. monic_irreducible_poly R f}"
  have a: "finite {d. d dvd n}" using finite_divisors_nat assms by simp
  have b: "finite {f. monic_irreducible_poly R f \<and> degree f = k}" for k
  proof -
    have "{f. monic_irreducible_poly R f \<and> degree f = k} \<subseteq> {f. f \<in> carrier P \<and> degree f \<le> k}"
      unfolding monic_irreducible_poly_def monic_poly_def by auto
    moreover have "finite {f. f \<in> carrier P \<and> degree f \<le> k}" sorry
    ultimately show ?thesis using finite_subset by simp
  qed

  have G_split: "?G = \<Union> {{f.  monic_irreducible_poly R f \<and> degree f = d} | d. d dvd n}"
    by auto
  have c: "finite ?G"
    using a b by (subst G_split, auto) 
  have d: "order R^n > 1" 
    using assms order_min one_less_power unfolding order_def by blast

  have "?lhs = degree (gauss_poly R (order R^n))"
    using d
    by (subst gauss_poly_degree[OF field_axioms], simp_all)
  also have "... = sum' (\<lambda>d. pmult\<^bsub>R\<^esub> d (gauss_poly R (order R^n)) * degree d) ?D"
    using d
    by (intro degree_monic_poly'[OF field_axioms, symmetric] gauss_poly_monic[OF field_axioms]) 
  also have "... = sum' (\<lambda>d. of_bool (degree d dvd n) * degree d) ?D"
    using multiplicity_of_factor_of_gauss_poly[OF assms]
    by (intro sum.cong', auto)
  also have "... = sum' (\<lambda>d. degree d) ?G"
    by (intro sum.mono_neutral_cong_right' subsetI, auto)
  also have "... = (\<Sum> d \<in> ?G. degree d)"
    using c by (intro sum.eq_sum, simp) 
  also have "... = 
    (\<Sum> f \<in> (\<Union> d \<in> {d. d dvd n}. {f. monic_irreducible_poly R f \<and> degree f = d}). degree f)"
    by (intro sum.cong, auto simp add:set_eq_iff)
  also have "... = (\<Sum>d | d dvd n. sum degree {f. monic_irreducible_poly R f \<and> degree f = d})"
    using a b by (subst sum.UNION_disjoint, auto simp add:set_eq_iff)
  also have "... = (\<Sum>d | d dvd n. sum (\<lambda>_. d) {f. monic_irreducible_poly R f \<and> degree f = d})"
    by (intro sum.cong, simp_all)
  also have "... = ?rhs"
    by (simp add:mult.commute)
  finally show ?thesis
    by simp
qed

end
end
