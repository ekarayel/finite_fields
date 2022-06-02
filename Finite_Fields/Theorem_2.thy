theory Theorem_2
imports 
  "Lemma_2_3" "Formal_Differentiation" "Ring_Characteristic" "Finite_Fields_Preliminary_Results"
begin

lemma (in domain)
  assumes "subfield K R"
  assumes "f \<in> carrier (K[X])" "degree f > 0"
  shows rupture_order: "order (Rupt K f) = card K^degree f"
    and rupture_char: "char (Rupt K f) = char R"
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
  finally show "order (Rupt K f) = card K^degree f" by simp

  have "char (Rupt K f) = char (R \<lparr> carrier := K \<rparr>)"
    using h.char_consistent d by simp
  also have "... = char R"
    using char_consistent[OF subfieldE(1)[OF assms(1)]] by simp
  finally show "char (Rupt K f) = char R" by simp

qed



context finite_field 
begin

interpretation polynomial_notation "R"
  by unfold_locales simp

interpretation p:principal_domain "poly_ring R"
  by (simp add: carrier_is_subfield univ_poly_is_principal)

lemma order_min:
  "order R > 1"
  using finite_field_min_order by simp

lemma div_gauss_poly_iff:
  assumes "n > 0"
  assumes "monic_irreducible_poly R f"
  shows "f pdivides\<^bsub>R\<^esub> gauss_poly R (order R^n) \<longleftrightarrow> degree f dvd n"
proof -
  have f_carr: "f \<in> carrier P" 
    using assms(2) unfolding monic_irreducible_poly_def monic_poly_def by simp
  have f_deg: "degree f > 0" 
    using assms(2) monic_poly_min_degree by fastforce

  define K where "K = Rupt\<^bsub>R\<^esub> (carrier R) f"
  have field_K: "field K"
    using assms(2) unfolding K_def monic_irreducible_poly_def monic_poly_def
    by (subst rupture_is_field_iff_pirreducible[OF carrier_is_subfield])  auto
  have a: "order K = order R^degree f" 
    using rupture_order[OF carrier_is_subfield] f_carr f_deg
    unfolding K_def order_def by simp
  have char_K: "char K = char R" 
    using rupture_char[OF carrier_is_subfield] f_carr f_deg
    unfolding K_def order_def by simp
  have "card (carrier K) > 0"
    using a f_deg order_min unfolding order_def by simp
  hence d: "finite (carrier K)" using card_ge_0_finite by auto
  interpret f: finite_field "K" using field_K d by (intro finite_fieldI, simp_all)
  define \<phi> where "\<phi> = rupture_surj (carrier R) f"
  interpret h:ring_hom_ring "P" "K" "\<phi>"
    unfolding K_def \<phi>_def using f_carr rupture_surj_hom[OF carrier_is_subring] by simp

  interpret r:ring_hom_ring "R" "P" "poly_of_const"
    using canonical_embedding_ring_hom[OF carrier_is_subring] by simp

  obtain rn where "order R = char K^rn" "rn > 0"
    unfolding char_K using finite_field_order by auto
  hence ord_rn: "order R ^n = char K^(rn * n)" using assms(1) 
    by (simp add: power_mult)

  interpret q:ring_hom_cring "K" "K" "\<lambda>x. x [^]\<^bsub>K\<^esub> order R^n"
    using ord_rn
    by (intro f.frobenius_hom f.finite_carr_imp_char_ge_0 d, simp) 

  have o1: "order R^degree f > 1" using f_deg order_min one_less_power by blast
  hence o11: "order R^degree f > 0" by linarith
  have o2: "order R^n > 1" using assms(1) order_min one_less_power by blast
  hence o21: "order R^n > 0" by linarith
  let ?g1 = "gauss_poly K (order R^degree f)"
  let ?g2 = "gauss_poly K (order R^n)"

  have g1_monic: "monic_poly K ?g1" using f.gauss_poly_monic[OF o1] by simp

  have c:"x [^]\<^bsub>K\<^esub> (order R^degree f) = x" if b:"x \<in> carrier K" for x
    using b d
    apply (subst a[symmetric])
    using x_pow_n_eq_x
    by (intro f.x_pow_n_eq_x, auto)

  have k_cycle: "\<phi> (poly_of_const x) [^]\<^bsub>K\<^esub> (order R^n) = \<phi>(poly_of_const x)" 
    if k_cycle_1: "x \<in> carrier R" for x
  proof -
    have "\<phi> (poly_of_const x) [^]\<^bsub>K\<^esub> (order R^n) = \<phi> (poly_of_const (x [^]\<^bsub>R\<^esub> (order R^n)))"
      using k_cycle_1 by (simp add: h.hom_nat_pow r.hom_nat_pow)
    also have "... = \<phi> (poly_of_const x)"
      using x_pow_n_eq_x' k_cycle_1 by simp
    finally show ?thesis by simp
  qed
  
  have roots_g1: "pmult\<^bsub>K\<^esub> d ?g1 \<ge> 1" if z1: "degree d = 1" "monic_irreducible_poly K d" for d
  proof -
    obtain x where x_def: "x \<in> carrier K" "d = [\<one>\<^bsub>K\<^esub>, \<ominus>\<^bsub>K\<^esub> x]"
      using f.degree_one_monic_poly z1 by auto
    interpret x:ring_hom_cring "poly_ring K" "K" "(\<lambda>p. f.eval p x)"
      by (intro f.eval_cring_hom[OF f.carrier_is_subring] x_def)
    have "ring.eval K ?g1 x = \<zero>\<^bsub>K\<^esub>"
      unfolding gauss_poly_def a_minus_def
      using f.var_closed[OF f.carrier_is_subring] f.eval_var x_def c
      by (simp, algebra)
    hence "f.is_root ?g1 x"
      using x_def f.gauss_poly_not_zero[OF o1]
      unfolding f.is_root_def univ_poly_zero by simp
    hence "[\<one>\<^bsub>K\<^esub>, \<ominus>\<^bsub>K\<^esub> x] pdivides\<^bsub>K\<^esub> ?g1"
      using f.is_root_imp_pdivides f.gauss_poly_carr by simp
    hence "d pdivides\<^bsub>K\<^esub> ?g1" by (simp add:x_def)
    thus "pmult\<^bsub>K\<^esub> d ?g1 \<ge> 1"
      using z1 f.gauss_poly_not_zero f.gauss_poly_carr o1
      by (subst f.multiplicity_ge_1_iff_pdivides, simp_all)
  qed

  show ?thesis
  proof
    assume f:"f pdivides\<^bsub>R\<^esub> gauss_poly R (order R^n)"
    have "(\<phi> X\<^bsub>R\<^esub>) [^]\<^bsub>K\<^esub> (order R^n) \<ominus>\<^bsub>K\<^esub> (\<phi> X\<^bsub>R\<^esub>) = \<phi> (gauss_poly R (order R^n))"
      unfolding gauss_poly_def a_minus_def using var_closed[OF carrier_is_subring]
      by (simp add: h.hom_nat_pow)
    also have "... = \<zero>\<^bsub>K\<^esub>" 
      unfolding K_def \<phi>_def using f_carr gauss_poly_carr f
      by (subst rupture_eq_0_iff[OF carrier_is_subfield], simp_all) 
    finally have "(\<phi> X\<^bsub>R\<^esub>) [^]\<^bsub>K\<^esub> (order R^n) \<ominus>\<^bsub>K\<^esub> (\<phi> X\<^bsub>R\<^esub>) = \<zero>\<^bsub>K\<^esub>" by simp
    hence g:"(\<phi> X\<^bsub>R\<^esub>) [^]\<^bsub>K\<^esub> (order R^n) = (\<phi> X\<^bsub>R\<^esub>)"
      using var_closed[OF carrier_is_subring] 
      by simp

    have roots_g2: "pmult\<^bsub>K\<^esub> d ?g2 \<ge> 1" if z1: "degree d = 1" "monic_irreducible_poly K d" for d
    proof -
      obtain y where y_def: "y \<in> carrier K" "d = [\<one>\<^bsub>K\<^esub>, \<ominus>\<^bsub>K\<^esub> y]"
        using f.degree_one_monic_poly z1 by auto

      interpret x:ring_hom_cring "poly_ring K" "K" "(\<lambda>p. f.eval p y)"
        by (intro f.eval_cring_hom[OF f.carrier_is_subring] y_def)
      obtain x where x_def: "x \<in> carrier P" "y = \<phi> x"
        using y_def unfolding \<phi>_def K_def rupture_def FactRing_def A_RCOSETS_def' by auto
      let ?\<tau>  = "\<lambda>i. poly_of_const (coeff x i)"
      have test: "?\<tau> i \<in> carrier P" for i
        by (intro r.hom_closed coeff_range carrier_is_subring x_def)
      have test_2: "coeff x i \<in> carrier R" for i 
        by (intro coeff_range carrier_is_subring x_def)

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
        using y_def f.gauss_poly_not_zero[OF o2]
        unfolding f.is_root_def univ_poly_zero by simp
      hence "d pdivides\<^bsub>K\<^esub> ?g2"
        unfolding y_def
        by (intro f.is_root_imp_pdivides f.gauss_poly_carr, simp)
      thus "pmult\<^bsub>K\<^esub> d ?g2 \<ge> 1"
        using z1 f.gauss_poly_carr f.gauss_poly_not_zero o2
        by (subst f.multiplicity_ge_1_iff_pdivides, auto)
    qed

    have "sum' (\<lambda>d. pmult\<^bsub>K\<^esub> d ?g1 * degree d) {d. monic_irreducible_poly K d} = degree ?g1"
      using f.gauss_poly_monic o1
      by (subst f.degree_monic_poly', simp_all)
    also have "... = order K"
      using f.gauss_poly_degree o1 a by simp
    also have "... = card ((\<lambda>k. [\<one>\<^bsub>K\<^esub>, \<ominus>\<^bsub>K\<^esub> k]) ` carrier K)"
      unfolding order_def 
      by (intro card_image[symmetric] inj_onI, simp_all, metis f.minus_minus) 
    also have "... = card {d. monic_irreducible_poly K d \<and> degree d = 1}"
      using f.degree_one_monic_poly
      by (intro arg_cong[where f="card"], simp add:set_eq_iff image_iff) 
    also have "... = sum (\<lambda>d. 1) {d. monic_irreducible_poly K d \<and> degree d = 1}" 
      by simp
    also have "... = sum' (\<lambda>d. 1) {d. monic_irreducible_poly K d \<and> degree d = 1}" 
      by (intro sum.eq_sum[symmetric] finite_subset[OF _ f.finite_poly(1)[OF f.carrier_is_subring d]])
       (auto simp add:monic_irreducible_poly_def monic_poly_def) 
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
        using f.degree_one_monic_poly v by auto
      hence "pmult\<^bsub>K\<^esub> d ?g1 \<ge> 1"
        using roots_g1 v by simp
      then show ?thesis using True by simp
    next
      case False
      then show ?thesis by simp
    qed
    moreover have "finite {d. monic_irreducible_poly K d \<and> pmult\<^bsub>K\<^esub> d ?g1 * degree d > 0}"
      by (intro finite_subset[OF _ f.factor_monic_poly_fin[OF g1_monic]] subsetI, simp)
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
      hence "degree d > 1" using f.monic_poly_min_degree[OF v1] by simp
      hence "pmult\<^bsub>K\<^esub> d ?g1 = 0" using v2 v1 by auto
      then show ?thesis by simp
    qed
    hence "?g1 pdivides\<^bsub>K\<^esub> ?g2"
      using o1 o2 f.divides_monic_poly f.gauss_poly_monic by simp
    thus "degree f dvd n"
      by (subst (asm) f.div_gauss_poly_iff_1[OF assms(1) f_deg order_min], simp) 
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
      unfolding K_def \<phi>_def using f_carr gauss_poly_carr
      by (subst (asm) rupture_eq_0_iff[OF carrier_is_subfield], simp_all) 
    moreover assume "degree f dvd n"
    
    hence "gauss_poly R (order R^degree f) pdivides\<^bsub>R\<^esub> (gauss_poly R (order R^n))"
      using div_gauss_poly_iff_1[OF assms(1) f_deg order_min] by simp
    ultimately show "f pdivides\<^bsub>R\<^esub> gauss_poly R (order R^n)"
      using f_carr a p.divides_trans unfolding pdivides_def by blast
  qed
qed

lemma gauss_poly_splitted:
  "splitted (gauss_poly R (order R))"
proof -
  have "degree q \<le> 1" if 
    a:"q \<in> carrier P" "pirreducible (carrier R) q" "q pdivides gauss_poly R (order R)" for q
  proof -
    have q_carr: "q \<in> carrier M" 
      using a unfolding ring_irreducible_def by simp
    moreover have "Divisibility.irreducible M q" 
      using a unfolding ring_irreducible_def
      by (intro p.irreducible_imp_irreducible_mult a, simp_all)
    ultimately obtain p where p_def: "monic_irreducible_poly R p" "q \<sim>\<^bsub>M\<^esub> p"
      using monic_poly_span by auto
    have p_carr: "p \<in> carrier P" "p \<noteq> []" 
      using p_def(1) unfolding monic_irreducible_poly_def monic_poly_def by auto
    moreover have "p divides\<^bsub>M\<^esub> q"
      using associatedE[OF p_def(2)] by auto
    hence "p pdivides q"
      unfolding pdivides_def using divides_mult_imp_divides by simp
    moreover have "q pdivides gauss_poly R (order R^1)"
      using a(3) by simp
    ultimately have "p pdivides gauss_poly R (order R^1)"
      unfolding pdivides_def using p.divides_trans by blast
    hence "degree p dvd 1"
      using  div_gauss_poly_iff[where n="1"] p_def(1) by simp
    hence "degree p = 1" by simp
    moreover have "q divides\<^bsub>M\<^esub> p"
      using associatedE[OF p_def(2)] by auto
    hence "q pdivides p"
      unfolding pdivides_def using divides_mult_imp_divides by simp
    hence "degree q \<le> degree p"
      using a(1) p_carr
      by (intro pdivides_imp_degree_le[OF carrier_is_subring]) auto
    ultimately show ?thesis by simp
  qed

  thus ?thesis
    using gauss_poly_carr
    by (intro trivial_factors_imp_splitted, auto)
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

  have o2: "order R^n > 1" 
    using order_min assms(1) one_less_power by blast
  hence o21: "order R^n > 0" by linarith

  obtain d :: nat where order_dim: "order R = char R ^ d" "d > 0"
    using finite_field_order by blast
  have "d * n > 0" using order_dim assms by simp
  hence char_dvd_order: "int (char R) dvd int (order R ^ n)"
    unfolding order_dim using finite_carr_imp_char_ge_0[OF finite_carrier]
    by (simp add:power_mult[symmetric])

  interpret h: ring_hom_ring  "R" "P" "poly_of_const"
    using canonical_embedding_ring_hom[OF carrier_is_subring] by simp

  have "f pdivides\<^bsub>R\<^esub> ?g"
    using True div_gauss_poly_iff[OF assms] by simp
  hence "pmult\<^bsub>R\<^esub> f ?g \<ge> 1"
    using multiplicity_ge_1_iff_pdivides[OF assms(2)] gauss_poly_carr gauss_poly_not_zero[OF o2] 
    by auto
  moreover have "pmult\<^bsub>R\<^esub> f ?g < 2"
  proof (rule ccontr)
    assume "\<not> pmult\<^bsub>R\<^esub> f ?g < 2"
    hence "pmult\<^bsub>R\<^esub> f ?g \<ge> 2" by simp
    hence "(f [^]\<^bsub>P\<^esub> (2::nat)) pdivides\<^bsub>R\<^esub> ?g"
      using gauss_poly_carr gauss_poly_not_zero[OF o2]
      by (subst (asm) multiplicity_ge_iff[OF assms(2), where k="2"], simp_all) 
    hence "(f [^]\<^bsub>P\<^esub> (2::nat)) divides\<^bsub>mult_of P\<^esub> ?g"
      unfolding pdivides_def 
      using f_carr gauss_poly_not_zero o2 gauss_poly_carr
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
      using f_carr pderiv_carr[OF carrier_is_subring] h_def p.int_embed_closed
      apply (intro arg_cong2[where f="(\<oplus>\<^bsub>P\<^esub>)"]) 
      by (subst p.m_comm, simp_all add:p.m_assoc)
    also have "... = f \<otimes>\<^bsub>P\<^esub> (int_embed P 2 \<otimes>\<^bsub>P\<^esub> pderiv\<^bsub>R\<^esub> f \<otimes>\<^bsub>P\<^esub> h \<oplus>\<^bsub>P\<^esub> f \<otimes>\<^bsub>P\<^esub> pderiv\<^bsub>R\<^esub> h)"
      using f_carr pderiv_carr[OF carrier_is_subring] h_def p.int_embed_closed
      by (subst p.r_distr, simp_all)
    finally have "\<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub> = f \<otimes>\<^bsub>P\<^esub> (int_embed P 2 \<otimes>\<^bsub>P\<^esub> pderiv\<^bsub>R\<^esub> f \<otimes>\<^bsub>P\<^esub> h \<oplus>\<^bsub>P\<^esub> f \<otimes>\<^bsub>P\<^esub> pderiv\<^bsub>R\<^esub> h)" 
      (is "_ = f \<otimes>\<^bsub>P\<^esub> ?q")
      by simp

    hence "f pdivides\<^bsub>R\<^esub> \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>"
      unfolding factor_def pdivides_def using f_carr pderiv_carr[OF carrier_is_subring] 
        h_def p.int_embed_closed
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
  have o2: "order R^n > 1" 
    using order_min assms(1) one_less_power by blast

  have "\<not>(f pdivides\<^bsub>R\<^esub> gauss_poly R (order R^n))"
    using div_gauss_poly_iff[OF assms] False by simp
  hence "pmult\<^bsub>R\<^esub> f (gauss_poly R (order R^n)) = 0"
    using multiplicity_ge_1_iff_pdivides[OF assms(2)] gauss_poly_carr gauss_poly_not_zero[OF o2] leI less_one
    by blast
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
    moreover have "finite {f. f \<in> carrier P \<and> degree f \<le> k}" 
      using finite_poly[OF carrier_is_subring finite_carrier] by simp
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
    by (subst gauss_poly_degree, simp_all)
  also have "... = sum' (\<lambda>d. pmult\<^bsub>R\<^esub> d (gauss_poly R (order R^n)) * degree d) ?D"
    using d
    by (intro degree_monic_poly'[symmetric] gauss_poly_monic) 
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
