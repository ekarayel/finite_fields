theory RingIso_Ext
  imports "HOL-Algebra.QuotRing" "Monic_Polynomial_Factorization"
begin

lemma lift_iso_to_poly_ring:
  assumes "h \<in> ring_iso R S" "domain R" "domain S"
  shows "map h \<in> ring_iso (poly_ring R) (poly_ring S)"
proof (rule ring_iso_memI)
  interpret dr: domain "R" using assms(2) by blast
  interpret ds: domain "S" using assms(3) by blast
  interpret pdr: domain "poly_ring R"
    using dr.univ_poly_is_domain[OF dr.carrier_is_subring] by simp
  interpret pds: domain "poly_ring S"
    using ds.univ_poly_is_domain[OF ds.carrier_is_subring] by simp
  interpret h: ring_hom_ring "R" "S" h
    using dr.is_ring ds.is_ring assms(1)
    by (intro ring_hom_ringI2, simp_all add:ring_iso_def)
  let ?R = "poly_ring R"
  let ?S = "poly_ring S"

  have h_img: "h ` (carrier R) = carrier S" 
    using assms(1) unfolding ring_iso_def bij_betw_def by auto
  have h_inj: "inj_on h (carrier R)" 
    using assms(1) unfolding ring_iso_def bij_betw_def by auto
  hence h_non_zero_iff: "x \<noteq> \<zero>\<^bsub>R\<^esub> \<Longrightarrow> x \<in> carrier R \<Longrightarrow> h x \<noteq> \<zero>\<^bsub>S\<^esub>" for x
    using h.hom_zero dr.zero_closed inj_onD by metis

  have norm_elim: "ds.normalize (map h x) = map h x" if a:"x \<in> carrier (poly_ring R)" for x 
  proof (cases "x")
    case Nil then show ?thesis by simp
  next
    case (Cons xh xt)
    have "xh \<in> carrier R" "xh \<noteq> \<zero>\<^bsub>R\<^esub>"
      using a unfolding Cons univ_poly_carrier[symmetric] polynomial_def by auto
    hence "h xh \<noteq> \<zero>\<^bsub>S\<^esub>" using h_non_zero_iff by simp
    then show ?thesis unfolding Cons by simp
  qed

  show t_1: "map h x \<in> carrier ?S" if a:"x \<in> carrier ?R" for x
    using a hd_in_set h_non_zero_iff hd_map
    unfolding univ_poly_carrier[symmetric] polynomial_def 
    by (cases x, auto)

  show "map h (x \<otimes>\<^bsub>?R\<^esub> y) = map h x \<otimes>\<^bsub>?S\<^esub> map h y" if a:"x \<in> carrier ?R" "y \<in> carrier ?R" for x y
  proof -
    have "map h (x \<otimes>\<^bsub>?R\<^esub> y) = ds.normalize (map h (x \<otimes>\<^bsub>?R\<^esub> y))"
      using a by (intro norm_elim[symmetric],simp) 
    also have "... = map h x \<otimes>\<^bsub>?S\<^esub> map h y"
      using a unfolding univ_poly_mult univ_poly_carrier[symmetric] polynomial_def
      by (intro h.poly_mult_hom'[of x y] , auto)
    finally show ?thesis by simp
  qed

  show "map h (x \<oplus>\<^bsub>?R\<^esub> y) = map h x \<oplus>\<^bsub>?S\<^esub> map h y" if a:"x \<in> carrier ?R" "y \<in> carrier ?R" for x y
  proof -
    have "map h (x \<oplus>\<^bsub>?R\<^esub> y) = ds.normalize (map h (x \<oplus>\<^bsub>?R\<^esub> y))"
      using a by (intro norm_elim[symmetric],simp) 
    also have "... = map h x \<oplus>\<^bsub>?S\<^esub> map h y"
      using a unfolding univ_poly_add univ_poly_carrier[symmetric] polynomial_def
      by (intro h.poly_add_hom'[of x y], auto)
    finally show ?thesis by simp
  qed

  show "map h \<one>\<^bsub>?R\<^esub> = \<one>\<^bsub>?S\<^esub>" 
    unfolding univ_poly_one by simp


  let ?hinv = "map (the_inv_into (carrier R) h)"

  have "map h \<in> carrier ?R \<rightarrow> carrier ?S" 
    using t_1 by simp
  moreover have "?hinv x \<in> carrier ?R" if a: "x \<in> carrier ?S" for x
  proof (cases "x = []")
    case True
    then show ?thesis by (simp add:univ_poly_carrier[symmetric] polynomial_def)
  next
    case False
    have set_x: "set x \<subseteq> h ` carrier R" 
      using a h_img unfolding univ_poly_carrier[symmetric] polynomial_def by auto

    have "lead_coeff x \<noteq> \<zero>\<^bsub>S\<^esub>" "lead_coeff x \<in> carrier S"
      using a False unfolding univ_poly_carrier[symmetric] polynomial_def by auto
    hence "the_inv_into (carrier R) h (lead_coeff x) \<noteq> the_inv_into (carrier R) h \<zero>\<^bsub>S\<^esub>" 
      using inj_on_the_inv_into[OF h_inj] inj_onD ds.zero_closed h_img by metis
    hence "the_inv_into (carrier R) h (lead_coeff x) \<noteq> \<zero>\<^bsub>R\<^esub>" 
      unfolding h.hom_zero[symmetric] the_inv_into_f_f[OF h_inj dr.zero_closed] by simp
    hence "lead_coeff (?hinv x) \<noteq> \<zero>\<^bsub>R\<^esub>" 
      using False by (simp add:hd_map)
    moreover have "the_inv_into (carrier R) h ` set x \<subseteq> carrier R" 
      using the_inv_into_into[OF h_inj] set_x
      by (intro image_subsetI) auto
    hence "set (?hinv x) \<subseteq> carrier R" by simp 
    ultimately show ?thesis by (simp add:univ_poly_carrier[symmetric] polynomial_def)
  qed
  moreover have "?hinv (map h x) = x" if a:"x \<in> carrier ?R" for x 
  proof -
    have set_x: "set x \<subseteq> carrier R" 
      using a unfolding univ_poly_carrier[symmetric] polynomial_def by auto
    have "?hinv (map h x) = map (\<lambda>y. the_inv_into (carrier R) h (h y)) x"
      by simp
    also have "... = map id x"
      using set_x by (intro map_cong, auto simp add:the_inv_into_f_f[OF h_inj])
    also have "... = x" by simp
    finally show ?thesis by simp
  qed
  moreover have "map h (?hinv x) = x" if a:"x \<in> carrier ?S" for x
  proof -
    have set_x: "set x \<subseteq> h ` carrier R" 
      using a h_img unfolding univ_poly_carrier[symmetric] polynomial_def by auto
    have "map h (?hinv x) = map (\<lambda>y. h (the_inv_into (carrier R) h y)) x"
      by simp
    also have "... = map id x"
      using set_x by (intro map_cong, auto simp add:f_the_inv_into_f[OF h_inj])
    also have "... = x" by simp
    finally show ?thesis by simp
  qed
  ultimately show "bij_betw (map h) (carrier ?R) (carrier ?S)" 
    by (intro bij_betwI[where g="?hinv"], auto) 
qed

lemma carrier_hom:
  assumes "f \<in> carrier (poly_ring R)"
  assumes "h \<in> ring_iso R S" "domain R" "domain S"
  shows "map h f \<in> carrier (poly_ring S)"
proof -
  note poly_iso = lift_iso_to_poly_ring[OF assms(2,3,4)] 
  show ?thesis
    using ring_iso_memE(1)[OF poly_iso assms(1)] by simp
qed

lemma monic_poly_hom:
  assumes "monic_poly R f"
  assumes "h \<in> ring_iso R S" "domain R" "domain S"
  shows "monic_poly S (map h f)"
proof -
  have c: "h \<in> ring_hom R S"
    using assms(2) ring_iso_def by auto
  have e: "f \<in> carrier (poly_ring R)" 
    using assms(1) unfolding monic_poly_def by simp

  have a:"f \<noteq> []"
    using assms(1) unfolding monic_poly_def by simp
  hence "map h f \<noteq> []" by simp
  moreover have "lead_coeff f = \<one>\<^bsub>R\<^esub>"
    using assms(1) unfolding monic_poly_def by simp
  hence "lead_coeff (map h f) = \<one>\<^bsub>S\<^esub>" 
    using ring_hom_one[OF c] by (simp add: hd_map[OF a])
  ultimately show ?thesis
    using carrier_hom[OF e assms(2-4)]
    unfolding monic_poly_def by simp
qed

lemma Units_hom:
  assumes "h \<in> ring_iso R S" "domain R" "domain S" "x \<in> carrier R"
  shows "x \<in> Units R \<longleftrightarrow>  h x \<in> Units S"
proof -

  interpret dr: domain "R" using assms(2) by blast
  interpret ds: domain "S" using assms(3) by blast
  interpret pdr: domain "poly_ring R"
    using dr.univ_poly_is_domain[OF dr.carrier_is_subring] by simp
  interpret pds: domain "poly_ring S"
    using ds.univ_poly_is_domain[OF ds.carrier_is_subring] by simp
  interpret h: ring_hom_ring "R" "S" h
    using dr.is_ring ds.is_ring assms(1)
    by (intro ring_hom_ringI2, simp_all add:ring_iso_def)

  have h_img: "h ` (carrier R) = carrier S" 
    using assms(1) unfolding ring_iso_def bij_betw_def by auto

  have h_inj_on: "inj_on h (carrier R)" 
    using assms(1) unfolding ring_iso_def bij_betw_def by auto

  hence h_one_iff: "h x = \<one>\<^bsub>S\<^esub> \<longleftrightarrow> x = \<one>\<^bsub>R\<^esub>" if "x \<in> carrier R" for x
    using h.hom_one that by (metis dr.one_closed inj_onD)

  have "x \<in> Units R \<longleftrightarrow> (\<exists>y\<in>carrier R. x \<otimes>\<^bsub>R\<^esub> y = \<one>\<^bsub>R\<^esub> \<and> y \<otimes>\<^bsub>R\<^esub> x = \<one>\<^bsub>R\<^esub>)"
    using assms unfolding Units_def by auto
  also have "... \<longleftrightarrow>  (\<exists>y\<in>carrier R. h x \<otimes>\<^bsub>S\<^esub> h y = h \<one>\<^bsub>R\<^esub> \<and> h y \<otimes>\<^bsub>S\<^esub> h x = h \<one>\<^bsub>R\<^esub>)"
    using h_one_iff assms by (intro bex_cong, simp_all flip:h.hom_mult)
  also have "... \<longleftrightarrow> (\<exists>y\<in>carrier S. h x \<otimes>\<^bsub>S\<^esub> y = h \<one>\<^bsub>R\<^esub> \<and> y \<otimes>\<^bsub>S\<^esub> h x = \<one>\<^bsub>S\<^esub>)"
    unfolding h_img[symmetric] by simp
  also have "... \<longleftrightarrow> h x \<in> Units S"
    using assms h.hom_closed unfolding Units_def by auto
  finally show ?thesis by simp
qed

lemma divides_hom:
  assumes "h \<in> ring_iso R S" "domain R" "domain S" "x \<in> carrier R" "y \<in> carrier R"
  shows "x divides\<^bsub>R\<^esub> y \<longleftrightarrow> (h x) divides\<^bsub>S\<^esub> (h y)"  (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  interpret dr: domain "R" using assms(2) by blast
  interpret ds: domain "S" using assms(3) by blast
  interpret pdr: domain "poly_ring R"
    using dr.univ_poly_is_domain[OF dr.carrier_is_subring] by simp
  interpret pds: domain "poly_ring S"
    using ds.univ_poly_is_domain[OF ds.carrier_is_subring] by simp
  interpret h: ring_hom_ring "R" "S" h
    using dr.is_ring ds.is_ring assms(1)
    by (intro ring_hom_ringI2, simp_all add:ring_iso_def)

  have h_inj_on: "inj_on h (carrier R)" 
    using assms(1) unfolding ring_iso_def bij_betw_def by auto
  have h_img: "h ` (carrier R) = carrier S" 
    using assms(1) unfolding ring_iso_def bij_betw_def by auto

  have "?lhs \<longleftrightarrow> (\<exists>c \<in> carrier R. y = x \<otimes>\<^bsub>R\<^esub> c)"
    unfolding factor_def by simp
  also have "... \<longleftrightarrow> (\<exists>c \<in> carrier R. h y = h x \<otimes>\<^bsub>S\<^esub> h c)"
    using assms(4,5) inj_onD[OF h_inj_on]
    by (intro bex_cong, auto simp flip:h.hom_mult) 
  also have "... \<longleftrightarrow> (\<exists>c \<in> carrier S. h y = h x  \<otimes>\<^bsub>S\<^esub> c)"
    unfolding h_img[symmetric] by simp
  also have "... \<longleftrightarrow> ?rhs" 
    unfolding factor_def by simp
  finally show ?thesis by simp
qed

lemma properfactor_hom:
  assumes "h \<in> ring_iso R S" "domain R" "domain S" "x \<in> carrier R" "b \<in> carrier R"
  shows "properfactor R b x \<longleftrightarrow> properfactor S (h b) (h x)" 
  using divides_hom[OF assms(1,2,3)] assms(4,5)
  unfolding properfactor_def by simp

lemma irreducible_hom:
  assumes "h \<in> ring_iso R S" "domain R" "domain S" "x \<in> carrier R"
  shows "irreducible R x = irreducible S (h x)"
proof -
  have h_img: "h ` (carrier R) = carrier S" 
    using assms(1) unfolding ring_iso_def bij_betw_def by auto

  have "irreducible R x \<longleftrightarrow> (x \<notin> Units R \<and> (\<forall>b\<in>carrier R. properfactor R b x \<longrightarrow> b \<in> Units R))"
    unfolding irreducible_def by simp
  also have "... \<longleftrightarrow> (x \<notin> Units R \<and> (\<forall>b\<in>carrier R. properfactor S (h b) (h x) \<longrightarrow> b \<in> Units R))"
    using properfactor_hom[OF assms(1,2,3)] assms(4) by simp
  also have "... \<longleftrightarrow> (h x \<notin> Units S \<and> (\<forall>b\<in>carrier R. properfactor S (h b) (h x) \<longrightarrow> h b \<in> Units S))"
    using assms(4) Units_hom[OF assms(1,2,3)] by simp
  also have "...\<longleftrightarrow> (h x \<notin> Units S \<and> (\<forall>b\<in>h ` carrier R. properfactor S b (h x) \<longrightarrow> b \<in> Units S))"
    by simp
  also have "... \<longleftrightarrow> irreducible S (h x)"
    unfolding h_img irreducible_def by simp
  finally show ?thesis by simp
qed

lemma pirreducible_hom:
  assumes "h \<in> ring_iso R S" "domain R" "domain S"
  assumes "f \<in> carrier (poly_ring R)"
  shows "pirreducible\<^bsub>R\<^esub> (carrier R) f = pirreducible\<^bsub>S\<^esub> (carrier S) (map h f)" (is "?lhs = ?rhs")
proof -
  note lift_iso = lift_iso_to_poly_ring[OF assms(1,2,3)]
  interpret dr: domain "R" using assms(2) by blast
  interpret ds: domain "S" using assms(3) by blast
  interpret pdr: domain "poly_ring R"
    using dr.univ_poly_is_domain[OF dr.carrier_is_subring] by simp
  interpret pds: domain "poly_ring S"
    using ds.univ_poly_is_domain[OF ds.carrier_is_subring] by simp


  have mh_inj_on: "inj_on (map h) (carrier (poly_ring R))" 
    using lift_iso unfolding ring_iso_def bij_betw_def by auto
  moreover have "map h \<zero>\<^bsub>poly_ring R\<^esub> = \<zero>\<^bsub>poly_ring S\<^esub>" by (simp add:univ_poly_zero)
  ultimately have mh_zero_iff: "map h f = \<zero>\<^bsub>poly_ring S\<^esub> \<longleftrightarrow> f = \<zero>\<^bsub>poly_ring R\<^esub>"
    using assms(4) by (metis pdr.zero_closed inj_onD)

  have "?lhs \<longleftrightarrow> (f \<noteq> \<zero>\<^bsub>poly_ring R\<^esub> \<and> irreducible (poly_ring R) f)"
    unfolding ring_irreducible_def by simp
  also have "... \<longleftrightarrow> (f \<noteq> \<zero>\<^bsub>poly_ring R\<^esub> \<and> irreducible (poly_ring S) (map h f))"
    using irreducible_hom[OF lift_iso pdr.domain_axioms pds.domain_axioms] assms(4) by simp
  also have "... \<longleftrightarrow> (map h f \<noteq> \<zero>\<^bsub>poly_ring S\<^esub> \<and> irreducible (poly_ring S) (map h f))"
    using mh_zero_iff by simp
  also have "... \<longleftrightarrow> ?rhs"
    unfolding ring_irreducible_def by simp
  finally show ?thesis by simp
qed

lemma monic_irreducible_poly_hom:
  assumes "monic_irreducible_poly R f"
  assumes "h \<in> ring_iso R S" "domain R" "domain S"
  shows "monic_irreducible_poly S (map h f)"
proof -
 have a:"pirreducible\<^bsub>R\<^esub> (carrier R) f" "f \<in> carrier (poly_ring R)"  "monic_poly R f"
    using assms(1) unfolding monic_poly_def monic_irreducible_poly_def by auto
 
  have "pirreducible\<^bsub>S\<^esub> (carrier S) (map h f)"
    using a pirreducible_hom assms by auto  
  moreover have "monic_poly S (map h f)"
    using a monic_poly_hom[OF _ assms(2,3,4)] by simp
  ultimately show ?thesis
    unfolding monic_irreducible_poly_def by simp
qed

end