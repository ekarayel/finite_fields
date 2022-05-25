theory Lemma_2_3
imports 
  "HOL-Algebra.Multiplicative_Group"
  "Formal_Differentiation"
  "Monic_Polynomial_Factorization"

begin
lemma  (in field) f_comm_group_1:
  "x \<in> carrier R \<Longrightarrow> x \<noteq> \<zero> \<Longrightarrow> y \<in> carrier R \<Longrightarrow> y \<noteq> \<zero> \<Longrightarrow> x \<otimes> y = \<zero> \<Longrightarrow> False" 
  using integral by auto

lemma (in field) f_comm_group_2:
  assumes "x \<in> carrier R"
  assumes "x \<noteq> \<zero>"
  shows " \<exists>y\<in>carrier R - {\<zero>}. y \<otimes> x = \<one>"
proof -
  have x_unit: "x \<in> Units R" using field_Units assms by simp
  thus ?thesis unfolding Units_def by auto
qed

sublocale field < mult_of: comm_group "mult_of R"
  rewrites "mult (mult_of R) = mult R"
       and "one  (mult_of R) = one R"
  by (auto intro!:comm_groupI f_comm_group_1 m_assoc m_comm f_comm_group_2)

lemma (in domain) div_neg:
  assumes "a \<in> carrier R" "b \<in> carrier R"
  assumes "a divides b"
  shows "a divides (\<ominus> b)"
proof -
  obtain r1 where r1_def: "r1 \<in> carrier R" "a \<otimes> r1 = b"
    using assms by (auto simp:factor_def) 

  have "a \<otimes> (\<ominus> r1) = \<ominus> (a \<otimes> r1)"
    using assms(1) r1_def(1) by algebra
  also have "... = \<ominus> b"
    using r1_def(2) by simp
  finally have "\<ominus>b = a \<otimes> (\<ominus> r1)" by simp
  moreover have "\<ominus>r1 \<in> carrier R"
    using r1_def(1) by simp
  ultimately show ?thesis
    by (auto simp:factor_def) 
qed

lemma (in domain) div_sum:
  assumes "a \<in> carrier R" "b \<in> carrier R" "c \<in> carrier R"
  assumes "a divides b"
  assumes "a divides c"
  shows "a divides (b \<oplus> c)"
proof -
  obtain r1 where r1_def: "r1 \<in> carrier R" "a \<otimes> r1 = b"
    using assms by (auto simp:factor_def) 

  obtain r2 where r2_def: "r2 \<in> carrier R" "a \<otimes> r2 = c"
    using assms by (auto simp:factor_def) 

  have "a \<otimes> (r1 \<oplus> r2) = (a \<otimes> r1) \<oplus> (a \<otimes> r2)"
    using assms(1) r1_def(1) r2_def(1) by algebra
  also have "... = b \<oplus> c"
    using r1_def(2) r2_def(2) by simp
  finally have "b \<oplus> c = a \<otimes> (r1 \<oplus> r2)" by simp
  moreover have "r1 \<oplus> r2 \<in> carrier R"
    using r1_def(1) r2_def(1) by simp
  ultimately show ?thesis
    by (auto simp:factor_def) 
qed

lemma (in domain) div_sum_iff:
  assumes "a \<in> carrier R" "b \<in> carrier R" "c \<in> carrier R"
  assumes "a divides b"
  shows "a divides (b \<oplus> c) \<longleftrightarrow> a divides c"
proof 
  assume "a divides (b \<oplus> c)"
  moreover have "a divides (\<ominus> b)"
    using div_neg assms(1,2,4) by simp
  ultimately have "a divides ((b \<oplus> c) \<oplus> (\<ominus> b))"
    using div_sum assms by simp
  also have "... = c" using assms(1,2,3) by algebra
  finally show "a divides c" by simp
next
  assume "a divides c"
  thus "a divides (b \<oplus> c)"
    using assms by (intro div_sum) auto
qed

lemma (in field) x_pow_n_eq_x:
  assumes "finite (carrier R)"
  assumes "x \<in> carrier R"
  shows "x [^] (order R) = x"
proof (cases "x = \<zero>")
  case True
  have "order R > 0"
    using assms(1) order_gt_0_iff_finite by simp
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
    using order_gt_0_iff_finite assms(1) unfolding order_def by simp
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

lemma (in field) x_pow_n_eq_x':
  assumes "finite (carrier R)"
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
    using x_pow_n_eq_x[OF assms(1)] assms(2) by simp
  also have "... = x"
    using Suc by simp
  finally show ?case by simp
qed

lemma (in principal_domain) geom:
  fixes q:: nat
  assumes [simp]: "a \<in> carrier R"
  shows "(a \<ominus> \<one>) \<otimes> (\<Oplus>i\<in>{0..<q}. a [^] i) = (a [^] q \<ominus> \<one>)"
    (is "?lhs = ?rhs")
proof -
  have [simp]: "a [^] i \<in> carrier R" for i :: nat
    by (intro nat_pow_closed assms)
  have [simp]: "\<ominus> \<one> \<otimes> x = \<ominus> x" if "x \<in> carrier R" for x
    using l_minus l_one one_closed that by presburger

  let ?cterm = "(\<Oplus>i\<in>{1..<q}. a [^] i)"

  have "?lhs = a \<otimes> (\<Oplus>i\<in>{0..<q}. a [^] i)  \<ominus> (\<Oplus>i\<in>{0..<q}. a [^] i)"
    unfolding a_minus_def by (subst l_distr, simp_all add:Pi_def)
  also have "... = (\<Oplus>i\<in>{0..<q}. a \<otimes> a [^] i) \<ominus> (\<Oplus>i\<in>{0..<q}. a [^] i)"
    by (subst finsum_rdistr, simp_all add:Pi_def)
  also have "... = (\<Oplus>i\<in>{0..<q}. a [^] (Suc i)) \<ominus> (\<Oplus>i\<in>{0..<q}. a [^] i)"
    by (subst nat_pow_Suc, simp_all add:m_comm)
  also have "... = (\<Oplus>i\<in>Suc ` {0..<q}. a [^] i) \<ominus> (\<Oplus>i\<in>{0..<q}. a [^] i)"
    by (subst finsum_reindex, simp_all)
  also have "... = (\<Oplus>i\<in>insert q {1..<q}. a [^] i) \<ominus> (\<Oplus>i\<in> insert 0 {1..<q}. a [^] i)"
  proof (cases "q > 0")
    case True
    then show ?thesis by (intro arg_cong2[where f="\<lambda>x y. x \<ominus> y"] finsum_cong, auto) 
  next
    case False
    then show ?thesis by (simp, algebra)
  qed
  also have "... = (a [^] q \<oplus> ?cterm) \<ominus> (\<one> \<oplus> ?cterm)"
    by simp
  also have "... = a [^] q \<oplus> ?cterm \<oplus> (\<ominus> \<one> \<oplus> \<ominus> ?cterm)"
    unfolding a_minus_def by (subst minus_add, simp_all)
  also have "... = a [^] q \<oplus> (?cterm \<oplus> (\<ominus> \<one> \<oplus> \<ominus> ?cterm))"
    by (subst a_assoc, simp_all)
  also have "... = a [^] q \<oplus> (?cterm \<oplus> (\<ominus> ?cterm \<oplus> \<ominus> \<one>))"
    by (subst a_comm[where x="\<ominus> \<one>"], simp_all)
  also have "... = a [^] q \<oplus> ((?cterm \<oplus> (\<ominus> ?cterm)) \<oplus> \<ominus> \<one>)"
    by (subst a_assoc, simp_all)
  also have "... = a [^] q \<oplus> (\<zero> \<oplus> \<ominus> \<one>)"
    by (subst r_neg, simp_all)
  also have "... = a [^] q \<ominus> \<one>" 
    unfolding a_minus_def by simp
  finally show ?thesis by simp
qed

lemma (in domain) rupture_eq_0_iff:
  assumes "subfield K R" "p \<in> carrier (K[X])" "q \<in> carrier (K[X])"
  shows "rupture_surj K p q = \<zero>\<^bsub>Rupt K p\<^esub> \<longleftrightarrow> p pdivides q" (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  interpret h:ring_hom_ring "K[X]" "(Rupt K p)" "(rupture_surj K p)"
    using assms subfieldE by (intro rupture_surj_hom) auto

  have a: "q pmod p \<in> (\<lambda>q. q pmod p) ` carrier (K [X])" 
    using assms(3) by simp
  have "\<zero>\<^bsub>K[X]\<^esub> = \<zero>\<^bsub>K[X]\<^esub> pmod p" 
    using assms(1,2) long_division_zero(2)
    by (simp add:univ_poly_zero)
  hence b: "\<zero>\<^bsub>K[X]\<^esub> \<in> (\<lambda>q. q pmod p) ` carrier (K[X])" 
    by (simp add:image_iff) auto

  have "?lhs \<longleftrightarrow> rupture_surj K p (q pmod p) = rupture_surj K p (\<zero>\<^bsub>K[X]\<^esub>)" 
    apply (subst h.hom_zero)
    apply (subst rupture_surj_composed_with_pmod[OF assms])
    by simp
  also have "... \<longleftrightarrow> q pmod p = \<zero>\<^bsub>K[X]\<^esub>"
    using assms(3)
    by (intro inj_on_eq_iff[OF rupture_surj_inj_on[OF assms(1,2)]] a b)
  also have "... \<longleftrightarrow> ?rhs"
    unfolding univ_poly_zero
    by (intro pmod_zero_iff_pdivides[OF assms(1)] assms(2,3))
  finally show "?thesis" by simp
qed

lemma (in domain) split_poly_in_finsum:
  assumes "subring K R"
  assumes "p \<in> carrier (K[X])"
  shows "p = finsum (K[X]) (\<lambda>i. poly_of_const (coeff p i) \<otimes>\<^bsub>K[X]\<^esub> X [^]\<^bsub>K[X]\<^esub> i) {..<length p}"
proof -
  interpret p:domain "K[X]"
    using assms by (simp add: univ_poly_is_domain)

  let ?I = "{i. i < length p \<and> coeff p i \<noteq> \<zero>\<^bsub>R\<^esub>}"
  let ?J = "{i. i < length p \<and> coeff p i = \<zero>\<^bsub>R\<^esub>}"
  let ?coeff = "\<lambda>i. poly_of_const (local.coeff p i)"

  have [simp]: "poly_of_const \<zero> = \<zero>\<^bsub>K [X]\<^esub>"
    by (simp add:univ_poly_zero poly_of_const_def)

  have set_p:"set p \<subseteq> K"
    using assms(1,2) coeff_img(3)[of p]
    by (simp add:univ_poly_carrier[symmetric] polynomial_def) auto

  have c: "poly_of_const x \<in> carrier (K[X])" if c1:"x \<in> K" for x
    using c1 univ_poly_carrier
    by (simp add:poly_of_const_def) auto
  have d:"(a, b) \<in> set (dense_repr p) \<Longrightarrow> poly_of_const a \<in> carrier (K[X])" for a b
    using dense_repr_set_fst[OF set_p]
    by (intro c) auto
  have "range (coeff p) \<subseteq> insert \<zero> K"
    using assms(1,2) coeff_img(3)[of p]
    by (simp add:univ_poly_carrier[symmetric] polynomial_def) auto
  also have "... \<subseteq> K"
    using assms(1) by (simp add: subringE(2))
  finally have "range (coeff p) \<subseteq> K" by simp
  hence "coeff p i \<in> K" for i by auto
  hence "?coeff i \<in> carrier (K[X])" for i
    by (intro c, simp)
  hence b: "?coeff i \<otimes>\<^bsub>K [X]\<^esub> X [^]\<^bsub>K [X]\<^esub> i \<in> carrier (K[X])" for i
    using var_pow_closed[OF assms(1)] by simp

  have e: "i \<in> set (dense_repr p) \<Longrightarrow> [fst i] = poly_of_const (fst i)" for i
    using dense_repr_set_fst[OF set_p] by (simp add:poly_of_const_def, blast)

  have a:"set (dense_repr p) = (\<lambda>i. (coeff p i, i)) ` ?I"
  proof (induction p)
    case Nil
    then show ?case by simp
  next
    case (Cons a p)
    have "set (dense_repr (a#p)) = (if a \<noteq> \<zero>\<^bsub>R\<^esub> then {(a, length p)} else {}) \<union> (set (dense_repr p))"
      by simp
    also have "... = 
      (\<lambda>i. (coeff (a#p) i, i)) ` (if a \<noteq> \<zero>\<^bsub>R\<^esub> then {length p} else {}) \<union> 
      (\<lambda>i. (coeff (a#p) i, i)) ` {i. i < length p \<and> coeff p i \<noteq> \<zero>\<^bsub>R\<^esub>}"
      using Cons  by simp
    also have "... = (\<lambda>i. (coeff (a#p) i, i)) ` ((if a \<noteq> \<zero>\<^bsub>R\<^esub> then {length p} else {}) \<union> {i. i < length p \<and> coeff p i \<noteq> \<zero>\<^bsub>R\<^esub>})"
      by (subst set_eq_iff, auto)
    also have "... = (\<lambda>i. (coeff (a#p) i, i)) ` {i. i < length (a#p) \<and> coeff (a#p) i \<noteq> \<zero>\<^bsub>R\<^esub>}"
      by (intro arg_cong2[where f="(`)"], auto simp add:set_eq_iff)
    finally 
    show ?case by simp
  qed

  have "p = (\<Oplus>\<^bsub>K[X]\<^esub> t \<in> set (dense_repr p). [ fst t ] \<otimes>\<^bsub>K[X]\<^esub> (X [^]\<^bsub>K[X]\<^esub> (snd t)))"
    using var_pow_finsum_decomp[OF assms(1,2)] by simp
  also have "... = 
    (\<Oplus>\<^bsub>K[X]\<^esub> t \<in> set (dense_repr p). poly_of_const (fst t) \<otimes>\<^bsub>K[X]\<^esub> (X [^]\<^bsub>K[X]\<^esub> (snd t)))"
    using d var_pow_closed[OF assms(1)] c e by (intro p.finsum_cong', simp_all add:Pi_def)
  also have "... = 
    (\<Oplus>\<^bsub>K[X]\<^esub> t \<in> (\<lambda>i. (coeff p i, i)) ` ?I. poly_of_const (fst t) \<otimes>\<^bsub>K[X]\<^esub> (X [^]\<^bsub>K[X]\<^esub> (snd t)))"
    by (subst a, simp)
  also have "... = (\<Oplus>\<^bsub>K[X]\<^esub> t \<in> ?I. ?coeff t \<otimes>\<^bsub>K[X]\<^esub> (X [^]\<^bsub>K[X]\<^esub> t))"
    using b
    by (subst p.finsum_reindex) (auto intro!: inj_onI simp add:Pi_def image_def) 
  also have "... = 
    (\<Oplus>\<^bsub>K[X]\<^esub> t \<in> ?I. ?coeff t \<otimes>\<^bsub>K[X]\<^esub> (X [^]\<^bsub>K[X]\<^esub> t)) \<oplus>\<^bsub>K[X]\<^esub> (\<Oplus>\<^bsub>K[X]\<^esub> t \<in> ?J. \<zero>\<^bsub>K[X]\<^esub>)"
    using p.finsum_closed b
    by (subst p.finsum_zero, auto) 
  also have "... = 
    (\<Oplus>\<^bsub>K[X]\<^esub> t \<in> ?I. ?coeff t \<otimes>\<^bsub>K[X]\<^esub> (X [^]\<^bsub>K[X]\<^esub> t)) \<oplus>\<^bsub>K[X]\<^esub> 
    (\<Oplus>\<^bsub>K[X]\<^esub> t \<in> ?J. ?coeff t \<otimes>\<^bsub>K[X]\<^esub> (X [^]\<^bsub>K[X]\<^esub> t))"
    using b var_pow_closed[OF assms(1)]
    by (intro arg_cong2[where f="(\<oplus>\<^bsub>K[X]\<^esub>)"] p.finsum_cong', auto)
  also have "... = (\<Oplus>\<^bsub>K[X]\<^esub> i \<in> ?I\<union>?J. poly_of_const (coeff p i) \<otimes>\<^bsub>K[X]\<^esub> (X [^]\<^bsub>K[X]\<^esub> i))"
    using b by (subst p.finsum_Un_disjoint) auto
  also have "... = (\<Oplus>\<^bsub>K[X]\<^esub> i \<in> {..<length p}. poly_of_const (coeff p i) \<otimes>\<^bsub>K[X]\<^esub> (X [^]\<^bsub>K[X]\<^esub> i))"
    using b by (intro p.finsum_cong') auto     
  finally show ?thesis by simp
qed

definition gauss_poly where 
  "gauss_poly K n = X\<^bsub>K\<^esub> [^]\<^bsub>poly_ring K\<^esub> (n::nat) \<ominus>\<^bsub>poly_ring K\<^esub> X\<^bsub>K\<^esub>"

context field
begin

interpretation polynomial_notation "R"
  by unfold_locales simp

interpretation p:principal_domain "poly_ring R"
  by (simp add: carrier_is_subfield univ_poly_is_principal)

lemma lemma_2:
  fixes l m :: nat
  assumes "l > 0"
  shows "(X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> l \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) pdivides\<^bsub>R\<^esub> (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> m \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) \<longleftrightarrow> l dvd m"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  define q where "q = m div l"
  define r where "r = m mod l"
  have m_def: "m = q * l + r" and r_range: "r < l"
    using assms by (auto simp add:q_def r_def) 

  have pow_sum_carr:"(\<Oplus>\<^bsub>P\<^esub>i\<in>{0..<q}. (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> l)[^]\<^bsub>P\<^esub> i) \<in> carrier P" 
    using var_pow_closed[OF carrier_is_subring]
    by (intro p.finsum_closed, simp)

  have "(X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> (q*l) \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) = ((X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> l)[^]\<^bsub>P\<^esub> q) \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>"
    using var_closed[OF carrier_is_subring]
    by (subst p.nat_pow_pow, simp_all add:algebra_simps)
  also have "... =
    (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> l \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) \<otimes>\<^bsub>P\<^esub> (\<Oplus>\<^bsub>P\<^esub>i\<in>{0..<q}. (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> l) [^]\<^bsub>P\<^esub> i)" 
    using var_pow_closed[OF carrier_is_subring]
    by (subst p.geom[symmetric], simp_all)
  finally have pow_sum_fact:"(X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> (q*l) \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) =
    (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> l \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) \<otimes>\<^bsub>P\<^esub> (\<Oplus>\<^bsub>P\<^esub>i\<in>{0..<q}. (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> l) [^]\<^bsub>P\<^esub> i)" by simp
  
  have "(X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> l \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) divides\<^bsub>P\<^esub> (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> (q*l) \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>)"
    by (rule dividesI[OF pow_sum_carr pow_sum_fact])

  hence c:"(X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> l \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) divides\<^bsub>P\<^esub> X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> r \<otimes>\<^bsub>P\<^esub> (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> (q * l) \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>)"
    using var_pow_closed[OF carrier_is_subring]
    by (intro p.divides_prod_l, auto)

  have "(X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> m \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) = X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> (r + q * l) \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>"
    unfolding m_def using add.commute by metis
  also have "... = (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> r) \<otimes>\<^bsub>P\<^esub> (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> (q*l)) \<oplus>\<^bsub>P\<^esub> (\<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>)"
    using var_closed[OF carrier_is_subring] 
    by (subst p.nat_pow_mult, auto simp add:a_minus_def)
  also have "... = ((X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> r) \<otimes>\<^bsub>P\<^esub> (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> (q*l) \<oplus>\<^bsub>P\<^esub> (\<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>)) \<oplus>\<^bsub>P\<^esub> (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> r)) \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>"
    using var_pow_closed[OF carrier_is_subring]
    by algebra
  also have "... = (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> r) \<otimes>\<^bsub>P\<^esub> (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> (q*l) \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) \<oplus>\<^bsub>P\<^esub> (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> r) \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>"
    by algebra
  also have "... = (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> r) \<otimes>\<^bsub>P\<^esub> (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> (q*l) \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) \<oplus>\<^bsub>P\<^esub> ((X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> r) \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>)"
    unfolding a_minus_def using var_pow_closed[OF carrier_is_subring]
    by (subst p.a_assoc, auto)
  finally have a:"(X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> m \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) = 
    (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> r) \<otimes>\<^bsub>P\<^esub> (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> (q*l) \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) \<oplus>\<^bsub>P\<^esub> (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> r \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>)"
    (is "_ = ?x")
    by simp

  have xn_m_1_deg': "degree (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> n \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) = n" if n_gt_0: "n > 0" for n :: nat
  proof -
    have "degree (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> n \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) = degree (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> n \<oplus>\<^bsub>P\<^esub> \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>)"
      by (simp add:a_minus_def)
    also have "... = max (degree (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> n)) (degree (\<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>))"
      using 
        var_pow_closed[OF carrier_is_subring] var_pow_carr[OF carrier_is_subring] 
        var_pow_degree[OF carrier_is_subring] univ_poly_a_inv_degree[OF carrier_is_subring] 
        degree_one n_gt_0
      by (subst degree_add_distinct[OF carrier_is_subring], auto)
    also have "... = n"
      using var_pow_degree[OF carrier_is_subring] degree_one univ_poly_a_inv_degree[OF carrier_is_subring]
      by simp
    finally show ?thesis by simp
  qed

  have xn_m_1_deg: "degree (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> n \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) = n" for n :: nat
  proof (cases "n > 0")
    case True
    then show ?thesis using xn_m_1_deg' by auto
  next
    case False
    hence "n = 0" by simp
    hence "degree (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> n \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) = degree (\<zero>\<^bsub>P\<^esub>)"
      by (intro arg_cong[where f="degree"], simp)
    then show ?thesis using False by (simp add:univ_poly_zero)
  qed

  have b: "degree (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> l \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) > degree (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> r \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>)"
    using r_range unfolding xn_m_1_deg by simp

  have xn_m_1_carr: "X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> n \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub> \<in> carrier P" for n :: nat 
    unfolding a_minus_def
    by (intro p.a_closed var_pow_closed[OF carrier_is_subring], simp)

  have "?lhs \<longleftrightarrow> (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> l \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) pdivides\<^bsub>R\<^esub> ?x"
    by (subst a, simp) 
  also have "... \<longleftrightarrow> (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> l \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) pdivides\<^bsub>R\<^esub> (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> r \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>)"
    unfolding pdivides_def by (intro p.div_sum_iff c var_pow_closed[OF carrier_is_subring]
        xn_m_1_carr p.a_closed p.m_closed)
  also have "... \<longleftrightarrow> r = 0"
  proof (cases "r = 0")
    case True
    have "(X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> l \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) pdivides\<^bsub>R\<^esub> \<zero>\<^bsub>P\<^esub>" 
      unfolding univ_poly_zero
      by (intro pdivides_zero[OF carrier_is_subring] xn_m_1_carr) 
    also have "... = (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> r \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>)"
      by (simp add:a_minus_def True) algebra
    finally show ?thesis using True by simp
  next
    case False
    hence "degree (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> r \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) > 0" using xn_m_1_deg by simp 
    hence "X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> r \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub> \<noteq> []" by auto
    hence "\<not>(X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> l \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) pdivides\<^bsub>R\<^esub> (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> r \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>)"
      using pdivides_imp_degree_le[OF carrier_is_subring] b xn_m_1_carr
      by (metis le_antisym less_or_eq_imp_le nat_neq_iff)
    thus ?thesis using False by simp
  qed
  also have "... \<longleftrightarrow> l dvd m"
    unfolding m_def using r_range assms by auto
  finally show ?thesis
    by simp
qed

lemma gauss_poly_factor: 
  assumes "n > 0"
  shows "gauss_poly R n = (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> (n-1) \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) \<otimes>\<^bsub>P\<^esub> X\<^bsub>R\<^esub>" (is "_ = ?rhs")
proof -
  have a:"1 + (n - 1) = n"
    using assms by simp
  have "gauss_poly R n = X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> (1+(n-1)) \<ominus>\<^bsub>P\<^esub> X\<^bsub>R\<^esub>"
    unfolding gauss_poly_def by (subst a, simp)
  also have "... = (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> (n-1)) \<otimes>\<^bsub>P\<^esub> X\<^bsub>R\<^esub> \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub> \<otimes>\<^bsub>P\<^esub> X\<^bsub>R\<^esub>"
    using var_closed[OF carrier_is_subring] by simp 
  also have "... = ?rhs"
    unfolding a_minus_def using var_closed[OF carrier_is_subring] l_one
    by (subst p.l_distr, auto, algebra)
  finally show ?thesis by simp
qed

lemma var_neq_zero: "X\<^bsub>R\<^esub> \<noteq> \<zero>\<^bsub>P\<^esub>"
  by (simp add:var_def univ_poly_zero)

lemma var_pow_eq_one_iff: "X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> k = \<one>\<^bsub>P\<^esub> \<longleftrightarrow> k = (0::nat)"
proof (cases "k=0")
  case True
  then show ?thesis   using var_closed(1)[OF carrier_is_subring] by simp
next
  case False
  have "degree (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> k) = k "
    using var_pow_degree[OF carrier_is_subring] by simp
  also have "... \<noteq> degree (\<one>\<^bsub>P\<^esub>)" using False degree_one by simp
  finally have "degree (X\<^bsub>R\<^esub> [^]\<^bsub>P\<^esub> k) \<noteq> degree \<one>\<^bsub>P\<^esub>" by simp
  then show ?thesis by auto
qed

lemma gauss_poly_carr: "gauss_poly R n \<in> carrier P"
  using var_closed(1)[OF carrier_is_subring]
  unfolding gauss_poly_def by simp

lemma gauss_poly_degree:
  assumes "n > 1"
  shows "degree (gauss_poly R n) = n" 
proof -
  have "degree (gauss_poly R n) = max n 1"
    unfolding gauss_poly_def a_minus_def
    using var_pow_carr[OF carrier_is_subring] var_carr[OF carrier_is_subring] degree_var
    using var_pow_degree[OF carrier_is_subring] univ_poly_a_inv_degree[OF carrier_is_subring]
    using assms by (subst degree_add_distinct[OF carrier_is_subring], auto)
  also have "... = n" using assms by simp
  finally show ?thesis by simp
qed

lemma gauss_poly_not_zero: 
  assumes "n > 1"
  shows "gauss_poly R n \<noteq> \<zero>\<^bsub>P\<^esub>"
proof -
  have "degree (gauss_poly R n) \<noteq> degree ( \<zero>\<^bsub>P\<^esub>)"
    using assms by (subst gauss_poly_degree, simp_all add:univ_poly_zero)
  thus ?thesis by auto
qed

lemma gauss_poly_monic:
  assumes "n > 1" 
  shows "monic_poly R (gauss_poly R n)"
proof -
  have "monic_poly R (X [^]\<^bsub>P\<^esub> n)" 
    by (intro monic_poly_pow monic_poly_var) 
  moreover have "\<ominus>\<^bsub>P\<^esub> X \<in> carrier P" 
    using var_closed[OF carrier_is_subring] by simp
  moreover have "degree (\<ominus>\<^bsub>P\<^esub> X) < degree (X [^]\<^bsub>P\<^esub> n)" 
    using assms univ_poly_a_inv_degree[OF carrier_is_subring] var_closed[OF carrier_is_subring]
    using degree_var
    unfolding var_pow_degree[OF carrier_is_subring] by (simp)
  ultimately show ?thesis
    unfolding gauss_poly_def a_minus_def
    by (intro monic_poly_add_distinct, auto)
qed

lemma geom_nat: 
  fixes q :: nat
  fixes x :: "_ :: {comm_ring,monoid_mult}"
  shows "(x-1) * (\<Sum>i \<in> {..<q}. x^i) = x^q-1"
  by (induction q, simp, simp add:algebra_simps)

lemma lemma_3:
  fixes a :: int
  fixes l m :: nat
  assumes "l > 0" "a > 1"
  shows "(a ^ l - 1) dvd (a ^ m - 1) \<longleftrightarrow> l dvd m"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  define q where "q = m div l"
  define r where "r = m mod l"
  have m_def: "m = q * l + r" and r_range: "r < l" "r \<ge> 0"
    using assms by (auto simp add:q_def r_def) 

  have "a ^ (l * q) - 1 = (a ^ l) ^ q - 1"
    by (simp add: power_mult)
  also have "... = (a^l - 1) * (\<Sum>i \<in> {..<q}. (a^l)^i)"
    by (subst geom_nat[symmetric], simp) 
  finally have "a ^ (l * q) - 1 = (a^l - 1) * (\<Sum>i \<in> {..<q}. (a^l)^i)"
    by simp
  hence c:"a ^ l - 1 dvd a^ r * (a ^ (q * l) - 1)" by (simp add:mult.commute)

  have "a ^ m - 1 = a ^ (r + q * l) - 1"
    unfolding m_def using add.commute by metis
  also have "... = (a ^ r) * (a ^ (q*l)) -1"
    by (simp add: power_add)
  also have "... = ((a ^ r) * (a ^ (q*l) -1)) + (a ^ r) - 1" 
    by (simp add: right_diff_distrib)
  also have "... = (a ^ r) * (a ^ (q*l) - 1) + ((a ^ r) - 1)"
    by simp
  finally have a:"a ^ m - 1 = (a ^ r) * (a ^ (q*l) - 1) + ((a ^ r) - 1)" (is "_ = ?x")
    by simp

  have "?lhs \<longleftrightarrow> (a^l -1) dvd ?x"
    by (subst a, simp)
  also have "... \<longleftrightarrow> (a^l -1) dvd (a^r -1)"
    using c dvd_add_right_iff by auto
  also have "... \<longleftrightarrow> r = 0"
  proof
    assume "a ^ l - 1 dvd a ^ r - 1"
    hence "a ^ l - 1  \<le> a ^ r -1 \<or> r = 0 " 
      using assms r_range zdvd_not_zless by force
    moreover have "a ^ r < a^l" using assms r_range by simp
    ultimately show "r= 0"by simp
  next
    assume "r = 0"
    thus "a ^ l - 1 dvd a ^ r - 1" by simp
  qed
  also have "... \<longleftrightarrow> l dvd m"
    using r_def by auto
  finally show ?thesis by simp
qed

lemma div_gauss_poly_iff_1:
  assumes "m > 0" "n > 0" "a > 1"
  shows "gauss_poly R (a^n) pdivides\<^bsub>R\<^esub> gauss_poly R (a^m) \<longleftrightarrow> n dvd m" (is "?lhs=?rhs")
proof -
  have a:"a^m > 1" using assms one_less_power by blast
  hence a1: "a^m > 0" by linarith
  have b:"a^n > 1" using assms one_less_power by blast
  hence b1:"a^n > 0" by linarith

  have "?lhs \<longleftrightarrow>
    (X [^]\<^bsub>P\<^esub> (a^n-1) \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) \<otimes>\<^bsub>P\<^esub> X pdivides 
    (X [^]\<^bsub>P\<^esub> (a^m-1) \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) \<otimes>\<^bsub>P\<^esub> X"
    using  gauss_poly_factor a1 b1 by simp
  also have "... \<longleftrightarrow> (X [^]\<^bsub>P\<^esub> (a^n-1) \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) pdivides (X [^]\<^bsub>P\<^esub> (a^m-1) \<ominus>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>)"
    using var_closed[OF carrier_is_subring] a b var_neq_zero
    by (subst pdivides_mult_r, simp_all add:var_pow_eq_one_iff) 
  also have "... \<longleftrightarrow> a^n-1 dvd a^m-1"
    using b by (subst lemma_2, simp, simp) 
  also have "... \<longleftrightarrow> int (a^n-1) dvd int (a^m-1)"
    by (subst of_nat_dvd_iff, simp)
  also have "... \<longleftrightarrow> int a^n-1 dvd int a^m-1"
    using a b by (simp add:of_nat_diff)
  also have "... \<longleftrightarrow> n dvd m"
    using assms
    by (subst lemma_3, simp_all)
  finally show ?thesis by simp
qed

end


end