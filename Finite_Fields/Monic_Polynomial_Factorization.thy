theory Monic_Polynomial_Factorization
imports
  Divisibility_Ext
  "HOL-Algebra.Polynomial_Divisibility"
begin

lemma (in domain) finprod_mult_of:
  assumes "finite A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<in> carrier (mult_of R)"
  shows "finprod R f A = finprod (mult_of R) f A"
  using assms by (induction A rule:finite_induct, auto) 

definition pmult :: "_ \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> nat" ("pmult\<index>") 
  where "pmult\<^bsub>R\<^esub> d p = multiplicity (mult_of (poly_ring R)) d p" 

definition monic_poly :: "_ \<Rightarrow> 'a list \<Rightarrow> bool"
  where "monic_poly R f = (f \<noteq> [] \<and> lead_coeff f = \<one>\<^bsub>R\<^esub> \<and> f \<in> carrier (poly_ring R))"

definition monic_irreducible_poly where
  "monic_irreducible_poly R f = (monic_poly R f \<and> pirreducible\<^bsub>R\<^esub> (carrier R) f)"

context 
  fixes R (structure)
  assumes a:"field R"
begin

interpretation field "R" using a by simp
interpretation p:principal_domain "poly_ring R"
  by (simp add: carrier_is_subfield univ_poly_is_principal)

private abbreviation P where "P \<equiv> poly_ring R"
private abbreviation M where "M \<equiv> mult_of (poly_ring R)"

lemma lead_coeff_carr:
  assumes "x \<in> carrier M"
  shows "lead_coeff x \<in> carrier R - {\<zero>}"
proof (cases x)
  case Nil
  then show ?thesis using assms by (simp add:univ_poly_zero)
next
  case (Cons a list)
  hence a: "polynomial (carrier R) (a # list)"
    using assms univ_poly_carrier carrier_is_subring by auto
  have "lead_coeff x = a"
    using Cons by simp
  also have "a \<in> carrier R - {\<zero>}"
    using lead_coeff_not_zero a by simp
  finally show ?thesis by simp
qed

lemma lead_coeff_poly_of_const:
  assumes "r \<noteq> \<zero>"
  shows "lead_coeff (poly_of_const r) = r"
  using assms
  by (simp add:poly_of_const_def)

lemma lead_coeff_mult:
  assumes "f \<in> carrier M"
  assumes "g \<in> carrier M"
  shows "lead_coeff (f \<otimes>\<^bsub>P\<^esub> g) = lead_coeff f \<otimes> lead_coeff g"
  unfolding univ_poly_mult using assms univ_poly_carrier[where R="R" and K="carrier R"]
  by (subst poly_mult_lead_coeff[OF carrier_is_subring]) 
   (simp_all add:univ_poly_zero)


lemma monic_poly_one: "monic_poly R \<one>\<^bsub>P\<^esub>"
proof -
  have "\<one>\<^bsub>P\<^esub> \<in> carrier P"
    by simp
  thus ?thesis
    by (simp add:univ_poly_one monic_poly_def)
qed

lemma monic_poly_carr:
  assumes "monic_poly R f"
  shows "f \<in> carrier P"
  using assms unfolding monic_poly_def by simp

lemma monic_poly_carr_2:
  assumes "monic_poly R f"
  shows "f \<in> carrier M"
  using assms unfolding monic_poly_def by (simp add:univ_poly_zero)

lemma monic_poly_mult:
  assumes "monic_poly R f"
  assumes "monic_poly R g"
  shows "monic_poly R (f \<otimes>\<^bsub>P\<^esub> g)"
proof -
  have "lead_coeff (f \<otimes>\<^bsub>P\<^esub> g) = lead_coeff f \<otimes>\<^bsub>R\<^esub> lead_coeff g"
    using assms monic_poly_carr_2
    by (subst lead_coeff_mult) auto
  also have "... =  \<one>"
    using assms unfolding monic_poly_def by simp
  finally have "lead_coeff (f \<otimes>\<^bsub>P\<^esub> g) = \<one>\<^bsub>R\<^esub>" by simp
  moreover have "(f \<otimes>\<^bsub>P\<^esub> g) \<in> carrier M"
    using monic_poly_carr_2 assms by blast
  ultimately show ?thesis
    by (simp add:monic_poly_def univ_poly_zero)
qed

lemma monic_poly_pow:
  assumes "monic_poly R f"
  shows "monic_poly R (f [^]\<^bsub>P\<^esub> (n::nat))"
  using assms by (induction n, auto simp:monic_poly_one monic_poly_mult)

lemma monic_poly_prod:
  assumes "finite A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> monic_poly R (f x)"
  shows "monic_poly R (finprod P f A)"
  using assms 
proof (induction A rule:finite_induct)
  case empty
  then show ?case by (simp add:monic_poly_one)
next
  case (insert x F)
  have a: "f \<in> F \<rightarrow> carrier P" 
    using insert monic_poly_carr by simp
  have b: "f x \<in> carrier P" 
    using insert monic_poly_carr by simp
  have "monic_poly R (f x \<otimes>\<^bsub>P\<^esub> finprod P f F)"
    using insert by (intro monic_poly_mult) auto
  thus ?case
    using insert a b by (subst p.finprod_insert, auto)
qed

lemma monic_poly_not_assoc:
  assumes "monic_poly R f"
  assumes "monic_poly R g"
  assumes "f \<sim>\<^bsub>M\<^esub> g"
  shows "f = g"
proof -
  obtain u where u_def: "f = g \<otimes>\<^bsub>P\<^esub> u" "u \<in> Units M"
    using p.mult_of.associatedD2 assms monic_poly_carr_2 by blast

  hence "u \<in> Units P" by simp
  then obtain v where v_def: "u = [v]" "v \<noteq> \<zero>\<^bsub>R\<^esub>" "v \<in> carrier R"
    using univ_poly_carrier_units by auto

  have "\<one> = lead_coeff f"
    using assms(1) by (simp add:monic_poly_def)
  also have  "... = lead_coeff (g \<otimes>\<^bsub>P\<^esub> u)"
    by (simp add:u_def)
  also have "... = lead_coeff g \<otimes> lead_coeff u"
    using assms(2) monic_poly_carr_2 v_def u_def(2)
    by (subst lead_coeff_mult, auto simp add:univ_poly_zero) 
  also have "... = lead_coeff g \<otimes> v"
    using v_def by simp
  also have "... = v"
    using assms(2) v_def(3) by (simp add:monic_poly_def)
  finally have "\<one> = v" by simp
  hence "u = \<one>\<^bsub>P\<^esub>" 
    using v_def by (simp add:univ_poly_one)
  thus "f = g"
    using u_def assms monic_poly_carr by simp
qed


lemma monic_poly_span: "{x. x \<in> carrier M \<and> irreducible M x} \<subseteq> 
  (\<Union> (assocs M ` {p. monic_irreducible_poly R p}))"  (is "?lhs \<subseteq> ?rhs")
proof (rule subsetI)
  fix x 
  assume a:"x \<in> ?lhs"
  define z where "z = poly_of_const (inv (lead_coeff x))"
  define y where "y = x \<otimes>\<^bsub>P\<^esub> z"

  have x_carr: "x \<in> carrier M" using a by simp

  hence lx_ne_0: "lead_coeff x \<noteq> \<zero>" 
    and lx_unit: "lead_coeff x \<in> Units R" 
    using lead_coeff_carr[OF x_carr] by (auto simp add:field_Units)
  have lx_inv_ne_0: "inv (lead_coeff x) \<noteq> \<zero>"  
    using lx_unit 
    by (metis Units_closed Units_r_inv r_null zero_not_one)
  have lx_inv_carr: "inv (lead_coeff x) \<in> carrier R" 
    using lx_unit by simp

  have "z \<in> carrier P"
    using lx_inv_carr poly_of_const_over_carrier unfolding z_def by auto
  moreover have "z \<noteq> \<zero>\<^bsub>P\<^esub>" 
    using lx_inv_ne_0
    by (simp add:z_def poly_of_const_def univ_poly_zero)
  ultimately have z_carr: "z \<in> carrier M" by simp
  have z_unit: "z \<in> Units M"
    using lx_inv_ne_0 lx_inv_carr
    by (simp add:univ_poly_carrier_units z_def poly_of_const_def)
  have y_exp: "y = x \<otimes>\<^bsub>M\<^esub> z" 
    by (simp add:y_def)
  hence y_carr: "y \<in> carrier M" 
    using x_carr z_carr p.mult_of.m_closed by simp

  have "irreducible M y"
    unfolding y_def using a z_unit z_carr
    by (intro p.mult_of.irreducible_prod_rI, auto)
  moreover have "lead_coeff y = \<one>\<^bsub>R\<^esub>" 
    unfolding y_def using x_carr z_carr lx_inv_ne_0 lx_unit
    by (simp add: lead_coeff_mult z_def lead_coeff_poly_of_const)
  hence "monic_poly R y"
    using y_carr unfolding monic_poly_def by (simp add:univ_poly_zero) 
  ultimately have "y \<in> {p. monic_irreducible_poly R p}"
    using p.irreducible_mult_imp_irreducible y_carr
    by (simp add:monic_irreducible_poly_def ring_irreducible_def)
  moreover have "y \<sim>\<^bsub>M\<^esub> x" 
    by (intro p.mult_of.associatedI2[OF z_unit] y_def x_carr)
  hence "x \<sim>\<^bsub>M\<^esub> y"
    using x_carr y_carr by (simp add:p.mult_of.associated_sym)
  hence "x \<in> assocs M y" 
    using x_carr y_carr by (simp add:eq_closure_of_def elem_def)
  ultimately show "x \<in> ?rhs" by auto
qed

lemma factor_monic_poly:
  assumes "monic_poly R a"
  shows "a = (\<Otimes>\<^bsub>P\<^esub>d\<in>{d. monic_irreducible_poly R d \<and> d pdivides a}. d [^]\<^bsub>P\<^esub> multiplicity M d a)"
    (is "?lhs = ?rhs")
proof -
  define S where "S = {d. monic_irreducible_poly R d}"
  let ?T = "{d. monic_irreducible_poly R d \<and> d pdivides a}"

  have sp_1: "S \<subseteq> {x \<in> carrier M. irreducible M x}" 
    unfolding S_def monic_irreducible_poly_def ring_irreducible_def using monic_poly_carr
    by (intro subsetI, simp add: p.irreducible_imp_irreducible_mult) 
  have sp_2: "x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x \<sim>\<^bsub>M\<^esub> y \<Longrightarrow> x = y" for x y 
    unfolding S_def monic_irreducible_poly_def
    using monic_poly_not_assoc by simp
  have sp_3: "{x \<in> carrier M. irreducible M x} \<subseteq> (\<Union> ((assocs M) ` S))" 
    unfolding S_def using monic_poly_span by simp
  have sp_4: "a \<in> carrier M" 
    using assms monic_poly_carr_2 unfolding monic_irreducible_poly_def by simp

  have b_1:"monic_irreducible_poly R x \<Longrightarrow> x \<in> carrier M" for x 
    unfolding monic_irreducible_poly_def using monic_poly_carr_2 by simp
  have b_2:"monic_irreducible_poly R x \<Longrightarrow> irreducible M x" for x
    unfolding monic_irreducible_poly_def ring_irreducible_def 
    by (simp add: monic_poly_carr p.irreducible_imp_irreducible_mult)
  have b_3:"monic_irreducible_poly R x \<Longrightarrow> x \<in> carrier P" for x 
    unfolding monic_irreducible_poly_def using monic_poly_carr by simp

  have a_carr: "a \<in> carrier P - {\<zero>\<^bsub>P\<^esub>}" 
    using sp_4 by simp

  have "?T = {d. monic_irreducible_poly R d \<and> d divides\<^bsub>P\<^esub> a}" 
    by ( simp add:pdivides_def)
  also have "... = {d. monic_irreducible_poly R d \<and> d divides\<^bsub>M\<^esub> a}" 
    using p.divides_imp_divides_mult[OF b_3 a_carr]
    by (intro order_antisym subsetI, simp, simp) 
  also have "... = {d \<in> S. multiplicity M d a > 0}"
    unfolding S_def using p.mult_of.multiplicity_gt_0_iff[OF b_1 b_2 sp_4]
    by (intro order_antisym subsetI, auto)

  finally have t:"?T = {d \<in> S. multiplicity M d a > 0}" by simp

  have fin_T: "finite ?T"
    unfolding t by (intro p.mult_of.split_factors(1)[OF sp_1 sp_2 sp_3 sp_4]) auto

  have a:"x [^]\<^bsub>P\<^esub> (n::nat) \<in> carrier M" if a1:"monic_irreducible_poly R x" for x n
  proof -
    have "monic_poly R (x [^]\<^bsub>P\<^esub> n)"
      using a1 monic_poly_pow unfolding monic_irreducible_poly_def by auto
    thus "x [^]\<^bsub>P\<^esub> n \<in> carrier M"
      using monic_poly_carr_2 by simp
  qed

  have "?lhs \<sim>\<^bsub>M\<^esub> finprod M (\<lambda>d. d [^]\<^bsub>M\<^esub> (multiplicity M d a)) ?T"
    unfolding t by (intro p.mult_of.split_factors(2)[OF sp_1 sp_2 sp_3 sp_4], simp_all)
  also have "... = finprod M (\<lambda>d. d [^]\<^bsub>P\<^esub> (multiplicity M d a)) ?T"
    by (simp add:nat_pow_mult_of)
  also have "... = ?rhs"
    using fin_T a by (subst p.finprod_mult_of, auto) 
  finally have "?lhs \<sim>\<^bsub>M\<^esub> ?rhs" by simp
  moreover have "monic_poly R ?rhs" 
    using fin_T 
    by (intro monic_poly_prod monic_poly_pow, auto simp:monic_irreducible_poly_def) 
  ultimately show ?thesis
    using monic_poly_not_assoc assms monic_irreducible_poly_def
  by blast
qed

lemma degree_monic_poly':
  assumes "monic_poly R f"
  shows "sum' (\<lambda>d. pmult\<^bsub>R\<^esub> d f * degree d) {d. monic_irreducible_poly R d} = degree f" 
  sorry

lemma monic_poly_min_degree:
  assumes "monic_irreducible_poly R f"
  shows  "degree f \<ge> 1"
  using assms unfolding monic_irreducible_poly_def monic_poly_def
  by (intro pirreducible_degree[OF carrier_is_subfield]) auto

lemma degree_one_monic_poly:
  "monic_irreducible_poly R f \<and> degree f = 1 \<longleftrightarrow> (\<exists>x \<in> carrier R. f = [\<one>\<^bsub>R\<^esub>, \<ominus>\<^bsub>R\<^esub>x])"
  sorry

lemma multiplicity_ge_iff:
  assumes "monic_irreducible_poly R d"
  shows "pmult\<^bsub>R\<^esub> d f \<ge> k  \<longleftrightarrow> d [^]\<^bsub>P\<^esub> k pdivides\<^bsub>R\<^esub> f"
  sorry

lemma multiplicity_ge_1_iff_pdivides:
  assumes "monic_irreducible_poly R d"
  shows "pmult\<^bsub>R\<^esub> d f \<ge> 1  \<longleftrightarrow> d pdivides\<^bsub>R\<^esub> f"
  using multiplicity_ge_iff[OF assms, where k="1"] sorry
  

lemma divides_monic_poly:
  assumes "monic_poly R f" "monic_poly R g"
  assumes "\<And>d. monic_irreducible_poly R d \<Longrightarrow> pmult\<^bsub>R\<^esub> d f \<le> pmult\<^bsub>R\<^esub> d g" 
  shows "f pdivides\<^bsub>R\<^esub> g"
  sorry



end

end