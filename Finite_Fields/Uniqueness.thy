theory Uniqueness
  imports
    Theorem_2
    Card_Irreducible_Polynomials
    SimpleFields
    RingIso_Ext
begin

definition char_iso :: "_ \<Rightarrow> int set \<Rightarrow> 'a" where "char_iso R x = the_elem (int_embed R ` x)"

lemma (in ring) char_iso:
  "char_iso R \<in> ring_iso (ZFact (int (char R))) (R\<lparr>carrier := char_subring R\<rparr>)"
proof -
  interpret h: ring_hom_ring "int_ring" "R" "int_embed R"
    using int_embed_ring_hom by simp

  have "a_kernel \<Z> R (int_embed R) = {x. int_embed R x = \<zero>}"
    unfolding a_kernel_def kernel_def by simp
  also have "... = {x. char R dvd x}"
    using embed_char_eq_0_iff by simp
  also have "... = PIdl\<^bsub>\<Z>\<^esub> (int (char R))" 
    unfolding cgenideal_def by auto
  also have "... = Idl\<^bsub>\<Z>\<^esub> {int (char R)}"
    using int.cgenideal_eq_genideal by simp
  finally have a:"a_kernel \<Z> R (int_embed R) = Idl\<^bsub>\<Z>\<^esub> {int (char R)}"
    by simp
  show  "?thesis"
    unfolding char_iso_def ZFact_def a[symmetric]
    by (intro h.FactRing_iso_set_aux)
qed

lemma ring_hom_cong:
  assumes "\<And>x. x \<in> carrier R \<Longrightarrow> f' x = f x" 
  assumes "ring R"
  assumes "f \<in> ring_hom R S"
  shows "f' \<in> ring_hom R S"
proof -
  interpret ring "R" using assms(2) by simp
  show ?thesis 
    using assms(1) ring_hom_memE[OF assms(3)]
    by (intro ring_hom_memI, auto) 
qed

lemma (in ring) quot_quot_hom: 
  assumes "ideal I R"
  assumes "ideal J R"
  assumes "I \<subseteq> J"
  shows "(\<lambda>x. (J <+>\<^bsub>R\<^esub> x)) \<in> ring_hom (R Quot I) (R Quot J)"  
proof (rule ring_hom_memI)
  interpret ji: ideal J R
    using assms(2) by simp
  interpret ii: ideal I R
    using assms(1) by simp

  have a:"J <+>\<^bsub>R\<^esub> I = J"
    using assms(3) unfolding set_add_def set_mult_def by auto

  show "J <+>\<^bsub>R\<^esub> x \<in> carrier (R Quot J)" if "x \<in> carrier (R Quot I)" for x
  proof -
    have " \<exists>y\<in>carrier R. x = I +> y" 
      using that unfolding FactRing_def A_RCOSETS_def' by simp
    then obtain y where y_def: "y \<in> carrier R" "x = I +> y"
      by auto
    have "J <+>\<^bsub>R\<^esub> (I +> y) = (J <+>\<^bsub>R\<^esub> I) +> y"
      using y_def(1) by (subst a_setmult_rcos_assoc) auto
    also have "... = J +> y" using a by simp
    finally have "J <+>\<^bsub>R\<^esub> (I +> y) = J +> y" by simp
    thus ?thesis
      using y_def unfolding FactRing_def A_RCOSETS_def' by auto 
  qed

  show "J <+>\<^bsub>R\<^esub> x \<otimes>\<^bsub>R Quot I\<^esub> y = (J <+>\<^bsub>R\<^esub> x) \<otimes>\<^bsub>R Quot J\<^esub> (J <+>\<^bsub>R\<^esub> y)"
    if "x \<in> carrier (R Quot I)" "y \<in> carrier (R Quot I)" for x y
  proof -
    have "\<exists>x1\<in>carrier R. x = I +> x1" "\<exists>y1\<in>carrier R. y = I +> y1" 
      using that unfolding FactRing_def A_RCOSETS_def' by auto
    then obtain x1 y1 
      where x1_def: "x1 \<in> carrier R" "x = I +> x1"
        and y1_def: "y1 \<in> carrier R" "y = I +> y1"
      by auto
    have "J <+>\<^bsub>R\<^esub> x \<otimes>\<^bsub>R Quot I\<^esub> y =  J <+>\<^bsub>R\<^esub> (I +> x1 \<otimes> y1)"
      using x1_def y1_def
      by (simp add: FactRing_def ii.rcoset_mult_add)
    also have "... = (J <+>\<^bsub>R\<^esub> I) +> x1 \<otimes> y1"
      using x1_def(1) y1_def(1)
      by (subst a_setmult_rcos_assoc) auto
    also have "... = J +> x1 \<otimes> y1"
      using a by simp
    also have "... = [mod J:] (J +> x1) \<Otimes> (J +> y1)" 
      using x1_def(1) y1_def(1) by (subst ji.rcoset_mult_add, auto)
    also have "... = [mod J:] ((J <+>\<^bsub>R\<^esub> I) +> x1) \<Otimes> ((J <+>\<^bsub>R\<^esub> I) +> y1)" 
      using a by simp
    also have "... = [mod J:] (J <+>\<^bsub>R\<^esub> (I +> x1)) \<Otimes> (J <+>\<^bsub>R\<^esub> (I +> y1))"
      using x1_def(1) y1_def(1)
      by (subst (1 2) a_setmult_rcos_assoc) auto
    also have "... = (J <+>\<^bsub>R\<^esub> x) \<otimes>\<^bsub>R Quot J\<^esub> (J <+>\<^bsub>R\<^esub> y)"
      using x1_def y1_def by (simp add: FactRing_def)
    finally show ?thesis by simp
  qed

  show "J <+>\<^bsub>R\<^esub> x \<oplus>\<^bsub>R Quot I\<^esub> y = (J <+>\<^bsub>R\<^esub> x) \<oplus>\<^bsub>R Quot J\<^esub> (J <+>\<^bsub>R\<^esub> y)"
    if "x \<in> carrier (R Quot I)" "y \<in> carrier (R Quot I)" for x y
  proof -
    have "\<exists>x1\<in>carrier R. x = I +> x1" "\<exists>y1\<in>carrier R. y = I +> y1" 
      using that unfolding FactRing_def A_RCOSETS_def' by auto
    then obtain x1 y1 
      where x1_def: "x1 \<in> carrier R" "x = I +> x1"
        and y1_def: "y1 \<in> carrier R" "y = I +> y1"
      by auto
    have "J <+>\<^bsub>R\<^esub> x \<oplus>\<^bsub>R Quot I\<^esub> y = J <+>\<^bsub>R\<^esub> ((I +> x1) <+>\<^bsub>R\<^esub> (I +> y1))"
      using x1_def y1_def by (simp add:FactRing_def)
    also have "... = J <+>\<^bsub>R\<^esub> (I +> (x1 \<oplus> y1))"
      using x1_def y1_def ii.a_rcos_sum by simp
    also have "... = (J <+>\<^bsub>R\<^esub> I) +> (x1 \<oplus> y1)"
      using x1_def y1_def by (subst a_setmult_rcos_assoc) auto
    also have "... = J +> (x1 \<oplus> y1)"
      using a by simp
    also have "... = ((J <+>\<^bsub>R\<^esub> I) +> x1) <+>\<^bsub>R\<^esub> ((J <+>\<^bsub>R\<^esub> I) +> y1)"
      using x1_def y1_def ji.a_rcos_sum a by simp
    also have "... =  J <+>\<^bsub>R\<^esub> (I +> x1) <+>\<^bsub>R\<^esub> (J <+>\<^bsub>R\<^esub> (I +> y1))" 
      using x1_def y1_def by (subst (1 2) a_setmult_rcos_assoc) auto
    also have "... = (J <+>\<^bsub>R\<^esub> x) \<oplus>\<^bsub>R Quot J\<^esub> (J <+>\<^bsub>R\<^esub> y)"
      using x1_def y1_def by (simp add:FactRing_def)
    finally show ?thesis by simp
  qed

  have "J <+>\<^bsub>R\<^esub> \<one>\<^bsub>R Quot I\<^esub> = J <+>\<^bsub>R\<^esub> (I +> \<one>)"
    unfolding FactRing_def by simp
  also have "... = (J <+>\<^bsub>R\<^esub> I) +> \<one>" 
    by (subst a_setmult_rcos_assoc) auto
  also have "... = J +> \<one>" using a by simp
  also have "... = \<one>\<^bsub>R Quot J\<^esub>"
    unfolding FactRing_def by simp
  finally show "J <+>\<^bsub>R\<^esub> \<one>\<^bsub>R Quot I\<^esub> = \<one>\<^bsub>R Quot J\<^esub>" 
    by simp
qed

lemma (in ring) quot_carr:
  assumes "ideal I R"
  assumes "y \<in> carrier (R Quot I)"
  shows "y \<subseteq> carrier R"
proof -
  interpret ideal I R using assms(1) by simp
  have "y \<in> a_rcosets I"
    using assms(2) unfolding FactRing_def by simp
  then obtain v where y_def: "y = I +> v" "v \<in> carrier R"
    unfolding A_RCOSETS_def' by auto
  have "I +> v \<subseteq> carrier R" 
    using y_def(2) a_r_coset_subset_G a_subset by presburger
  thus "y \<subseteq> carrier R" unfolding y_def by simp
qed

lemma (in ring) set_add_zero:
  assumes "A \<subseteq> carrier R"
  shows "{\<zero>} <+>\<^bsub>R\<^esub> A = A"
proof -
  have "{\<zero>} <+>\<^bsub>R\<^esub> A = (\<Union>x\<in>A. {\<zero> \<oplus> x})"
    using assms unfolding set_add_def set_mult_def by simp
  also have "... = (\<Union>x\<in>A. {x})"
    using assms by (intro arg_cong[where f="Union"] image_cong, auto)
  also have "... = A" by simp
  finally show ?thesis by simp
qed

lemma (in finite_field) eval_on_root_is_iso:
  defines "p \<equiv> char R"
  assumes "f \<in> carrier (poly_ring (ZFact p))" 
  assumes "pirreducible\<^bsub>(ZFact p)\<^esub> (carrier (ZFact p)) f" "order R = p^degree f"
  assumes "x \<in> carrier R" "eval (map (char_iso R) f) x = \<zero>"
  shows "ring_hom_ring (Rupt\<^bsub>(ZFact p)\<^esub> (carrier (ZFact p)) f) R 
    (\<lambda>g. the_elem ((\<lambda>g'. eval (map (char_iso R) g') x) ` g))"
proof -
  let ?P = "poly_ring (ZFact p)"

  have char_pos: "char R > 0"
    using finite_carr_imp_char_ge_0[OF finite_carrier] by simp

  have p_prime: "Factorial_Ring.prime p" 
    unfolding p_def 
    using characteristic_is_prime[OF char_pos] by simp

  interpret zf: finite_field "ZFact p"
    using zfact_prime_is_finite_field p_prime by simp
  interpret pzf: principal_domain "poly_ring (ZFact p)"
    using zf.univ_poly_is_principal[OF zf.carrier_is_subfield] by simp

  interpret i: ideal "(PIdl\<^bsub>?P\<^esub> f)" "?P" 
    by (intro pzf.cgenideal_ideal assms(2))
  have rupt_carr: "y \<in> carrier (Rupt\<^bsub>ZFact p\<^esub> (carrier (ZFact p)) f) \<Longrightarrow> y \<subseteq> carrier (poly_ring (ZFact p))" for y
    unfolding rupture_def using pzf.quot_carr i.ideal_axioms by simp

  have rupt_is_ring: "ring (Rupt\<^bsub>ZFact p\<^esub> (carrier (ZFact p)) f)"
    unfolding rupture_def by (intro i.quotient_is_ring)

  have "map (char_iso R) \<in> ring_iso ?P (poly_ring (R\<lparr>carrier := char_subring R\<rparr>))"
    using lift_iso_to_poly_ring[OF char_iso] zf.domain_axioms 
    using char_ring_is_subdomain subdomain_is_domain by (simp add:p_def)
  moreover have "(char_subring R)[X] = poly_ring (R \<lparr>carrier := char_subring R\<rparr>)"
    using univ_poly_consistent[OF char_ring_is_subring] by simp
  ultimately have "map (char_iso R) \<in> ring_hom ?P ((char_subring R)[X])"
    by (simp add:ring_iso_def)
  moreover have "(\<lambda>p. eval p x) \<in> ring_hom ((char_subring R)[X]) R"
    using eval_is_hom char_ring_is_subring assms(5) by simp
  ultimately have "(\<lambda>p. eval p x) \<circ> map (char_iso R) \<in> ring_hom ?P R"
    using ring_hom_trans by blast
  hence a:"(\<lambda>p. eval (map (char_iso R) p) x) \<in> ring_hom ?P R"
    by (simp add:comp_def)
  interpret h:ring_hom_ring "?P" "R" "(\<lambda>p. eval (map (char_iso R) p) x)"
    by (intro ring_hom_ringI2 zf.univ_poly_is_ring[OF zf.carrier_is_subring] a ring_axioms)

  let ?h = "(\<lambda>p. eval (map (char_iso R) p) x)"
  let ?J = "a_kernel (poly_ring (ZFact (int p))) R ?h"

  have "?h ` a_kernel (poly_ring (ZFact (int p))) R ?h \<subseteq> {\<zero>}"
    by auto
  moreover have "\<zero>\<^bsub>?P\<^esub> \<in> a_kernel (poly_ring (ZFact (int p))) R ?h" "?h \<zero>\<^bsub>?P\<^esub> = \<zero>" 
    unfolding a_kernel_def' by simp_all
  hence "{\<zero>} \<subseteq> ?h ` a_kernel (poly_ring (ZFact (int p))) R ?h"
    by simp
  ultimately have c:"?h ` a_kernel (poly_ring (ZFact (int p))) R ?h = {\<zero>}" by auto

  have d: "PIdl\<^bsub>?P\<^esub> f \<subseteq> a_kernel ?P R ?h"
  proof (rule subsetI) 
    fix y assume "y \<in> PIdl\<^bsub>?P\<^esub> f"
    then obtain y' where y'_def: "y' \<in> carrier ?P" "y = y' \<otimes>\<^bsub>?P\<^esub> f" 
      unfolding cgenideal_def by auto
    have "?h y = ?h (y' \<otimes>\<^bsub>?P\<^esub> f)" by (simp add:y'_def)
    also have "... = ?h y' \<otimes> ?h f"
      using y'_def assms(2) by simp
    also have "... = ?h y' \<otimes> \<zero>"
      using assms(6) by simp
    also have "... = \<zero>"
      using y'_def by simp
    finally have "?h y = \<zero>" by simp
    moreover have "y \<in> carrier ?P" using y'_def assms(2) by simp
    ultimately show "y \<in> a_kernel ?P R ?h"
      unfolding a_kernel_def kernel_def by simp
  qed

  have "(\<lambda>y. the_elem ((\<lambda>p. eval (map (char_iso R) p) x) ` y)) \<in> ring_hom (?P Quot ?J) R"
    using h.the_elem_hom by simp
  moreover have "(\<lambda>y. ?J <+>\<^bsub>?P\<^esub> y) 
    \<in> ring_hom (Rupt\<^bsub>(ZFact p)\<^esub> (carrier (ZFact p)) f) (?P Quot ?J)"
    unfolding rupture_def
    by (intro pzf.quot_quot_hom pzf.cgenideal_ideal assms(2) h.kernel_is_ideal d) 
  ultimately have "(\<lambda>y. the_elem (?h ` y)) \<circ> (\<lambda>y. ?J <+>\<^bsub>?P\<^esub> y)
    \<in> ring_hom (Rupt\<^bsub>(ZFact p)\<^esub> (carrier (ZFact p)) f) R"
    using ring_hom_trans by blast
  hence b:"(\<lambda>y. the_elem (?h ` (?J <+>\<^bsub>?P\<^esub> y))) \<in> ring_hom (Rupt\<^bsub>(ZFact p)\<^esub> (carrier (ZFact p)) f) R"
    by (simp add:comp_def)
  have "?h ` y = ?h ` (?J <+>\<^bsub>?P\<^esub> y)" if "y \<in> carrier (Rupt\<^bsub>ZFact p\<^esub> (carrier (ZFact p)) f)" for y
  proof -
    have y_range: "y \<subseteq> carrier ?P"
      using rupt_carr that by simp
    have "?h ` y = {\<zero>} <+>\<^bsub>R\<^esub> ?h ` y"
      using y_range h.hom_closed by (subst set_add_zero, auto)
    also have "... = ?h ` ?J <+>\<^bsub>R\<^esub> ?h ` y"
      by (subst c, simp)
    also have "... = ?h ` (?J <+>\<^bsub>?P\<^esub> y)"
      by (subst set_add_hom[OF a _ y_range], subst a_kernel_def') auto
    finally show ?thesis by simp
  qed
  hence "(\<lambda>y. the_elem (?h ` y)) \<in> ring_hom (Rupt\<^bsub>(ZFact p)\<^esub> (carrier (ZFact p)) f) R"
    by (intro ring_hom_cong[OF _ rupt_is_ring b] arg_cong[where f="the_elem"], simp)
  thus ?thesis
    by (intro ring_hom_ringI2 rupt_is_ring ring_axioms, simp)
qed

lemma (in domain) pdivides_consistent:
  assumes "subfield K R" "f \<in> carrier (K[X])" "g \<in> carrier (K[X])"
  shows "f pdivides g \<longleftrightarrow> f pdivides\<^bsub>R \<lparr> carrier := K \<rparr>\<^esub> g"
proof -
  have a:"subring K R" 
    using assms(1) subfieldE(1) by auto
  let ?S = "R \<lparr> carrier := K \<rparr>"
  have "f pdivides g \<longleftrightarrow> f divides\<^bsub>K[X]\<^esub> g"
    using pdivides_iff_shell[OF assms] by simp
  also have "... \<longleftrightarrow> (\<exists>x \<in> carrier (K[X]). f \<otimes>\<^bsub>K[X]\<^esub> x = g)"
    unfolding pdivides_def factor_def by auto
  also have "... \<longleftrightarrow> (\<exists>x \<in> carrier (poly_ring ?S). f \<otimes>\<^bsub>poly_ring ?S\<^esub> x = g)"
    using univ_poly_consistent[OF a] by simp
  also have "... \<longleftrightarrow> f divides\<^bsub>poly_ring ?S\<^esub> g"
    unfolding pdivides_def factor_def by auto
  also have "... \<longleftrightarrow> f pdivides\<^bsub>?S\<^esub> g"
    unfolding pdivides_def by simp
  finally show ?thesis by simp
qed

lemma (in domain) embed_hom:
  assumes "subring K R"
  shows "ring_hom_ring (K[X]) (poly_ring R) id"
proof (rule ring_hom_ringI)
  show "ring (K[X])"
    using univ_poly_is_ring[OF assms(1)] by simp
  show "ring (poly_ring R)"
    using univ_poly_is_ring[OF carrier_is_subring] by simp
  have "K \<subseteq> carrier R" 
    using subringE(1)[OF assms(1)] by simp
  thus "\<And>x. x \<in> carrier (K [X]) \<Longrightarrow> id x \<in> carrier (poly_ring R)"
    unfolding univ_poly_carrier[symmetric] polynomial_def by auto
  show "id (x \<otimes>\<^bsub>K [X]\<^esub> y) = id x \<otimes>\<^bsub>poly_ring R\<^esub> id y" 
    if "x \<in> carrier (K [X])" "y \<in> carrier (K [X])" for x y
    unfolding univ_poly_mult by simp
  show "id (x \<oplus>\<^bsub>K [X]\<^esub> y) = id x \<oplus>\<^bsub>poly_ring R\<^esub> id y"
    if "x \<in> carrier (K [X])" "y \<in> carrier (K [X])" for x y
    unfolding univ_poly_add by simp
  show "id \<one>\<^bsub>K [X]\<^esub> = \<one>\<^bsub>poly_ring R\<^esub>"
    unfolding univ_poly_one by simp
qed

lemma (in finite_field) find_root:
  assumes "subfield K R"
  assumes "monic_irreducible_poly (R \<lparr> carrier := K \<rparr>) f"
  assumes "order R = card K^degree f"
  obtains x where "eval f x = \<zero>" "x \<in> carrier R"
proof -
  define \<tau> :: "'a list \<Rightarrow> 'a list" where "\<tau> = id"
  let ?K = "R \<lparr> carrier := K \<rparr>"
  have "finite K" 
    using assms(1) by (intro finite_subset[OF _ finite_carrier], simp)
  hence fin_K: "finite (carrier (?K))" 
    by simp 
  interpret f: finite_field "?K"
    using assms(1) subfield_iff fin_K finite_fieldI by blast
  have b:"subring K R" 
    using assms(1) subfieldE(1) by blast
  interpret e: ring_hom_ring "(K[X])" "(poly_ring R)" "\<tau>"
    using embed_hom[OF b] by (simp add:\<tau>_def)

  have a: "card K^degree f > 1"
    using assms(3) finite_field_min_order by simp
  have "f \<in> carrier (poly_ring ?K)"
    using f.monic_poly_carr assms(2)
    unfolding monic_irreducible_poly_def by simp
  hence f_carr_2: "f \<in> carrier (K[X])"
    using univ_poly_consistent[OF b] by simp
  have f_carr: "f \<in> carrier (poly_ring R)"
    using e.hom_closed[OF f_carr_2] unfolding \<tau>_def by simp

  have gp_carr: "gauss_poly ?K (order ?K^degree f) \<in> carrier (K[X])"
    using f.gauss_poly_carr univ_poly_consistent[OF b] by simp

  have "gauss_poly ?K (order ?K^degree f) = gauss_poly ?K (card K^degree f)"
    by (simp add:Coset.order_def)
  also have "... =  X\<^bsub>?K\<^esub> [^]\<^bsub>poly_ring ?K\<^esub> card K ^ degree f \<ominus>\<^bsub>poly_ring ?K\<^esub> X\<^bsub>?K\<^esub>"
    unfolding gauss_poly_def by simp
  also have "... = X\<^bsub>R\<^esub> [^]\<^bsub>K[X]\<^esub> card K ^ degree f  \<ominus>\<^bsub>K[X]\<^esub> X\<^bsub>R\<^esub>"
    unfolding var_def using univ_poly_consistent[OF b] by simp
  also have "... = \<tau> (X\<^bsub>R\<^esub> [^]\<^bsub>K[X]\<^esub> card K ^ degree f  \<ominus>\<^bsub>K[X]\<^esub> X\<^bsub>R\<^esub>)"
    unfolding \<tau>_def by simp
  also have "... = gauss_poly R (card K^degree f)"
    unfolding gauss_poly_def a_minus_def using var_closed[OF b]
    by (simp add:e.hom_nat_pow, simp add:\<tau>_def)
  finally have gp_consistent: "gauss_poly ?K (order ?K^degree f) = gauss_poly R (card K^degree f)"
    by simp

  have deg_f: "degree f > 0" 
    using f.monic_poly_min_degree[OF assms(2)] by simp

  have "splitted f"
  proof (cases "degree f > 1")
    case True
  
    have "f pdivides\<^bsub>?K\<^esub> gauss_poly ?K (order ?K^degree f)"
      using f.div_gauss_poly_iff[OF deg_f assms(2)] by simp
    hence "f pdivides gauss_poly ?K (order ?K^degree f)"
      using pdivides_consistent[OF assms(1)] f_carr_2 gp_carr by simp
    hence "f pdivides gauss_poly R (card K^degree f)"
      using gp_consistent by simp
    moreover have "splitted (gauss_poly R (card K^degree f))" 
      unfolding assms(3)[symmetric] using gauss_poly_splitted by simp
    moreover have "gauss_poly R (card K^degree f) \<noteq> []" 
      using gauss_poly_not_zero a by (simp add: univ_poly_zero)
    ultimately show "splitted f"
      using pdivides_imp_splitted f_carr gauss_poly_carr by auto
  next
    case False
    hence "degree f = 1" using deg_f by simp
    thus ?thesis using f_carr degree_one_imp_splitted by auto
  qed
  hence "size (roots f) > 0" using deg_f unfolding splitted_def by simp
  then obtain x where x_def: "x \<in> carrier R" "is_root f x"
    using roots_mem_iff_is_root[OF f_carr]
    by (metis f_carr nonempty_has_size not_empty_rootsE)
  have "eval f x = \<zero>"
    using x_def is_root_def by blast
  thus ?thesis using x_def using that by simp
qed

lemma (in finite_field) find_iso_from_zfact:
  defines "p \<equiv> int (char R)"
  assumes "monic_irreducible_poly (ZFact p) f"
  assumes "order R = char R^degree f"
  shows "\<exists>\<phi>. \<phi> \<in> ring_iso (Rupt\<^bsub>(ZFact p)\<^esub> (carrier (ZFact p)) f) R"
proof -
  have char_pos: "char R > 0"
    using finite_carr_imp_char_ge_0[OF finite_carrier] by simp

  interpret zf: finite_field "ZFact p"
    unfolding p_def using zfact_prime_is_finite_field 
    using characteristic_is_prime[OF char_pos] by simp

  let ?f' = "map (char_iso R) f" 
  let ?F = "Rupt\<^bsub>(ZFact p)\<^esub> (carrier (ZFact p)) f"

  have "domain (R\<lparr>carrier := char_subring R\<rparr>)"
    using char_ring_is_subdomain subdomain_is_domain by simp 

  hence "monic_irreducible_poly (R \<lparr> carrier := char_subring R \<rparr>) ?f'" 
    using char_iso p_def
    by (intro monic_irreducible_poly_hom[OF assms(2) _ zf.domain_axioms]) auto
  moreover have "order R = card (char_subring R)^degree ?f'"
    using assms(3) unfolding char_def by simp
  ultimately obtain x where x_def: "eval ?f' x = \<zero>" "x \<in> carrier R"
    using find_root[OF char_ring_is_subfield[OF char_pos]] by blast
  let ?\<phi> = "(\<lambda>g. the_elem ((\<lambda>g'. eval (map (char_iso R) g') x) ` g))"
  interpret r: ring_hom_ring "?F" "R" "?\<phi>"
    using assms(2,3) unfolding monic_irreducible_poly_def monic_poly_def
    unfolding p_def by (intro eval_on_root_is_iso x_def, auto) 
  have a:"?\<phi> \<in> ring_hom ?F R" 
    using r.homh by auto

  have "field (Rupt\<^bsub>ZFact p\<^esub> (carrier (ZFact p)) f)"
    using assms(2)
    unfolding monic_irreducible_poly_def monic_poly_def
    by (subst zf.rupture_is_field_iff_pirreducible[OF zf.carrier_is_subfield], simp_all) 
  hence b:"inj_on ?\<phi> (carrier ?F)"
    using non_trivial_field_hom_is_inj[OF a _ field_axioms] by simp

  have "card (?\<phi> ` carrier ?F) = order ?F"
    using card_image[OF b] unfolding Coset.order_def by simp
  also have "... =  card (carrier (ZFact p))^degree f"
    using assms(2) zf.monic_poly_min_degree[OF assms(2)]
    unfolding monic_irreducible_poly_def monic_poly_def
    by (intro zf.rupture_order[OF zf.carrier_is_subfield]) auto
  also have "... = char R ^degree f"
    unfolding p_def by (subst card_zfact_carr[OF char_pos], simp)
  also have "... = card (carrier R)"
    using assms(3) unfolding Coset.order_def by simp  
  finally have "card (?\<phi> ` carrier ?F) = card (carrier R)" by simp
  moreover have "?\<phi> ` carrier ?F \<subseteq> carrier R"
    by (intro image_subsetI, simp)
  ultimately have "?\<phi> ` carrier ?F = carrier R"
    by (intro card_seteq finite_carrier, auto) 
  hence "bij_betw ?\<phi> (carrier ?F) (carrier R)"
    using b bij_betw_imageI by auto

  thus ?thesis
    unfolding ring_iso_def using a b by auto
qed

theorem 
  assumes "finite_field F\<^sub>1"
  assumes "finite_field F\<^sub>2"
  assumes "order F\<^sub>1 = order F\<^sub>2"
  shows "F\<^sub>1 \<simeq> F\<^sub>2"
proof -
  obtain n where o1: "order F\<^sub>1 = char F\<^sub>1^n" "n > 0"
    using finite_field.finite_field_order[OF assms(1)] by auto
  obtain m where o2: "order F\<^sub>2 = char F\<^sub>2^m" "m > 0"
    using finite_field.finite_field_order[OF assms(2)] by auto

  interpret f1: "finite_field" F\<^sub>1 using assms(1) by simp 
  interpret f2: "finite_field" F\<^sub>2 using assms(2) by simp 

  have char_pos: "char F\<^sub>1 > 0" "char F\<^sub>2 > 0"
    using f1.finite_carrier f1.finite_carr_imp_char_ge_0 
    using f2.finite_carrier f2.finite_carr_imp_char_ge_0 by auto
  hence char_prime: "Factorial_Ring.prime (char F\<^sub>1)" "Factorial_Ring.prime (char F\<^sub>2)"
    using f1.characteristic_is_prime f2.characteristic_is_prime by auto

  have "char F\<^sub>1^n = char F\<^sub>2^m" 
    using o1 o2 assms(3) by simp
  hence eq: "n = m" "char F\<^sub>1 = char F\<^sub>2"
    using char_prime char_pos o1(2) o2(2) prime_power_inj' by auto

  obtain p where p_def: "p = char F\<^sub>1" "p = char F\<^sub>2" 
    using eq by simp

  have p_prime: "Factorial_Ring.prime p" 
    unfolding p_def(1) using f1.characteristic_is_prime char_pos by simp

  interpret zf: finite_field "ZFact (int p)"
    using zfact_prime_is_finite_field p_prime o1(2) 
    using prime_nat_int_transfer by blast

  obtain f where f_def: "monic_irreducible_poly (ZFact (int p)) f" "degree f = n"
    using zf.exist_irred o1(2) by auto

  let ?F\<^sub>0  = "Rupt\<^bsub>(ZFact p)\<^esub> (carrier (ZFact p)) f" 

  obtain \<phi>\<^sub>1 where \<phi>\<^sub>1_def: "\<phi>\<^sub>1 \<in> ring_iso ?F\<^sub>0 F\<^sub>1"
    using f1.find_iso_from_zfact f_def o1 unfolding p_def by auto
  obtain \<phi>\<^sub>2 where \<phi>\<^sub>2_def: "\<phi>\<^sub>2 \<in> ring_iso ?F\<^sub>0 F\<^sub>2"
    using f2.find_iso_from_zfact f_def o2 unfolding p_def(2) eq(1) by auto

  have "?F\<^sub>0 \<simeq> F\<^sub>1" using \<phi>\<^sub>1_def is_ring_iso_def by auto
  moreover have "?F\<^sub>0 \<simeq> F\<^sub>2" using \<phi>\<^sub>2_def is_ring_iso_def by auto
  moreover have "field ?F\<^sub>0" 
    using f_def(1) zf.monic_poly_carr monic_irreducible_poly_def
    by (subst zf.rupture_is_field_iff_pirreducible[OF zf.carrier_is_subfield]) auto
  hence "ring ?F\<^sub>0" using field.is_ring by auto
  ultimately show ?thesis 
    using ring_iso_trans ring_iso_sym by blast
qed

end