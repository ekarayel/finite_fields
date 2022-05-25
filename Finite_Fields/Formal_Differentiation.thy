theory Formal_Differentiation
  imports "HOL-Algebra.Polynomial_Divisibility"
begin

definition int_embed :: "_ \<Rightarrow> int \<Rightarrow> _"  where
  "int_embed R k = add_pow R k \<one>\<^bsub>R\<^esub>"

definition pderiv ("pderiv\<index>") where 
  "pderiv\<^bsub>R\<^esub> x = ring.normalize R (
    map (\<lambda>i. int_embed R i \<otimes>\<^bsub>R\<^esub> ring.coeff R x i) (rev [1..<length x]))"

lemma (in ring) add_pow_consistent:
  fixes i :: "int"
  assumes "subring K R"
  assumes "k \<in> K"
  shows "add_pow R i k = add_pow (R \<lparr> carrier := K \<rparr>) i k" (is "?lhs = ?rhs")
proof -
  have a:"subgroup K (add_monoid R)" 
    using assms(1) subring.axioms by auto
  have "add_pow R i k = k [^]\<^bsub>add_monoid R\<lparr>carrier := K\<rparr>\<^esub> i" 
    using add.int_pow_consistent[OF a assms(2)] by simp
  also have "... = ?rhs"
    unfolding add_pow_def by simp
  finally show ?thesis by simp
qed

lemma (in ring) int_embed_consistent:
  assumes "subring K R"
  shows "int_embed R i = int_embed (R \<lparr> carrier := K \<rparr>) i"
proof -
  have a:"\<one> = \<one>\<^bsub>R \<lparr> carrier := K \<rparr>\<^esub>" by simp
  have b:"\<one>\<^bsub>R\<lparr>carrier := K\<rparr>\<^esub> \<in> K" 
    using assms subringE(3) by auto
  show ?thesis
    unfolding int_embed_def a using b add_pow_consistent[OF assms(1)] by simp
qed

lemma (in ring) int_embed_closed:
  "int_embed R k \<in> carrier R"
  unfolding int_embed_def using add.int_pow_closed by simp

lemma (in ring) int_embed_range:
  assumes "subring K R"
  shows "int_embed R k \<in> K"
proof -
  let ?R' =  "R \<lparr> carrier := K \<rparr>"
  interpret x:ring ?R'
    using subring_is_ring[OF assms] by simp
  have "int_embed R k = int_embed ?R' k"
    using int_embed_consistent[OF assms] by simp
  also have "...  \<in> K"
    using x.int_embed_closed by simp
  finally show ?thesis by simp
qed

lemma (in ring) int_embed_zero:
  "int_embed R 0 = \<zero>\<^bsub>R\<^esub>"
  by (simp add:int_embed_def add_pow_def)  

lemma (in ring) int_embed_one:
  "int_embed R 1 = \<one>\<^bsub>R\<^esub>"
  by (simp add:int_embed_def)  

lemma (in ring) int_embed_add:
  "int_embed R (x+y) = int_embed R x \<oplus>\<^bsub>R\<^esub> int_embed R y"
  by (simp add:int_embed_def add.int_pow_mult)  

lemma (in ring) int_embed_inv:
  "int_embed R (-x) = \<ominus>\<^bsub>R\<^esub> int_embed R x" (is "?lhs = ?rhs")
proof -
  have "?lhs = int_embed R (-x) \<oplus> (int_embed R x \<ominus> int_embed R x)"
    using int_embed_closed by simp
  also have "... = int_embed R (-x) \<oplus> int_embed R x \<oplus> (\<ominus> int_embed R x)"
    using int_embed_closed by (subst a_minus_def, subst a_assoc, auto)
  also have "... = int_embed R (-x +x) \<oplus> (\<ominus> int_embed R x)"
    by (subst int_embed_add, simp)
  also have "... = ?rhs"
    using int_embed_closed
    by (simp add:int_embed_zero)
  finally show ?thesis by simp
qed

lemma (in ring) int_embed_diff:
  "int_embed R (x-y) = int_embed R x \<ominus>\<^bsub>R\<^esub> int_embed R y" (is "?lhs = ?rhs")
proof -
  have "?lhs = int_embed R (x + (-y))"  by simp
  also have "... = ?rhs" by (subst int_embed_add, simp add:a_minus_def int_embed_inv)
  finally show ?thesis by simp
qed

lemma (in ring) int_embed_mult_aux:
  "int_embed R (x*int y) = int_embed R x \<otimes> int_embed R y"
proof (induction y)
  case 0
  then show ?case by (simp add:int_embed_closed int_embed_zero)
next
  case (Suc y)
  have "int_embed R (x * int (Suc y)) = int_embed R (x + x * int y)"
    by (simp add:algebra_simps) 
  also have "... = int_embed R x \<oplus> int_embed R (x * int y)"
    by (subst int_embed_add, simp)
  also have "... = int_embed R x \<otimes> \<one> \<oplus> int_embed R x \<otimes> int_embed R y"
    using int_embed_closed
    by (subst Suc, simp)
  also have "... = int_embed R x \<otimes> (int_embed R 1 \<oplus> int_embed R y)"
    using int_embed_closed by (subst r_distr, simp_all add:int_embed_one)
  also have "... = int_embed R x \<otimes> int_embed R (1+int y)"
    by (subst int_embed_add, simp)
  also have "... = int_embed R x \<otimes> int_embed R (Suc y)"
    by simp
  finally show ?case by simp
qed

lemma (in ring) int_embed_mult:
  "int_embed R (x*y) = int_embed R x \<otimes>\<^bsub>R\<^esub> int_embed R y"
proof (cases "y \<ge> 0")
  case True
  then obtain y' where y_def: "y = int y'" using nonneg_int_cases by auto
  have "int_embed R (x * y) = int_embed R (x * int y')"
    unfolding y_def by simp
  also have "... = int_embed R x \<otimes> int_embed R y'"
    by (subst int_embed_mult_aux, simp)
  also have "... = int_embed R x \<otimes> int_embed R y"
    unfolding y_def by simp
  finally show ?thesis by simp
next
  case False
  then obtain y' where y_def: "y = - int y'" 
    by (meson nle_le nonpos_int_cases)
  have "int_embed R (x * y) = int_embed R (-(x * int y'))"
    unfolding y_def by simp
  also have "... = \<ominus> (int_embed R (x * int y'))"
    by (subst int_embed_inv, simp)
  also have "... = \<ominus> (int_embed R x \<otimes> int_embed R y')"
    by (subst int_embed_mult_aux, simp)
  also have "... = int_embed R x \<otimes> \<ominus> int_embed R y'"
    using int_embed_closed by algebra
  also have "... = int_embed R x \<otimes> int_embed R (-y')"
    by (subst int_embed_inv, simp)
  also have "... = int_embed R x \<otimes> int_embed R y"
    unfolding y_def by simp
  finally show ?thesis by simp
qed

context domain
begin

lemma coeff_range:
  assumes "subring K R"
  assumes "f \<in> carrier (K[X])"
  shows "coeff f i \<in> K"
proof -
  have "coeff f i \<in> set f \<union> {\<zero>}"
    using coeff_img(3) by auto
  also have "... \<subseteq> K \<union> {\<zero>}"
    using assms(2) univ_poly_carrier polynomial_incl by blast
  also have "... \<subseteq> K" 
    using subringE[OF assms(1)] by simp
  finally show ?thesis by simp
qed

lemma pderiv_carr:
  assumes "subring K R"
  assumes "f \<in> carrier (K[X])"
  shows "pderiv f \<in> carrier (K[X])"
proof -
  have "int_embed R i \<otimes> coeff f i \<in> K" for i
    using coeff_range[OF assms] int_embed_range[OF assms(1)] subringE[OF assms(1)] by simp
  hence "polynomial K (pderiv f)"
    unfolding pderiv_def by (intro normalize_gives_polynomial, auto)
  thus ?thesis
    using univ_poly_carrier by auto
qed

lemma pderiv_coeff:
  assumes "subring K R"
  assumes "f \<in> carrier (K[X])"
  shows "coeff (pderiv f) k = int_embed R (Suc k) \<otimes> coeff f (Suc k)" (is "?lhs = ?rhs")
proof (cases "k + 1  < length f")
  case True
  define j where "j = length f - k - 2"
  define d where "d = map (\<lambda>i. int_embed R i \<otimes> local.coeff f i) (rev [1..<length f])"

  have a: "j+1 < length f" using True unfolding j_def by simp
  have b: "j < length [1..<length f]" using a by simp
  have c: "k < length d" unfolding d_def using True by simp
  have d: "degree d - k = j" unfolding d_def j_def by simp
  have e: "rev [Suc 0..<length f] ! j = length f - 1 - j" using b  by (subst rev_nth, auto)
  have f: "length f - j - 1 = k+1" unfolding j_def using True by simp

  have "coeff (pderiv f ) k = coeff (normalize d) k"
    unfolding pderiv_def d_def by simp
  also have "... = coeff d k"
    using normalize_coeff by simp
  also have "... = d ! j"
    using c d by (subst coeff_nth, auto)
  also have "... = int_embed R (length f - j - 1) \<otimes> local.coeff f (length f - j - 1)"
    using b e unfolding d_def by simp
  also have "... = ?rhs"
    using f by simp
  finally show ?thesis by simp
next
  case False
  hence "Suc k \<ge> length f"
    by simp
  hence a:"coeff f (Suc k) = \<zero>"
    using coeff_img by blast
  have b:"coeff (pderiv f) k = \<zero>"
    unfolding pderiv_def normalize_coeff[symmetric] using False
    by (intro coeff_length, simp)
  show ?thesis 
    using int_embed_range[OF carrier_is_subring] by (simp add:a b) 
qed


lemma pderiv_const:
  assumes "degree x = 0"
  shows "pderiv x = \<zero>\<^bsub>K[X]\<^esub>"
proof -
  consider
    (1) "length x = 0" | (2) "length x = 1"
    using assms by linarith
  then show ?thesis
  proof (cases)
    case 1
    then show ?thesis by (simp add:univ_poly_zero pderiv_def)
  next
    case 2
    then obtain y where "x = [y]" by (cases x, auto) 
    then show ?thesis by (simp add:univ_poly_zero pderiv_def)
  qed
qed

lemma pderiv_var:
  shows "pderiv X = \<one>\<^bsub>K[X]\<^esub>"
  unfolding var_def pderiv_def by (simp add:univ_poly_one int_embed_def)

lemma pderiv_zero:
  shows "pderiv \<zero>\<^bsub>K[X]\<^esub> = \<zero>\<^bsub>K[X]\<^esub>"
  unfolding pderiv_def univ_poly_zero by simp

lemma coeff_add:
  assumes "subring K R"
  assumes "f \<in> carrier (K[X])" "g \<in> carrier (K[X])"
  shows "coeff (f \<oplus>\<^bsub>K[X]\<^esub> g) i = coeff f i \<oplus>\<^bsub>R\<^esub> coeff g i"
proof -
  have a:"set f \<subseteq> carrier R"
    using assms(1,2) univ_poly_carrier subringE(1)[OF assms(1)] polynomial_incl by blast
  have b:"set g \<subseteq> carrier R" 
    using assms(1,3) univ_poly_carrier subringE(1)[OF assms(1)] polynomial_incl by blast
  show ?thesis
    unfolding univ_poly_add poly_add_coeff[OF a b] by simp
qed

lemma pderiv_add:
  assumes "subring K R"
  assumes [simp]: "f \<in> carrier (K[X])" "g \<in> carrier (K[X])"
  shows "pderiv (f \<oplus>\<^bsub>K[X]\<^esub> g) = pderiv f \<oplus>\<^bsub>K[X]\<^esub> pderiv g" (is "?lhs = ?rhs")
proof -
  interpret p: ring "(K[X])"
    using univ_poly_is_ring[OF assms(1)] by simp

  let ?n = "(\<lambda>i. int_embed R i)"

  have a[simp]:"?n k \<in> carrier R" for k
    using int_embed_range[OF carrier_is_subring] by auto
  have b[simp]:"coeff f k \<in> carrier R" if b1:"f \<in> carrier (K[X])" for k f
    using coeff_range[OF assms(1)] subringE(1)[OF assms(1)] b1 by auto

  have "coeff ?lhs i = coeff ?rhs i" for i
  proof -
    have "coeff ?lhs i = ?n (i+1) \<otimes> coeff (f \<oplus>\<^bsub>K [X]\<^esub> g) (i+1)"
      by (simp add: pderiv_coeff[OF assms(1)])
    also have "... = ?n (i+1) \<otimes> (coeff f (i+1) \<oplus> coeff g (i+1))"
      by (subst coeff_add[OF assms], simp)
    also have "... = ?n (i+1) \<otimes> coeff f (i+1) \<oplus> int_embed R (i+1) \<otimes> coeff g (i+1)"
      by (subst r_distr, simp_all)
    also have "... = coeff (pderiv f) i \<oplus> coeff (pderiv g) i"
      by (simp add: pderiv_coeff[OF assms(1)])
    also have "... = coeff (pderiv f \<oplus>\<^bsub>K [X]\<^esub> pderiv g) i"
      using pderiv_carr[OF assms(1)] by (subst coeff_add[OF assms(1)], auto) 
    finally show ?thesis by simp
  qed
  hence "coeff ?lhs = coeff ?rhs" by auto
  thus "?lhs = ?rhs"
    using pderiv_carr[OF assms(1)]
    by (subst coeff_iff_polynomial_cond[where K="K"])
      (simp_all add:univ_poly_carrier)+
qed

lemma pderiv_inv:
  assumes "subring K R"
  assumes [simp]: "f \<in> carrier (K[X])"
  shows "pderiv (\<ominus>\<^bsub>K[X]\<^esub> f) = \<ominus>\<^bsub>K[X]\<^esub> pderiv f" (is "?lhs = ?rhs")
proof -
  interpret p: cring "(K[X])"
    using univ_poly_is_cring[OF assms(1)] by simp

  have "pderiv (\<ominus>\<^bsub>K[X]\<^esub> f) = pderiv (\<ominus>\<^bsub>K[X]\<^esub> f) \<oplus>\<^bsub>K[X]\<^esub> \<zero>\<^bsub>K[X]\<^esub>"
    using pderiv_carr[OF assms(1)]
    by (subst p.r_zero, simp_all)
  also have "... = pderiv (\<ominus>\<^bsub>K[X]\<^esub> f) \<oplus>\<^bsub>K[X]\<^esub> (pderiv f \<ominus>\<^bsub>K[X]\<^esub> pderiv f)" 
    using pderiv_carr[OF assms(1)] by simp
  also have "... = pderiv (\<ominus>\<^bsub>K[X]\<^esub> f) \<oplus>\<^bsub>K[X]\<^esub> pderiv f \<ominus>\<^bsub>K[X]\<^esub> pderiv f" 
    using pderiv_carr[OF assms(1)] unfolding a_minus_def by (simp add:p.a_assoc)
  also have "... = pderiv (\<ominus>\<^bsub>K[X]\<^esub> f \<oplus>\<^bsub>K[X]\<^esub> f) \<ominus>\<^bsub>K[X]\<^esub> pderiv f" 
    by (subst pderiv_add[OF assms(1)], simp_all)
  also have "... = pderiv \<zero>\<^bsub>K[X]\<^esub> \<ominus>\<^bsub>K[X]\<^esub> pderiv f"
    by (subst p.l_neg, simp_all)
  also have "... = \<zero>\<^bsub>K[X]\<^esub> \<ominus>\<^bsub>K[X]\<^esub> pderiv f"
    by (subst pderiv_zero, simp)
  also have "... = \<ominus>\<^bsub>K[X]\<^esub> pderiv f"
    unfolding a_minus_def using pderiv_carr[OF assms(1)]
    by (subst p.l_zero, simp_all)
  finally show "pderiv (\<ominus>\<^bsub>K[X]\<^esub> f) = \<ominus>\<^bsub>K[X]\<^esub> pderiv f"
    by simp
qed


lemma coeff_mult:
  assumes "subring K R"
  assumes "f \<in> carrier (K[X])" "g \<in> carrier (K[X])"
  shows "coeff (f \<otimes>\<^bsub>K[X]\<^esub> g) i = (\<Oplus> k \<in> {..i}. (coeff f) k \<otimes> (coeff g) (i - k))"
proof -
  have a:"set f \<subseteq> carrier R"
    using assms(1,2) univ_poly_carrier subringE(1)[OF assms(1)] polynomial_incl by blast
  have b:"set g \<subseteq> carrier R" 
    using assms(1,3) univ_poly_carrier subringE(1)[OF assms(1)] polynomial_incl by blast
  show ?thesis
    unfolding univ_poly_mult poly_mult_coeff[OF a b] by simp
qed

lemma pderiv_mult:
  assumes "subring K R"
  assumes [simp]: "f \<in> carrier (K[X])" "g \<in> carrier (K[X])"
  shows "pderiv (f \<otimes>\<^bsub>K[X]\<^esub> g) = pderiv f \<otimes>\<^bsub>K[X]\<^esub> g \<oplus>\<^bsub>K[X]\<^esub> f \<otimes>\<^bsub>K[X]\<^esub> pderiv g" 
    (is "?lhs = ?rhs")
proof -
  interpret p: cring "(K[X])"
    using univ_poly_is_cring[OF assms(1)] by simp

  let ?n = "(\<lambda>i. int_embed R i)"

  have a[simp]:"?n k \<in> carrier R" for k 
    using int_embed_range[OF carrier_is_subring] by auto
  have b[simp]:"coeff f k \<in> carrier R" if b1:"f \<in> carrier (K[X])" for k f
    using coeff_range[OF assms(1)] subringE(1)[OF assms(1)] b1 by auto

  have "coeff ?lhs i = coeff ?rhs i" for i
  proof -
    have "coeff ?lhs i = ?n (i+1) \<otimes> coeff (f \<otimes>\<^bsub>K [X]\<^esub> g) (i+1)"
      using assms(2,3) by (simp add: pderiv_coeff[OF assms(1)])
    also have "... = ?n (i+1) \<otimes> (\<Oplus> k \<in> {..i+1}. coeff f k \<otimes> (coeff g (i + 1 - k)))"
      by (subst coeff_mult[OF assms], simp)
    also have "... = (\<Oplus> k \<in> {..i+1}. ?n (i+1) \<otimes> (coeff f k \<otimes> coeff g (i + 1 - k)))"
      by (intro finsum_rdistr, simp_all add:Pi_def) 
    also have "... = (\<Oplus> k \<in> {..i+1}. ?n k \<otimes> (coeff f k \<otimes> coeff g (i + 1 - k)) \<oplus>
     ?n (i+1-k) \<otimes> (coeff f k \<otimes> coeff g (i + 1 - k)))" 
      using int_embed_add[symmetric] 
      by (intro finsum_cong',simp_all add:l_distr[symmetric] of_nat_diff) 
    also have "... = (\<Oplus> k \<in> {..i+1}. ?n k \<otimes> coeff f k \<otimes> coeff g (i + 1 - k) \<oplus>
      coeff f k \<otimes> (?n (i+1-k) \<otimes> coeff g (i + 1 - k)))" 
      using Pi_def a b m_assoc m_comm
      by (intro finsum_cong' arg_cong2[where f="(\<oplus>)"], simp_all)
    also have "... = (\<Oplus> k \<in> {..i+1}. ?n k \<otimes> coeff f (k) \<otimes> coeff g (i + 1 - k)) \<oplus>
      (\<Oplus> k \<in> {..i+1}. coeff f k \<otimes> (?n (i+1-k) \<otimes> coeff g (i + 1 - k)))" 
      by (subst finsum_addf[symmetric], simp_all add:Pi_def) 
    also have "... = (\<Oplus> k \<in> insert 0 {1..i+1}. ?n k \<otimes> coeff f (k) \<otimes> coeff g (i + 1 - k)) \<oplus>
      (\<Oplus> k \<in> insert (i+1) {..i}. coeff f k \<otimes> (?n (i+1-k) \<otimes> coeff g (i + 1 - k)))" 
      using subringE(1)[OF assms(1)]
      by (intro arg_cong2[where f="(\<oplus>)"] finsum_cong', auto simp add:set_eq_iff)
    also have "... = (\<Oplus> k \<in> {1..i+1}. ?n k \<otimes> coeff f (k) \<otimes> coeff g (i + 1 - k)) \<oplus>
      (\<Oplus> k \<in> {..i}. coeff f k \<otimes> (?n (i + 1 -k) \<otimes> coeff g (i + 1 - k)))" 
      by (subst (1 2) finsum_insert, auto simp add:int_embed_zero)
    also have "... = (\<Oplus> k \<in> Suc ` {..i}. ?n k \<otimes> coeff f (k) \<otimes> coeff g (i + 1 - k)) \<oplus>
      (\<Oplus> k \<in> {..i}. coeff f k \<otimes> (?n (i + 1 -k) \<otimes> coeff g (i + 1- k)))" 
      by (intro arg_cong2[where f="(\<oplus>)"] finsum_cong', simp_all add:Pi_def atMost_atLeast0)
    also have "... = (\<Oplus> k \<in> {..i}. ?n (k+1) \<otimes> coeff f (k+1) \<otimes> coeff g (i - k)) \<oplus>
      (\<Oplus> k \<in> {..i}. coeff f k \<otimes> (?n (i+1-k) \<otimes> coeff g (i+1- k)))" 
      by (subst finsum_reindex, auto)
    also have "... = (\<Oplus> k \<in> {..i}. coeff (pderiv f) k \<otimes> coeff g (i - k)) \<oplus>
      (\<Oplus> k \<in> {..i}. coeff f k \<otimes> coeff (pderiv g) (i - k))" 
      using Suc_diff_le
      by (subst (1 2) pderiv_coeff[OF assms(1)], auto intro!: finsum_cong')
    also have "... = coeff (pderiv f \<otimes>\<^bsub>K[X]\<^esub> g) i \<oplus> coeff (f \<otimes>\<^bsub>K[X]\<^esub> pderiv g) i"
      using pderiv_carr[OF assms(1)]
      by (subst (1 2) coeff_mult[OF assms(1)], auto)
    also have "... = coeff ?rhs i" 
      using pderiv_carr[OF assms(1)]
      by (subst coeff_add[OF assms(1)], auto)
    finally show ?thesis by simp
  qed

  hence "coeff ?lhs = coeff ?rhs" by auto
  thus "?lhs = ?rhs"
    using pderiv_carr[OF assms(1)]
    by (subst coeff_iff_polynomial_cond[where K="K"])
     (simp_all add:univ_poly_carrier)
qed

lemma pderiv_pow:
  assumes "n > (0 :: nat)"
  assumes "subring K R"
  assumes [simp]: "f \<in> carrier (K[X])"
  shows "pderiv (f [^]\<^bsub>K[X]\<^esub> n) = int_embed (K[X]) n \<otimes>\<^bsub>K[X]\<^esub> f [^]\<^bsub>K[X]\<^esub> (n-1) \<otimes>\<^bsub>K[X]\<^esub> pderiv f" 
    (is "?lhs = ?rhs")
proof -
  interpret p: cring "(K[X])"
    using univ_poly_is_cring[OF assms(2)] by simp

  let ?n = "\<lambda>n. int_embed (K[X]) n"

  have [simp]: "?n i \<in> carrier (K[X])" for i 
    using p.int_embed_range[OF p.carrier_is_subring] by simp

  obtain m where n_def: "n = Suc m" using assms(1) lessE by blast
  have  "pderiv (f [^]\<^bsub>K[X]\<^esub> (m+1)) = ?n (m+1) \<otimes>\<^bsub>K[X]\<^esub> f [^]\<^bsub>K[X]\<^esub> m \<otimes>\<^bsub>K[X]\<^esub> pderiv f" 
  proof (induction m)
    case 0
    then show ?case 
      using pderiv_carr[OF assms(2)] assms(3) p.int_embed_one by simp
  next
    case (Suc m)
    have "pderiv (f [^]\<^bsub>K [X]\<^esub> (Suc m + 1)) = pderiv (f [^]\<^bsub>K [X]\<^esub> (m+1) \<otimes>\<^bsub>K[X]\<^esub> f) "
      by simp
    also have "... = pderiv (f [^]\<^bsub>K [X]\<^esub> (m+1)) \<otimes>\<^bsub>K[X]\<^esub> f \<oplus>\<^bsub>K[X]\<^esub> f [^]\<^bsub>K [X]\<^esub> (m+1) \<otimes>\<^bsub>K[X]\<^esub> pderiv f"
      using assms(3) by (subst pderiv_mult[OF assms(2)], auto)
    also have "... = (?n (m+1) \<otimes>\<^bsub>K [X]\<^esub> f [^]\<^bsub>K [X]\<^esub> m \<otimes>\<^bsub>K [X]\<^esub> pderiv f) \<otimes>\<^bsub>K[X]\<^esub> f 
      \<oplus>\<^bsub>K[X]\<^esub> f [^]\<^bsub>K [X]\<^esub> (m+1) \<otimes>\<^bsub>K[X]\<^esub> pderiv f"
      by (subst Suc(1), simp)  
    also have "... = ?n (m+1) \<otimes>\<^bsub>K[X]\<^esub> (f [^]\<^bsub>K [X]\<^esub> (m+1) \<otimes>\<^bsub>K[X]\<^esub> pderiv f) 
             \<oplus>\<^bsub>K[X]\<^esub> \<one>\<^bsub>K [X]\<^esub> \<otimes>\<^bsub>K[X]\<^esub> (f [^]\<^bsub>K [X]\<^esub> (m+1) \<otimes>\<^bsub>K[X]\<^esub> pderiv f)"
      using assms(3) pderiv_carr[OF assms(2)]
      apply (intro arg_cong2[where f="(\<oplus>\<^bsub>K[X]\<^esub>)"])
      apply (simp add:p.m_assoc)
       apply (simp add:p.m_comm)
      by simp
    also have "... = (?n (m+1) \<oplus>\<^bsub>K[X]\<^esub> \<one>\<^bsub>K [X]\<^esub>) \<otimes>\<^bsub>K [X]\<^esub> (f [^]\<^bsub>K [X]\<^esub> (m+1) \<otimes>\<^bsub>K [X]\<^esub> pderiv f)"
      using assms(3) pderiv_carr[OF assms(2)] 
      by (subst p.l_distr[symmetric], simp_all)
    also have "... = (\<one>\<^bsub>K [X]\<^esub> \<oplus>\<^bsub>K[X]\<^esub> ?n (m+1)) \<otimes>\<^bsub>K [X]\<^esub> (f [^]\<^bsub>K [X]\<^esub> (m+1) \<otimes>\<^bsub>K [X]\<^esub> pderiv f)"
      using assms(3) pderiv_carr[OF assms(2)]
      by (subst p.a_comm, simp_all)
    also have "... = ?n (1+ Suc m) \<otimes>\<^bsub>K [X]\<^esub> f [^]\<^bsub>K [X]\<^esub> (Suc m) \<otimes>\<^bsub>K [X]\<^esub> pderiv f"
      using assms(3) pderiv_carr[OF assms(2)] of_nat_add
      apply (subst (2) of_nat_add, subst p.int_embed_add)
      by (simp add:p.m_assoc p.int_embed_one) 
    finally show ?case by simp
  qed
  thus "?thesis" using n_def by auto
qed

lemma pderiv_var_pow:
  assumes "n > (0::nat)"
  assumes "subring K R"
  shows "pderiv (X [^]\<^bsub>K[X]\<^esub> n) = int_embed (K[X]) n \<otimes>\<^bsub>K[X]\<^esub> X [^]\<^bsub>K[X]\<^esub> (n-1)"
proof -
  interpret p: cring "(K[X])"
    using univ_poly_is_cring[OF assms(2)] by simp

  have [simp]: "int_embed (K[X]) i \<in> carrier (K[X])" for i
    using p.int_embed_range[OF p.carrier_is_subring] by simp

  show ?thesis
    using var_closed[OF assms(2)] pderiv_var[where K="K"] pderiv_carr[OF assms(2)]
    by (subst pderiv_pow[OF assms(1,2)], simp, simp)
qed

lemma int_embed_consistent_with_poly_of_const:
  assumes "subring K R"
  shows "int_embed (K[X]) m = poly_of_const (int_embed R m)"
proof -
  define K' where "K' = R \<lparr> carrier := K \<rparr>"
  interpret p: cring "(K[X])"
    using univ_poly_is_cring[OF assms] by simp
  interpret d: domain "K'"
    unfolding K'_def
    using assms(1) subdomainI' subdomain_is_domain by simp
  interpret h: ring_hom_ring  "K'" "K[X]" "poly_of_const"
    unfolding K'_def
    using canonical_embedding_ring_hom[OF assms(1)] by simp

  define n where "n=nat (abs m)"

  have a1: "int_embed (K[X]) (int n) = poly_of_const (int_embed K' n)"
  proof (induction n)
    case 0
    then show ?case by (simp add:d.int_embed_zero p.int_embed_zero)
  next
    case (Suc n)
    then show ?case
      using d.int_embed_closed
      by (simp add:p.int_embed_add p.int_embed_one d.int_embed_add d.int_embed_one)
  qed
  also have "... = poly_of_const (int_embed R n)"
    unfolding K'_def using int_embed_consistent[OF assms] by simp
  finally have a: "int_embed (K[X]) (int n) = poly_of_const (int_embed R (int n))" by simp

  have "int_embed (K[X]) (-(int n)) = poly_of_const (int_embed K' (- (int n)))"
    using d.int_embed_closed a1 by (simp add: p.int_embed_inv d.int_embed_inv)
  also have "... = poly_of_const (int_embed R (- (int n)))"
    unfolding K'_def using int_embed_consistent[OF assms] by simp
  finally have b: "int_embed (K[X]) (-int n) = poly_of_const (int_embed R (-int n))" by simp

  show ?thesis
    using a b n_def by (cases "m \<ge> 0", simp, simp)
qed

end

end