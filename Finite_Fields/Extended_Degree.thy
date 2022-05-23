theory Extended_Degree
  imports "HOL-Algebra.Polynomial_Divisibility" "HOL-Library.Extended_Real"
begin

definition ext_degree where
  "ext_degree f = (if f = [] then (-\<infinity>) else ereal (degree f))"

context domain
begin 
lemma poly_mult_degree_ext:
  assumes "f \<in> carrier (poly_ring R)"
  assumes "g \<in> carrier (poly_ring R)"
  shows "ext_degree (f \<otimes>\<^bsub>poly_ring R\<^esub> g) = ext_degree f + ext_degree g"
proof -
  consider (1) "f \<noteq> [] \<and> g \<noteq> []" | (2) "f = []" | (3) "g = []" by blast
  then show ?thesis
  proof (cases)
    case 1
    hence "degree  (f \<otimes>\<^bsub>poly_ring R\<^esub> g) = degree f + degree g"
      unfolding univ_poly_mult using assms
      by (subst poly_mult_degree_eq[OF carrier_is_subring]) (auto simp:univ_poly_carrier)
    moreover have "f \<otimes>\<^bsub>poly_ring R\<^esub> g \<noteq> []"
      unfolding univ_poly_mult
      using poly_mult_integral[OF carrier_is_subring] 1 univ_poly_carrier assms by blast
    ultimately show ?thesis using 1 by (simp add:ext_degree_def)
  next
    case 2
    then show ?thesis
      by (simp add:univ_poly_mult ext_degree_def)
  next
    case 3
    moreover have "polynomial\<^bsub>R\<^esub> (carrier R) f"
      using assms univ_poly_carrier by auto
    hence "set f \<subseteq> carrier R"
      by (auto simp add: polynomial_def) 
    hence "poly_mult f [] = []"
      by (rule poly_mult_zero)
    ultimately show ?thesis 
      by (simp add:univ_poly_mult ext_degree_def)
  qed
qed


lemma poly_add_degree_ext:
  assumes "f \<in> carrier (poly_ring R)"
  assumes "g \<in> carrier (poly_ring R)"
  assumes "ext_degree f \<noteq> ext_degree g"
  shows "ext_degree (f \<oplus>\<^bsub>poly_ring R\<^esub> g) = max (ext_degree f) (ext_degree g)"
  sorry

lemma poly_neg_degree_ext:
  assumes "f \<in> carrier (poly_ring R)"
  shows "ext_degree (\<ominus>\<^bsub>poly_ring R\<^esub> f) = ext_degree f"
  sorry

lemma poly_prod_degree_ext:
  assumes "finite A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<in> carrier (poly_ring R)"
  shows 
    "ext_degree (finprod (poly_ring R) f A) = (\<Sum>x \<in> A. ext_degree (f x))"
  using assms
proof (induct A rule:finite_induct)
  case empty
  interpret x:cring "poly_ring R"
    using carrier_is_subring domain.univ_poly_is_cring domain_axioms by auto
  show ?case by (simp add:univ_poly_one ext_degree_def)
next
  case (insert x F)
  interpret x:cring "poly_ring R"
    using carrier_is_subring domain.univ_poly_is_cring domain_axioms by auto
  have a:"f \<in> F \<rightarrow> carrier (poly_ring R)"
    using insert by blast
  have b:"f x \<in> carrier (poly_ring R)"
    using insert by blast

  have "ext_degree (finprod (poly_ring R) f (insert x F)) = 
    ext_degree (f x \<otimes>\<^bsub>poly_ring R\<^esub> finprod (poly_ring R) f F)"
    using a b insert by simp
  also have "... = ext_degree (f x) + ext_degree (finprod (poly_ring R) f F)"
    using b insert
    by (subst poly_mult_degree_ext) auto
  also have "... = ext_degree (f x) + (\<Sum>y \<in> F. ext_degree (f y))"
    using insert
    by (subst insert(3)) auto
  also have "... = (\<Sum>y \<in> (insert x F). ext_degree (f y))" using insert by simp
  finally show ?case by simp
qed

lemma one_deg:
  "ext_degree \<one>\<^bsub>poly_ring R\<^esub> = 0"
  by (simp add:univ_poly_one ext_degree_def)

lemma var_deg:
  "ext_degree X = 1"
  by (simp add:var_def ext_degree_def)

lemma pow_deg:
  "ext_degree (X [^]\<^bsub>poly_ring R\<^esub> n) = ereal (n::nat)"
proof -
  have a:"degree (X [^]\<^bsub>poly_ring R\<^esub> n) = n"
    using var_closed(1)[OF carrier_is_subring]
    by (subst polynomial_pow_degree) (auto simp add:var_def)
  have "X [^]\<^bsub>poly_ring R\<^esub> n \<noteq> []" 
  proof (cases "n > 0")
    case True
    have "X [^]\<^bsub>poly_ring R\<^esub> n = [] \<Longrightarrow> degree [] = n"
      using a by simp
    hence "X [^]\<^bsub>poly_ring R\<^esub> n \<noteq> []" using True by auto
    then show ?thesis by simp
  next
    case False
    hence "n = 0" by simp
    then show ?thesis by (simp add:var_def univ_poly_one)
  qed
  thus ?thesis using a
    by (simp add:ext_degree_def)
qed

lemma degree_eq_ext_degree:
  assumes "ext_degree x = ereal (real n)" 
  shows "degree x = n"
  using assms
  by (cases "x = []", auto simp:ext_degree_def)

end

end