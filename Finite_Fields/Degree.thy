theory Degree
  imports "HOL-Algebra.Polynomial_Divisibility"
begin

lemma (in ring) degree_add_distinct:
  assumes "subring K R" 
  assumes "f \<in> carrier (K[X]) - {\<zero>\<^bsub>K[X]\<^esub>}"
  assumes "g \<in> carrier (K[X]) - {\<zero>\<^bsub>K[X]\<^esub>}"
  assumes "degree f \<noteq> degree g"
  shows "degree (f \<oplus>\<^bsub>K[X]\<^esub> g) = max (degree f) (degree g)"
  unfolding univ_poly_add using assms(2,3,4) 
  by (subst poly_add_degree_eq[OF assms(1)])
    (auto simp:univ_poly_carrier univ_poly_zero)

lemma (in domain) degree_mult:
  assumes "subring K R" 
  assumes "f \<in> carrier (K[X]) - {\<zero>\<^bsub>K[X]\<^esub>}"
  assumes "g \<in> carrier (K[X]) - {\<zero>\<^bsub>K[X]\<^esub>}"
  shows "degree (f \<otimes>\<^bsub>K[X]\<^esub> g) = degree f + degree g"
  unfolding univ_poly_mult using assms(2,3) 
  by (subst poly_mult_degree_eq[OF assms(1)])
    (auto simp:univ_poly_carrier univ_poly_zero)

lemma (in ring) degree_one:
  "degree (\<one>\<^bsub>K[X]\<^esub>) = 0"
  unfolding univ_poly_one by simp

lemma (in domain) pow_non_zero: "x \<in> carrier R \<Longrightarrow> x \<noteq> \<zero> \<Longrightarrow> x [^] (n :: nat) \<noteq> \<zero>"
  using integral by (induction n, auto) 

lemma (in domain) degree_pow:
  assumes "subring K R" 
  assumes "f \<in> carrier (K[X]) - {\<zero>\<^bsub>K[X]\<^esub>}"
  shows "degree (f [^]\<^bsub>K[X]\<^esub> n) = degree f * n"
proof -
  interpret p:domain "K[X]"
    using univ_poly_is_domain[OF assms(1)] by simp

  show ?thesis
  proof (induction n)
    case 0
    then show ?case by (simp add:univ_poly_one)
  next
    case (Suc n)
    have "degree (f [^]\<^bsub>K [X]\<^esub> Suc n) = degree (f [^]\<^bsub>K [X]\<^esub> n \<otimes>\<^bsub>K[X]\<^esub> f)"
      by simp
    also have "... = degree (f [^]\<^bsub>K [X]\<^esub> n) + degree f"
      using p.pow_non_zero assms(2)
      by (subst degree_mult[OF assms(1)], auto)
    also have "... = degree f * Suc n"
      by (subst Suc, simp)
    finally show ?case by simp
  qed
qed

lemma (in ring) degree_var:
  "degree (X\<^bsub>R\<^esub>) = 1"
  unfolding var_def by simp

lemma (in domain) var_carr:
  fixes n :: nat
  assumes "subring K R"
  shows "X\<^bsub>R\<^esub> \<in> carrier (K[X]) - {\<zero>\<^bsub>K [X]\<^esub>}"
proof -
  have "X\<^bsub>R\<^esub> \<in> carrier (K[X])" 
    using var_closed[OF assms(1)] by simp
  moreover have "X \<noteq> \<zero>\<^bsub>K [X]\<^esub>"
    unfolding var_def univ_poly_zero by simp
  ultimately show ?thesis by simp
qed

lemma (in domain) var_pow_carr:
  fixes n :: nat
  assumes "subring K R"
  shows "X\<^bsub>R\<^esub> [^]\<^bsub>K [X]\<^esub> n \<in> carrier (K[X]) - {\<zero>\<^bsub>K [X]\<^esub>}"
proof -
  interpret p:domain "K[X]"
    using univ_poly_is_domain[OF assms(1)] by simp

  have "X\<^bsub>R\<^esub> [^]\<^bsub>K [X]\<^esub> n \<in> carrier (K[X])" 
    using var_pow_closed[OF assms(1)] by simp
  moreover have "X \<noteq> \<zero>\<^bsub>K [X]\<^esub>"
    unfolding var_def univ_poly_zero by simp
  hence "X\<^bsub>R\<^esub> [^]\<^bsub>K [X]\<^esub> n \<noteq> \<zero>\<^bsub>K [X]\<^esub>"
    using var_closed(1)[OF assms(1)]
    by (intro p.pow_non_zero, auto)
  ultimately show ?thesis by simp
qed

lemma (in domain) var_pow_degree:
  fixes n :: nat
  assumes "subring K R"
  shows "degree (X\<^bsub>R\<^esub> [^]\<^bsub>K [X]\<^esub> n) = n"
  using var_carr[OF assms(1)] degree_var
  by (subst degree_pow[OF assms(1)], auto)

lemma (in domain) finprod_non_zero:
  assumes "finite A"
  assumes "f \<in> A \<rightarrow> carrier R - {\<zero>}"
  shows "(\<Otimes>i \<in> A. f i) \<in> carrier R - {\<zero>}"
  using assms
proof (induction A rule:finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x F)
  have "finprod R f (insert x F) = f x \<otimes> finprod R f F"
    using insert by (subst finprod_insert, simp_all add:Pi_def)
  also have "... \<in> carrier R-{\<zero>}"
    using integral insert by auto
  finally show ?case by simp
qed

lemma (in domain) degree_prod:
  assumes "finite A"
  assumes "subring K R" 
  assumes "f \<in> A \<rightarrow> carrier (K[X]) - {\<zero>\<^bsub>K[X]\<^esub>}"
  shows "degree (\<Otimes>\<^bsub>K[X]\<^esub>i \<in> A. f i) = (\<Sum>i \<in> A. degree (f i))"
  using assms
proof -
  interpret p:domain "K[X]"
    using univ_poly_is_domain[OF assms(2)] by simp

  show ?thesis
    using assms(1,3)
  proof (induction A rule: finite_induct)
    case empty
    then show ?case by (simp add:univ_poly_one)
  next
    case (insert x F)
    have "degree (finprod (K [X]) f (insert x F)) = degree (f x \<otimes>\<^bsub>K [X]\<^esub> finprod (K [X]) f F)"
      using insert by (subst p.finprod_insert, auto)
    also have "... = degree (f x) + degree (finprod (K [X]) f F)"
      using insert p.finprod_non_zero[OF insert(1)]
      by (subst degree_mult[OF assms(2)], simp_all) 
    also have "... = degree (f x) + (\<Sum>i \<in> F. degree (f i))"
      using insert by (subst insert(3), auto) 
    also have "... = (\<Sum>i \<in> insert x F. degree (f i))"
      using insert by simp
    finally show ?case by simp
  qed
qed

end