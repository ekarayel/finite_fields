section \<open>Introduction\<close>

text \<open>The classification consists of three theorems:
\begin{itemize}
\item \emph{Existence}: For each prime power $p^n$ there exists a finite field of that size. This is shown at the conclusion of Section~\ref{sec:card_irred}.
\item \emph{Uniqueness}: Any two finite fields of the same size are isomorphic. This is shown at the conclusion of Section~\ref{sec:uniq}.
\item \emph{Completeness}: A finite fields size must be a prime power. This is shown in Section~\ref{sec:ring_char}.
\end{itemize}
\<close>

section \<open>Preliminary Results\<close>

theory Finite_Fields_Preliminary_Results
  imports "HOL-Algebra.Polynomial_Divisibility"
begin

subsection \<open>Summation in the discrete topology\<close>

text \<open>The following lemmas transfer the corresponding result from the summation over finite sets
to summation over functions which vanish outside of a finite set. The reason the latter concept
of summation is useful in this entry, stems from the fact that elements of a factorial monoid
can be represented as products over a possibly infinite set of irreducible factors, where 
only finitely many occur with a non-zero power.\<close>

lemma sum'_subtractf_nat:
  fixes f :: "'a \<Rightarrow> nat"
  assumes "finite {i \<in> A. f i \<noteq> 0}"
  assumes "\<And>i. i \<in> A \<Longrightarrow> g i \<le> f i"
  shows "sum' (\<lambda>i. f i - g i) A = sum' f A - sum' g A"
    (is "?lhs = ?rhs")
proof -
  have c:"finite {i \<in> A. g i \<noteq> 0}"
    using assms(2)
    by (intro finite_subset[OF _ assms(1)] subsetI, force) 
  let ?B = "{i \<in> A. f i \<noteq> 0 \<or> g i \<noteq> 0}"

  have b:"?B = {i \<in> A. f i \<noteq> 0} \<union> {i \<in> A. g i \<noteq> 0}"
    by (auto simp add:set_eq_iff)
  have a:"finite ?B"
    using assms(1) c by (subst b, simp)
  have "?lhs = sum' (\<lambda>i. f i - g i) ?B"
    by (intro sum.mono_neutral_cong_right', simp_all)
  also have "... = sum (\<lambda>i. f i - g i) ?B"
    by (intro sum.eq_sum a) 
  also have "... = sum f ?B - sum g ?B"
    using assms(2) by (subst sum_subtractf_nat, auto)
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

subsection \<open>Factorization\<close>

notation carrier ("(_\<^sup>C)" [90] 90)

text \<open>This section contains additional results building on top of the development in
@{theory "HOL-Algebra.Divisibility"}.\<close>

definition factor_mset where "factor_mset G x = 
  (THE f. (\<exists> as. f = fmset G as \<and> wfactors G as x \<and> set as \<subseteq> carrier G))"

text \<open>In @{theory "HOL-Algebra.Divisibility"} it is already verified that the multiset representing
the factorization of an element of a factorial monoid into irreducible factors is well-defined.
With these results it is then possible to define @{term "factor_mset"} and show its properties,
without referring to a factorization in list form first.\<close>

definition multiplicity where
  "multiplicity G d g = Max {(n::nat). (d [^]\<^bsub>G\<^esub> n) divides\<^bsub>G\<^esub> g}"

definition canonical_irreducibles where 
  "canonical_irreducibles G A = (
    A \<subseteq> {a. a \<in> carrier G \<and> irreducible G a} \<and>
    (\<forall>x y. x \<in> A \<longrightarrow> y \<in> A \<longrightarrow> x \<sim>\<^bsub>G\<^esub> y \<longrightarrow> x = y) \<and>
    (\<forall>x \<in> carrier G. irreducible G x \<longrightarrow> (\<exists>y \<in> A. x \<sim>\<^bsub>G\<^esub> y)))"

text \<open>A set of irreducible elements that contains exactly one element from each equivalence class
of an irreducible element formed by association, is called a set of 
@{term "canonical_irreducibles"}. An example is the set of monic irreducible polynomials as
representatives of all irreducible polynomials.\<close>

context factorial_monoid
begin

lemma assoc_as_fmset_eq:
  assumes "wfactors G as a"
    and "wfactors G bs b"
    and "a \<in> carrier G"
    and "b \<in> carrier G"
    and "set as \<subseteq> carrier G"
    and "set bs \<subseteq> carrier G"
  shows "a \<sim> b \<longleftrightarrow> (fmset G as = fmset G bs)"
proof -
  have "a \<sim> b \<longleftrightarrow> (a divides b \<and> b divides a)"
    by (simp add:associated_def)
  also have "... \<longleftrightarrow> (fmset G as \<subseteq># fmset G bs \<and> fmset G bs \<subseteq># fmset G as)"
    using divides_as_fmsubset assms by blast
  also have "... \<longleftrightarrow> (fmset G as = fmset G bs)" by auto
  finally show ?thesis by simp
qed

lemma factor_mset_aux_1:
  assumes "a \<in> carrier G" "set as \<subseteq> carrier G" "wfactors G as a"
  shows "factor_mset G a = fmset G as"
proof -
  define H where "H = {as. wfactors G as a \<and> set as \<subseteq> carrier G}"
  have b:"as \<in> H"
    using H_def assms by simp

  have c: "x \<in> H \<Longrightarrow> y \<in> H  \<Longrightarrow> fmset G x = fmset G y" for x y
    unfolding H_def using assoc_as_fmset_eq associated_refl assms by blast 

  have "factor_mset G a = (THE f. \<exists>as \<in> H. f= fmset G as)"
    by (simp add:factor_mset_def H_def, metis) 

  also have "... = fmset G as"
    using b 
    apply (intro the1_equality) apply auto
    using c by blast
  finally have "factor_mset G a = fmset G as" by simp

  thus ?thesis
    using b unfolding H_def by auto
qed

lemma factor_mset_aux:
  assumes "a \<in> carrier G"
  shows "\<exists>as. factor_mset G a = fmset G as \<and> wfactors G as a \<and> 
    set as \<subseteq> carrier G"
proof -
  obtain as where as_def: "wfactors G as a" "set as \<subseteq> carrier G"
    using wfactors_exist assms by blast
  thus ?thesis using factor_mset_aux_1 assms by blast
qed

lemma factor_mset_set:
  assumes "a \<in> carrier G"
  assumes "x \<in># factor_mset G a" 
  obtains y where "y \<in> carrier G" "irreducible G y" "assocs G y = x" 
proof -
  obtain as where as_def: "factor_mset G a = fmset G as \<and> wfactors G as a \<and> set as \<subseteq> carrier G"
    using factor_mset_aux assms by blast
  hence "x \<in># fmset G as"
    using assms by simp
  hence "x \<in> assocs G ` set as"
    using assms as_def by (simp add:fmset_def)
  hence "\<exists>y. y \<in> set as \<and> x = assocs G y"
    by auto
  moreover have "y \<in> set as \<Longrightarrow> y \<in> carrier G \<and> irreducible G y" for y
    using as_def wfactors_def by (simp add: wfactors_def) auto
  ultimately show ?thesis
    using that by blast
qed

lemma factor_mset_mult:
  assumes "a \<in> carrier G" "b \<in> carrier G"
  shows "factor_mset G (a \<otimes> b) = factor_mset G a + factor_mset G b"
proof -
  obtain as where as_def: "factor_mset G a = fmset G as \<and> wfactors G as a \<and> set as \<subseteq> carrier G"
    using factor_mset_aux assms by blast
  obtain bs where bs_def: "factor_mset G b = fmset G bs \<and> wfactors G bs b \<and> set bs \<subseteq> carrier G"
    using factor_mset_aux assms(2) by blast
  have "a \<otimes> b \<in> carrier G" using assms by auto
  then obtain cs where cs_def:
    "factor_mset G (a \<otimes> b) = fmset G cs \<and> wfactors G cs (a \<otimes> b) \<and> set cs \<subseteq> carrier G"
    using factor_mset_aux assms  by blast
  have "fmset G cs = fmset G as + fmset G bs"
    using as_def bs_def cs_def assms 
    by (intro  mult_wfactors_fmset[where a="a" and b="b"]) auto
  thus ?thesis
    using as_def bs_def cs_def by auto
qed

lemma factor_mset_unit: "factor_mset G \<one> = {#}"
proof -
  have "factor_mset G \<one> = factor_mset G (\<one> \<otimes> \<one>)"
    by simp
  also have "... = factor_mset G \<one> + factor_mset G \<one>"
    by (intro factor_mset_mult, auto)
  finally show "factor_mset G \<one> = {#}"
    by simp
qed

lemma factor_mset_irred: 
  assumes "x \<in> carrier G" "irreducible G x"
  shows "factor_mset G x = image_mset (assocs G) {#x#}"
proof -
  have "wfactors G [x] x"
    using assms by (simp add:wfactors_def)
  hence "factor_mset G x = fmset G [x]"
    using factor_mset_aux_1 assms by simp
  also have "... = image_mset (assocs G) {#x#}"
    by (simp add:fmset_def)
  finally show ?thesis by simp
qed

lemma factor_mset_divides:
  assumes "a \<in> carrier G" "b \<in> carrier G"
  shows "a divides b \<longleftrightarrow> factor_mset G a \<subseteq># factor_mset G b"
proof -
  obtain as where as_def: "factor_mset G a = fmset G as \<and> wfactors G as a \<and> set as \<subseteq> carrier G"
    using factor_mset_aux assms by blast
  obtain bs where bs_def: "factor_mset G b = fmset G bs \<and> wfactors G bs b \<and> set bs \<subseteq> carrier G"
    using factor_mset_aux assms(2) by blast
  hence "a divides b \<longleftrightarrow> fmset G as \<subseteq># fmset G bs"
    using as_def bs_def assms
    by (intro divides_as_fmsubset) auto
  also have "... \<longleftrightarrow> factor_mset G a \<subseteq># factor_mset G b"
    using as_def bs_def by simp
  finally show ?thesis by simp
qed

lemma factor_mset_sim:
  assumes "a \<in> carrier G" "b \<in> carrier G"
  shows "a \<sim> b \<longleftrightarrow> factor_mset G a = factor_mset G b"
  using factor_mset_divides assms
  by (simp add:associated_def) auto

lemma factor_mset_prod:
  assumes "finite A"
  assumes "f ` A \<subseteq> carrier G" 
  shows "factor_mset G (\<Otimes>a \<in> A. f a) = (\<Sum>a \<in> A. factor_mset G (f a))"
  using assms
proof (induction A rule:finite_induct)
  case empty
  then show ?case by (simp add:factor_mset_unit)
next
  case (insert x F)
  have "factor_mset G (finprod G f (insert x F)) = factor_mset G (f x \<otimes> finprod G f F)"
    using insert by (subst finprod_insert) auto
  also have "... = factor_mset G (f x) + factor_mset G (finprod G f F)"
    using insert by (intro factor_mset_mult finprod_closed) auto
  also have "... = factor_mset G (f x) + (\<Sum>a \<in> F. factor_mset G (f a))"
    using insert by simp
  also have "... = (\<Sum>a\<in>insert x F. factor_mset G (f a))"
    using insert by simp
  finally show ?case by simp
qed

lemma factor_mset_pow:
  assumes "a \<in> carrier G"
  shows "factor_mset G (a [^] n) = repeat_mset n (factor_mset G a)"
proof (induction n)
  case 0
  then show ?case by (simp add:factor_mset_unit)
next
  case (Suc n)
  have "factor_mset G (a [^] Suc n) = factor_mset G (a [^] n \<otimes> a)"
    by simp
  also have "... = factor_mset G (a [^] n) + factor_mset G a"
    using assms by (intro factor_mset_mult) auto
  also have "... = repeat_mset n (factor_mset G a) + factor_mset G a"
    using Suc by simp
  also have "... = repeat_mset (Suc n) (factor_mset G a)"
    by simp
  finally show ?case by simp
qed

lemma image_mset_sum:
  assumes "finite F"
  shows "image_mset h (\<Sum>x \<in> F. f x) = (\<Sum>x \<in> F. image_mset h (f x))"
  using assms
  by (induction F rule:finite_induct, simp, simp)

lemma decomp_mset: "(\<Sum>x\<in>set_mset R. replicate_mset (count R x) x) = R"
  by (rule multiset_eqI, simp add:count_sum count_eq_zero_iff)

lemma factor_mset_count:
  assumes "a \<in> carrier G" "d \<in> carrier G" "irreducible G d"
  shows "count (factor_mset G a) (assocs G d) = multiplicity G d a"
proof -
  have a:"count (factor_mset G a) (assocs G d) \<ge> m \<longleftrightarrow> d [^] m divides a"
    (is "?lhs \<longleftrightarrow> ?rhs") for m
  proof -
    have "?lhs \<longleftrightarrow> replicate_mset m (assocs G d) \<subseteq># factor_mset G a"
      by (simp add:count_le_replicate_mset_subset_eq)
    also have "... \<longleftrightarrow> factor_mset G (d [^] m) \<subseteq># factor_mset G a"
      using assms(2,3) by (simp add:factor_mset_pow factor_mset_irred)
    also have "... \<longleftrightarrow> ?rhs"
      using assms(1,2) by (subst factor_mset_divides) auto
    finally show ?thesis by simp
  qed

  define M where "M = {(m::nat). d [^] m divides a}"

  have M_alt: "M = {m. m \<le> count (factor_mset G a) (assocs G d)}"
    using a by (simp add:M_def)

  hence "Max M = count (factor_mset G a) (assocs G d)"
    by (intro Max_eqI, auto)
  thus ?thesis
    unfolding multiplicity_def M_def by auto
qed

lemma multiplicity_ge_iff:
  assumes "d \<in> carrier G" "irreducible G d" "a \<in> carrier G"
  shows "multiplicity G d a \<ge> k \<longleftrightarrow> d [^]\<^bsub>G\<^esub> k divides\<^bsub>G\<^esub> a" (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  have "?lhs \<longleftrightarrow> count (factor_mset G a) (assocs G d) \<ge> k"
    using factor_mset_count[OF assms(3,1,2)] by simp
  also have "... \<longleftrightarrow> replicate_mset k (assocs G d) \<subseteq># factor_mset G a"
    by (subst count_le_replicate_mset_subset_eq, simp) 
  also have "... \<longleftrightarrow> repeat_mset k (factor_mset G d) \<subseteq># factor_mset G a" 
    by (subst factor_mset_irred[OF assms(1,2)], simp)
  also have "... \<longleftrightarrow> factor_mset G (d [^]\<^bsub>G\<^esub> k) \<subseteq># factor_mset G a" 
    by (subst factor_mset_pow[OF assms(1)], simp)
  also have "... \<longleftrightarrow> (d [^] k) divides\<^bsub>G\<^esub> a"
    using assms(1) factor_mset_divides[OF _ assms(3)] by simp
  finally show ?thesis by simp
qed

lemma multiplicity_gt_0_iff:
  assumes "d \<in> carrier G" "irreducible G d" "a \<in> carrier G"
  shows "multiplicity G d a > 0 \<longleftrightarrow> d divides\<^bsub>G\<^esub> a"
  using multiplicity_ge_iff[OF assms(1,2,3), where k="1"] assms
  by auto

lemma factor_mset_count_2:
  assumes "a \<in> carrier G" 
  assumes "\<And>z. z \<in> carrier G \<Longrightarrow> irreducible G z \<Longrightarrow> y \<noteq> assocs G z"
  shows "count (factor_mset G a) y = 0"
  using factor_mset_set [OF assms(1)] assms(2) by (metis count_inI)

lemma factor_mset_choose:
  assumes "a \<in> carrier G" "set_mset R \<subseteq> carrier G"
  assumes "image_mset (assocs G) R = factor_mset G a" 
  shows "a \<sim> (\<Otimes>x\<in>set_mset R. x [^] count R x)" (is "a \<sim> ?rhs")
proof -
  have b:"irreducible G x" if a:"x \<in># R" for x
  proof -
    have x_carr: "x \<in> carrier G" 
      using a assms(2) by auto
    have "assocs G x \<in> assocs G ` set_mset R"
      using a by simp
    hence "assocs G x \<in># factor_mset G a"
      using assms(3) a in_image_mset by metis
    then obtain z where z_def: "z \<in> carrier G" "irreducible G z" "assocs G x = assocs G z"
      using factor_mset_set assms(1) by metis
    have "z \<sim> x" using z_def(1,3) assocs_eqD x_carr by simp 
    thus ?thesis using z_def(1,2) x_carr irreducible_cong by simp
  qed

  have "factor_mset G ?rhs = (\<Sum>x\<in>set_mset R. factor_mset G (x [^] count R x))"
    using assms(2) by (subst factor_mset_prod, auto) 
  also have "... = (\<Sum>x\<in>set_mset R. repeat_mset (count R x) (factor_mset G x))"
    using assms(2) by (intro sum.cong, auto simp add:factor_mset_pow)
  also have "... = (\<Sum>x\<in>set_mset R. repeat_mset (count R x) (image_mset (assocs G) {#x#}))"
    using assms(2) b by (intro sum.cong, auto simp add:factor_mset_irred)
  also have "... = (\<Sum>x\<in>set_mset R. image_mset (assocs G) (replicate_mset (count R x) x))"
    by simp
  also have "... = image_mset (assocs G) (\<Sum>x\<in>set_mset R. (replicate_mset (count R x) x))"
    by (simp add: image_mset_sum)
  also have "... = image_mset (assocs G) R"
    by (simp add:decomp_mset)
  also have "... = factor_mset G a"
    using assms by simp
  finally have "factor_mset G ?rhs = factor_mset G a" by simp
  moreover have "(\<Otimes>x\<in>set_mset R. x [^] count R x) \<in> carrier G"
    using assms(2) by (intro finprod_closed, auto)
  ultimately show ?thesis 
    using assms(1) by (subst factor_mset_sim) auto
qed

lemma divides_iff_mult_mono:
  assumes "a \<in> carrier G" "b \<in> carrier G" 
  assumes "canonical_irreducibles G R"
  assumes "\<And>d. d \<in> R \<Longrightarrow> multiplicity G d a \<le> multiplicity G d b"
  shows "a divides b"
proof -
  have "count (factor_mset G a) d \<le> count (factor_mset G b) d" for d
  proof (cases "\<exists>y. irreducible G y \<and> y \<in> carrier G \<and> d = assocs G y")
    case True
    then obtain y where y_def: "irreducible G y" "y \<in> carrier G" "d = assocs G y" by blast
    then obtain z where z_def: "z \<in> R" "y \<sim> z"
      using assms(3) unfolding canonical_irreducibles_def by metis
    have z_more: "irreducible G z" "z \<in> carrier G"
      using z_def(1) assms(3) unfolding canonical_irreducibles_def by auto
    have "y \<in> assocs G z" using z_def(2) z_more(2) y_def(2) 
      by (simp add: closure_ofI2)
    hence d_def: "d = assocs G z" using y_def(2,3) z_more(2)  assocs_repr_independence by blast
    have "count (factor_mset G a) d = multiplicity G z a"
      unfolding d_def by (intro factor_mset_count[OF assms(1) z_more(2,1)])
    also have "... \<le> multiplicity G z b"
      using assms(4) z_def(1) by simp
    also have "... = count (factor_mset G b) d"
      unfolding d_def by (intro factor_mset_count[symmetric, OF assms(2) z_more(2,1)])
    finally show ?thesis by simp 
  next
    case False
    have "count (factor_mset G a) d = 0" using False
      by (intro factor_mset_count_2[OF assms(1)], simp)
    moreover have "count (factor_mset G b) d = 0" using False
      by (intro factor_mset_count_2[OF assms(2)], simp)
    ultimately show ?thesis by simp
  qed

  hence "factor_mset G a \<subseteq># factor_mset G b" 
    unfolding subseteq_mset_def by simp
  thus ?thesis using factor_mset_divides assms(1,2) by simp
qed

lemma count_image_mset_inj:
  assumes "inj_on f R" "x \<in> R" "set_mset A \<subseteq> R"
  shows "count (image_mset f A) (f x) = count A x"
proof (cases "x \<in># A")
  case True
  hence "(f y = f x \<and> y \<in># A) = (y = x)" for y 
    by (meson assms(1) assms(3) inj_onD subsetD)
  hence "(f -` {f x} \<inter> set_mset A) = {x}" 
    by (simp add:set_eq_iff)
  thus ?thesis
    by (subst count_image_mset, simp)
next
  case False
  hence "x \<notin> set_mset A" by simp
  hence "f x \<notin> f ` set_mset A" using assms
    by (simp add: inj_on_image_mem_iff)
  hence "count (image_mset f A) (f x) = 0" 
    by (simp add:count_eq_zero_iff)
  thus ?thesis by (metis count_inI False)
qed

text \<open>Factorization of an element from a @{locale "factorial_monoid"} using a selection of representatives 
from each equivalence class formed by @{term "(\<sim>)"}.\<close>

lemma split_factors:
  assumes "canonical_irreducibles G R"
  assumes "a \<in> carrier G"
  shows 
    "finite {d. d \<in> R \<and> multiplicity G d a > 0}"
    "a \<sim> (\<Otimes>d\<in>{d. d \<in> R \<and> multiplicity G d a > 0}. d [^] multiplicity G d a)" (is "a \<sim> ?rhs")
proof -
  have r_1: "R \<subseteq> {x. x \<in> carrier G \<and> irreducible G x}" 
    using assms(1) unfolding canonical_irreducibles_def by simp
  have r_2: "\<And>x y. x \<in> R \<Longrightarrow> y \<in> R \<Longrightarrow> x \<sim> y \<Longrightarrow> x = y" 
    using assms(1) unfolding canonical_irreducibles_def by simp
  
  have assocs_inj: "inj_on (assocs G) R"
    using r_1 r_2 assocs_eqD by (intro inj_onI, blast) 
  
  define R' where
    "R' = (\<Sum>d\<in> {d. d \<in> R \<and> multiplicity G d a > 0}. replicate_mset (multiplicity G d a) d)"

  have "\<And>x. x \<in> R \<and> 0 < multiplicity G x a \<Longrightarrow> count (factor_mset G a) (assocs G x) > 0"
    using assms r_1 r_2 
    by (subst factor_mset_count[OF assms(2)]) auto
  hence "assocs G ` {d \<in> R. 0 < multiplicity G d a} \<subseteq> set_mset (factor_mset G a)"
    by (intro image_subsetI, simp)
  hence a:"finite (assocs G ` {d \<in> R. 0 < multiplicity G d a})"
    using finite_subset by auto

  show "finite {d \<in> R. 0 < multiplicity G d a}" 
    using assocs_inj inj_on_subset[OF assocs_inj]
    by (intro finite_imageD[OF a], simp)

  hence count_R': "count R' d = (if d \<in> R then multiplicity G d a else 0)" for d
    by (auto simp add:R'_def count_sum) 

  have set_R': "set_mset R' = {d \<in> R. 0 < multiplicity G d a}"
    unfolding set_mset_def using count_R' by auto

  have "count (image_mset (assocs G) R') x = count (factor_mset G a) x" for x
  proof (cases "\<exists>x'. x' \<in> R \<and> x = assocs G x'")
    case True
    then obtain x' where x'_def: "x' \<in> R" "x = assocs G x'"
      by blast
    have "count (image_mset (assocs G) R') x = count R' x'"
      using assocs_inj inj_on_subset[OF assocs_inj] x'_def
      by (subst x'_def(2), subst count_image_mset_inj[OF assocs_inj], auto simp add:set_R') 
    also have "... = multiplicity G x' a"
      using count_R' x'_def by simp
    also have "... = count (factor_mset G a) (assocs G x')"
      using x'_def(1) r_1
      by (subst factor_mset_count[OF assms(2)]) auto
    also have "... = count (factor_mset G a) x"
      using x'_def(2) by simp
    finally show ?thesis by simp
  next
    case False
    have a:"x \<noteq> assocs G z" 
      if a1: "z \<in> carrier G" and a2: "irreducible G z" for z
    proof -
      obtain v where v_def: "v \<in> R" "z \<sim> v"
        using a1 a2 assms(1) unfolding canonical_irreducibles_def by auto
      hence "z \<in> assocs G v"
        using a1 r_1 v_def(1) by (simp add: closure_ofI2)
      hence "assocs G z = assocs G v"
        using a1 r_1 v_def(1)  assocs_repr_independence
        by auto
      moreover have "x \<noteq> assocs G v"
        using False v_def(1) by simp
      ultimately show ?thesis by simp
    qed

    have "count (image_mset (assocs G) R') x = 0"
      using False count_R' by (simp add: count_image_mset) auto
    also have "... = count (factor_mset G a) x"
      using a
      by (intro factor_mset_count_2[OF assms(2), symmetric]) auto 
    finally show ?thesis by simp
  qed

  hence "image_mset (assocs G) R' = factor_mset G a"
    by (rule multiset_eqI)

  moreover have "set_mset R' \<subseteq> carrier G" 
    using r_1 by (auto simp add:set_R') 
  ultimately have "a \<sim> (\<Otimes>x\<in>set_mset R'. x [^] count R' x)"
    using assms(2) by (intro factor_mset_choose, auto)
  also have "... = ?rhs"
    using set_R' assms r_1 r_2
    by (intro finprod_cong', auto simp add:count_R')
  finally show "a \<sim> ?rhs" by simp
qed

end

subsection \<open>Polynomials\<close>

text \<open>The embedding of the constant polynomials into the polynomials is injective:\<close>

lemma (in ring) poly_of_const_inj:
  "inj poly_of_const"
proof -
  have "coeff (poly_of_const x) 0 = x" for x 
    unfolding poly_of_const_def normalize_coeff[symmetric]
    by simp
  thus ?thesis by (metis injI)
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


text \<open>The following are versions of the properties of the degree's of polynomials, that abstract
over the definition of the polynomial ring structure.

In the theories @{theory "HOL-Algebra.Polynomials"} and 
@{theory "HOL-Algebra.Polynomial_Divisibility"} these abstract version are usually indicated with
the suffix ``shell'', e.g.: @{thm [source] "domain.pdivides_iff_shell"}.\<close>

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

lemma (in ring) coeff_add:
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

subsection \<open>Ring Isomorphisms\<close>

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

lemma carrier_hom':
  assumes "f \<in> carrier (poly_ring R)"
  assumes "h \<in> ring_hom R S" "domain R" "domain S" "inj_on h (carrier R)"
  shows "map h f \<in> carrier (poly_ring S)"
proof -
  let ?S = "S \<lparr> carrier := h ` carrier R \<rparr>"

  interpret dr: domain "R" using assms(3) by blast
  interpret ds: domain "S" using assms(4) by blast
  interpret h1: ring_hom_ring R S h
    using assms(2) ring_hom_ringI2 dr.ring_axioms ds.ring_axioms by blast 
  have subr: "subring (h ` carrier R) S" 
    using h1.img_is_subring[OF dr.carrier_is_subring] by blast
  interpret h: ring_hom_ring "((h ` carrier R)[X]\<^bsub>S\<^esub>)" "poly_ring S" "id"
    using ds.embed_hom[OF subr] by simp

  let ?S = "S \<lparr> carrier := h ` carrier R \<rparr>"
  have "h \<in> ring_hom R ?S"
    using assms(2) unfolding ring_hom_def by simp
  moreover have "bij_betw h (carrier R) (carrier ?S)"
    using assms(5) bij_betw_def by auto
  ultimately have h_iso: "h \<in> ring_iso R ?S"
    unfolding ring_iso_def by simp


  have dom_S: "domain ?S" 
    using ds.subring_is_domain[OF subr] by simp

  note poly_iso = lift_iso_to_poly_ring[OF h_iso assms(3) dom_S]
  have "map h f \<in> carrier (poly_ring ?S)"
    using ring_iso_memE(1)[OF poly_iso assms(1)] by simp
  also have "carrier (poly_ring ?S) = carrier (univ_poly S (h ` carrier R))"
    using ds.univ_poly_consistent[OF subr] by simp
  also have "... \<subseteq> carrier (poly_ring S)"
    using h.hom_closed by auto
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



lemma irreducible_hom:
  assumes "h \<in> ring_iso R S" "domain R" "domain S" "x \<in> carrier R"
  shows "irreducible R x = irreducible S (h x)"
proof -
  have h_img: "h ` (carrier R) = carrier S" 
    using assms(1) unfolding ring_iso_def bij_betw_def by auto

  have "irreducible R x \<longleftrightarrow> (x \<notin> Units R \<and> (\<forall>b\<in>carrier R. properfactor R b x \<longrightarrow> b \<in> Units R))"
    unfolding Divisibility.irreducible_def by simp
  also have "... \<longleftrightarrow> (x \<notin> Units R \<and> (\<forall>b\<in>carrier R. properfactor S (h b) (h x) \<longrightarrow> b \<in> Units R))"
    using properfactor_hom[OF assms(1,2,3)] assms(4) by simp
  also have "... \<longleftrightarrow> (h x \<notin> Units S \<and> (\<forall>b\<in>carrier R. properfactor S (h b) (h x) \<longrightarrow> h b \<in> Units S))"
    using assms(4) Units_hom[OF assms(1,2,3)] by simp
  also have "...\<longleftrightarrow> (h x \<notin> Units S \<and> (\<forall>b\<in>h ` carrier R. properfactor S b (h x) \<longrightarrow> b \<in> Units S))"
    by simp
  also have "... \<longleftrightarrow> irreducible S (h x)"
    unfolding h_img Divisibility.irreducible_def by simp
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

subsection \<open>Divisibility\<close>

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

text \<open>Adapted from the proof of @{thm [source] domain.polynomial_rupture}\<close>

lemma (in domain) rupture_surj_as_eval:
  assumes "subring K R" and "p \<in> carrier (K[X])" "q \<in> carrier (K[X])"
  shows "rupture_surj K p q = ring.eval (Rupt K p) (map ((rupture_surj K p) \<circ> poly_of_const) q) (rupture_surj K p X)"
proof -
  let ?surj = "rupture_surj K p"

  interpret UP: domain "K[X]"
    using univ_poly_is_domain[OF assms(1)] .
  interpret Hom: ring_hom_ring "K[X]" "Rupt K p" ?surj
    using rupture_surj_hom(2)[OF assms(1,2)] .

  have "(Hom.S.eval) (map (?surj \<circ> poly_of_const) q) (?surj X) = ?surj ((UP.eval) (map poly_of_const q) X)"
    using Hom.eval_hom[OF UP.carrier_is_subring var_closed(1)[OF assms(1)]
          map_norm_in_poly_ring_carrier[OF assms(1,3)]] by simp
  also have " ... = ?surj q"
    unfolding sym[OF eval_rewrite[OF assms(1,3)]] ..
  finally show ?thesis by simp
qed

end
