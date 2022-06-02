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
  shows "sum' (\<lambda>i. f i - g i) A = sum' f A - sum' g A" (is "?lhs = ?rhs")
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

text \<open>This section contains additional results building on top of the development in
@{theory "HOL-Algebra.Divisibility"}.\<close>

definition factor_mset 
  where "factor_mset G x = (THE f. (\<exists> as. f = fmset G as \<and> wfactors G as x \<and> set as \<subseteq> carrier G))"

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
    (\<forall>x \<in> carrier G. irreducible G x \<longrightarrow> (\<exists>y \<in> A. x \<sim>\<^bsub>G\<^esub> y))
  )"

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
  shows "\<exists>as. factor_mset G a = fmset G as \<and> wfactors G as a \<and> set as \<subseteq> carrier G"
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
  shows "factor_mset G (finprod G f A) = (\<Sum>a \<in> A. factor_mset G (f a))"
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

end
