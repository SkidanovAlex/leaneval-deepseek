import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.CStarAlgebra.Classes

namespace Commons.Algebra.MvPolynomial

open _root_.MvPolynomial
open scoped BigOperators Pointwise

noncomputable section

/-!
# Coefficient bound for the linear-form substitution

For a matrix `Λ : Matrix (Fin N) (Fin N) ℂ` whose entries are bounded by `M`, we consider
the substitution sending the variable `X (h, j)` to the linear form
`∑ k, C (Λ k j) * X (h, k)`.  We prove that the coefficients of the substituted polynomial
are bounded by `B * (N*M+1)^(∑ h, d h)`, where `B` bounds the coefficient `ℓ¹`-norm of the
original polynomial `P` and `d h` bounds the `h`-th block degree of every monomial of `P`.

The proof bounds the coefficient `ℓ¹`-norm (sum of the norms of the coefficients) of the
substitution of each monomial by the product of the `ℓ¹`-norms of the substituted linear
forms, which are each at most `N*M`.
-/

/-- Coefficient-`ℓ¹` norm of a multivariate polynomial with complex coefficients: the sum of
the norms of its coefficients. -/
private def cl1 {σ : Type*} (p : MvPolynomial σ ℂ) : ℝ :=
  ∑ m ∈ p.support, ‖p.coeff m‖

private lemma cl1_nonneg {σ : Type*} (p : MvPolynomial σ ℂ) : 0 ≤ cl1 p :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

private lemma cl1_coeff_le {σ : Type*} [DecidableEq σ] (p : MvPolynomial σ ℂ)
    (m : σ →₀ ℕ) : ‖p.coeff m‖ ≤ cl1 p := by
  rw [cl1]
  by_cases hm : m ∈ p.support
  · exact Finset.single_le_sum (fun i _ => norm_nonneg _) hm
  · rw [MvPolynomial.notMem_support_iff.mp hm, norm_zero]
    exact Finset.sum_nonneg fun _ _ => norm_nonneg _

private lemma cl1_monomial {σ : Type*} [DecidableEq σ] (s : σ →₀ ℕ) (c : ℂ) :
    cl1 (MvPolynomial.monomial s c) = ‖c‖ := by
  classical
  rw [cl1]
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · rw [MvPolynomial.support_monomial, if_neg hc, Finset.sum_singleton,
      MvPolynomial.coeff_monomial]
    simp

private lemma cl1_C {σ : Type*} [DecidableEq σ] (c : ℂ) :
    cl1 (MvPolynomial.C c : MvPolynomial σ ℂ) = ‖c‖ := by
  rw [MvPolynomial.C_apply]
  exact cl1_monomial 0 c

private lemma cl1_C_mul_X {σ : Type*} [DecidableEq σ] (a : ℂ) (y : σ) :
    cl1 (MvPolynomial.C a * MvPolynomial.X y : MvPolynomial σ ℂ) = ‖a‖ := by
  rw [MvPolynomial.C_mul_X_eq_monomial]
  exact cl1_monomial _ _

private lemma cl1_C_mul_le {σ : Type*} [DecidableEq σ] (c : ℂ) (p : MvPolynomial σ ℂ) :
    cl1 (MvPolynomial.C c * p) ≤ ‖c‖ * cl1 p := by
  classical
  have hsupp : (MvPolynomial.C c * p).support ⊆ p.support := by
    intro m hm
    rw [MvPolynomial.mem_support_iff] at hm ⊢
    intro h
    exact hm (by rw [MvPolynomial.coeff_C_mul, h, mul_zero])
  calc cl1 (MvPolynomial.C c * p)
      = ∑ m ∈ (MvPolynomial.C c * p).support, ‖c‖ * ‖p.coeff m‖ := by
        rw [cl1]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [MvPolynomial.coeff_C_mul, norm_mul]
    _ = ‖c‖ * ∑ m ∈ (MvPolynomial.C c * p).support, ‖p.coeff m‖ := by
        rw [Finset.mul_sum]
    _ ≤ ‖c‖ * ∑ m ∈ p.support, ‖p.coeff m‖ := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg c)
        exact Finset.sum_le_sum_of_subset_of_nonneg hsupp (fun _ _ _ => norm_nonneg _)
    _ = ‖c‖ * cl1 p := by rw [cl1]

private lemma cl1_add_le {σ : Type*} [DecidableEq σ] (p q : MvPolynomial σ ℂ) :
    cl1 (p + q) ≤ cl1 p + cl1 q := by
  classical
  have h1 : cl1 (p + q) ≤ ∑ m ∈ p.support ∪ q.support, ‖(p + q).coeff m‖ := by
    rw [cl1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (MvPolynomial.support_add)
      (fun _ _ _ => norm_nonneg _)
  have h2 : ∑ m ∈ p.support ∪ q.support, ‖(p + q).coeff m‖ ≤
      ∑ m ∈ p.support ∪ q.support, (‖p.coeff m‖ + ‖q.coeff m‖) := by
    apply Finset.sum_le_sum
    intro m _
    rw [MvPolynomial.coeff_add]
    exact norm_add_le _ _
  have hsplit : ∑ m ∈ p.support ∪ q.support, (‖p.coeff m‖ + ‖q.coeff m‖)
      = (∑ m ∈ p.support ∪ q.support, ‖p.coeff m‖)
        + ∑ m ∈ p.support ∪ q.support, ‖q.coeff m‖ :=
    Finset.sum_add_distrib
  have hp : ∑ m ∈ p.support ∪ q.support, ‖p.coeff m‖ = cl1 p := by
    rw [cl1]
    exact (Finset.sum_subset Finset.subset_union_left
      (fun m _ hm => by rw [MvPolynomial.notMem_support_iff.mp hm, norm_zero])).symm
  have hq : ∑ m ∈ p.support ∪ q.support, ‖q.coeff m‖ = cl1 q := by
    rw [cl1]
    exact (Finset.sum_subset Finset.subset_union_right
      (fun m _ hm => by rw [MvPolynomial.notMem_support_iff.mp hm, norm_zero])).symm
  calc cl1 (p + q) ≤ ∑ m ∈ p.support ∪ q.support, ‖(p + q).coeff m‖ := h1
    _ ≤ ∑ m ∈ p.support ∪ q.support, (‖p.coeff m‖ + ‖q.coeff m‖) := h2
    _ = cl1 p + cl1 q := by rw [hsplit, hp, hq]

private lemma cl1_sum_le {σ : Type*} [DecidableEq σ] {ι : Type*} (s : Finset ι)
    (A : ι → MvPolynomial σ ℂ) :
    cl1 (∑ i ∈ s, A i) ≤ ∑ i ∈ s, cl1 (A i) := by
  classical
  have key : ∀ i ∈ s,
      ∑ m ∈ (∑ i ∈ s, A i).support, ‖(A i).coeff m‖ ≤ cl1 (A i) := by
    intro i hi
    have hsub : (A i).support ⊆ (∑ i ∈ s, A i).support ∪ (A i).support :=
      Finset.subset_union_right
    have hzero : ∀ x ∈ (∑ i ∈ s, A i).support ∪ (A i).support,
        x ∉ (A i).support → ‖(A i).coeff x‖ = 0 := by
      intro x _ hxn
      rw [MvPolynomial.notMem_support_iff.mp hxn, norm_zero]
    calc ∑ m ∈ (∑ i ∈ s, A i).support, ‖(A i).coeff m‖
        ≤ ∑ m ∈ (∑ i ∈ s, A i).support ∪ (A i).support, ‖(A i).coeff m‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
            (fun m _ _ => norm_nonneg _)
      _ = ∑ m ∈ (A i).support, ‖(A i).coeff m‖ :=
          (Finset.sum_subset hsub hzero).symm
      _ = cl1 (A i) := by rw [cl1]
  calc cl1 (∑ i ∈ s, A i)
      ≤ ∑ m ∈ (∑ i ∈ s, A i).support, ∑ i ∈ s, ‖(A i).coeff m‖ := by
        rw [cl1]
        apply Finset.sum_le_sum
        intro m _
        rw [MvPolynomial.coeff_sum]
        exact norm_sum_le _ _
    _ = ∑ i ∈ s, ∑ m ∈ (∑ i ∈ s, A i).support, ‖(A i).coeff m‖ := Finset.sum_comm
    _ ≤ ∑ i ∈ s, cl1 (A i) := Finset.sum_le_sum key

/-- Combinatorial core of the submultiplicativity of the coefficient `ℓ¹`-norm: the pairs
`(x.1, x.2)` with `x.1 ∈ A` and `x.2 ∈ B` occurring in the antidiagonals over `S` are counted
at most once. -/
private lemma sum_antidiagonal_le_mul_real {M : Type*} [AddMonoid M] [DecidableEq M]
    [Finset.HasAntidiagonal M] (A B S : Finset M) (f g : M → ℝ)
    (hf : ∀ a, 0 ≤ f a) (hg : ∀ b, 0 ≤ g b) :
    ∑ m ∈ S, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m,
        (if x.1 ∈ A ∧ x.2 ∈ B then f x.1 * g x.2 else 0)
      ≤ (∑ a ∈ A, f a) * (∑ b ∈ B, g b) := by
  classical
  set T : M → Finset (M × M) := fun m =>
    (Finset.HasAntidiagonal.antidiagonal m).filter (fun x => x.1 ∈ A ∧ x.2 ∈ B) with hT
  have hinner : ∀ m, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m,
        (if x.1 ∈ A ∧ x.2 ∈ B then f x.1 * g x.2 else 0)
      = ∑ x ∈ T m, f x.1 * g x.2 := by
    intro m
    rw [hT]
    simp only [Finset.sum_filter]
  have hpair : (S : Set M).PairwiseDisjoint T := by
    intro m _ m' _ hne
    change Disjoint (T m) (T m')
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [hT] at hx hx'
    simp only [Finset.mem_filter] at hx hx'
    have h1 : x.1 + x.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hx.1
    have h2 : x.1 + x.2 = m' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx'.1
    exact hne (h1.symm.trans h2)
  have hsubset : S.biUnion T ⊆ A ×ˢ B := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨m, _, hxm⟩ := hx
    rw [hT, Finset.mem_filter] at hxm
    rw [Finset.mem_product]
    exact hxm.2
  calc ∑ m ∈ S, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m,
        (if x.1 ∈ A ∧ x.2 ∈ B then f x.1 * g x.2 else 0)
      = ∑ m ∈ S, ∑ x ∈ T m, f x.1 * g x.2 := Finset.sum_congr rfl (fun m _ => hinner m)
    _ = ∑ x ∈ S.biUnion T, f x.1 * g x.2 := (Finset.sum_biUnion hpair).symm
    _ ≤ ∑ x ∈ A ×ˢ B, f x.1 * g x.2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun x _ _ => mul_nonneg (hf x.1) (hg x.2))
    _ = (∑ a ∈ A, f a) * (∑ b ∈ B, g b) := by
        rw [Finset.sum_mul_sum]
        exact Finset.sum_product' A B (fun a b => f a * g b)

private lemma cl1_mul_le {σ : Type*} [DecidableEq σ] (p q : MvPolynomial σ ℂ) :
    cl1 (p * q) ≤ cl1 p * cl1 q := by
  classical
  have step1 : cl1 (p * q) ≤ ∑ m ∈ p.support + q.support, ‖(p * q).coeff m‖ := by
    rw [cl1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (MvPolynomial.support_mul p q)
      (fun _ _ _ => norm_nonneg _)
  have step2 : ∑ m ∈ p.support + q.support, ‖(p * q).coeff m‖ ≤
      ∑ m ∈ p.support + q.support,
        ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m, ‖p.coeff x.1‖ * ‖q.coeff x.2‖ := by
    apply Finset.sum_le_sum
    intro m _
    rw [MvPolynomial.coeff_mul]
    calc ‖∑ x ∈ Finset.HasAntidiagonal.antidiagonal m, p.coeff x.1 * q.coeff x.2‖
        ≤ ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m, ‖p.coeff x.1 * q.coeff x.2‖ :=
          norm_sum_le _ _
      _ = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m, ‖p.coeff x.1‖ * ‖q.coeff x.2‖ := by
          apply Finset.sum_congr rfl
          intro x _
          rw [norm_mul]
  have step3 : ∑ m ∈ p.support + q.support,
        ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m, ‖p.coeff x.1‖ * ‖q.coeff x.2‖
      = ∑ m ∈ p.support + q.support,
        ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m,
          (if x.1 ∈ p.support ∧ x.2 ∈ q.support then
            ‖p.coeff x.1‖ * ‖q.coeff x.2‖ else 0) := by
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : x.1 ∈ p.support ∧ x.2 ∈ q.support
    · rw [if_pos h]
    · rw [if_neg h]
      rcases not_and_or.mp h with h1 | h2
      · rw [MvPolynomial.notMem_support_iff.mp h1, norm_zero, zero_mul]
      · rw [MvPolynomial.notMem_support_iff.mp h2, norm_zero, mul_zero]
  have step4 : ∑ m ∈ p.support + q.support,
        ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m,
          (if x.1 ∈ p.support ∧ x.2 ∈ q.support then
            ‖p.coeff x.1‖ * ‖q.coeff x.2‖ else 0) ≤ cl1 p * cl1 q := by
    have h := sum_antidiagonal_le_mul_real p.support q.support (p.support + q.support)
      (fun a => ‖p.coeff a‖) (fun b => ‖q.coeff b‖)
      (fun a => norm_nonneg _) (fun b => norm_nonneg _)
    simpa only [cl1] using h
  exact step1.trans (step2.trans (step3.le.trans step4))

private lemma cl1_pow_le {σ : Type*} [DecidableEq σ] (p : MvPolynomial σ ℂ) (k : ℕ) :
    cl1 (p ^ k) ≤ cl1 p ^ k := by
  induction k with
  | zero => simpa using (cl1_C (σ := σ) (1 : ℂ)).le
  | succ k ih =>
      rw [pow_succ, pow_succ]
      exact (cl1_mul_le (p ^ k) p).trans
        (mul_le_mul_of_nonneg_right ih (cl1_nonneg p))

private lemma cl1_prod_le {σ : Type*} [DecidableEq σ] {ι : Type*} (s : Finset ι)
    (A : ι → MvPolynomial σ ℂ) :
    cl1 (∏ i ∈ s, A i) ≤ ∏ i ∈ s, cl1 (A i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (cl1_C (σ := σ) (1 : ℂ)).le
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      exact (cl1_mul_le (A a) (∏ i ∈ s, A i)).trans
        (mul_le_mul_of_nonneg_left ih (cl1_nonneg (A a)))

/-- The substitution sending `X (h, j)` to the linear form `∑ k, C (Λ k j) * X (h, k)`. -/
private def linSubst {m N : ℕ} (Λ : Matrix (Fin N) (Fin N) ℂ) :
    Fin m × Fin N → MvPolynomial (Fin m × Fin N) ℂ :=
  fun x => ∑ k : Fin N, MvPolynomial.C (Λ k x.2) * MvPolynomial.X (x.1, k)

/-- The coefficient `ℓ¹`-norm of `linSubst Λ x` is at most `N * M`. -/
private lemma cl1_linSubst_le {m N : ℕ} (Λ : Matrix (Fin N) (Fin N) ℂ) (M : ℝ)
    (hM : 0 ≤ M) (hΛ : ∀ i j, ‖Λ i j‖ ≤ M) (x : Fin m × Fin N) :
    cl1 (linSubst Λ x) ≤ (N : ℝ) * M := by
  classical
  rw [linSubst]
  calc cl1 (∑ k : Fin N, MvPolynomial.C (Λ k x.2) * MvPolynomial.X (x.1, k))
      ≤ ∑ k : Fin N, cl1 (MvPolynomial.C (Λ k x.2) * MvPolynomial.X (x.1, k)) :=
        cl1_sum_le _ _
    _ = ∑ k : Fin N, ‖Λ k x.2‖ := by
        apply Finset.sum_congr rfl
        intro k _
        exact cl1_C_mul_X _ _
    _ ≤ ∑ _k : Fin N, M := Finset.sum_le_sum (fun k _ => hΛ k x.2)
    _ = (N : ℝ) * M := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Coefficient-`ℓ¹` bound for the substitution of a single monomial. -/
private lemma cl1_aeval_monomial_le {m N : ℕ} (Λ : Matrix (Fin N) (Fin N) ℂ) (M : ℝ)
    (hM : 0 ≤ M) (hΛ : ∀ i j, ‖Λ i j‖ ≤ M) (d : Fin m → ℕ)
    (u : Fin m × Fin N →₀ ℕ) (hu : ∀ h : Fin m, ∑ k : Fin N, u (h, k) ≤ d h) (c : ℂ) :
    cl1 (MvPolynomial.aeval (linSubst Λ) (MvPolynomial.monomial u c))
      ≤ ‖c‖ * ((N : ℝ) * M + 1) ^ (∑ h : Fin m, d h) := by
  classical
  have hfsub_le : ∀ x : Fin m × Fin N, cl1 (linSubst Λ x) ≤ (N : ℝ) * M :=
    fun x => cl1_linSubst_le Λ M hM hΛ x
  have hbase_nn : 0 ≤ (N : ℝ) * M := mul_nonneg (Nat.cast_nonneg N) hM
  have hprod : (u.prod fun i k => linSubst Λ i ^ k)
      = ∏ x ∈ u.support, linSubst Λ x ^ u x := rfl
  have hsum_support : ∑ x ∈ u.support, u x = ∑ x : Fin m × Fin N, u x := by
    rw [Finset.sum_subset (Finset.subset_univ _)
      (fun x _ hx => Finsupp.notMem_support_iff.mp hx)]
  have hsum_le : (∑ x : Fin m × Fin N, u x) ≤ ∑ h : Fin m, d h := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_le_sum (fun h _ => hu h)
  rw [MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq, hprod]
  calc cl1 (MvPolynomial.C c * ∏ x ∈ u.support, linSubst Λ x ^ u x)
      ≤ ‖c‖ * cl1 (∏ x ∈ u.support, linSubst Λ x ^ u x) := cl1_C_mul_le _ _
    _ ≤ ‖c‖ * ∏ x ∈ u.support, cl1 (linSubst Λ x ^ u x) :=
        mul_le_mul_of_nonneg_left (cl1_prod_le _ _) (norm_nonneg c)
    _ ≤ ‖c‖ * ∏ x ∈ u.support, (cl1 (linSubst Λ x)) ^ u x :=
        mul_le_mul_of_nonneg_left
          (Finset.prod_le_prod (fun i _ => cl1_nonneg _) (fun i _ => cl1_pow_le _ _))
          (norm_nonneg c)
    _ ≤ ‖c‖ * ∏ x ∈ u.support, ((N : ℝ) * M) ^ u x :=
        mul_le_mul_of_nonneg_left
          (Finset.prod_le_prod
            (fun i _ => pow_nonneg (cl1_nonneg _) _)
            (fun i _ => pow_le_pow_left₀ (cl1_nonneg _) (hfsub_le i) _))
          (norm_nonneg c)
    _ = ‖c‖ * ((N : ℝ) * M) ^ (∑ x ∈ u.support, u x) := by
        rw [Finset.prod_pow_eq_pow_sum]
    _ = ‖c‖ * ((N : ℝ) * M) ^ (∑ x : Fin m × Fin N, u x) := by rw [hsum_support]
    _ ≤ ‖c‖ * ((N : ℝ) * M + 1) ^ (∑ x : Fin m × Fin N, u x) :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hbase_nn (le_add_of_nonneg_right zero_le_one) _) (norm_nonneg c)
    _ ≤ ‖c‖ * ((N : ℝ) * M + 1) ^ (∑ h : Fin m, d h) :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ (le_add_of_nonneg_left hbase_nn) hsum_le) (norm_nonneg c)

theorem coeff_aeval_linForm_le {m N : ℕ} (Λ : Matrix (Fin N) (Fin N) ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hΛ : ∀ i j, ‖Λ i j‖ ≤ M)
    (P : MvPolynomial (Fin m × Fin N) ℂ) (B : ℝ)
    (hP : ∑ J ∈ P.support, ‖P.coeff J‖ ≤ B)
    (d : Fin m → ℕ) (hdeg : ∀ J ∈ P.support, ∀ h : Fin m, ∑ k : Fin N, J (h, k) ≤ d h) :
    ∀ J, ‖(MvPolynomial.aeval
        (fun x : Fin m × Fin N =>
          ∑ k : Fin N, MvPolynomial.C (Λ k x.2) * MvPolynomial.X (x.1, k)) P).coeff J‖
      ≤ B * ((N : ℝ) * M + 1) ^ (∑ h : Fin m, d h) := by
  classical
  intro J
  have hbase_nn : 0 ≤ (N : ℝ) * M := mul_nonneg (Nat.cast_nonneg N) hM
  have hmap : MvPolynomial.aeval (linSubst Λ) P
      = ∑ u ∈ P.support,
          MvPolynomial.aeval (linSubst Λ) (MvPolynomial.monomial u (P.coeff u)) := by
    conv_lhs => rw [MvPolynomial.as_sum P]
    rw [map_sum]
  have hstep : cl1 (MvPolynomial.aeval (linSubst Λ) P)
      ≤ ∑ u ∈ P.support,
          cl1 (MvPolynomial.aeval (linSubst Λ) (MvPolynomial.monomial u (P.coeff u))) := by
    rw [hmap]
    exact cl1_sum_le _ _
  have hbound : ∑ u ∈ P.support,
        cl1 (MvPolynomial.aeval (linSubst Λ) (MvPolynomial.monomial u (P.coeff u)))
      ≤ ∑ u ∈ P.support, ‖P.coeff u‖ * ((N : ℝ) * M + 1) ^ (∑ h : Fin m, d h) := by
    apply Finset.sum_le_sum
    intro u hu
    exact cl1_aeval_monomial_le Λ M hM hΛ d u (hdeg u hu) (P.coeff u)
  calc ‖(MvPolynomial.aeval (linSubst Λ) P).coeff J‖
      ≤ cl1 (MvPolynomial.aeval (linSubst Λ) P) := cl1_coeff_le _ _
    _ ≤ ∑ u ∈ P.support,
          cl1 (MvPolynomial.aeval (linSubst Λ) (MvPolynomial.monomial u (P.coeff u))) := hstep
    _ ≤ ∑ u ∈ P.support, ‖P.coeff u‖ * ((N : ℝ) * M + 1) ^ (∑ h : Fin m, d h) := hbound
    _ = (∑ u ∈ P.support, ‖P.coeff u‖) * ((N : ℝ) * M + 1) ^ (∑ h : Fin m, d h) := by
        rw [Finset.sum_mul]
    _ ≤ B * ((N : ℝ) * M + 1) ^ (∑ h : Fin m, d h) :=
        mul_le_mul_of_nonneg_right hP (pow_nonneg (add_nonneg hbase_nn zero_le_one) _)

end

end Commons.Algebra.MvPolynomial