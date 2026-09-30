import Mathlib
import Submission.Work.BW.DefsB

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-! ## Basic properties of the homogenisation `homog`

`homog D P = ∑_{s ∈ P.support} P.coeff s * ∏_i X_{i,1}^{s_i} X_{i,0}^{D_i - s_i}` is the
homogenisation of `P` to the multidegree `D`.  This file records the three facts used everywhere
downstream:

* it is multihomogeneous of multidegree `D` (when the exponents of `P` fit into `D`);
* it does not kill a nonzero `P`;
* dehomogenising at `X_{i,0} = 1`, `X_{i,1} = y_i` recovers `eval y P`. -/

/-- The weighted degree of the monomial `∏ i, X (i,1)^(s i) * X (i,0)^(D i - s i)` is `fsD D`,
whenever the exponents `s i` fit into `D i`. -/
private lemma sum_weight_monomial {N : ℕ} (D : Fin (N + 1) → ℕ) (s : Fin (N + 1) →₀ ℕ)
    (hs : ∀ i, s i ≤ D i) :
    (∑ i : Fin (N + 1), (s i • mdeg N (i, 1) + (D i - s i) • mdeg N (i, 0))) = fsD D := by
  have h2 : ∀ i, s i • mdeg N (i, 1) + (D i - s i) • mdeg N (i, 0)
      = D i • Finsupp.single i 1 := by
    intro i
    simp only [mdeg]
    rw [← add_nsmul, Nat.add_sub_cancel' (hs i)]
  rw [Finset.sum_congr rfl (fun i _ => h2 i)]
  ext j
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp [fsD, Finsupp.equivFunOnFinite_symm_apply_apply]

lemma homog_basic {N : ℕ} (D : Fin (N + 1) → ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ)
    (h : ∀ i, P.degreeOf i ≤ D i) :
    homog D P ∈ homPiece N (fsD D) ∧ (P ≠ 0 → homog D P ≠ 0) ∧
      ∀ y : Fin (N + 1) → ℂ,
        MvPolynomial.eval (conePt N y) (homog D P) = MvPolynomial.eval y P := by
  -- Dehomogenisation: evaluating `homog D P` at the cone point `(X_{i,0}, X_{i,1}) = (1, y i)`
  -- recovers `eval y P`.
  have h3 : ∀ y : Fin (N + 1) → ℂ,
      MvPolynomial.eval (conePt N y) (homog D P) = MvPolynomial.eval y P := by
    intro y
    rw [homog, MvPolynomial.eval_sum, MvPolynomial.eval_eq']
    apply Finset.sum_congr rfl
    intro s _
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_prod]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_pow, MvPolynomial.eval_pow,
      MvPolynomial.eval_X, MvPolynomial.eval_X]
    simp only [conePt]
    norm_num
  -- Multihomogeneity: every monomial of the sum has weighted degree `fsD D`.
  have h1 : homog D P ∈ homPiece N (fsD D) := by
    rw [homPiece, MvPolynomial.mem_weightedHomogeneousSubmodule, homog]
    refine MvPolynomial.IsWeightedHomogeneous.sum (R := ℂ) (σ := Fin (N + 1) × Fin 2)
      (M := Fin (N + 1) →₀ ℕ) P.support
      (fun s => MvPolynomial.C (P.coeff s) *
        ∏ i : Fin (N + 1), MvPolynomial.X (i, 1) ^ (s i) * MvPolynomial.X (i, 0) ^ (D i - s i))
      (fsD D) ?_
    intro s hs
    have hsle : ∀ i, s i ≤ D i :=
      fun i => le_trans (MvPolynomial.le_degreeOf_of_mem_support i hs) (h i)
    have hprod : MvPolynomial.IsWeightedHomogeneous (R := ℂ) (mdeg N)
        (∏ i : Fin (N + 1), MvPolynomial.X (i, 1) ^ (s i) * MvPolynomial.X (i, 0) ^ (D i - s i))
        (∑ i : Fin (N + 1), (s i • mdeg N (i, 1) + (D i - s i) • mdeg N (i, 0))) := by
      apply MvPolynomial.IsWeightedHomogeneous.prod
      intro i _
      exact ((MvPolynomial.isWeightedHomogeneous_X ℂ (mdeg N) (i, 1)).pow _).mul
        ((MvPolynomial.isWeightedHomogeneous_X ℂ (mdeg N) (i, 0)).pow _)
    rw [sum_weight_monomial D s hsle] at hprod
    exact MvPolynomial.IsWeightedHomogeneous.C_mul hprod _
  -- Nonvanishing: if `homog D P = 0` then `eval y P = 0` for every `y`, so `P = 0`.
  have h2 : P ≠ 0 → homog D P ≠ 0 := by
    intro hP hz
    apply hP
    apply MvPolynomial.funext
    intro y
    rw [← h3 y, hz]
    simp
  exact ⟨h1, h2, h3⟩

end Work.BW
