import Mathlib
import Submission.Commons.Analysis.GaussianMeasure.multivariate_hermite_orthogonal
import Submission.Commons.Analysis.GaussianMeasure.multivariate_hermite_norm
-- ⚠ IMPORT-CLASH WORKAROUND (session 123): the commons `memLp_hermite_product` pulls in
-- `memLp_mvpoly_withDensity_exp_neg_sq_half` → `bobkov_strong_nD`, which clashes with
-- `brascamp_lieb_truncated` (duplicate `toLp_norm_sq`).  `Submission.HermiteProductMemLp` is a
-- verbatim copy of the commons lemma whose (unused) `bobkov_strong_nD` import is deleted.
import Submission.HermiteProductMemLp
import Submission.Commons.Analysis.GaussianMeasure.integrable_exp_neg_norm_sq_half

/-!
# Hermite chaos bookkeeping (finite Hermite sums)

Bookkeeping for the Wiener chaos decomposition needed for Pisier's bound
`K(X) ≤ 4(1 + log₂ d(X, ℓ₂ⁿ))` on the Gaussian K-convexity constant
(see `Submission/Blueprint.lean`, session 120).

Ambient setting: `E_N := EuclideanSpace ℝ (Fin N)` with the Gaussian weight measure
`μ N := volume.withDensity (x ↦ ofReal (exp (-‖x‖²/2)))` (i.e. `(2π)^{N/2}` times the standard
Gaussian measure; the constant cancels in every estimate used below).

`herm α x = ∏ᵢ H_{αᵢ}(xᵢ)` are the multivariate Hermite polynomials, orthogonal for `μ N`
(`multivariate_hermite_orthogonal`, `multivariate_hermite_norm` from the commons).  Here we record
the consequences for finite linear combinations: Pythagoras and Bessel.
-/

open MeasureTheory Polynomial
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

namespace Submission.GaussianChaos

noncomputable def μ (N : ℕ) : Measure (EuclideanSpace ℝ (Fin N)) :=
  volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2 / 2)))

/-- The multivariate Hermite polynomial `∏ᵢ H_{αᵢ}(xᵢ)`. -/
noncomputable def herm {N : ℕ} (α : Fin N → ℕ) (x : EuclideanSpace ℝ (Fin N)) : ℝ :=
  ∏ i, Polynomial.aeval (x.ofLp i) (Polynomial.hermite (α i))

/-- The squared `L²(μ N)`-norm (energy) of `herm α`. -/
noncomputable def energy {N : ℕ} (α : Fin N → ℕ) : ℝ :=
  (∏ i, ((α i).factorial : ℝ)) * Real.sqrt (2 * Real.pi) ^ N

theorem energy_pos {N : ℕ} (α : Fin N → ℕ) : 0 < energy α := by
  have h1 : (0 : ℝ) < ∏ i, ((α i).factorial : ℝ) := by
    apply Finset.prod_pos
    intro i _
    exact_mod_cast Nat.factorial_pos (α i)
  have h2 : (0 : ℝ) < Real.sqrt (2 * Real.pi) ^ N := by positivity
  exact mul_pos h1 h2

theorem energy_ne_zero {N : ℕ} (α : Fin N → ℕ) : energy α ≠ 0 := (energy_pos α).ne'

/-- `μ N` is a finite measure (the Gaussian weight has finite total mass). -/
instance instIsFiniteMeasure (N : ℕ) : IsFiniteMeasure (μ N) := by
  rw [μ]
  refine MeasureTheory.isFiniteMeasure_withDensity ?_
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (Commons.Analysis.GaussianMeasure.integrable_exp_neg_norm_sq_half (n := N))
    (Filter.Eventually.of_forall fun x => Real.exp_nonneg _)]
  exact ENNReal.ofReal_ne_top

/-- Bridge: integrals against `μ N` are the usual Gaussian-weighted Lebesgue integrals. -/
theorem integral_μ (N : ℕ) (f : EuclideanSpace ℝ (Fin N) → ℝ) :
    ∫ x, f x ∂μ N = ∫ x, f x * Real.exp (-‖x‖ ^ 2 / 2) := by
  rw [μ, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards with x
  rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  ring

theorem integral_herm_sq {N : ℕ} (α : Fin N → ℕ) :
    ∫ x, (herm α x) ^ 2 ∂μ N = energy α := by
  rw [integral_μ, energy]
  simpa only [herm] using
    (Commons.Analysis.GaussianMeasure.multivariate_hermite_norm (m := N) α)

theorem integral_herm_mul_herm {N : ℕ} {α β : Fin N → ℕ} (h : α ≠ β) :
    ∫ x, herm α x * herm β x ∂μ N = 0 := by
  rw [integral_μ]
  simpa only [herm] using
    (Commons.Analysis.GaussianMeasure.multivariate_hermite_orthogonal (m := N) α β h)

theorem memLp_herm {N : ℕ} (α : Fin N → ℕ) : MemLp (herm α) 2 (μ N) := by
  have h := Commons.Analysis.GaussianMeasure.memLp_hermite_product (N := N) α
  simp only [herm, μ] at h ⊢
  exact h

theorem integrable_herm_mul_herm {N : ℕ} (α β : Fin N → ℕ) :
    Integrable (fun x => herm α x * herm β x) (μ N) :=
  MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 1)
    (MemLp.mul' (p := 2) (q := 2) (r := 1) (memLp_herm β) (memLp_herm α))

theorem integrable_herm_mul {N : ℕ} {f : EuclideanSpace ℝ (Fin N) → ℝ} (hf : MemLp f 2 (μ N))
    (α : Fin N → ℕ) : Integrable (fun x => f x * herm α x) (μ N) :=
  MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 1)
    (MemLp.mul' (p := 2) (q := 2) (r := 1) (memLp_herm α) hf)

/-! ### Pythagoras and Bessel for finite Hermite sums -/

theorem integral_sq_finset_sum {N : ℕ} (s : Finset (Fin N → ℕ)) (c : (Fin N → ℕ) → ℝ) :
    ∫ x, (∑ α ∈ s, c α * herm α x) ^ 2 ∂μ N = ∑ α ∈ s, (c α) ^ 2 * energy α := by
  have hpt : ∀ x : EuclideanSpace ℝ (Fin N),
      (∑ α ∈ s, c α * herm α x) ^ 2
        = ∑ α ∈ s, ∑ β ∈ s, (c α * c β) * (herm α x * herm β x) := by
    intro x
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro β _
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro α hα
    rw [MeasureTheory.integral_finsetSum]
    · rw [Finset.sum_eq_single α]
      · rw [integral_const_mul]
        have hsq : (∫ a, herm α a * herm α a ∂μ N) = energy α := by
          rw [show (fun a : EuclideanSpace ℝ (Fin N) => herm α a * herm α a)
              = (fun a => (herm α a) ^ 2) from by funext a; ring, integral_herm_sq]
        rw [hsq]
        ring
      · intro β _ hβ
        rw [integral_const_mul, integral_herm_mul_herm (Ne.symm hβ), mul_zero]
      · intro h
        exact absurd hα h
    · intro β _
      exact (integrable_herm_mul_herm α β).const_mul _
  · intro α _
    exact MeasureTheory.integrable_finsetSum s (fun β _ =>
      (integrable_herm_mul_herm α β).const_mul _)


/-! ### Vector-valued Hermite sums -/

section Vector

variable {n : ℕ}

/-- A finite `X`-valued Hermite sum `x ↦ ∑_{α ∈ s} H_α(x) • C_α`. -/
noncomputable def hermSum {N : ℕ} (s : Finset (Fin N → ℕ))
    (C : (Fin N → ℕ) → EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin n) :=
  fun x => ∑ α ∈ s, (herm α x) • C α

theorem hermSum_apply {N : ℕ} (s : Finset (Fin N → ℕ))
    (C : (Fin N → ℕ) → EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin N)) :
    hermSum s C x = ∑ α ∈ s, (herm α x) • C α := rfl

set_option maxHeartbeats 4000000 in
/-- Bilinear Pythagoras: the `L²` inner product of two finite `X`-valued Hermite sums. -/
theorem integral_inner_finset_sum {N : ℕ} (s : Finset (Fin N → ℕ))
    (C D : (Fin N → ℕ) → EuclideanSpace ℝ (Fin n)) :
    ∫ x, inner ℝ (hermSum s C x) (hermSum s D x) ∂μ N
      = ∑ α ∈ s, (inner ℝ (C α) (D α)) * energy α := by
  have hpt : ∀ x : EuclideanSpace ℝ (Fin N), inner ℝ (hermSum s C x) (hermSum s D x)
        = ∑ α ∈ s, ∑ β ∈ s, inner ℝ (C α) (D β) * (herm α x * herm β x) := by
    intro x
    simp only [hermSum]
    rw [sum_inner]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl fun α hα => ?_
    rw [MeasureTheory.integral_finsetSum]
    · rw [Finset.sum_eq_single α]
      · rw [MeasureTheory.integral_const_mul]
        rw [show (fun x : EuclideanSpace ℝ (Fin N) => herm α x * herm α x)
            = (fun x => (herm α x) ^ 2) from by funext x; ring, integral_herm_sq]
      · intro β _ hβ
        rw [MeasureTheory.integral_const_mul, integral_herm_mul_herm (Ne.symm hβ), mul_zero]
      · intro h
        exact absurd hα h
    · intro β _
      exact (integrable_herm_mul_herm α β).const_mul _
  · intro α _
    exact MeasureTheory.integrable_finsetSum s fun β _ =>
      (integrable_herm_mul_herm α β).const_mul _

set_option maxHeartbeats 4000000 in
/-- Pythagoras for `X`-valued finite Hermite sums (Euclidean norm on `X`). -/
theorem integral_norm_sq_finset_sum {N : ℕ} (s : Finset (Fin N → ℕ))
    (C : (Fin N → ℕ) → EuclideanSpace ℝ (Fin n)) :
    ∫ x, ‖hermSum s C x‖ ^ 2 ∂μ N = ∑ α ∈ s, ‖C α‖ ^ 2 * energy α := by
  have hpt : ∀ x : EuclideanSpace ℝ (Fin N), ‖hermSum s C x‖ ^ 2
        = inner ℝ (hermSum s C x) (hermSum s C x) := by
    intro x
    rw [real_inner_self_eq_norm_sq]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_inner_finset_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [real_inner_self_eq_norm_sq]

end Vector

end Submission.GaussianChaos
