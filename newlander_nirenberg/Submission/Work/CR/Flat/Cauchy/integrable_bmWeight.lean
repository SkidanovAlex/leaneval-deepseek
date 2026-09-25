import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmSetup

namespace Work.CR.Flat.Cauchy

open scoped NNReal ENNReal
open MeasureTheory Set

/-- The Euclidean norm dominates the sup norm on `ℂⁿ`, so its square, `nrmSq`, is at least
`‖x‖ ^ 2`. -/
lemma sq_norm_le_nrmSq {n : ℕ} (y : Fin n → ℂ) : ‖y‖ ^ 2 ≤ nrmSq y := by
  have h := norm_le_eucNorm y
  have h2 := nrmSq_eq_eucNorm_sq y
  nlinarith [norm_nonneg y, eucNorm_nonneg y]

/-- **The radial weight of the Bochner–Martinelli constant.**  For `n ≥ 1` the function
`x ↦ n/(1+nrmSq x)^{n+1}` on `ℂⁿ` (Lebesgue measure, `nrmSq x = Σ_j ‖x_j‖²`) is integrable, and
its integral is positive.  Hence the normalising constant
`bmGamma n = -∫ x, n/(1+nrmSq x)^{n+1}` of the Bochner–Martinelli formula is non-zero
(see `Work.CR.Flat.Cauchy.bmGamma_ne_zero_of`). -/
theorem integrable_bmWeight {n : ℕ} (hn : 0 < n) :
    Integrable (fun y : Fin n → ℂ => (n : ℝ) / (nrmSq y + 1) ^ (n + 1)) ∧
      0 < ∫ y : Fin n → ℂ, (n : ℝ) / (nrmSq y + 1) ^ (n + 1) := by
  -- `ℂⁿ` is a real vector space of dimension `2n`; the integrand decays like `‖y‖ ^ (-2(n+1))`,
  -- which is summable in dimension `2n`.
  have hfr : Module.finrank ℝ (Fin n → ℂ) = 2 * n := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Complex.finrank_real_complex, smul_eq_mul]
    ring
  have hfin : (Module.finrank ℝ (Fin n → ℂ) : ℝ) < 2 * ((n : ℝ) + 1) := by
    rw [hfr]; push_cast; linarith
  have hexp : -(2 * ((n : ℝ) + 1)) / 2 = -((n : ℝ) + 1) := by ring
  -- The model Japanese-bracket integral `∫ (1 + ‖y‖²)^{-(n+1)}`: integrable since the exponent
  -- exceeds the dimension of `ℂⁿ`.
  have hG : Integrable (fun x : Fin n → ℂ => (1 + ‖x‖ ^ 2) ^ (-((n : ℝ) + 1))) volume := by
    simpa only [hexp] using (integrable_rpow_neg_one_add_norm_sq (μ := volume) (E := Fin n → ℂ)
      (r := 2 * ((n : ℝ) + 1)) hfin)
  have hG2 : Integrable (fun x : Fin n → ℂ => (n : ℝ) * (1 + ‖x‖ ^ 2) ^ (-((n : ℝ) + 1))) volume :=
    hG.const_mul (n : ℝ)
  have hmeas : AEStronglyMeasurable (fun y : Fin n → ℂ => (n : ℝ) / (nrmSq y + 1) ^ (n + 1)) volume := by
    apply Measurable.aestronglyMeasurable
    have h1 : Measurable (fun y : Fin n → ℂ => nrmSq y) := by unfold nrmSq; fun_prop
    exact Measurable.const_div ((h1.add measurable_const).pow_const (n + 1)) (n : ℝ)
  -- `nrmSq y ≥ ‖y‖ ^ 2`, so the weight is dominated by the model function.
  have hbnd : ∀ᵐ y ∂(volume : Measure (Fin n → ℂ)),
      ‖(n : ℝ) / (nrmSq y + 1) ^ (n + 1)‖ ≤ (n : ℝ) * (1 + ‖y‖ ^ 2) ^ (-((n : ℝ) + 1)) := by
    filter_upwards with y
    have hx : (0:ℝ) ≤ nrmSq y + 1 := by linarith [nrmSq_nonneg y]
    have hnorm : ‖(n : ℝ) / (nrmSq y + 1) ^ (n + 1)‖
        = (n : ℝ) * (nrmSq y + 1) ^ (-((n : ℝ) + 1)) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Nat.cast_nonneg n) (pow_nonneg hx _)),
        div_eq_mul_inv, ← Real.rpow_natCast (nrmSq y + 1) (n + 1), ← Real.rpow_neg hx]
      push_cast
      ring_nf
    have hmono : (nrmSq y + 1) ^ (-((n : ℝ) + 1)) ≤ (1 + ‖y‖ ^ 2) ^ (-((n : ℝ) + 1)) :=
      Real.rpow_le_rpow_of_nonpos (x := 1 + ‖y‖ ^ 2) (y := nrmSq y + 1) (by positivity)
        (by have h := sq_norm_le_nrmSq y; linarith) (neg_nonpos.mpr (by positivity))
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg n)
  have hFint : Integrable (fun y : Fin n → ℂ => (n : ℝ) / (nrmSq y + 1) ^ (n + 1)) volume :=
    hG2.mono' hmeas hbnd
  refine ⟨hFint, ?_⟩
  -- Positivity: the weight is strictly positive everywhere.
  rw [integral_pos_iff_support_of_nonneg (fun y => div_nonneg (Nat.cast_nonneg n)
    (pow_nonneg (by linarith [nrmSq_nonneg y]) _)) hFint]
  have hsupp : Function.support (fun y : Fin n → ℂ => (n : ℝ) / (nrmSq y + 1) ^ (n + 1))
      = Set.univ := by
    ext y
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    apply div_ne_zero (by exact_mod_cast hn.ne')
    have hx : (0:ℝ) < nrmSq y + 1 := by linarith [nrmSq_nonneg y]
    positivity
  rw [hsupp]
  exact Measure.measure_univ_pos.mpr (NeZero.ne volume)

end Work.CR.Flat.Cauchy
