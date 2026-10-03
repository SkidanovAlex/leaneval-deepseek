import Mathlib

namespace Work.KMTAreas

/-- The "extremal" identity behind the complex-interpolation step of the MSW single-torsion
reduction: for `q > 1` the map `z ↦ z · ‖z‖^{q-2}` has `enorm`-norm `‖z‖^{q-1}`, and the
exponent `q/(q-1)` is the conjugate exponent, so its norm to the `q/(q-1)`-th power is `‖z‖^q`.

(Here `enorm` is the `ENNReal`-valued norm `‖·‖ₑ`; the statement is an identity of extended
nonnegative reals, and both sides are finite.) -/
theorem MSW_extremal_enorm {q : ℝ} (hq : 1 < q) (z : ℂ) :
    enorm (z * Complex.ofReal ((‖z‖ : ℝ) ^ (q - 2))) ^ (q / (q - 1)) = enorm z ^ q := by
  have hq1 : (0:ℝ) < q - 1 := by linarith
  have hqne : q - 1 ≠ 0 := ne_of_gt hq1
  have hqpos : (0:ℝ) < q := by linarith
  have hqp : (0:ℝ) < q / (q - 1) := div_pos hqpos hq1
  have hr : (0:ℝ) ≤ ‖z‖ := norm_nonneg z
  -- the nnnorm of the real factor: it is `rpow` on `NNReal`
  have h2 : ‖((‖z‖ : ℝ) ^ (q - 2))‖₊ = ‖z‖₊ ^ (q - 2) := by
    rw [Real.nnnorm_of_nonneg (Real.rpow_nonneg hr _), ← NNReal.coe_inj]
    simp [NNReal.coe_rpow]
  -- the nnnorm of `z * ‖z‖^{q-2}` is `‖z‖₊^{q-1}`
  have hA : ‖z * Complex.ofReal ((‖z‖ : ℝ) ^ (q - 2))‖₊ = ‖z‖₊ ^ (q - 1) := by
    rw [nnnorm_mul, Complex.nnnorm_real, h2]
    have h : (1:ℝ) + (q - 2) ≠ 0 := by linarith
    have h3 : (1:ℝ) + (q - 2) = q - 1 := by ring
    have key : ‖z‖₊ ^ (q - 1) = ‖z‖₊ * ‖z‖₊ ^ (q - 2) := by
      rw [← h3, NNReal.rpow_add' h, NNReal.rpow_one]
    exact key.symm
  calc enorm (z * Complex.ofReal ((‖z‖ : ℝ) ^ (q - 2))) ^ (q / (q - 1))
      = ((‖z * Complex.ofReal ((‖z‖ : ℝ) ^ (q - 2))‖₊ : NNReal) : ENNReal) ^ (q / (q - 1)) := by
          rw [enorm_eq_nnnorm]
    _ = ↑(‖z * Complex.ofReal ((‖z‖ : ℝ) ^ (q - 2))‖₊ ^ (q / (q - 1)) : NNReal) :=
          (ENNReal.coe_rpow_of_nonneg _ hqp.le).symm
    _ = ↑((‖z‖₊ ^ (q - 1)) ^ (q / (q - 1)) : NNReal) := by rw [hA]
    _ = ↑(‖z‖₊ ^ q : NNReal) := by
          rw [← NNReal.rpow_mul, mul_div_cancel₀ q hqne]
    _ = (↑‖z‖₊ : ENNReal) ^ q := ENNReal.coe_rpow_of_nonneg _ hqpos.le
    _ = enorm z ^ q := by rw [enorm_eq_nnnorm]

end Work.KMTAreas
