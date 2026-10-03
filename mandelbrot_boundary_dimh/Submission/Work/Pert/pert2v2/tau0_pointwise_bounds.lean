import Mathlib
import Submission.Work.Interfaces.Parabolic

namespace Work.Pert.pert2v2

theorem tau0_pointwise_bounds {f₀ : ℂ → ℂ} {D₀ : Set ℂ}
    (d : MandelDim.ParabData f₀ D₀) {K : Set ℂ} {MK CW : ℝ}
    (hMK : ∀ w ∈ K, ‖d.E w‖ ≤ MK)
    (hW : ∀ w ∈ K, ∀ m : ℕ,
      ‖MandelDim.tau0 (f₀^[m] (d.φ w)) - ((m : ℂ) + d.E w)‖
        ≤ CW * (1 + Real.log ((m : ℝ) + 1)))
    {w : ℂ} (hw : w ∈ K) (m : ℕ) :
    ‖MandelDim.tau0 (f₀^[m] (d.φ w))‖
        ≤ (m : ℝ) + MK + CW * (1 + Real.log ((m : ℝ) + 1)) + 2 ∧
      (m : ℝ) - MK - CW * (1 + Real.log ((m : ℝ) + 1))
        ≤ (MandelDim.tau0 (f₀^[m] (d.φ w))).re := by
  -- Write `T` for the point under consideration, `c = m + E w` for the reference point and
  -- `B = CW * (1 + log (m+1))` for the allowed deviation.
  set T := MandelDim.tau0 (f₀^[m] (d.φ w)) with hT
  set c : ℂ := (m : ℂ) + d.E w with hc
  set B : ℝ := CW * (1 + Real.log ((m : ℝ) + 1)) with hB
  have hWm : ‖T - c‖ ≤ B := by rw [hT, hc, hB]; exact hW w hw m
  have hMKw : ‖d.E w‖ ≤ MK := hMK w hw
  constructor
  · -- upper bound: `‖T‖ ≤ ‖T - c‖ + ‖c‖ ≤ B + (m + MK)`.
    have hc' : ‖c‖ ≤ (m : ℝ) + MK := by
      calc ‖c‖ = ‖(m : ℂ) + d.E w‖ := by rw [hc]
        _ ≤ ‖(m : ℂ)‖ + ‖d.E w‖ := norm_add_le _ _
        _ = (m : ℝ) + ‖d.E w‖ := by rw [Complex.norm_natCast]
        _ ≤ (m : ℝ) + MK := by linarith [hMKw]
    have hmain : ‖T‖ ≤ B + ((m : ℝ) + MK) := by
      calc ‖T‖ = ‖(T - c) + c‖ := by congr 1; ring
        _ ≤ ‖T - c‖ + ‖c‖ := norm_add_le _ _
        _ ≤ B + ((m : ℝ) + MK) := add_le_add hWm hc'
    linarith
  · -- lower bound on the real part: `T.re ≥ (T - c).re + c.re ≥ -B + (m - MK)`.
    have h1 : -‖T - c‖ ≤ (T - c).re := by
      have h := Complex.abs_re_le_norm (T - c)
      rw [abs_le] at h
      linarith [h.1]
    have h2 : -MK ≤ (d.E w).re := by
      have h := Complex.abs_re_le_norm (d.E w)
      rw [abs_le] at h
      linarith [h.1, hMKw]
    have h3 : T.re = (T - c).re + c.re := by
      rw [← Complex.add_re, sub_add_cancel]
    have h4 : c.re = (m : ℝ) + (d.E w).re := by
      rw [hc, Complex.add_re]; simp
    rw [h3, h4]
    linarith [h1, h2, hWm]

end Work.Pert.pert2v2
