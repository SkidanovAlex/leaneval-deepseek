import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace Commons.MeasureTheory.Volume

set_option autoImplicit false

/-- The Lebesgue measure of the cube `[-r, r]^d` in `ℝ^d` is `(2 * r) ^ d`. -/
theorem volume_pi_Icc {d : ℕ} (r : ℝ) (hr : 0 ≤ r) :
    (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
        (Set.pi Set.univ (fun _ : Fin d => Set.Icc (-r) r)) =
      ENNReal.ofReal ((2 * r) ^ d) := by
  rw [MeasureTheory.volume_pi_pi]
  simp only [Real.volume_Icc]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by linarith : (0 : ℝ) ≤ r - -r)]
  rw [show r - -r = 2 * r by ring]

end Commons.MeasureTheory.Volume