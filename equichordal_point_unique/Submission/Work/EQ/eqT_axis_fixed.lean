import Mathlib
import Submission.Work.EQ.normEqCurve_structure

namespace Work.EQ

/-- `polarPt` is `2π`-periodic in the angle. -/
lemma polarPt_period (c r θ : ℝ) : polarPt c r (θ + 2 * Real.pi) = polarPt c r θ := by
  simp only [polarPt]
  rw [show ((↑(θ + 2 * Real.pi) : ℂ)) * Complex.I
      = (↑θ : ℂ) * Complex.I + (2 * ↑Real.pi * Complex.I) by push_cast; ring]
  rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- **`eqT a` fixes the two real-axis points of a normalised equichordal curve.**
Both axis points `polarPt (-(a/2)) (ρ₁ 0) 0` and `polarPt (-(a/2)) (ρ₁ π) π` are the two
points where the curve meets the real axis; the two unit chord steps through `O₂` then `O₁`
carry each one to the other and back. -/
theorem eqT_axis_fixed {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ρ₁ ρ₂ : ℝ → ℝ}
    (hC : NormEqCurve a ρ₁ ρ₂) :
    eqT a (polarPt (-(a/2)) (ρ₁ 0) 0) = polarPt (-(a/2)) (ρ₁ 0) 0 ∧
    eqT a (polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi)
      = polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15,
    hc16, hc17, hc18⟩ := normEqCurve_structure ha0 ha1 hC
  -- `A = polarPt (-(a/2)) (ρ₁ 0) 0` is `polarPt (a/2) (ρ₂ 0) 0` (hc8),
  -- `B = polarPt (-(a/2)) (ρ₁ π) π` is `polarPt (a/2) (ρ₂ π) π` (hc9).
  constructor
  · -- `eqT a A = A`.
    rw [eqT]
    have hfirst : chordMap (O2_sym a) (polarPt (-(a/2)) (ρ₁ 0) 0)
        = polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi := by
      rw [hc8, hc6 0, hc9]
      simp only [zero_add]
    rw [hfirst]
    have hsecond : chordMap (O1_sym a) (polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi)
        = polarPt (-(a/2)) (ρ₁ 0) 0 := by
      rw [hc5 Real.pi]
      rw [show Real.pi + Real.pi = 0 + 2 * Real.pi by ring, hc3 0, polarPt_period]
    exact hsecond
  · -- `eqT a B = B`.
    rw [eqT]
    have hfirst : chordMap (O2_sym a) (polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi)
        = polarPt (-(a/2)) (ρ₁ 0) 0 := by
      rw [hc9, hc6 Real.pi]
      rw [show Real.pi + Real.pi = 0 + 2 * Real.pi by ring, hc4 0, polarPt_period]
      rw [hc8]
    rw [hfirst]
    have hsecond : chordMap (O1_sym a) (polarPt (-(a/2)) (ρ₁ 0) 0)
        = polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi := by
      rw [hc5 0]
      simp only [zero_add]
    exact hsecond

end Work.EQ
