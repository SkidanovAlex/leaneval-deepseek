import Mathlib
import Submission.Work.Pert.V5.W2.Setup

namespace Work.Pert.V5.W2

theorem clear_pos {Ξ M Kp Rde : ℝ} {α : ℂ} {z₀ : ℂ} {a b : ℝ}
    (hΞ : 0 < Ξ) (hM : 2 ^ 10 ≤ M) (hInF1 : MandelDim.InF1 α)
    (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ))) (hRde : 0 < Rde)
    (hab : a ≤ b) (hb : b ≤ -(Ξ + 2 ^ 10))
    (hre : ∀ ξ ∈ Set.Icc a b, |ξ| ≤ 20 * (M + 2 + Ξ))
    (hmarg : ∀ ξ ∈ Set.Icc a b,
      Real.sqrt 2 * Rde ≤ min (mgA Ξ α ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I))
                               (mgB Ξ ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I))) :
    ∀ ξ ∈ Set.Icc a b, ∀ k : ℤ,
      ‖α‖ * 2 ^ 10 ≤ ‖α * ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I) - (k : ℂ)‖ := by
  intro ξ hξ k
  -- `hb` forces `ξ ≤ -(Ξ + 2^10) < 0`, so `|Re w| = |ξ| ≥ Ξ + 2^10 ≥ 2^10`, hence `‖w‖ ≥ 2^10`.
  have hξle : ξ ≤ -(Ξ + 2 ^ 10) := le_trans hξ.2 hb
  have hξneg : ξ ≤ 0 := by linarith [hΞ]
  have hwre : ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I).re = ξ := by
    simp [Complex.add_re]
  have hnorm : (2 : ℝ) ^ 10 ≤ ‖((ξ : ℂ) + (z₀.im : ℂ) * Complex.I)‖ := by
    have h1 : |ξ| ≤ ‖((ξ : ℂ) + (z₀.im : ℂ) * Complex.I)‖ := by
      simpa only [hwre] using Complex.abs_re_le_norm ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I)
    have h2 : |ξ| = -ξ := abs_of_nonpos hξneg
    have h3 : (2 : ℝ) ^ 10 ≤ Ξ + 2 ^ 10 := by linarith
    linarith
  exact Work.Pert.V5.clear_lattice_gate hΞ hM hInF1 hα
    (by simpa only [hwre] using hre ξ hξ) hnorm k

end Work.Pert.V5.W2
