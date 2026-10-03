import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Parab.Setup

namespace Work.Parab.coordData

/-- If `ζ` points into the wedge `|arg ζ| ≥ 5π/12` (encoded quantitatively as
`ζ.re ≤ ‖ζ‖/3`) and `w` is an `E`-perturbation of `ζ` with `9 (E + |ξ|) < ‖ζ‖`, then the
vertex-`ξ` sector `QLeft ξ = {w | π/3 < |arg (w + ξ)|}` contains `w`: the perturbation and the
vertex shift move `w + ξ` by at most `E + |ξ|` in real part and in norm, while `2 ζ.re ≤ 2‖ζ‖/3`
leaves a gap `‖ζ‖/3` compared with `‖ζ‖`. -/
theorem qleft_close_vertex {ζ w : ℂ} {ξ : ℝ} {E : ℝ}
    (hζ3 : ζ.re ≤ ‖ζ‖ / 3) (hE : 0 ≤ E) (hw : ‖w - ζ‖ ≤ E)
    (hbig : 9 * (E + |ξ|) < ‖ζ‖) :
    w ∈ MandelDim.QLeft ξ := by
  rw [Work.Parab.QLeft_iff]
  have ha : 0 ≤ E + |ξ| := add_nonneg hE (abs_nonneg ξ)
  -- real part: `w + ξ` has real part at most `ζ.re + (E + |ξ|)`.
  have hre : (w + (ξ : ℂ)).re ≤ ζ.re + (E + |ξ|) := by
    have h₁ : (w - ζ).re ≤ ‖w - ζ‖ := Complex.re_le_norm _
    have h₂ : (w - ζ).re = w.re - ζ.re := by simp
    have h₃ : w.re ≤ ζ.re + E := by linarith
    have h₄ : w.re + ξ ≤ ζ.re + (E + |ξ|) := by linarith [le_abs_self ξ]
    rw [Complex.add_re, Complex.ofReal_re]
    exact h₄
  -- norm: `w + ξ` is at least `‖ζ‖ - (E + |ξ‖`.
  have hnorm : ‖ζ‖ ≤ ‖w + (ξ : ℂ)‖ + (E + |ξ|) := by
    have h₁ : ζ = (w + (ξ : ℂ)) - (w - ζ) - (ξ : ℂ) := by ring
    rw [h₁]
    have h₃ : ‖(w + (ξ : ℂ)) - (w - ζ) - (ξ : ℂ)‖
        ≤ ‖(w + (ξ : ℂ)) - (w - ζ)‖ + ‖(ξ : ℂ)‖ := norm_sub_le _ _
    have h₄ : ‖(w + (ξ : ℂ)) - (w - ζ)‖ ≤ ‖w + (ξ : ℂ)‖ + ‖w - ζ‖ := norm_sub_le _ _
    have h₅ : ‖(ξ : ℂ)‖ = |ξ| := by rw [Complex.norm_real, Real.norm_eq_abs]
    linarith [norm_nonneg (w + (ξ : ℂ))]
  have hre2 : 2 * (w + (ξ : ℂ)).re ≤ 2 * (ζ.re + (E + |ξ|)) := by linarith
  linarith

end Work.Parab.coordData
