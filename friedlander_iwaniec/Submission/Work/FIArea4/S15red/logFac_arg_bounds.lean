import Mathlib
import Submission.Work.FITop3.Defs3
import Submission.Work.FITop3.Smooth
import Submission.Work.FITop3.Smooth.sm_props
import Submission.Work.FITop3.Majorant.majorant_props
import Submission.Work.FITop3.Witness.exists_primary_norm
import Submission.Work.FIArea4.S15prim_defs
import Submission.Work.FIArea4.S15delta
import Submission.Work.FIArea4.arg_sub_bounds

namespace Work.FIArea4.S15red

/-- **Angular separation of two points of the polar box from `|Δ| ≥ 2`.**

Two points `z₁, z₂` of the same polar box (5.14) whose determinant is at least `2` have principal
arguments differing by between `1/N` and `1`.

The upper bound is the box itself: both arguments lie in the interval `(φ, φ + 2πθ]` of length
`2πθ ≤ 1`.  The lower bound uses `|Δ| = |z₁||z₂|·|sin(α₂-α₁)|`, the box bound
`|zᵢ| ≤ √((1+θ)N)` and `|sin u| ≤ |u|`:
`|α₂-α₁| ≥ |sin(α₂-α₁)| ≥ 2/((1+θ)N) ≥ 1/N`, since `θ ≤ 1`. -/
theorem logFac_arg_bounds (Pa : Work.FITop.Params) (φ : ℝ) {z1 z2 : GaussianInt}
    (h1 : Work.FITop3.InPolarBox Pa φ z1) (h2 : Work.FITop3.InPolarBox Pa φ z2)
    (hΔ : 2 ≤ Work.FIPlan.absDelta z1 z2) :
    1 / (Pa.N : ℝ) ≤ |(z2 : ℂ).arg - (z1 : ℂ).arg| ∧
      |(z2 : ℂ).arg - (z1 : ℂ).arg| ≤ 1 := by
  have hθ1 : Pa.θ ≤ 1 := Work.FIArea4.theta_le_one Pa
  have hπθ : 2 * Real.pi * Pa.θ ≤ 1 := Work.FIArea4.two_pi_theta_le_one Pa
  have hN1 : (1 : ℝ) ≤ (Pa.N : ℝ) := by exact_mod_cast Pa.hN1
  have hNpos : (0 : ℝ) < (Pa.N : ℝ) := by linarith
  have hDpos : 0 < (1 + Pa.θ) * Pa.N := by
    have : 0 < 1 + Pa.θ := by linarith [Pa.hθ0]
    positivity
  -- norms of the two points
  have hgn1 : ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) ≤ (1 + Pa.θ) * Pa.N := h1.2.2.1
  have hgn2 : ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) ≤ (1 + Pa.θ) * Pa.N := h2.2.2.1
  have hs1 : ‖z1.toComplex‖ ≤ Real.sqrt ((1 + Pa.θ) * Pa.N) := by
    rw [← Work.FIArea4.sqrt_gnorm z1]; exact Real.sqrt_le_sqrt hgn1
  have hs2 : ‖z2.toComplex‖ ≤ Real.sqrt ((1 + Pa.θ) * Pa.N) := by
    rw [← Work.FIArea4.sqrt_gnorm z2]; exact Real.sqrt_le_sqrt hgn2
  have hprod : ‖z1.toComplex‖ * ‖z2.toComplex‖ ≤ (1 + Pa.θ) * Pa.N := by
    have hsq : Real.sqrt ((1 + Pa.θ) * Pa.N) * Real.sqrt ((1 + Pa.θ) * Pa.N)
        = (1 + Pa.θ) * Pa.N := by
      rw [← sq, Real.sq_sqrt (le_of_lt hDpos)]
    calc ‖z1.toComplex‖ * ‖z2.toComplex‖
        ≤ Real.sqrt ((1 + Pa.θ) * Pa.N) * Real.sqrt ((1 + Pa.θ) * Pa.N) :=
          mul_le_mul hs1 hs2 (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = (1 + Pa.θ) * Pa.N := hsq
  -- the determinant identity
  have hDelta : (Work.FIPlan.Delta z1 z2 : ℝ)
      = ‖z1.toComplex‖ * ‖z2.toComplex‖
        * Real.sin (Complex.arg z2.toComplex - Complex.arg z1.toComplex) := by
    rw [Work.FIPlan.Delta, GaussianInt.intCast_im, GaussianInt.toComplex_mul,
        GaussianInt.toComplex_star]
    exact Work.FIArea4.im_starRingEnd_mul z1.toComplex z2.toComplex
  have habs : ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
      = ‖z1.toComplex‖ * ‖z2.toComplex‖
        * |Real.sin (Complex.arg z2.toComplex - Complex.arg z1.toComplex)| := by
    rw [Work.FIPlan.absDelta, Nat.cast_natAbs, Int.cast_abs, hDelta,
        abs_mul, abs_mul, abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)]
  -- `|sin| ≥ |Δ|/((1+θ)N)`
  have hsin_ge : ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) / ((1 + Pa.θ) * Pa.N)
      ≤ |Real.sin (Complex.arg z2.toComplex - Complex.arg z1.toComplex)| := by
    rw [habs, div_le_iff₀ hDpos]
    have hcomm : ‖z1.toComplex‖ * ‖z2.toComplex‖
          * |Real.sin (Complex.arg z2.toComplex - Complex.arg z1.toComplex)|
        = |Real.sin (Complex.arg z2.toComplex - Complex.arg z1.toComplex)|
          * (‖z1.toComplex‖ * ‖z2.toComplex‖) := by ring
    rw [hcomm]
    exact mul_le_mul_of_nonneg_left hprod
      (abs_nonneg (Real.sin (Complex.arg z2.toComplex - Complex.arg z1.toComplex)))
  -- `|Δ| ≥ 2` combined with the previous line gives `|sin| ≥ 2/((1+θ)N)`
  have hcast2 : (2 : ℝ) ≤ ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by exact_mod_cast hΔ
  have hsin_ge2 : (2 : ℝ) / ((1 + Pa.θ) * Pa.N)
      ≤ |Real.sin (Complex.arg z2.toComplex - Complex.arg z1.toComplex)| :=
    le_trans (div_le_div_of_nonneg_right hcast2 (le_of_lt hDpos)) hsin_ge
  -- and `2/((1+θ)N) ≥ 1/N` because `θ ≤ 1`
  have hlow : 1 / (Pa.N : ℝ) ≤ 2 / ((1 + Pa.θ) * Pa.N) := by
    rw [le_div_iff₀ hDpos]
    have h1 : 1 / (Pa.N : ℝ) * ((1 + Pa.θ) * Pa.N) = 1 + Pa.θ := by
      field_simp
    rw [h1]
    linarith
  refine ⟨?_, ?_⟩
  · -- lower bound: `|arg₂ - arg₁| ≥ |sin(arg₂ - arg₁)| ≥ 2/((1+θ)N) ≥ 1/N`
    have hsin_le := Real.abs_sin_le_abs (x := Complex.arg z2.toComplex - Complex.arg z1.toComplex)
    linarith
  · -- upper bound: both arguments lie in `(φ, φ + 2πθ]`, an interval of length `2πθ ≤ 1`
    have hlt : |Complex.arg z2.toComplex - Complex.arg z1.toComplex| < 2 * Real.pi * Pa.θ := by
      rw [abs_lt]
      constructor <;> linarith [h1.2.2.2.1, h1.2.2.2.2, h2.2.2.2.1, h2.2.2.2.2]
    linarith

end Work.FIArea4.S15red
