import Mathlib
import Submission.Work.BW.bpOddDefs
import Submission.Work.BW.DefsAC

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Lower bound for a single Blaschke factor `β(z;k) = R(z−k)/(R²−kz)` away from the point `l`:
on the circle `‖z − l‖ = η` and with `|k|·(|l| + η) < R²`, any `u ≤ ‖z − k‖` satisfies
`R·u / (|R² − k·l| + |k|·η) ≤ ‖β(z;k)‖`.

The denominator `bpD` is `|R² − k·l| + |k|·η`, which dominates `‖R² − kz‖` since
`R² − kz = (R² − k·l) − k(z − l)`; the hypothesis `|k|·(|l| + η) < R²` makes `bpD` positive and
also rules out `R² − kz = 0` (which would force `|R² − k·l| = |k|·η` and hence
`R² ≤ |k·l| + |R² − k·l| = |k|·(|l| + η) < R²`). -/
theorem bpOdd_bfac_lower {R η u : ℝ} (hη : 0 ≤ η) (hR : 0 < R) {l k : ℤ} {z : ℂ}
    (hz : ‖z - (l:ℂ)‖ = η) (hu : 0 ≤ u) (huz : u ≤ ‖z - (k:ℂ)‖)
    (hden : |(k:ℝ)| * (|(l:ℝ)| + η) < R^2) :
    R * u / bpD R η l k ≤ ‖bfac R k z‖ := by
  -- The denominator `bpD` is positive.
  have hDpos : 0 < bpD R η l k := bpD_pos hη hden
  -- The complex denominator `R² − kz` is nonzero, hence of positive modulus.
  have hnormD_pos : 0 < ‖(R:ℂ)^2 - (k:ℂ)*z‖ := by
    rw [norm_pos_iff]
    intro hD0
    have hkeq : (R:ℂ)^2 = (k:ℂ)*z := sub_eq_zero.mp hD0
    have hk_eq : (k:ℂ)*(z - (l:ℂ)) = ((R^2 - (k:ℝ)*(l:ℝ) : ℝ) : ℂ) := by
      have h1 : (k:ℂ)*(z - (l:ℂ)) = (k:ℂ)*z - (k:ℂ)*(l:ℂ) := by ring
      rw [h1, ← hkeq]; push_cast; ring
    have habs : |R^2 - (k:ℝ)*(l:ℝ)| = |(k:ℝ)| * η := by
      have h := congrArg norm hk_eq
      rw [norm_mul, hz, Complex.norm_intCast, Complex.norm_real, Real.norm_eq_abs] at h
      exact h.symm
    -- `R² ≤ |k|·(|l| + η)`, contradicting the hypothesis `hden`.
    have hineq : R^2 ≤ |(k:ℝ)| * (|(l:ℝ)| + η) := by
      have h2 : |(k:ℝ)| * |(l:ℝ)| = |(k:ℝ)*(l:ℝ)| := (abs_mul _ _).symm
      rw [mul_add, h2, ← habs]
      have h4 := abs_sub_abs_le_abs_sub (R^2) ((k:ℝ)*(l:ℝ))
      rw [abs_of_nonneg (sq_nonneg R)] at h4
      linarith
    linarith [hden, hineq]
  -- `‖R² − kz‖ ≤ bpD`: triangle inequality after splitting off the term `R² − k·l`.
  have hD_le : ‖(R:ℂ)^2 - (k:ℂ)*z‖ ≤ bpD R η l k := by
    have hdecomp : (R:ℂ)^2 - (k:ℂ)*z
        = ((R^2 - (k:ℝ)*(l:ℝ) : ℝ) : ℂ) - (k:ℂ)*(z - (l:ℂ)) := by
      push_cast; ring
    rw [hdecomp, bpD]
    calc ‖((R^2 - (k:ℝ)*(l:ℝ) : ℝ) : ℂ) - (k:ℂ)*(z - (l:ℂ))‖
        ≤ ‖((R^2 - (k:ℝ)*(l:ℝ) : ℝ) : ℂ)‖ + ‖(k:ℂ)*(z - (l:ℂ))‖ := norm_sub_le _ _
      _ = |R^2 - (k:ℝ)*(l:ℝ)| + |(k:ℝ)| * η := by
          rw [norm_mul, hz, Complex.norm_real, Real.norm_eq_abs, Complex.norm_intCast]
  -- Cross-multiplied core inequality.
  have hkey : u * ‖(R:ℂ)^2 - (k:ℂ)*z‖ ≤ ‖z - (k:ℂ)‖ * bpD R η l k := by
    have h1 : u * ‖(R:ℂ)^2 - (k:ℂ)*z‖ ≤ u * bpD R η l k :=
      mul_le_mul_of_nonneg_left hD_le hu
    have h2 : u * bpD R η l k ≤ ‖z - (k:ℂ)‖ * bpD R η l k :=
      mul_le_mul_of_nonneg_right huz (le_of_lt hDpos)
    linarith
  -- Explicit modulus of the Blaschke factor.
  have hfac : ‖bfac R k z‖ = R * ‖z - (k:ℂ)‖ / ‖(R:ℂ)^2 - (k:ℂ)*z‖ := by
    unfold bfac
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  rw [hfac, div_le_div_iff₀ hDpos hnormD_pos]
  have := mul_le_mul_of_nonneg_left hkey (le_of_lt hR)
  nlinarith [this]

end Work.BW
