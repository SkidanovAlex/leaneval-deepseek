import Mathlib
import Submission.Work.EQ.Defs
import Submission.Work.EQ.hetero_local

namespace Work.EQ

/-- Algebraic form of the half-map about the centre `O₂ = a/2`.  Writing `w = P - O₂`, one has
`eqU a P + O₂ = ((1 - ‖w‖)/‖w‖) · w`.  This is the computation
`eqU a P + O₂ = -P + w/‖w‖ + O₂ = -w + w/‖w‖`. -/
lemma eqU_add_eqU (a : ℝ) (P : ℂ) (hw : P - ((a/2:ℝ):ℂ) ≠ 0) :
    Work.EQ.eqU a P + ((a/2:ℝ):ℂ)
      = (((1 - ‖P - ((a/2:ℝ):ℂ)‖)/‖P - ((a/2:ℝ):ℂ)‖ : ℝ) : ℂ) * (P - ((a/2:ℝ):ℂ)) := by
  have hcast : ∀ n : ℝ, (((1 - n)/n : ℝ) : ℂ) = (1 - (n:ℂ))/(n:ℂ) := by
    intro n; rw [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one]
  rw [Work.EQ.eqU, hcast]
  have h2 : ((‖P - ((a/2:ℝ):ℂ)‖ : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact norm_ne_zero_iff.mpr hw
  field_simp
  ring

/-- Explicit inverse of the half-map `eqU` on the open upper half plane.

For `P = O₂ + w` with `O₂ = a/2`, `w = P - O₂ ≠ 0`: since `eqU a P = -P + w/‖w‖`, one gets
`eqU a P + O₂ = (1 - ‖w‖) · w / ‖w‖`.  Hence, if in addition `‖w‖ < 1` (which holds for the points
of the curve, whose distance from `O₂` is `ρ₂`), the point `z = eqU a P` determines
`‖z + O₂‖ = 1 - ‖w‖` and the direction of `w`, so `P` is recovered from `z` by
`O₂ + (1 - ‖z + O₂‖) * (z + O₂)/‖z + O₂‖`.

Hint for the proof: set `w = P - O₂`, `r = ‖w‖ ≠ 0`, and use
`eqU a P + O₂ = (1 - r) * (w / r)`, `‖w / r‖ = 1`, `r < 1`, `(1 - r) ≠ 0`. -/
theorem arcInv_eqU {a : ℝ} {P : ℂ} (him : 0 < (P - (((a/2 : ℝ)) : ℂ)).im)
    (hr : ‖P - (((a/2 : ℝ)) : ℂ)‖ < 1) :
    (((a/2 : ℝ)) : ℂ) +
        (1 - ‖Work.EQ.eqU a P + (((a/2 : ℝ)) : ℂ)‖) *
          ((Work.EQ.eqU a P + (((a/2 : ℝ)) : ℂ)) / ‖Work.EQ.eqU a P + (((a/2 : ℝ)) : ℂ)‖)
      = P := by
  set b : ℂ := ((a/2 : ℝ) : ℂ) with hb
  set w : ℂ := P - b with hw
  set r : ℝ := ‖w‖ with hrr
  have hwne : w ≠ 0 := by
    intro h
    rw [h] at him
    simp at him
  have hwpos : 0 < r := by rw [hrr]; exact norm_pos_iff.mpr hwne
  have hcpos : 0 < (1 - r)/r := div_pos (by linarith) hwpos
  have hrne : ((r:ℝ):ℂ) ≠ 0 := by rw [Complex.ofReal_ne_zero]; exact hwpos.ne'
  have hcne : (((1-r)/r : ℝ) : ℂ) ≠ 0 := by rw [Complex.ofReal_ne_zero]; exact hcpos.ne'
  have hk : P - ((a/2:ℝ):ℂ) ≠ 0 := by rw [← hb, ← hw]; exact hwne
  have hZ2 : Work.EQ.eqU a P + b = (((1 - r)/r : ℝ) : ℂ) * w := by
    have h := eqU_add_eqU a P hk
    rw [← hb, ← hw, ← hrr] at h
    exact h
  have hnormZ : ‖Work.EQ.eqU a P + b‖ = 1 - r := by
    rw [hZ2, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos]
    rw [← hrr]
    field_simp
  have hunit : (Work.EQ.eqU a P + b)/‖Work.EQ.eqU a P + b‖ = w / ((r:ℝ):ℂ) := by
    rw [hnormZ, hZ2]
    have hcr : ((1 - r : ℝ) : ℂ) = (((1-r)/r : ℝ):ℂ) * ((r:ℝ):ℂ) := by
      rw [← Complex.ofReal_mul]; congr 1; field_simp
    rw [hcr]
    field_simp
  have hfin : (1 - ‖Work.EQ.eqU a P + b‖) * ((Work.EQ.eqU a P + b)/‖Work.EQ.eqU a P + b‖) = w := by
    rw [hunit, hnormZ]
    rw [Complex.ofReal_sub, Complex.ofReal_one]
    rw [show (1:ℂ) - (1 - (r:ℂ)) = (r:ℂ) from by ring]
    field_simp
  rw [hfin]
  rw [hw]
  ring

end Work.EQ
