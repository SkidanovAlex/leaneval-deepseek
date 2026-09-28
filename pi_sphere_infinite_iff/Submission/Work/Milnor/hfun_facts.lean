import Mathlib
import Submission.Work.Milnor.ChartDefs

/-!
# Facts about the function `hfun v = (4 - ‖v‖²)/(4 + ‖v‖²)` on `E3 = ℝ³`

The map `hfun` is the fibre-coordinate factor appearing in the chart expressions of the
Morse function on `Mk (-2)`.  We record the value and the first two derivatives at the
origin, the general shape of the differential, and the fact that the differential vanishes
only at the origin.

The proofs reduce everything to the scalar function `t ↦ (4-t)/(4+t)` and to
`fderiv ℝ (fun x ↦ ‖x‖^2) x = 2 • innerSL ℝ x` (Mathlib's `hasStrictFDerivAt_norm_sq`).
The latter is what produces the sign/scale `cgam`.
-/

open scoped RealInnerProductSpace

namespace Work.Milnor

noncomputable section

/-- Derivative of the scalar function `t ↦ (4-t)/(4+t)`, written in the form that matches
`cgam`: `d/dt (4-t)/(4+t) = -8/(4+t)^2 = -8 * (4+t)^(-2)`. -/
lemma hasDerivAt_hfunG (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun t : ℝ => (4 - t) / (4 + t)) (-8 * (4 + t) ^ (-(2:ℝ))) t := by
  have hpos : (0:ℝ) < 4 + t := by linarith
  have hrw : (4 + t) ^ (-(2:ℝ)) = ((4 + t) ^ 2)⁻¹ := by
    rw [Real.rpow_neg hpos.le]
    exact congrArg Inv.inv (Real.rpow_natCast (4 + t) 2)
  have h4 : HasDerivAt (fun t : ℝ => (4 - t) / (4 + t))
      (((-1) * (4 + t) - (4 - t) * 1) / (4 + t) ^ 2) t :=
    (hasDerivAt_id t).const_sub 4 |>.div ((hasDerivAt_id t).const_add 4) hpos.ne'
  refine h4.congr_deriv ?_
  rw [hrw, div_eq_mul_inv]
  have : ((-1) * (4 + t) - (4 - t) * 1) = (-8:ℝ) := by ring
  rw [this]

/-- `cgam 0 = -1`. -/
lemma cgam_zero : cgam 0 = -1 := by
  simp only [cgam, norm_zero]
  norm_num [Real.rpow_neg, Real.rpow_natCast]

/-- `cgam` never vanishes. -/
lemma cgam_ne_zero (x : E3) : cgam x ≠ 0 := by
  rw [cgam]
  have h : 0 < 4 + ‖x‖ ^ 2 := by positivity
  have h2 : 0 < (4 + ‖x‖ ^ 2) ^ (-(2:ℝ)) := Real.rpow_pos_of_pos h _
  exact mul_ne_zero (by norm_num) (ne_of_gt h2)

/-- The Fréchet differential of `hfun` at `x`. -/
lemma hasFDerivAt_hfun (x : E3) : HasFDerivAt hfun (cgam x • innerSL ℝ x) x := by
  have hg : HasDerivAt (fun t : ℝ => (4 - t) / (4 + t))
      (-8 * (4 + ‖x‖ ^ 2) ^ (-(2:ℝ))) (‖x‖ ^ 2) :=
    hasDerivAt_hfunG (‖x‖ ^ 2) (by positivity)
  have hf : HasFDerivAt (fun v : E3 => ‖v‖ ^ 2) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hcomp := hg.comp_hasFDerivAt x hf
  have hD : (-8 * (4 + ‖x‖ ^ 2) ^ (-(2:ℝ))) • (2 • innerSL ℝ x) = cgam x • innerSL ℝ x := by
    rw [cgam]
    ext y
    simp only [smul_apply, smul_eq_mul]
    ring
  rw [← hD]
  exact hcomp

/-- The derivative of `cgam` at the origin vanishes. -/
lemma cgam_hasFDerivAt_zero : HasFDerivAt cgam (0 : E3 →L[ℝ] ℝ) 0 := by
  have hN : HasFDerivAt (fun v : E3 => ‖v‖ ^ 2) (2 • innerSL ℝ (0:E3)) (0:E3) :=
    (hasStrictFDerivAt_norm_sq 0).hasFDerivAt
  have hu : HasFDerivAt (fun v : E3 => 4 + ‖v‖ ^ 2) (2 • innerSL ℝ (0:E3)) (0:E3) :=
    hN.const_add 4
  have hv : HasDerivAt (fun t : ℝ => t ^ (-(2:ℝ)))
      ((-(2:ℝ)) * (4 + ‖(0:E3)‖ ^ 2) ^ ((-(2:ℝ)) - 1)) (4 + ‖(0:E3)‖ ^ 2) :=
    Real.hasDerivAt_rpow_const (Or.inl (by positivity))
  have hcomp := hv.comp_hasFDerivAt (0:E3) hu
  have hcm := hcomp.const_mul (-16)
  have hz : ((-16:ℝ) • (((-(2:ℝ)) * (4 + ‖(0:E3)‖ ^ 2) ^ ((-(2:ℝ)) - 1)) •
      (2 • innerSL ℝ (0:E3)))) = 0 := by
    simp
  rw [hz] at hcm
  exact hcm

theorem hfun_facts :
    (hfun 0 = 1) ∧
    (fderiv ℝ hfun 0 = 0) ∧
    (∀ x : E3, fderiv ℝ hfun x = cgam x • innerSL ℝ x) ∧
    (fderiv ℝ (fderiv ℝ hfun) 0 = - (innerSL ℝ : E3 →L[ℝ] E3 →L[ℝ] ℝ)) ∧
    (∀ x : E3, fderiv ℝ hfun x = 0 ↔ x = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [hfun]
  · rw [(hasFDerivAt_hfun 0).fderiv]
    simp
  · intro x
    exact (hasFDerivAt_hfun x).fderiv
  · have hfderiv : fderiv ℝ hfun = cgam • (fun x : E3 => innerSL ℝ x) :=
      funext (fun x => (hasFDerivAt_hfun x).fderiv)
    have hsmul := cgam_hasFDerivAt_zero.smul
      (ContinuousLinearMap.hasFDerivAt (innerSL ℝ : E3 →L[ℝ] (E3 →L[ℝ] ℝ)))
    rw [hfderiv, hsmul.fderiv]
    simp [cgam_zero]
  · intro x
    rw [(hasFDerivAt_hfun x).fderiv]
    constructor
    · intro h
      have h2 : cgam x * (inner ℝ x x) = 0 := by
        have hc := congrArg (fun L : E3 →L[ℝ] ℝ => L x) h
        simpa [smul_apply, innerSL_apply_apply, smul_eq_mul] using hc
      have hx2 : ‖x‖ ^ 2 = 0 := by
        rw [← real_inner_self_eq_norm_sq]
        exact (mul_eq_zero.mp h2).resolve_left (cgam_ne_zero x)
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hx2)
    · intro hx
      rw [hx]
      simp

end

end Work.Milnor
