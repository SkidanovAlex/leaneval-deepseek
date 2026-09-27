import Mathlib
import Submission.Work.Drive.linGpDefs

namespace Work.Drive

/-!
# The boundary line `span {e₀, e₁}` of the disk model is the unit circle of `ℂ`

The disk model of the linear plane (`Work.Drive.linVecC`, `Submission/Work/Drive/linearPlaneChart.lean`)
parametrises the projective plane of `linStd = {v : v 3 = 0}` by the closed unit disk, and its
**boundary circle** `‖z‖ = 1` maps onto the projective *line* of the plane `span {e₀, e₁}` of `Eucl 3`
(the boundary line `linBdry id` of the identity chart, `Submission/Work/Drive/linShearCharts.lean`).

In the sphere coordinates the boundary circle of the disk model consists of the lifts
`linVecC z = (z, 0) ∈ ℂ² ≅ ℝ⁴` with `‖z‖ = 1`; these are exactly the vectors of `Eucl 3` lying in
`span {e₀, e₁}` (i.e. with vanishing last two coordinates) *up to a non-zero real factor*.  This file
records that fact: every non-zero vector of `span {e₀, e₁}` is a non-zero real multiple of a unit
boundary lift `linVecC z`, `‖z‖ = 1`.

The proof is two lines of coordinates.  Membership in `span {e₀, e₁}` is membership in the kernel of
the second complex coordinate `c₂` (`c₂ linE0 = c₂ linE1 = 0`), so such a `w` is
`ofComplex (c₁ w) 0`; if `w ≠ 0` then `c₁ w ≠ 0`, and then `‖c₁ w‖ • linVecC (c₁ w / ‖c₁ w‖) = w`
because `‖c₁ w / ‖c₁ w‖‖ = 1` makes the second component `1 - ‖·‖²` vanish (this is the identity
`Work.Drive.smul_linVecC`). -/

/-- **Every non-zero vector of the boundary line `span {e₀, e₁}` is a non-zero real multiple of a
unit boundary lift of the disk model.** -/
theorem exists_linVecC_smul_eq {w : Work.Drive.Eucl 3}
    (hw : w ∈ Submodule.span ℝ ({Work.Drive.linE0, Work.Drive.linE1} : Set (Work.Drive.Eucl 3)))
    (hw0 : w ≠ 0) :
    ∃ (z : ℂ) (a : ℝ), ‖z‖ = 1 ∧ a ≠ 0 ∧ a • Work.Drive.linVecC z = w := by
  -- the second complex coordinate is a linear functional vanishing on `e₀` and `e₁`
  have hc2 : Work.Drive.c₂ w = 0 := by
    obtain ⟨p, q, hpq⟩ := Submodule.mem_span_pair.mp hw
    rw [← hpq]
    simp [Work.Drive.c₂, Work.Drive.linE0, Work.Drive.linE1]
  -- hence `w = (c₁ w, 0)`
  have hw_eq : w = Work.Drive.ofComplex (Work.Drive.c₁ w) 0 := by
    have h := Work.Drive.ofComplex_c₁_c₂ w
    rw [hc2] at h
    exact h.symm
  -- and `c₁ w ≠ 0` since `w ≠ 0`
  have hc1 : Work.Drive.c₁ w ≠ 0 := by
    intro h
    apply hw0
    rw [hw_eq, h]
    ext i; fin_cases i <;> simp [Work.Drive.ofComplex]
  have hne : ((‖Work.Drive.c₁ w‖ : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact norm_ne_zero_iff.mpr hc1
  -- normalising `c₁ w` gives a unit complex number
  have hzn : ‖Work.Drive.c₁ w / (((‖Work.Drive.c₁ w‖ : ℝ)) : ℂ)‖ = 1 := by
    rw [norm_div, Work.Drive.norm_ofReal_eq_abs, abs_of_nonneg (norm_nonneg _),
      div_self (norm_ne_zero_iff.mpr hc1)]
  refine ⟨Work.Drive.c₁ w / (((‖Work.Drive.c₁ w‖ : ℝ)) : ℂ), ‖Work.Drive.c₁ w‖, hzn,
    norm_ne_zero_iff.mpr hc1, ?_⟩
  -- `‖c₁ w‖ • linVecC (c₁ w / ‖c₁ w‖) = (c₁ w, ‖c₁ w‖ * 0) = (c₁ w, 0) = w`
  rw [Work.Drive.smul_linVecC]
  have h1 : ((‖Work.Drive.c₁ w‖ : ℝ) : ℂ) * (Work.Drive.c₁ w / (((‖Work.Drive.c₁ w‖ : ℝ)) : ℂ))
      = Work.Drive.c₁ w := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hne]
  rw [h1, hzn]
  simp only [one_pow, sub_self, mul_zero, Complex.ofReal_zero]
  exact hw_eq.symm

end Work.Drive
