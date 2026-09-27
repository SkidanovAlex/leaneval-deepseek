import Mathlib
import Submission.Work.Drive.WindingNumber
import Submission.Work.Drive.exists_winding_ne_zero

/-!
# Translating the winding point to the origin (input A, translation step)

`CAPPING_ANALYSIS.md`'s input A wants an off-curve point about which `γ` winds `±1`
(the doubled values `±2` of `Work.Drive.winding`).  `Work.Drive.exists_winding_ne_zero` already
supplies such a point `p`; the capping, however, works about the **origin** (the axis of the
configuration space is `midpoint = 0`).  This file records the translation: the winding of `γ` about
`p` *is* the winding about the origin of the translate `t ↦ γ t - p`, and hence some translate of `γ`
has nonzero winding about the origin — after which `Work.Drive.position_angle_lift` applies with
`h0 : ∀ x, γ' x ≠ 0` and gives the position-angle lift whose total is `±1`.
-/

set_option autoImplicit false
noncomputable section

namespace Work.Drive

open scoped Topology

/-- **Translation of the winding point.**  The direction curves of `γ` about `p` and of the translate
`t ↦ γ t - p` about the origin are the same function. -/
theorem dirCurve_translate (γ : UnitAddCircle → ℝ × ℝ) (hγ : Continuous γ) (p : ℝ × ℝ)
    (hp : p ∉ Set.range γ) (h0 : (0 : ℝ × ℝ) ∉ Set.range (fun t : UnitAddCircle => γ t - p)) :
    Work.Drive.dirCurve (fun t : UnitAddCircle => γ t - p) (hγ.sub continuous_const) 0 h0
      = Work.Drive.dirCurve γ hγ p hp := by
  funext t
  simp only [Work.Drive.dirCurve, sub_zero]

/-- **Translation of the winding point, on the winding number.**  The winding of `γ` about `p` equals
the winding of the translate `t ↦ γ t - p` about the origin; so the capping may translate `γ`
(target-invariantly) to put the point of `Work.Drive.exists_winding_ne_zero` at the origin. -/
theorem winding_translate (γ : UnitAddCircle → ℝ × ℝ) (hγ : Continuous γ) {p : ℝ × ℝ}
    (hp : p ∉ Set.range γ)
    (h0 : (0 : ℝ × ℝ) ∉ Set.range (fun t : UnitAddCircle => γ t - p)) :
    Work.Drive.winding (fun t : UnitAddCircle => γ t - p) (hγ.sub continuous_const) h0
      = Work.Drive.winding γ hγ hp := by
  unfold Work.Drive.winding
  congr 1
  exact dirCurve_translate γ hγ p hp h0

/-- **Input A, in the form the capping uses.**  For a continuous injective `C¹` closed curve there is a
translate whose winding about the *origin* is nonzero — i.e., after translating `γ`, the origin is an
enclosed point, so the position angle about it exists and winds `±1`
(`CAPPING_ANALYSIS.md`, input A). -/
theorem exists_translate_origin_winding_ne_zero (γ : UnitAddCircle → ℝ × ℝ) (hγ : Continuous γ)
    (hinj : Function.Injective γ)
    (hsmooth : ContDiff ℝ 1 (fun t : ℝ => γ (t : UnitAddCircle))) :
    ∃ (c : ℝ × ℝ) (h0 : (0 : ℝ × ℝ) ∉ Set.range (fun t : UnitAddCircle => γ t - c)),
      Work.Drive.winding (fun t : UnitAddCircle => γ t - c) (hγ.sub continuous_const) h0 ≠ 0 := by
  obtain ⟨p, hp, hne⟩ := exists_winding_ne_zero γ hγ hinj hsmooth
  have h0 : (0 : ℝ × ℝ) ∉ Set.range (fun t : UnitAddCircle => γ t - p) := by
    rintro ⟨t, ht⟩
    exact hp ⟨t, sub_eq_zero.mp ht⟩
  exact ⟨p, h0, by rw [winding_translate γ hγ hp h0]; exact hne⟩

end Work.Drive
