import Mathlib
import Submission.Work.BoxShrink.PinchOff.RefuteNC.Config

/-!
# The upper half-region of the counterexample configuration is inessential

This module proves `Work.BoxShrink.PinchOff.RefuteNC.halfUp_inessential`: at the configuration of
`Config.lean` (the standard torus, box centre `(1, 19/10, 0)`, radius `1`, permutation `(0 1 2)`,
cutting plane `{x = 1/2}`) the **upper half-region** `Ω₊ = Ω ∩ {x > 1/2}` carries no essential
loop, so its winding span vanishes.

The mechanism is the one used for the tangent configuration
(`Work.BoxShrink.PinchOff.tangent_upperRegion_span_eq_bot_aux`, `TangentData/Basic.lean`): the
region confines the two parameters of a lift to *windows*, so no lift can advance by a nonzero
multiple of `2π` in either coordinate.  Concretely, a point `(2 + cos φ) cos θ, (2 + cos φ) sin θ,
sin φ` of `Ω₊` satisfies `(2 + cos φ) cos θ > 1/2` and `|(2 + cos φ) sin θ - 19/10| < 1`; hence

* `cos θ > 0` (the first bound, since `2 + cos φ > 0`), and
* `(2 + cos φ)² = x² + y² > (1/2)² + (9/10)² = 53/50 > (41/40)²`, so
  `cos φ > 41/40 - 2 = -39/40`.

Both are one-sided cosine bounds of the form handled by
`Work.BoxShrink.PinchOff.int_eq_zero_of_cos_gt`, which forces the corresponding winding
component of any loop carried by the region to vanish.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff.RefuteNC

noncomputable section

/-- **The upper half-region confines the parameters of its points.**  A point `ψ θ φ` of `Ω₊` has
`x = (2 + cos φ) cos θ > 1/2 > 0`, whence `cos θ > 0`, and `|y₁ - 19/10| < 1` gives
`(2 + cos φ)² = x² + y₁² > 53/50 > (41/40)²`, whence `cos φ > -39/40`. -/
theorem nc_upperRegion_shape {θ φ : ℝ}
    (h : Work.Core.torusMap θ φ ∈ Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard
      Work.BoxShrink.PinchOff.ncRad Work.BoxShrink.PinchOff.ncCtr
      Work.BoxShrink.PinchOff.ncCyc3 Work.BoxShrink.PinchOff.ncU) :
    0 < Real.cos θ ∧ (-39 / 40 : ℝ) < Real.cos φ := by
  obtain ⟨-, hbox, hy0⟩ := (Work.BoxShrink.Core.mem_upperRegion).mp h
  obtain ⟨h1, -, -⟩ := (Work.BoxShrink.PinchOff.mem_PBox_nc _).mp hbox
  simp only [Work.BoxShrink.PinchOff.ncCyc3_two, Work.BoxShrink.PinchOff.ncCtr_zero,
    Work.BoxShrink.PinchOff.ncU_eq] at hy0
  have hy0' : (1 / 2 : ℝ) < (Work.Core.torusMap θ φ) 0 := by linarith
  have h1' : (9 / 10 : ℝ) < (Work.Core.torusMap θ φ) 1 := by
    rw [abs_lt] at h1; linarith [h1.1]
  have hx0 : (Work.Core.torusMap θ φ) 0 = (2 + Real.cos φ) * Real.cos θ :=
    Work.CoreTopology.torusMap_apply_zero θ φ
  have hy1 : (Work.Core.torusMap θ φ) 1 = (2 + Real.cos φ) * Real.sin θ :=
    Work.CoreTopology.torusMap_apply_one θ φ
  have hρpos : (0 : ℝ) < 2 + Real.cos φ := by linarith [Real.neg_one_le_cos φ]
  have hcosθ : 0 < Real.cos θ := by nlinarith [hx0, hρpos, hy0']
  have hsum : (53 / 50 : ℝ) < (2 + Real.cos φ) ^ 2 := by
    have h2 : ((Work.Core.torusMap θ φ) 0) ^ 2 + ((Work.Core.torusMap θ φ) 1) ^ 2
        = (2 + Real.cos φ) ^ 2 := by
      rw [hx0, hy1]
      have h3 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
      nlinarith [h3]
    rw [← h2]
    nlinarith [hy0', h1']
  have hcosφ : (-39 / 40 : ℝ) < Real.cos φ := by
    have h416 : (41 / 40 : ℝ) ^ 2 < (53 / 50 : ℝ) := by norm_num
    have hlt : (41 / 40 : ℝ) < 2 + Real.cos φ := by nlinarith [hsum, hρpos]
    linarith
  exact ⟨hcosθ, hcosφ⟩

/-- **The upper half-region of the counterexample configuration carries no essential loop**: its
winding span vanishes. -/
theorem halfUp_inessential :
    Work.SurgeryInvariance.WindingSpan (Work.BoxShrink.PinchOff.surface Work.BoxShrink.PinchOff.idDiffeo)
      (Work.BoxShrink.PinchOff.HalfUp Work.BoxShrink.PinchOff.idDiffeo
        Work.BoxShrink.PinchOff.ncRad Work.BoxShrink.PinchOff.ncCtr
        Work.BoxShrink.PinchOff.ncCyc3 Work.BoxShrink.PinchOff.ncU) = ⊥ := by
  rw [Work.SurgeryInvariance.WindingSpan_eq_bot_iff]
  rintro ⟨γ, ⟨L, hL⟩, hγ⟩
  have hshape : ∀ t : ℝ, 0 < Real.cos (L.Θ t) ∧ (-39 / 40 : ℝ) < Real.cos (L.Φ t) := by
    intro t
    have hmem : Work.Core.torusMap (L.Θ t) (L.Φ t) ∈
        Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard
          Work.BoxShrink.PinchOff.ncRad Work.BoxShrink.PinchOff.ncCtr
          Work.BoxShrink.PinchOff.ncCyc3 Work.BoxShrink.PinchOff.ncU := by
      have h := hγ t
      rw [← L.lifts t] at h
      exact h
    exact nc_upperRegion_shape hmem
  have h1w : (L.winding).1 = 0 := by
    apply Work.BoxShrink.PinchOff.int_eq_zero_of_cos_gt (f := L.Θ) (c := 0) (m := (L.winding).1)
      L.contΘ (by norm_num) (by norm_num) (fun t => (hshape t).1)
    linarith [L.winding_spec.1]
  have h2w : (L.winding).2 = 0 := by
    apply Work.BoxShrink.PinchOff.int_eq_zero_of_cos_gt (f := L.Φ) (c := -39 / 40)
      (m := (L.winding).2) L.contΦ (by norm_num) (by norm_num) (fun t => (hshape t).2)
    linarith [L.winding_spec.2]
  exact hL (Prod.ext h1w h2w)

end

end Work.BoxShrink.PinchOff.RefuteNC
