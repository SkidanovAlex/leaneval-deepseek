import Mathlib
import Submission.Work.BoxShrink.PinchOff.TangentData.Basic

namespace Work.BoxShrink.PinchOff

/-!
# The slice of the tangent configuration carries no essential loop

The slicing plane `{x = 1}` of the tangent configuration is tangent to the standard torus at
`ψ 0 π`, and inside the (open) box the trace of the plane is the "X" shaped pair of arcs through
the tangency point: `Work.BoxShrink.PinchOff.sliceRegion_shape` records the two one-sided
confinements of the coordinates of any point of the slice,

* `0 < cos u` (from the plane equation `(2 + cos v) cos u = 1`), and
* `0 < cos (v - π)` (from the box bound `|y₁| < 13/10`).

Both are *global* confinement conditions on a continuous periodic function: a continuous real
function all of whose values have a positive cosine is confined to an interval of length `π`
(`Work.BoxShrink.PinchOff.abs_sub_lt_of_cos_gt`, with `c = 0`), so over one period a lift of a
loop of the slice can advance by less than `π < 2π` in each parameter, and its winding increment
must vanish.  Hence no loop of the slice is essential, i.e. the winding span of the slice is `⊥`.
-/

noncomputable section

open LeanEval.KnotTheory.PardonDistortion

/-- **The slice of the tangent configuration carries no essential loop**: the winding span of
`sliceRegion standard tangentRad tangentCtr tangentCyc3 0` in `ℚ² = H₁(T²; ℚ)` is `⊥`. -/
theorem tangent_sliceRegion_span_eq_bot :
    Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
      (Work.BoxShrink.Core.sliceRegion Work.CoreTopology.standard
        Work.BoxShrink.PinchOff.tangentRad Work.BoxShrink.PinchOff.tangentCtr
        Work.BoxShrink.PinchOff.tangentCyc3 0) = ⊥ := by
  rw [Work.SurgeryInvariance.WindingSpan_eq_bot_iff]
  rintro ⟨γ, ⟨L, hL⟩, hγ⟩
  -- every point of the slice satisfies the two one-sided bounds of `sliceRegion_shape`
  have hshape : ∀ t : ℝ, 0 < Real.cos (L.Θ t) ∧ 0 < Real.cos (L.Φ t - Real.pi) := fun t => by
    have hmem : Work.Core.torusMap (L.Θ t) (L.Φ t) ∈
        Work.BoxShrink.Core.sliceRegion Work.CoreTopology.standard
          Work.BoxShrink.PinchOff.tangentRad Work.BoxShrink.PinchOff.tangentCtr
          Work.BoxShrink.PinchOff.tangentCyc3 0 := by
      have h := hγ t
      rwa [← L.lifts t] at h
    exact Work.BoxShrink.PinchOff.sliceRegion_shape hmem
  -- both parameters are globally confined to an interval of length `π`
  have h1 : (L.winding).1 = 0 := by
    apply Work.BoxShrink.PinchOff.int_eq_zero_of_cos_gt (c := 0) (m := (L.winding).1) L.contΘ
      (by norm_num) (by norm_num) (fun t => (hshape t).1)
    have := L.winding_spec.1
    linarith
  have h2 : (L.winding).2 = 0 := by
    apply Work.BoxShrink.PinchOff.int_eq_zero_of_cos_gt (c := 0) (m := (L.winding).2)
      (L.contΦ.sub continuous_const) (by norm_num) (by norm_num)
      (fun t => (hshape t).2)
    show L.Φ (2 * Real.pi) - Real.pi - (L.Φ 0 - Real.pi) = (L.winding.2 : ℝ) * (2 * Real.pi)
    linarith [L.winding_spec.2]
  exact hL (Prod.ext h1 h2)

end

end Work.BoxShrink.PinchOff
