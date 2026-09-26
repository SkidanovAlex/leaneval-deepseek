import Mathlib
import Submission.Work.BoxShrink.PinchOff.TangentData.Basic

namespace Work.BoxShrink.PinchOff

/-!
# The box sphere of the tangent configuration carries no essential loop

The configuration (`TangentData/Basic.lean`) is the standard torus with the box centred at
`c = (1,0,0) = ψ 0 π`, side-length permutation `σ = (0 1 2)` and radius `s = 13/10`; the plane
`{x = 1}` is tangent to the torus at the centre.  The shape lemma `sphereSet_shape` says that a
point `ψ u v` of the torus lying on the box sphere `{boxNorm = 13/10}` satisfies

* `cos v > -0.95`, and
* `cos (u - π) > -0.92`  (equivalently `cos u < 0.92`).

Composing with a lift `L` of a closed curve of the torus whose image lies in the box sphere gives
two continuous functions,

`t ↦ cos (L.Φ t)` bounded below by `-0.95` and `t ↦ cos (L.Θ t - π)` bounded below by `-0.92`,

whose arguments advance over one period by `2π` times the two winding numbers.  Since a
continuous function `f` with `cos (f t) > c > -1` can advance by strictly less than `2π` over one
period (`abs_sub_lt_of_cos_gt`), both winding numbers vanish
(`int_eq_zero_of_cos_gt`).  Hence no such curve is essential.
-/

open Set

theorem tangent_sphereSet_not_containsEssentialLoop :
    ¬ (Work.CoreTopology.standard).ContainsEssentialLoop
      (Work.BoxShrink.Core.sphereSet Work.BoxShrink.PinchOff.tangentCtr
        Work.BoxShrink.PinchOff.tangentCyc3 Work.BoxShrink.PinchOff.tangentRad) := by
  rintro ⟨γ, hess, hmem⟩
  obtain ⟨L, hL⟩ := hess
  -- The shape lemma, transported along the lift, for every `t`.
  have hshape : ∀ t : ℝ, (-0.95 : ℝ) < Real.cos (L.Φ t) ∧
      (-0.92 : ℝ) < Real.cos (L.Θ t - Real.pi) := by
    intro t
    apply sphereSet_shape
    have h := L.lifts t
    simp only [Work.CoreTopology.standard_psi] at h
    rw [h]
    exact hmem t
  -- The meridian winding number vanishes.
  have hb : (L.winding).2 = 0 := by
    refine int_eq_zero_of_cos_gt (f := L.Φ) (c := (-0.95 : ℝ)) (m := (L.winding).2)
      L.contΦ (by norm_num) (by norm_num) (fun t => (hshape t).1) ?_
    have hspec := L.winding_spec
    linarith [hspec.2]
  -- The longitude winding number vanishes.
  have ha : (L.winding).1 = 0 := by
    refine int_eq_zero_of_cos_gt (f := fun t : ℝ => L.Θ t - Real.pi) (c := (-0.92 : ℝ))
      (m := (L.winding).1) (L.contΘ.sub continuous_const) (by norm_num) (by norm_num)
      (fun t => (hshape t).2) ?_
    have hspec := L.winding_spec
    linarith [hspec.1]
  exact hL (Prod.ext ha hb)

end Work.BoxShrink.PinchOff
