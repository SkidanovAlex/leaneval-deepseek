import Mathlib
import Submission.Work.CoreTopology.Disk
import Submission.Work.CoreTopology.circle_lift_eq_of_extends_disk
import Submission.Work.CoreTopology.TorusDichotomyDefs
import Submission.Work.CoreTopology.torusHeight_eq_one_iff
import Submission.Work.CoreTopology.horizVec_ne_zero_of_disc
import Submission.Work.CoreTopology.meridVec_ne_zero_of_disc
import Submission.Work.CoreTopology.horizVec_torusMap_div_norm
import Submission.Work.CoreTopology.meridVec_torusMap_div_norm
import Submission.Work.CoreTopology.disk_sign_dichotomy
import Submission.Work.CoreTopology.circle_lift_eq_of_extends_disk_of_normCircle

namespace Work.CoreTopology

set_option linter.unusedVariables false

/-- **The classification of compressing loops on the standard torus by their winding vector.** Let `α` be an essential closed curve on the standard torus of revolution which bounds an embedded disc in `ℝ³` whose interior is disjoint from the torus (Pardon's set `U`). Then `α` is homotopic in the torus to a multiple of the meridian or of the longitude: one of the two components of its winding vector vanishes for every lift.

The geometric input is that the interior of the bounding disc lies in one of the two components of `ℝ³ ∖ F`. These are the solid torus `{ (r-2)² + z² < 1 }` inside the torus and the exterior `{ 1 < (r-2)² + z² }`, where `r = sqrt (x²+y²)`, `z` the third coordinate; we also have the polynomial characterisation `P ∈ standard.carrier ↔ (x²+y²+z²+3)² = 16(x²+y²)`.

* If the (connected) open disc part lies in the bounded component, the longitude coordinate `θ` extends continuously: `P ↦ normalize (P₀, P₁)` is continuous and nonvanishing there (and on `F`), and its value at `α t = torusMap (Θ t) (Φ t)` is `Circle.exp (Θ t)`. Hence `t ↦ Circle.exp (L.Θ t)` extends continuously over the closed unit disc, and `circle_lift_eq_of_extends_disk` gives `L.Θ (2π) = L.Θ 0`, i.e. `a = 0` — for every lift `L`.
* If it lies in the unbounded component, the same argument with `P ↦ normalize (sqrt (P₀²+P₁²) - 2, P₂)`, whose value at `torusMap (Θ t) (Φ t)` is `Circle.exp (Φ t)`, gives `b = 0` for every lift. -/
theorem compressing_winding_dichotomy (α : ClosedCurve standard)
    (hess : IsEssential standard α) (hb : BoundsDiskInComplement standard α) :
    (∀ L : LiftOf standard α, (L.winding).2 = 0) ∨
      (∀ L : LiftOf standard α, (L.winding).1 = 0) := by
  obtain ⟨e, _hinj, hbd, hoff⟩ := hb
  -- The height function on the closed disc, and the fact that it misses the value `1`
  -- on the open disc (because the open disc avoids `F`, the level set `{torusHeight = 1}`).
  have hHcont : Continuous fun z : Metric.closedBall (0 : ℂ) 1 => torusHeight (e z) :=
    continuous_torusHeight.comp e.continuous
  have hne : ∀ z : Metric.closedBall (0 : ℂ) 1, ‖(z : ℂ)‖ < 1 → torusHeight (e z) ≠ 1 := by
    intro z hz h1
    exact hoff z hz ((torusHeight_eq_one_iff (e z)).mp h1)
  -- Hence the open disc lies entirely in one of the two components of the complement.
  rcases disk_sign_dichotomy (fun z => torusHeight (e z)) hHcont hne with hout | hin
  · -- The disc lies in the exterior component `{1 < torusHeight}`: the meridian coordinate
    -- `Φ` of any lift is a loop, so the second component of the winding vector vanishes.
    left
    intro L
    have hW0 : ∀ z : Metric.closedBall (0 : ℂ) 1, meridVec (e z) ≠ 0 :=
      meridVec_ne_zero_of_disc α e hbd hout
    have hlift : ∀ t : ℝ,
        normCircle (meridVec (e (circlePoint t))) (hW0 (circlePoint t)) = Circle.exp (L.Φ t) := by
      intro t
      apply Subtype.ext
      rw [normCircle_coe, Circle.coe_exp]
      rw [show e (circlePoint t) = α.γ t from hbd t,
        show α.γ t = Work.Core.torusMap (L.Θ t) (L.Φ t) from (L.lifts t).symm]
      exact meridVec_torusMap_div_norm (L.Θ t) (L.Φ t)
    have hloop : L.Φ (2 * Real.pi) = L.Φ 0 :=
      circle_lift_eq_of_extends_disk_of_normCircle (fun z => meridVec (e z))
        (continuous_meridVec.comp e.continuous) hW0 L.Φ L.contΦ hlift
    have hspec := L.winding_spec.2
    have hmul : ((L.winding).2 : ℝ) * (2 * Real.pi) = 0 := by linarith [hspec]
    rcases mul_eq_zero.mp hmul with h | h
    · exact_mod_cast h
    · exact absurd h two_pi_ne_zero
  · -- The disc lies in the bounded component `{torusHeight < 1}`: the longitude coordinate
    -- `Θ` of any lift is a loop, so the first component of the winding vector vanishes.
    right
    intro L
    have hW0 : ∀ z : Metric.closedBall (0 : ℂ) 1, horizVec (e z) ≠ 0 :=
      horizVec_ne_zero_of_disc α e hbd hin
    have hlift : ∀ t : ℝ,
        normCircle (horizVec (e (circlePoint t))) (hW0 (circlePoint t)) = Circle.exp (L.Θ t) := by
      intro t
      apply Subtype.ext
      rw [normCircle_coe, Circle.coe_exp]
      rw [show e (circlePoint t) = α.γ t from hbd t,
        show α.γ t = Work.Core.torusMap (L.Θ t) (L.Φ t) from (L.lifts t).symm]
      exact horizVec_torusMap_div_norm (L.Θ t) (L.Φ t)
    have hloop : L.Θ (2 * Real.pi) = L.Θ 0 :=
      circle_lift_eq_of_extends_disk_of_normCircle (fun z => horizVec (e z))
        (continuous_horizVec.comp e.continuous) hW0 L.Θ L.contΘ hlift
    have hspec := L.winding_spec.1
    have hmul : ((L.winding).1 : ℝ) * (2 * Real.pi) = 0 := by linarith [hspec]
    rcases mul_eq_zero.mp hmul with h | h
    · exact_mod_cast h
    · exact absurd h two_pi_ne_zero

end Work.CoreTopology
