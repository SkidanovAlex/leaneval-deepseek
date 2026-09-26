import Mathlib
import Submission.Work.Drive.EpsForm.WaypointDiscDefs

namespace Work.Drive.EpsForm

noncomputable section

/-- The parameter pair `(kapTheta, kapPhi)` is a lift of `kapCurve`: the curve is
*defined* by its parametrisation, so this is definitional. -/
def kapLift : Work.CoreTopology.LiftOf Work.CoreTopology.standard kapCurve where
  Θ := kapTheta
  Φ := kapPhi
  contΘ := continuous_kapTheta
  contΦ := continuous_kapPhi
  lifts := fun _ => rfl

@[simp] theorem kapLift_Θ (t : ℝ) : kapLift.Θ t = kapTheta t := rfl
@[simp] theorem kapLift_Φ (t : ℝ) : kapLift.Φ t = kapPhi t := rfl

/-- The lift `(kapTheta, kapPhi)` has vanishing winding vector: both coordinates are
`2π`-periodic, so they do not advance over one period. -/
theorem kapLift_winding : kapLift.winding = (0, 0) := by
  have hspec := kapLift.winding_spec
  have h1 : (kapLift.winding).1 = 0 := by
    have hΘ : kapLift.Θ (2 * Real.pi) = kapLift.Θ 0 := by
      rw [kapLift_Θ]; simpa using kapTheta_periodic 0
    have hmul : ((kapLift.winding).1 : ℝ) * (2 * Real.pi) = 0 := by
      have := hspec.1; rw [hΘ] at this; linarith
    rcases mul_eq_zero.mp hmul with h | h
    · exact_mod_cast h
    · exact absurd h Work.CoreTopology.two_pi_ne_zero
  have h2 : (kapLift.winding).2 = 0 := by
    have hΦ : kapLift.Φ (2 * Real.pi) = kapLift.Φ 0 := by
      rw [kapLift_Φ]; simpa using kapPhi_periodic 0
    have hmul : ((kapLift.winding).2 : ℝ) * (2 * Real.pi) = 0 := by
      have := hspec.2; rw [hΦ] at this; linarith
    rcases mul_eq_zero.mp hmul with h | h
    · exact_mod_cast h
    · exact absurd h Work.CoreTopology.two_pi_ne_zero
  exact Prod.ext h1 h2

/-- **The curve `κ` is inessential.**  The closed curve `kapCurve` of the standard torus
(`γ s = torusMap (kapTheta s) (kapPhi s)`, `kapTheta s = u0 + (v0-u0)|sin (s/2)|`,
`kapPhi s = phLift (kapTheta s)` for `sin s > 0` and `phLift (kapTheta s) + dlt (kapTheta
s)` for `sin s ≤ 0`) has vanishing winding vector, hence is not essential.

Route: the pair `(kapTheta, kapPhi)` is a lift of `kapCurve`
(`Work.CoreTopology.LiftOf`), because the curve is *defined* by the parametrisation
(`standard.psi = torusMap`).  Both coordinates are `2π`-periodic sequences:
`kapTheta (2π) - kapTheta 0 = 0` since `kapTheta (2π) = kapTheta 0 = u0`
(`kapTheta_periodic`, `kapTheta_zero`), and `kapPhi (2π) - kapPhi 0 = 0` since `kapPhi` is
`2π`-periodic (`Work.Drive.EpsForm.kapPhi_periodic`, proved in the imported file).  So that
lift has winding `(0,0)`, and by `Work.CoreTopology.LiftOf.winding_eq` (the winding vector
is independent of the lift) no lift of `kapCurve` has nonzero winding, i.e.
`¬ IsEssential standard kapCurve`. -/
theorem kapCurve_not_essential :
    ¬ Work.CoreTopology.IsEssential Work.CoreTopology.standard kapCurve := by
  intro h
  exact h.winding_ne kapLift (kapLift_winding)

end

end Work.Drive.EpsForm
