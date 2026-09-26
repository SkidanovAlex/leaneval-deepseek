import Submission.Work.Topology.Classical.Defs
import Submission.Work.Topology.Classical.jordanSchoenflies_single

/-!
# A Jordan curve on the round sphere bounds a disc with interior disjoint from the curve

The literal content of "assignment item 1": a simple closed curve on `RoundSphere` bounds a closed
disc contained in the sphere whose *interior* misses the curve.  This is
`Work.Topology.Classical.jordanSchoenflies_single` with the openness and covering clauses dropped
and the disjointness of the open disc from the curve made explicit (it follows from injectivity of
the disc, the boundary points being exactly the curve). -/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.CoreTopology
open Work.InnermostDisk

namespace Work.Topology.Classical

noncomputable section

/-- **A simple closed curve on the round sphere bounds a closed disc in the sphere whose interior
is disjoint from the curve.** -/
theorem bounds_disc_interior_disjoint (h : JordanSchoenfliesSphere) {c : ℝ → R3}
    (hc : IsJordanCurveRound c) :
    ∃ e : C(Disc, R3), Function.Injective e ∧ (∀ θ : ℝ, e (circlePoint θ) = c θ) ∧
      Set.range e ⊆ RoundSphere ∧
      (∀ z : Disc, ‖(z : ℂ)‖ < 1 → e z ∉ Set.range c) := by
  obtain ⟨e, -, hinj, -, hbd, -, hmem, -, -, -, -, -⟩ := jordanSchoenflies_single h hc
  refine ⟨e, hinj, hbd, ?_, ?_⟩
  · rintro _ ⟨z, rfl⟩
    exact hmem z
  · rintro z hz ⟨θ, hθ⟩
    have h1 : e z = e (circlePoint θ) := by rw [hbd θ, hθ]
    have h2 : z = circlePoint θ := hinj h1
    have h3 : ‖(z : ℂ)‖ = 1 := by rw [h2, circlePoint_coe, Complex.norm_exp_ofReal_mul_I]
    linarith

end

end Work.Topology.Classical
