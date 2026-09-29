import Mathlib
import Submission.Work.A14D.crux_defs
import Submission.Work.A14D.exists_sol_LZ_convex
import Submission.Work.A14D.eqOn_of_sol_LZ

namespace Work.A14D

open Complex Metric Filter
open scoped Topology

noncomputable section

/-- **Upper extension across the real axis.**  Every holomorphic solution `D` of `LZ y = 0` on
`Om1 = {Im ≠ 0 ∨ 1 < Re}` (in particular on the upper half-plane, `cruxU`) extends to a
holomorphic solution `G` of `LZ y = 0` on the convex region
`cruxV = ball 1 (8/9) ∩ {Re < 1}`, which meets the real axis but avoids the singular points
`0, 1/9, 1` of the operator.

Proof: `cruxV` is open and convex and `PZ ≠ 0` on it, so the second order linear ODE
`LZ y = 0` has a solution there with prescribed value and derivative at any point
(`exists_sol_LZ_convex`); pick the point `z₀ ∈ cruxU ∩ cruxV` and match `D` at `z₀`.  On the open
preconnected set `cruxU ∩ cruxV ⊆ Om1` the two solutions agree by uniqueness for the system
(`eqOn_of_sol_LZ`). -/
theorem crux_upper_extension (D : ℂ → ℂ) (hD : DifferentiableOn ℂ D Om1)
    (hDL : ∀ z ∈ Om1, LZ D z = 0) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G cruxV ∧ (∀ z ∈ cruxV, LZ G z = 0) ∧
      Set.EqOn G D (cruxU ∩ cruxV) := by
  obtain ⟨z₀, hz₀⟩ := nonempty_cruxU_inter_cruxV
  obtain ⟨G, hGdiff, hGz₀, hGder, -, hGL⟩ :=
    exists_sol_LZ_convex isOpen_cruxV convex_cruxV (fun z hz => PZ_ne_zero_of_mem_cruxV hz) hz₀.2
      (D z₀) (deriv D z₀)
  refine ⟨G, hGdiff, hGL, ?_⟩
  have hUo : IsOpen (cruxU ∩ cruxV) := isOpen_cruxU.inter isOpen_cruxV
  have hUc : IsPreconnected (cruxU ∩ cruxV) :=
    (convex_cruxU.inter convex_cruxV).isPreconnected
  have hP : ∀ z ∈ cruxU ∩ cruxV, PZ z ≠ 0 := fun _ hz => PZ_ne_zero_of_mem_cruxU_inter hz
  have hD' : DifferentiableOn ℂ D (cruxU ∩ cruxV) :=
    hD.mono fun _ hz => cruxU_subset_Om1 hz.1
  have hG' : DifferentiableOn ℂ G (cruxU ∩ cruxV) := hGdiff.mono Set.inter_subset_right
  have hDL' : ∀ z ∈ cruxU ∩ cruxV, LZ D z = 0 := fun _ hz => hDL _ (cruxU_subset_Om1 hz.1)
  have hGL' : ∀ z ∈ cruxU ∩ cruxV, LZ G z = 0 := fun _ hz => hGL _ hz.2
  exact eqOn_of_sol_LZ hUo hUc hP hG' hD' hGL' hDL' hz₀ hGz₀ hGder

end

end Work.A14D
