import Mathlib
import Submission.Work.A14D.crux_defs
import Submission.Work.A14D.exists_sol_LZ_convex
import Submission.Work.A14D.eqOn_of_sol_LZ

namespace Work.A14D

open Complex Metric

/-- **Lower-half-disc continuation.**  Every solution `D` of `LZ y = 0` on `Om1` restricts to the
open half-disc `cruxL ∩ cruxV` from a global solution `G` of `LZ y = 0` on the convex open set
`cruxV`, which is free of the singular points `0, 1/9, 1` of `LZ`.

`cruxV ⊆ {PZ ≠ 0}` is open, convex and contains `cruxL ∩ cruxV`, so
`exists_sol_LZ_convex` produces the solution `G` prescribed by the Cauchy data `(D z₀, (deriv D) z₀)`
at a point `z₀` of the lower half-disc; uniqueness `eqOn_of_sol_LZ` on the open preconnected set
`cruxL ∩ cruxV` then forces `G = D` there. -/
theorem crux_lower_extension (D : ℂ → ℂ) (hD : DifferentiableOn ℂ D Om1)
    (hDL : ∀ z ∈ Om1, LZ D z = 0) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G cruxV ∧ (∀ z ∈ cruxV, LZ G z = 0) ∧
      Set.EqOn G D (cruxL ∩ cruxV) := by
  obtain ⟨z₀, hz₀⟩ := nonempty_cruxL_inter_cruxV
  obtain ⟨G, hGdiff, hGz₀, hGd, _, hGL⟩ :=
    exists_sol_LZ_convex isOpen_cruxV convex_cruxV
      (fun z hz => PZ_ne_zero_of_mem_cruxV hz) hz₀.2
      (D z₀) (deriv D z₀)
  refine ⟨G, hGdiff, hGL, ?_⟩
  refine eqOn_of_sol_LZ (isOpen_cruxL.inter isOpen_cruxV)
    (Convex.isPreconnected (convex_cruxL.inter convex_cruxV))
    (fun z hz => PZ_ne_zero_of_mem_cruxL_inter hz) (hGdiff.mono Set.inter_subset_right)
    (hD.mono cruxL_inter_cruxV_subset_Om1)
    (fun z hz => hGL z hz.2)
    (fun z hz => hDL z (cruxL_inter_cruxV_subset_Om1 hz)) hz₀ hGz₀ hGd

end Work.A14D
