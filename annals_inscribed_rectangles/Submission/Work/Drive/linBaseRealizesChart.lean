import Mathlib
import Submission.Work.Drive.linShearCharts

/-!
# Every linear chart is the middle member of the repaired family `linBase A`

The `hn2` producer must build its reference plane from a linear chart whose normal functional is the one
the `(F1)` lane chose (`GenAlong ℓ` along the two class lifts, see `F1_GENERICITY_RESOLUTION.md`), while
the ends lane needs the general position of the three linear planes.  The repaired family
`Work.Drive.linBase A` of `Drive/linShearCharts.lean` satisfies the general position for **every** `A`
(`Work.Drive.finrank_iInf_linSub_linBase`, `Work.Drive.hgen_linBase`), so it remains to realise the
chosen chart inside it — and that is *exact*:

> `Work.Drive.linBase_rightInverse` —
> `linBase ((coordPermCLM (coordPerms 2)).symm.trans ((linShear 2).symm.trans φ)) 2 = φ`

for every `φ`.  Hence the reference plane of the `(F1)` lane is *literally* the third plane of a
general-position triple of repaired linear charts: no genericity of the functional is lost, and the
parametric oddness `Work.Drive.refTriple_mixedFactors` (which is existential in its own `φ`) applies to
the producer's reference plane verbatim.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-- **The repaired family hits every linear chart in slot `2`**, with the explicit parameter
`A := φ * (linShear 2)⁻¹ * (coordPermCLM (coordPerms 2))⁻¹`.  (`linBase A k = A ∘ coordPermCLM
(coordPerms k) ∘ linShear k`, `Work.Drive.linBase_apply`.) -/
theorem linBase_rightInverse (φ : Eucl 3 ≃L[ℝ] Eucl 3) :
    linBase ((coordPermCLM (coordPerms 2)).symm.trans
      ((linShear 2).symm.trans φ)) 2 = φ := by
  ext x
  simp only [linBase_apply, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.symm_apply_apply]

/-- **The reference chart can be prescribed, with general position for free.**  For every linear chart
`φ₂` and every `c > 0` there is a triple `φ` of linear charts with `φ 2 = φ₂` and the general position
of the three planes (`hrank`) *and* the boundary avoidance `hgen` of `linPlaneChartsEndTripleReg`/
`exists_linPlaneCharts_hgen` (the two clauses the ends lane's counting needs).

This is the one-stop form of the "φ-chooser" for the `hn2` producer: the `(F1)` lane's chart (whose
normal functional is the `GenAlong`-generic one) becomes the *third* plane of a general-position triple,
so the reference plane `refPlanePres φ lam` carries the chosen functional *and* the ends lane's
non-degeneracy data. -/
theorem exists_triple_chart_of_middle (φ₂ : Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c) :
    ∃ φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3,
      φ 2 = φ₂ ∧
      ∃ h : Module.finrank ℝ ↥(⨅ k : Fin 3, linSub (φ k)) = 1,
        ∀ (k : Fin 3) (z : ℂ), ‖z‖ = 1 →
          linPlaneChart (φ k) c hc z ≠ linCommonPt φ c hc h :=
  ⟨linBase ((coordPermCLM (coordPerms 2)).symm.trans ((linShear 2).symm.trans φ₂)),
    linBase_rightInverse φ₂, finrank_iInf_linSub_linBase _, fun k z hz =>
      hgen_linBase _ c hc k z hz⟩

end

end Work.Drive
