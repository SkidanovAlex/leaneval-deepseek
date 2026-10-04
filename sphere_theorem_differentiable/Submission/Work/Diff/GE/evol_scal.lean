import Mathlib
import Submission.Diff.Grad
import Submission.CurvatureVec
import Submission.ChartCurv
import Submission.Diff.Evol
import Submission.Work.Diff.GE.evol_scal_kit
import Submission.Work.Diff.Evol.curv_variation
import Submission.Work.Diff.GE.curv_evolution_kit
import Submission.Work.Diff.GE.flowContAtZeroScal_of_isRicciFlow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

CONTEXT: this is one area of the Brendle–Schoen differentiable sphere theorem, driven by the lead. Read HANDOFF.md.
The contracts in Submission/Diff/Interfaces.lean and Submission/Diff/Alg.lean are frozen. Your statement's hypotheses are other
areas' contracts: USE them, do not re-prove them. Go wide: file all the independent sub-lemmas at once,
each with an exact statement, and write your assembly against their statements. If your statement looks
false or unprovable as stated, say so at once in `declare_false` with a precise reason. The lead will fix it.
ROUTE. Hamilton's evolution equations under Ricci flow (Hamilton 1982 §7, 13; Chow–Knopf ch. 6; Topping ch. 2).
Derive them from LCVariation with h = −2Ric.
Uhlenbeck trick: at fixed x, frames with ∂ₜeᵢ = Ric(eᵢ)^♯ stay G(t)-orthonormal, and in them the components
R_ijkl = g(R(eᵢ,eⱼ)eₗ, eₖ) satisfy ∂ₜR = ΔR + Q(R), with Q exactly as in Alg.lean.
Norms are frame-independent, so rmNormSq etc. may be computed in these frames.
SANITY (prove as a lemma first): Q (Iso n) = (2*(n−1)) • Iso n. The unit round sphere under Ricci flow has
g(t) = (1 − 2(n−1)t)g₀ and R = K·Iso with K' = 2(n−1)K², consistent with ∂R = Q(R) when ∇R = 0.
Also scalAlg (Q R) = 2 ricSq R (the scal equation), and Δ|T|² = 2⟨T,ΔT⟩ + 2|∇T|² (the |Rm|² equation).
For EV2 the ∇Rm equation is ∂ₜ∇Rm = Δ∇Rm + Rm*∇Rm. The −2|∇²Rm|² term may be dropped.
-/

/-
Assembly of EV3 (implemented per the lead's later guidance, see `evol_scal_kit.lean`):

* `Work.Diff.Evol.curv_variation` (contract CV) gives `CurvVariation I M` from `LCVariation`;
* `Work.Diff.GE.curv_evolution_kit` (contract CE, assembled in this area; the Evol area's
  `Work.Diff.Evol.curv_evolution` proves the same statement) gives
  `∂ₛ rmFrame = lapRmFrame + Q(rmFrame)` in Uhlenbeck frames;
* `Work.Diff.GE.laplAt_scalAt_eq_scalAlg_lapRmFrame` (in `scal_lapl.lean`) gives the scalar case of
  contract LP, `scalAlg (lapRmFrame) = Δ scal`, without any parallel frame;
* `Work.Diff.GE.evol_scal_kit` assembles these into `hasDerivAt` on the interior `(0,T)` and (via
  `Work.Diff.GE.derivWithin_Ico_zero`, needing continuity of both sides at `0⁺` --
  `Work.Diff.GE.flowContAtZeroScal_of_isRicciFlow`) also at `t = 0`;
* the frame-independence lemmas in the kit (`scalAt_eq_scalAlg_rmFrame_of_isONFrame`), the
  `Q`-trace identity (`scalAlg_Q_rmFrame`, from H2 `Work.Diff.Alg.Pinch.scalAlg_Q`) and
  `ricNormSq_eq_ricSq_rmFrame` convert the component evolution into the frozen quantities.
-/

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

theorem evol_scal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : LCSmooth I M) (hLV : LCVariation I M) :
    EvolScal I M := by
  have hCV : CurvVariation I M := Work.Diff.Evol.curv_variation hLC hLV
  have hCE : CurvEvolution I M := Work.Diff.GE.curv_evolution_kit hLC hLV hCV
  have hcont : FlowContAtZeroScal (I := I) (M := M) :=
    Work.Diff.GE.flowContAtZeroScal_of_isRicciFlow hLC
  exact evol_scal_of_CE_of_FlowCont hLC hCE hcont

end Work.Diff.GE
