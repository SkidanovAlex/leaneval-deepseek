/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/ClassCStepSlice.lean` — the class-`C` step with the increment's
# metric data taken from the SLICE

`ThetaFromEps.classC_step_of_epsMem` (`EpsEngine/ThetaFromEps.lean`, the lead's ruling of
2026-10-12) is the drop-in replacement for `classC_step_of_flat`: it needs no θ-uniformity at all,
with the increment's data

    SmoothOpen (epsInc n τ),  HkMem α 4 (epsInc n τ),  EpsMem α (epsInc n τ),  fsm (Pz (J_ε (epsInc n τ)))

as its only inputs beyond the datum's class-`C` clause.  `EpsEngine/EpsIncData.lean` produces the
first two of those from the corresponding data of the **slice** `slice (epsIter g₀ (n+1)) τ` (which
the engine's own `SmoothOpen`/`(H4)` clauses supply); this module performs that substitution, so
that the class-`C` clause of the `(n+1)`-st Picard level follows from

* the datum's `ClassC α (Pz (J_ε g₀))`, `SmoothOpen g₀`, `HkMem α 4 g₀`,
* `SmoothOpen`/`HkMem α 4` of the *slice* `slice (epsIter g₀ (n+1)) τ`,
* `EpsMem α (epsInc n τ)` — on the route supplied by `BddLip_of_epsClass` +
  `EpsSq_intervalIntegral_le_gen` (the engine's `EpsSq`-sized gate), **not** by `epsMem_epsInc`
  (whose `AK`-hypotheses the engine does not carry), and
* `fsm (Pz (J_ε (epsInc n τ)))` — the single remaining analytic residual.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.EpsEngine.ThetaFromEps
import Submission.Work.FTS.EpsEngine.EpsIncData

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The class-`C` clause of the `(n+1)`-st Picard level, from the slice's metric data.**  This is
`ThetaFromEps.classC_step_of_epsMem` with the increment's `SmoothOpen`/`ℋ⁴` inputs produced from the
slice (`EpsIncData.smoothOpen_epsInc`, `EpsIncData.hkMem_epsInc`). -/
theorem classC_step_of_slice {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {τ : ℝ} {n : ℕ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1) (hα1 : α ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hC₀ : Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε g₀)))
    (hgsm : Work.FTS.EllipticEst.SmoothOpen g₀) (hgmem : Work.Spaces.HkMem α 4 g₀)
    (hsmS : Work.FTS.EllipticEst.SmoothOpen (slice (epsIter α ρ ε Φs E g₀ (n + 1)) τ))
    (hmemS : Work.Spaces.HkMem α 4 (slice (epsIter α ρ ε Φs E g₀ (n + 1)) τ))
    (hIEps : Work.FTS.StrongEps.EpsMem α (epsInc α ρ ε Φs E g₀ n τ))
    (hIfsm : ∀ m : ℕ, ContDiffOn ℝ m
      (Work.Elliptic.Fstar (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε
        (epsInc α ρ ε Φs E g₀ n τ)))) (Set.Ioi 0)) :
    Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε
      (slice (epsIter α ρ ε Φs E g₀ (n + 1)) τ))) :=
  Work.FTS.EpsEngine.ThetaFromEps.classC_step_of_epsMem hρ hα hα1 hε hε1 hC₀ hgsm hgmem
    (smoothOpen_epsInc hsmS hgsm) (hkMem_epsInc hsmS hgsm hmemS hgmem) hIEps hIfsm

end Work.FTS.EpsEngine
