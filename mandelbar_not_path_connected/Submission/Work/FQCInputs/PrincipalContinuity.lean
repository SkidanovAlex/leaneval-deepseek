/-
# `Work.FQCInputs.PrincipalContinuity` — the MRMT-continuity input (S1 of the lead's design)

The continuation argument for the simplicity of the transported parabolic point
(`Submission/Work/NOTES_LEAD_mandelbar_simple.md` §3) needs one analytic input that is not yet in
the workspace: **continuity of the principal solution of the Beltrami equation in the
coefficient**, along coefficients that are uniformly admissible, uniformly supported and converge
almost everywhere.

It is being proved in the area `MRMTCont` as `Work.MRMT.Found.principal_tendsto_of_ae` (the
locally-uniform form).  Until it lands, the pointwise form below is carried as a named hypothesis;
`PrincipalContinuity.of_principal_tendsto_of_ae` records how the MRMT statement discharges it.
-/
import Mathlib
import Submission.Work.FQC.Defs
import Submission.Work.MRMTCont.Main

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology ComplexConjugate
open MeasureTheory Filter Set Function
open Classical

set_option linter.unusedVariables false

noncomputable section

namespace Work.FQCInputs

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.EL (RootParabolic F K)

/-- **The MRMT-continuity input (S1 of the lead's design).**  Along a sequence `μs` of uniformly
admissible coefficients — uniformly norm-bounded by `k < 1` with a common support ball — converging
almost everywhere to an admissible `μ`, the principal solutions converge locally uniformly. -/
def PrincipalContinuity : Prop :=
  ∀ {μs : ℕ → ℂ → ℂ} {μ : ℂ → ℂ}, (∀ j, Work.MRMT.Found.Admissible (μs j)) →
    Work.MRMT.Found.Admissible μ → ∀ (R k : ℝ), k < 1 →
    (∀ j, Function.support (μs j) ⊆ Metric.closedBall 0 R) →
    (Function.support μ ⊆ Metric.closedBall 0 R) →
    (∀ j, ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μs j z‖ ≤ k) →
    (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μ z‖ ≤ k) →
    (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      Tendsto (fun j => μs j z) atTop (𝓝 (μ z))) →
    TendstoLocallyUniformly (fun j => (Work.MRMT.Found.principal (μs j) : ℂ → ℂ))
      (Work.MRMT.Found.principal μ) atTop

/-- **The MRMT-continuity input is available**: `Work.MRMT.Found.principal_tendsto_of_ae`
(area `MRMTCont`, `Submission/Work/MRMTCont/Main.lean`) has exactly the hypotheses of
`PrincipalContinuity`. -/
theorem PrincipalContinuity.found : PrincipalContinuity :=
  fun hμs hμ R k hk hsupp hsuppμ hb hbμ hT =>
    Work.MRMT.Found.principal_tendsto_of_ae hμs hμ (R := R) (k := k) hk hsupp hsuppμ hb hbμ hT

/-- The pointwise consequence of `PrincipalContinuity`, which is the form consumed by the
continuation argument of `SimpleTransfer.lean`. -/
theorem PrincipalContinuity.tendsto_apply (h : PrincipalContinuity)
    {μs : ℕ → ℂ → ℂ} {μ : ℂ → ℂ} (hμs : ∀ j, Work.MRMT.Found.Admissible (μs j))
    (hμ : Work.MRMT.Found.Admissible μ) (R k : ℝ) (hk : k < 1)
    (hsupp : ∀ j, Function.support (μs j) ⊆ Metric.closedBall 0 R)
    (hsuppμ : Function.support μ ⊆ Metric.closedBall 0 R)
    (hb : ∀ j, ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μs j z‖ ≤ k)
    (hbμ : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μ z‖ ≤ k)
    (hT : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      Tendsto (fun j => μs j z) atTop (𝓝 (μ z))) (z : ℂ) :
    Tendsto (fun j => (Work.MRMT.Found.principal (μs j) : ℂ → ℂ) z) atTop
      (𝓝 (Work.MRMT.Found.principal μ z)) :=
  ((h hμs hμ R k hk hsupp hsuppμ hb hbμ hT).tendstoLocallyUniformlyOn (s := Set.univ)).tendsto_at
    (Set.mem_univ z)

end Work.FQCInputs

end
