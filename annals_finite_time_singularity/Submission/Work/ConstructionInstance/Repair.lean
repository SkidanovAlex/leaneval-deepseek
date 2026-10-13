/-
# `Work.ConstructionInstance.Repair` — the `C^{1,α}` clause of `ConstructedSolution` is not needed

`Work.SolutionDelivery.ConstructedSolution` asks of the self-similar vorticity `ωS` the clause

  `ωS_cdh : IsContDiffHolder ℝ α ωS`   (`ωS` is `C^{1,α}`).

That clause is **false** for the construction's vorticity (`Refute.lean`), and it is moreover
*not used*: the only consumer of it in the whole `SolutionDelivery` chain is
`Work.SolutionDelivery.ConstructedSolution.ω₀_holder` (`Basic.lean`) →
`DatumCut.cutDatum_holder_of_contDiffHolder` → `DatumCut.datumData_of_cut`, i.e. the derivation of
the Lichtenstein–Gunther datum classes `EulerData`/`EulerDataBS` of `u₀ = BS (χ(ρ/L)·ωS)`.
Those need only the *α-Hölder-ness* of `ωS` (and its boundedness).

This file supplies the repair:

* `cutDatum_holder_of_holder` — the cut-off of a **bounded** `α`-Hölder field is `α`-Hölder
  (from `Work.Stability.holder_smul_of_bounded_lipschitz` and the bounded Lipschitz cut-off
  factor), replacing `DatumCut.cutDatum_holder_of_contDiffHolder`;
* `datumData_of_cut_of_holder` — the full datum construction with that weakened hypothesis,
  replacing `DatumCut.datumData_of_cut`.

Consequently the patch to `Work.SolutionDelivery` is: replace the field
`ωS_cdh : IsContDiffHolder ℝ α ωS` by `ωS_holder : Holder α ωS` in `Defs.lean`, and replace the
two uses above by the two lemmas of this file; every other declaration of
`Submission/Work/SolutionDelivery/` keeps its statement verbatim, because `Holder α` (not
`IsContDiffHolder`) is exactly what they consume.  `Data.constructedSolution` records the clause
in its data structure precisely so that the present interface can be instantiated.
-/
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.ConstructionInstance.Defs
import Submission.Work.SolutionDelivery.DatumCut
import Submission.Work.SolutionDelivery.DatumCut.datumData_of_cut
import Submission.Work.Stability.OmegaCutHolder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.ConstructionInstance

/-- **The cut-off preserves `α`-Hölder regularity** (for a *bounded* field, `α ≤ 1`): the
cut-off factor `x ↦ χ(ρ(x)/L)` is bounded and Lipschitz, and a bounded Lipschitz scalar times a
bounded `α`-Hölder field is `α`-Hölder. -/
theorem cutDatum_holder_of_holder {L : ℝ} (hL : 0 < L) {α : NNReal} (hα1 : α ≤ 1)
    {ω : R3 → R3} (hbdd : IsBoundedFun ω) (hω : Holder α ω) :
    Holder α (Work.SolutionDelivery.cutDatum L ω) := by
  have hcut : Work.SolutionDelivery.cutDatum L ω = Work.Stability.cutFactor L • ω :=
    Work.Stability.omegaCut_eq_smul L ω
  rw [hcut]
  obtain ⟨K, hK⟩ := Work.Stability.cutFactor_lipschitz hL
  exact Work.Stability.holder_smul_of_bounded_lipschitz hα1
    (Work.Stability.cutFactor_bounded L) hK hbdd hω

/-- **The Hölder chain, made explicit**: the *bounded* `α`-Hölder regularity of the self-similar
vorticity implies the `α`-Hölder regularity of the cut-off datum `omega₀ = χ(ρ/L)·omegaS`, which is
exactly the hypothesis of `datumData_of_cut_of_holder` below, i.e. the whole datum side of the
assembly.  (`hholderS : Holder α (omegaS (profExp α) g)` is the residual field of
`ConstructionData`; the boundedness is `Basic.omegaS_norm_le`.) -/
theorem holder_omega₀_of_holder {p : ℝ} {g : ℝ → ℝ → ℝ} {L M : ℝ} (hL : 0 < L)
    {α : NNReal} (hα1 : α ≤ 1) (hbdd : ∀ x : R3, ‖omegaS p g x‖ ≤ M)
    (h : Holder α (omegaS p g)) : Holder α (omega₀ p g L) :=
  cutDatum_holder_of_holder hL hα1
    (Work.Stability.isBoundedFun_of_forall_norm_le hbdd) h

/-- **The Lichtenstein–Gunther datum classes of the cut-off datum, from `Holder α` only.**

This is `Work.SolutionDelivery.DatumCut.datumData_of_cut` with the hypothesis
`IsContDiffHolder ℝ α ω` weakened to `Holder α ω` (plus the boundedness used by the cut-off
lemma); it is the *only* place in the assembly chain where the `C^{1,α}` clause of `ωS` is
consumed. -/
theorem datumData_of_cut_of_holder {α : NNReal} (hlwp : Work.LWP.LWPInputs α) {L M : ℝ}
    (hL : 0 < L) (hM : 0 ≤ M) (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) ≤ 1)
    {ω : R3 → R3} (hmeas : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume)
    (hbdd : ∀ x : R3, ‖ω x‖ ≤ M) (hholder : Holder α ω)
    (hdiv : ∀ x : R3, FiniteTimeSingularity.div (Work.SolutionDelivery.cutDatum L ω) x = 0)
    (hodd : FiniteTimeSingularity.IsOdd
      (Work.LWP.biotSavart (Work.SolutionDelivery.cutDatum L ω))) :
    Work.LWP.EulerData α (Work.LWP.biotSavart (Work.SolutionDelivery.cutDatum L ω)) ∧
      Work.LWP.EulerDataBS α (Work.LWP.biotSavart (Work.SolutionDelivery.cutDatum L ω)) := by
  have hα1' : α ≤ 1 := NNReal.coe_le_coe.mp hα1
  have hR : (0 : ℝ) ≤ 2 * L := by linarith
  have hint : Integrable (Work.SolutionDelivery.cutDatum L ω) :=
    Work.SolutionDelivery.cutDatum_integrable hL hmeas hbdd
  have hbfun : IsBoundedFun ω :=
    Work.Stability.isBoundedFun_of_forall_norm_le hbdd
  have hholder' : Holder α (Work.SolutionDelivery.cutDatum L ω) :=
    cutDatum_holder_of_holder hL hα1' hbfun hholder
  have hsupp : ∀ y : R3,
      Work.SolutionDelivery.cutDatum L ω y ≠ 0 → y ∈ Metric.closedBall 0 (2 * L) :=
    fun y hy => Work.SolutionDelivery.cutDatum_support (L := L) hL (ω := ω) y hy
  have hdec : Work.LWP.VorticityDecay α (Work.SolutionDelivery.cutDatum L ω) :=
    Work.SolutionDelivery.vorticityDecay_of_support_bdd hR hM hsupp
      (Work.SolutionDelivery.cutDatum_bdd hbdd)
  have h := Work.LWP.assembly_data hlwp hR hM hint (Work.SolutionDelivery.cutDatum_bdd hbdd)
    hholder' hdiv hsupp hodd hdec
  exact ⟨h.1, h.2.1⟩

/-- **The maximal solution exists from the weakened datum class.**  This is
`Work.SolutionDelivery.exists_maximal_of_datum` with `IsContDiffHolder ℝ α ωS` replaced by
`Holder α ωS` (plus boundedness); it shows that the `hmax` field of
`Work.SolutionDelivery.ConstructedSolution` is *not* the obstruction to the repair. -/
theorem exists_maximal_of_datum_of_holder {α : NNReal} (hlwp : Work.LWP.LWPInputs α) {L M : ℝ}
    (hL : 0 < L) (hM : 0 ≤ M) {ωS : R3 → R3}
    (hmeas : MeasureTheory.AEStronglyMeasurable ωS MeasureTheory.volume)
    (hbdd : ∀ x : R3, ‖ωS x‖ ≤ M) (hholder : Holder α ωS)
    (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) ≤ 1)
    (hdiv : ∀ x : R3, FiniteTimeSingularity.div (Work.SolutionDelivery.cutDatum L ωS) x = 0)
    (hodd : FiniteTimeSingularity.IsOdd
      (Work.LWP.biotSavart (Work.SolutionDelivery.cutDatum L ωS))) :
    ∃ T : ℝ, 0 < T ∧
      Nonempty (Work.LWP.MaximalSolution α
        (Work.LWP.biotSavart (Work.SolutionDelivery.cutDatum L ωS)) T) :=
  let h := datumData_of_cut_of_holder hlwp hL hM hα hα1 hmeas hbdd hholder hdiv hodd
  hlwp.maxExists _ h.1 h.2

end Work.ConstructionInstance
