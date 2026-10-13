import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SolutionDelivery.DatumCut
import Submission.Work.SolutionDelivery.Datum

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SolutionDelivery.DatumCut

open FiniteTimeSingularity MeasureTheory

/-! ## The `C^{0,α}` class of the cut-off datum

`cutDatum L ω = chi(ρ/L) • ω` is supported in the ball of radius `2L`, so although `ω` itself
need not be bounded (only its derivative is), the cut-off datum is.  Being `C^{1,α}` with
bounded derivative it is Lipschitz, and a bounded Lipschitz function is `α`-Hölder for `α ≤ 1`
(`Work.Stability.HolderOfBoundedLipschitz`). -/

/-- **The cut-off datum is `α`-Hölder** (`α ≤ 1`).  The `C^{1,α}` class is preserved by the
cut-off (`Work.Stability.OmegaCutHolder`), the cut-off datum is bounded (continuous, compactly
supported), hence Lipschitz (bounded derivative), hence `α`-Hölder for `α ≤ 1`. -/
theorem cutDatum_holder_of_contDiffHolder {L : ℝ} (hL : 0 < L) {α : NNReal} (hα1 : α ≤ 1)
    {ω : Work.SolutionDelivery.R3 → Work.SolutionDelivery.R3}
    (hcdh : IsContDiffHolder ℝ α ω) :
    Holder α (Work.SolutionDelivery.cutDatum L ω) := by
  have hICD : IsContDiffHolder ℝ α (Work.SolutionDelivery.cutDatum L ω) :=
    Work.Stability.OmegaCutHolder hL hα1 hcdh
  have hbdd : IsBoundedFun (Work.SolutionDelivery.cutDatum L ω) := by
    refine Work.Stability.isBoundedFun_of_continuous_of_eq_zero_of_norm_gt (R := 2 * L)
      hICD.1.continuous fun x hx => ?_
    by_contra hne
    have hmem := Work.SolutionDelivery.cutDatum_support (L := L) hL (ω := ω) x hne
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    exact absurd hmem (not_le.mpr hx)
  obtain ⟨K, hK⟩ := Work.Stability.LipschitzOfBoundedFderiv
    (hICD.1.differentiable one_ne_zero) hICD.2.1
  exact Work.Stability.HolderOfBoundedLipschitz hα1 hbdd hK

/-- **The cut-off datum in the Lichtenstein–Gunther data classes.**

If `ω` is `C^{1,α}` with `α ≤ 1`, measurable and bounded, then the cut-off datum
`ω₀ = χ(ρ/L)·ω` of `St1` produces Lichtenstein–Gunther admissible data `u₀ = BS ω₀`: the
analytic datum class `EulerData` (divergence-free, odd, `C^{1,α}` with `α`-power vorticity decay)
and the Biot–Savart-compatible class `EulerDataBS`.  The proof is the assembly's datum
construction `Work.LWP.assembly_data` applied to `ω₀`, whose four vorticity clauses are: the
`L¹`-integrability of a measurable bounded compactly supported field
(`cutDatum_integrable`), its `L^∞` bound `M` (`cutDatum_bdd`), its `C^{0,α}`-regularity
(`cutDatum_holder_of_contDiffHolder`), and the `α`-power decay, which is automatic for compact
support (`vorticityDecay_of_support_bdd`, with the support radius `2L` of `cutDatum_support`). -/
theorem datumData_of_cut {α : NNReal} (hlwp : Work.LWP.LWPInputs α) {L M : ℝ}
    (hL : 0 < L) (hM : 0 ≤ M) (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) ≤ 1)
    {ω : Work.SolutionDelivery.R3 → Work.SolutionDelivery.R3}
    (hmeas : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume)
    (hbdd : ∀ x, ‖ω x‖ ≤ M) (hcdh : IsContDiffHolder ℝ α ω)
    (hdiv : ∀ x, FiniteTimeSingularity.div (Work.SolutionDelivery.cutDatum L ω) x = 0)
    (hodd : FiniteTimeSingularity.IsOdd (Work.LWP.biotSavart (Work.SolutionDelivery.cutDatum L ω))) :
    Work.LWP.EulerData α (Work.LWP.biotSavart (Work.SolutionDelivery.cutDatum L ω)) ∧
      Work.LWP.EulerDataBS α (Work.LWP.biotSavart (Work.SolutionDelivery.cutDatum L ω)) := by
  have hα1' : α ≤ 1 := NNReal.coe_le_coe.mp hα1
  have hR : (0 : ℝ) ≤ 2 * L := by linarith
  have hint : Integrable (Work.SolutionDelivery.cutDatum L ω) :=
    Work.SolutionDelivery.cutDatum_integrable hL hmeas hbdd
  have hholder : Holder α (Work.SolutionDelivery.cutDatum L ω) :=
    cutDatum_holder_of_contDiffHolder hL hα1' hcdh
  have hsupp : ∀ y : Work.SolutionDelivery.R3,
      Work.SolutionDelivery.cutDatum L ω y ≠ 0 → y ∈ Metric.closedBall 0 (2 * L) :=
    fun y hy => Work.SolutionDelivery.cutDatum_support (L := L) hL (ω := ω) y hy
  have hdec : Work.LWP.VorticityDecay α (Work.SolutionDelivery.cutDatum L ω) :=
    Work.SolutionDelivery.vorticityDecay_of_support_bdd hR hM hsupp
      (Work.SolutionDelivery.cutDatum_bdd hbdd)
  have h := Work.LWP.assembly_data hlwp hR hM hint (Work.SolutionDelivery.cutDatum_bdd hbdd)
    hholder hdiv hsupp hodd hdec
  exact ⟨h.1, h.2.1⟩

end Work.SolutionDelivery.DatumCut
