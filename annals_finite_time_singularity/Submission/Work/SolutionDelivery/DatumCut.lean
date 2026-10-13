/-
# `Work.SolutionDelivery.DatumCut` — the concrete cut-off datum of `St1`

`Work.Stability.omegaCut L ω = χ(ρ/L) • ω` is the physical cut-off of `St1`: `χ` is a `C^∞` bump
equal to `1` on `[-1,1]` and `0` outside `(-2,2)`, and `ρ(x) = ‖x‖`.  This module defines the
**cut-off datum**
`cutDatum L ω = χ(ρ/L) • ω`
and proves the elementary properties that the assembly's datum construction consumes:

* its support is contained in the ball of radius `2L` (so the `α`-power vorticity decay is
  automatic, `Work.SolutionDelivery.vorticityDecay_of_support_bdd`);
* it is bounded by the bound of `ω` (`|χ| ≤ 1`);
* it is integrable when `ω` is measurable and bounded (`Work.SolutionDelivery.Integrable`);
* it is `α`-Hölder when `ω` is `C^{1,α}` and `α ≤ 1`
  (`Work.Stability.OmegaCutHolder` for the `C^{1,α}` class of the cut-off, plus
  Lipschitz ⟹ Hölder).
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SolutionDelivery.Integrable.integrable_of_support_subset_closedBall
import Submission.Work.Stability.OmegaCutHolder
import Submission.Work.Stability.OmegaCutSupport

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.SolutionDelivery

/-- **The cut-off datum is supported in the ball of radius `2L`.** -/
theorem cutDatum_support {L : ℝ} (hL : 0 < L) {ω : R3 → R3} :
    ∀ x : R3, cutDatum L ω x ≠ 0 → x ∈ Metric.closedBall 0 (2 * L) := by
  intro x hx
  have h1 : Work.Stability.chi (Work.Cyl.rho x / L) ≠ 0 := by
    intro h0
    exact hx (by simp [cutDatum, Work.Stability.omegaCut, h0])
  exact Work.Stability.cutFactor_support_subset (L := L) hL
    (by simpa [Function.mem_support] using h1)

/-- **The cut-off datum is bounded by the bound of `ω`.** -/
theorem cutDatum_bdd {L M : ℝ} {ω : R3 → R3} (h : ∀ x, ‖ω x‖ ≤ M) :
    ∀ x : R3, ‖cutDatum L ω x‖ ≤ M := by
  intro x
  have h1 : |Work.Stability.chi (Work.Cyl.rho x / L)| ≤ 1 := by
    rw [abs_of_nonneg (Work.Stability.chi_nonneg _)]
    exact Work.Stability.chi_le_one _
  have h2 := h x
  rw [cutDatum, Work.Stability.omegaCut, norm_smul, Real.norm_eq_abs]
  calc |Work.Stability.chi (Work.Cyl.rho x / L)| * ‖ω x‖ ≤ 1 * M :=
        mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = M := one_mul M

/-- The cut-off datum of a measurable field is measurable (the cut-off factor is continuous). -/
theorem cutDatum_measurable {L : ℝ} {ω : R3 → R3} (h : AEStronglyMeasurable ω volume) :
    AEStronglyMeasurable (cutDatum L ω) volume := by
  have hscalar : AEStronglyMeasurable (fun x : R3 => Work.Stability.chi (Work.Cyl.rho x / L))
      volume := by
    have hc : Continuous fun x : R3 => Work.Stability.chi (‖x‖ / L) :=
      Work.Stability.chi_continuous.comp (continuous_norm.div_const L)
    have heq : (fun x : R3 => Work.Stability.chi (Work.Cyl.rho x / L))
        = fun x : R3 => Work.Stability.chi (‖x‖ / L) := by
      funext x
      rw [Work.Cyl.rho_eq_norm x]
    rw [heq]
    exact hc.aestronglyMeasurable
  exact hscalar.smul h

/-- **The cut-off datum is integrable** when `ω` is measurable and bounded. -/
theorem cutDatum_integrable {L M : ℝ} (hL : 0 < L) {ω : R3 → R3}
    (hmeas : AEStronglyMeasurable ω volume) (hbdd : ∀ x, ‖ω x‖ ≤ M) :
    Integrable (cutDatum L ω) volume :=
  Integrable.integrable_of_support_subset_closedBall (R := 2 * L) (M := M)
    (cutDatum_measurable hmeas) (cutDatum_support hL) (cutDatum_bdd hbdd)

end Work.SolutionDelivery
