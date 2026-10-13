/-
# `integrable_physVort_slice` — integrability and boundedness of the physical vorticity slice

For a regularity package `h : RegPkg α S A B g` and a fake time `τ ∈ [0,S]`, the physical
vorticity slice

  `x ↦ physVort α A B g x τ = A(τ)⁻¹ • F(ρ(x)^{3α}/B(τ), θ(x), τ) • e_θ(x)`

is (i) integrable for Lebesgue measure on `ℝ³` and (ii) a bounded function.

Both are far-field consequences of the two structural clauses of `RegPkg` that make the physical
vorticity decay at infinity:

* the full profile `F = F_* + g` is compactly supported in the self-similar variable
  `z = ρ(x)^{3α}/B(τ)` (`RegPkg.hsupp`), so the slice is supported in a ball
  (`Work.FTS.Regularity.physVort_support`);
* the slice is bounded on the ball (`Work.FTS.Regularity.physVort_bound`: the jet bound on `g`
  together with `|F_*| ≤ 20·3α·Γ ≤ 20·3α` and `‖e_θ‖ ≤ 1`, divided by the lower bound `a₀ ≤ A τ`).

Boundedness is the second conjunct.  For integrability, a bounded function of compact support is
integrable as soon as it is measurable: the slice is ae-strongly measurable
(`Work.FTS.Regularity.physVort_slice_aesm`, which rests on the `α`-Hölder estimate
`Work.FTS.Regularity.physVort_holder_slice`), and the ball has finite Lebesgue measure
(`MeasureTheory.measure_closedBall_lt_top`, from `IsFiniteMeasureOnCompacts volume`).
-/
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.FTS.Regularity.physVort_bound
import Submission.Work.FTS.Regularity.physVort_support
import Submission.Work.FTS.Regularity.physVort_bundle

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Physical.RegPkg

open MeasureTheory

/-- **A bounded, ae-strongly-measurable function of compact (ball) support on `ℝ³` is
integrable.**  This is the general principle behind integrability of the physical vorticity slice:
integrability on the ball comes from the finite measure of the ball
(`IntegrableOn.of_bound`), and it upgrades to integrability on all of `ℝ³` because the function
vanishes off the ball (`integrableOn_iff_integrable_of_support_subset`). -/
theorem integrable_of_bounded_of_support_subset_closedBall {E : Type*} [NormedAddCommGroup E]
    {f : Work.FTS.Regularity.R3 → E} {R M : ℝ}
    (hmeas : AEStronglyMeasurable f volume)
    (hbdd : ∀ x, ‖f x‖ ≤ M)
    (hsupp : Function.support f ⊆ Metric.closedBall (0 : Work.FTS.Regularity.R3) R) :
    MeasureTheory.Integrable f := by
  have hIntOn : IntegrableOn f (Metric.closedBall (0 : Work.FTS.Regularity.R3) R) volume :=
    IntegrableOn.of_bound measure_closedBall_lt_top hmeas.restrict M
      (Filter.Eventually.of_forall hbdd)
  exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hIntOn

/-- **The physical vorticity slice is bounded and integrable.** -/
theorem integrable_physVort_slice {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.Regularity.RegPkg α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) S) :
    MeasureTheory.Integrable (fun x : Work.FTS.Regularity.R3 =>
      Work.FTS.Regularity.physVort α A B g x τ) ∧
    IsBoundedFun (fun x : Work.FTS.Regularity.R3 =>
      Work.FTS.Regularity.physVort α A B g x τ) := by
  obtain ⟨M, -, hM⟩ := Work.FTS.Regularity.physVort_bound h
  obtain ⟨R, -, hR⟩ := Work.FTS.Regularity.physVort_support h
  have hint : MeasureTheory.Integrable (fun x : Work.FTS.Regularity.R3 =>
      Work.FTS.Regularity.physVort α A B g x τ) :=
    integrable_of_bounded_of_support_subset_closedBall (R := R) (M := M)
      (Work.FTS.Regularity.physVort_slice_aesm h τ hτ)
      (fun x => hM τ hτ x)
      (fun x hx => hR τ hτ x (Function.mem_support.mp hx))
  refine ⟨hint, ?_⟩
  exact isBounded_iff_forall_norm_le.mpr ⟨M, fun y hy => by
    obtain ⟨x, -, rfl⟩ := hy
    exact hM τ hτ x⟩

end Work.FTS.Physical.RegPkg
