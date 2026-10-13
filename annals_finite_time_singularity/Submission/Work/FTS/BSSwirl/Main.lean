/-
# `Work.FTS.BSSwirl.Main` — the Biot–Savart law for swirl vorticity (item 7a)

This module assembles the chapter and proves `theorem biotSavartSwirl : BiotSavartSwirl`, i.e. for a
compactly supported `α`-Hölder swirl vorticity `ω = f(r,z) • e_θ` with `0 < α < 1`,

  `∇ × (BS ω) = ω`   and   `div (BS ω) = 0`   everywhere on `ℝ³`.

The proof route is documented in `NOTES.md`; the analytic ingredients live in the sibling modules
of this directory.  This module currently contains the glue lemma `continuous_vorticity`; the
assembly is added once the analytic ingredients are in place.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.FTS.BSSwirl.Defs
import Submission.Work.FTS.BSSwirl.Book
import Submission.Work.FTS.BSSwirl.eq_zero_of_forall_inner_test
import Submission.Work.FTS.BSSwirl.div_biotSavart_eq_zero
import Submission.Work.FTS.BSSwirl.contDiff_div_and_support
import Submission.Work.FTS.BSSwirl.contDiff_vorticity_and_support
import Submission.Work.FTS.BSSwirl.hasFDerivAt_newtonPotential
import Submission.Work.FTS.BSSwirl.contDiff_one_newtonPotential
import Submission.Work.FTS.BSSwirl.weakDivFree_swirlField
import Submission.Work.FTS.BSSwirl.integral_vorticity_biotSavart_eq
import Submission.Work.FTS.Top.Integrable.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.BSSwirl

noncomputable section

/-- **The inner product of a continuous field with a compactly supported one is integrable.** -/
theorem integrable_inner_of_hasCompactSupport {V Ψ : R3 → R3} (hV : Continuous V)
    (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ) :
    Integrable (fun x => inner ℝ (V x) (Ψ x)) := by
  refine (hV.inner hΨ).integrable_of_hasCompactSupport ?_
  refine hΨc.isCompact.of_isClosed_subset (isClosed_tsupport _) (closure_mono ?_)
  intro y hy
  contrapose! hy
  rw [Function.mem_support, not_not] at hy ⊢
  rw [hy, inner_zero_right]

/-- **The pointwise Biot–Savart law for a weakly divergence-free vorticity.**  For a bounded,
compactly supported, `α`-Hölder vorticity whose distributional divergence vanishes,
`∇ × (BS ω) = ω` everywhere. -/
theorem vorticity_biotSavart_of_weakDivFree {ω : R3 → R3} {R M α C : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M) (hα : 0 < α) (hC : 0 ≤ C)
    (hbdd : ∀ y, ‖ω y‖ ≤ M) (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hmeas : AEStronglyMeasurable ω volume)
    (hholder : ∀ a b : R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ α)
    (hdiv : WeakDivFree ω) :
    ∀ x, vorticity (Work.LWP.biotSavart ω) x = ω x := by
  have hBS : ContDiff ℝ 1 (Work.LWP.biotSavart ω) :=
    Work.CoreResiduals.BiotSavart.biotSavart_contDiff_one hR hM hα hbdd hsupp hmeas hholder
  have hωc : Continuous ω := continuous_of_holder_pointwise hα hholder
  have hdA : ∀ x, HasFDerivAt (newtonPotential ω) (potDeriv ω x) x :=
    fun x => hasFDerivAt_newtonPotential hR.le hM hbdd hsupp hmeas x
  have hCA : ContDiff ℝ 1 (newtonPotential ω) :=
    contDiff_one_newtonPotential hR.le hM hbdd hsupp hmeas hdA
  have hweak : ∀ Ψ : R3 → R3, (∀ n : ℕ, ContDiff ℝ n Ψ) → HasCompactSupport Ψ →
      ∫ x, inner ℝ (vorticity (Work.LWP.biotSavart ω) x) (Ψ x) = ∫ x, inner ℝ (ω x) (Ψ x) :=
    integral_vorticity_biotSavart_eq hR hM hα hC hbdd hsupp hmeas hholder hdiv hdA hCA
  have hmain : ∀ x, (fun y => vorticity (Work.LWP.biotSavart ω) y - ω y) x = 0 := by
    refine eq_zero_of_forall_inner_test ((continuous_vorticity hBS).sub hωc) ?_
    intro Ψ hΨ hΨc
    have h1 := hweak Ψ hΨ hΨc
    have hΨcont : Continuous Ψ := (hΨ 1).continuous
    have h2 : (fun x => inner ℝ (vorticity (Work.LWP.biotSavart ω) x - ω x) (Ψ x))
        = fun x => inner ℝ (vorticity (Work.LWP.biotSavart ω) x) (Ψ x)
            - inner ℝ (ω x) (Ψ x) := by
      funext x
      rw [inner_sub_left]
    rw [h2, integral_sub]
    · rw [h1, sub_self]
    · exact integrable_inner_of_hasCompactSupport (continuous_vorticity hBS) hΨcont hΨc
    · exact integrable_inner_of_hasCompactSupport hωc hΨcont hΨc
  intro x
  simpa [sub_eq_zero] using hmain x

/-- **Item 7a of the lead's design: the Biot–Savart law for a compactly supported `α`-Hölder swirl
field.**  For every compactly supported `α`-Hölder swirl vorticity `ω = f(r,z) • e_θ` with
`0 < α < 1`, the Biot–Savart velocity inverts the curl and is divergence-free everywhere. -/
theorem biotSavartSwirl : BiotSavartSwirl := by
  intro f C α R hα0 hα1 ω hholder hsupp
  have hstep : ∀ {R' : ℝ}, 0 < R' → (∀ x, swirlField f x ≠ 0 → ‖x‖ ≤ R') →
      (∀ x, vorticity (Work.LWP.biotSavart (swirlField f)) x = swirlField f x) ∧
        ∀ x, div (Work.LWP.biotSavart (swirlField f)) x = 0 := by
    intro R' hR' hsupp'
    obtain ⟨M, hM0, hbdd⟩ := exists_bound_of_holderWith_support hα0 hholder hsupp'
    have hmeas : AEStronglyMeasurable (swirlField f) volume :=
      aestronglyMeasurable_of_holderWith hholder hα0
    have hpoint : ∀ a b : R3, ‖swirlField f a - swirlField f b‖ ≤
        (C : ℝ) * ‖a - b‖ ^ ((α : ℝ≥0) : ℝ) := fun a b => holderWith_dist_le hholder a b
    have hsuppB : ∀ x, swirlField f x ≠ 0 → x ∈ Metric.closedBall (0 : R3) R' := fun x hx =>
      Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hsupp' x hx)
    have hdiv : WeakDivFree (swirlField f) :=
      weakDivFree_swirlField hM0 hR'.le hbdd hmeas hsuppB
    exact ⟨vorticity_biotSavart_of_weakDivFree hR' hM0 hα0 (NNReal.coe_nonneg C) hbdd hsuppB
        hmeas hpoint hdiv,
      div_biotSavart_eq_zero hR' hM0 hα0 (NNReal.coe_nonneg C) hbdd hsuppB hmeas hpoint⟩
  by_cases hR : 0 < R
  · exact hstep hR hsupp
  · have hR0 : R ≤ 0 := le_of_not_gt hR
    have hzero : ∀ x, swirlField f x = 0 := eq_zero_of_holderWith_support_le hα0 hholder hsupp hR0
    have hsupp1 : ∀ x, swirlField f x ≠ 0 → ‖x‖ ≤ (1 : ℝ) := by
      intro x hx
      rw [hzero x] at hx
      exact absurd rfl hx
    exact hstep one_pos hsupp1

end

end Work.FTS.BSSwirl
