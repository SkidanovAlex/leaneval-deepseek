import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.IP4Prep

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of a dominated slot, from integrability of the dominator on the open quadrant

The slot transfer consumes `Integrable`-certificates over the *whole* plane for slot integrands
`ρ · (D_z^bD_θ^a A)²`.  The datum `A` is smooth on the open quadrant `Q0` and vanishes off the
closed quadrant (`hA0`), so every mixed slot of `A` vanishes off `Q0` as well
(`IP4Prep.mixed_eq_zero_of_zero_off`), and the slot integrand is supported on `Q0`; on `Q0` the
weight `ρ` is nonnegative (`hρ0`) and continuous (`hρc`), and the slot integrand is dominated by
the `H^m`-integrand of the target `D` (`hdom`).  Hence integrability of the latter on `Q0` gives
integrability of the slot integrand over the whole plane.

The only measure-theoretic content is the passage "integrable on `Q0` + supported on `Q0` ⟹
integrable over the plane", which is the indicator form of `IntegrableOn`:

`Integrable (Q0.indicator F) volume ↔ IntegrableOn F Q0 volume` (`integrable_indicator_iff`)
together with `Q0.indicator F = F` (because `F` vanishes off `Q0`).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

theorem integrable_slot_of_dom {α : ℝ} {m a b : ℕ} {ρ : ℝ → ℝ → ℝ} {A D : Work.FTS.Galerkin.Fn} (hAsm : Work.FTS.EllipticEst.SmoothOpen A) (hA0 : ∀ z θ : ℝ, ¬ (0 < z ∧ 0 < θ ∧ θ < π / 2) → A z θ = 0) (hρc : ContinuousOn (Function.uncurry ρ) Work.FTS.EllipticEst.Q0) (hρ0 : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ ρ z θ) (hdom : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → ρ z θ * (Work.Spaces.mixed b a A z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α m D z θ) (hint : MeasureTheory.Integrable (Function.uncurry (Work.Spaces.HkIntegrand α m D)) (MeasureTheory.volume.restrict Work.FTS.EllipticEst.Q0)) : MeasureTheory.Integrable (Function.uncurry (fun z θ => ρ z θ * (Work.Spaces.mixed b a A z θ) ^ 2)) MeasureTheory.volume := by
  set F : ℝ × ℝ → ℝ :=
    Function.uncurry (fun z θ => ρ z θ * (Work.Spaces.mixed b a A z θ) ^ 2) with hF
  have hQ0m : MeasurableSet Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  -- the slot integrand vanishes off the open quadrant
  have hF0 : ∀ p : ℝ × ℝ, p ∉ Work.FTS.EllipticEst.Q0 → F p = 0 := by
    intro p hp
    have h : ¬ (0 < p.1 ∧ 0 < p.2 ∧ p.2 < π / 2) :=
      fun hc => hp (Work.FTS.EllipticEst.mem_Q0.mpr hc)
    have hz : Work.Spaces.mixed b a A p.1 p.2 = 0 :=
      mixed_eq_zero_of_zero_off hA0 b a p.1 p.2 h
    show ρ p.1 p.2 * (Work.Spaces.mixed b a A p.1 p.2) ^ 2 = 0
    rw [hz]
    ring
  -- nonnegativity on the open quadrant
  have hFnn : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 ≤ F p := by
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    show 0 ≤ ρ p.1 p.2 * (Work.Spaces.mixed b a A p.1 p.2) ^ 2
    exact mul_nonneg (hρ0 p.1 (le_of_lt hz) p.2 ⟨le_of_lt hθ0, le_of_lt hθ1⟩) (sq_nonneg _)
  -- continuity on the open quadrant (hence a.e. strong measurability for the restricted measure)
  have hcont : ContinuousOn F Work.FTS.EllipticEst.Q0 := by
    change ContinuousOn
      (Function.uncurry (fun z θ => ρ z θ * (Work.Spaces.mixed b a A z θ) ^ 2))
      Work.FTS.EllipticEst.Q0
    exact hρc.mul ((hAsm.mixed b a).continuousOn.pow 2)
  have haesm : AEStronglyMeasurable F (MeasureTheory.volume.restrict Work.FTS.EllipticEst.Q0) :=
    hcont.aestronglyMeasurable hQ0m
  -- the domination, a.e. for the restricted measure
  have hbnd : ∀ᵐ p ∂(MeasureTheory.volume.restrict Work.FTS.EllipticEst.Q0),
      ‖F p‖ ≤ Function.uncurry (Work.Spaces.HkIntegrand α m D) p :=
    MeasureTheory.ae_restrict_of_forall_mem hQ0m (fun p hp => by
      have hle : F p ≤ Function.uncurry (Work.Spaces.HkIntegrand α m D) p := by
        show ρ p.1 p.2 * (Work.Spaces.mixed b a A p.1 p.2) ^ 2
          ≤ Work.Spaces.HkIntegrand α m D p.1 p.2
        exact hdom p.1 p.2 hp
      rw [Real.norm_eq_abs, abs_of_nonneg (hFnn p hp)]
      exact hle)
  -- integrability on the quadrant, from the dominator
  have hon : MeasureTheory.Integrable F (MeasureTheory.volume.restrict Work.FTS.EllipticEst.Q0) :=
    hint.mono' haesm hbnd
  -- transfer to the whole plane through the indicator
  have hsupp : Function.support F ⊆ Work.FTS.EllipticEst.Q0 := by
    intro p hp
    by_contra h
    exact hp (hF0 p h)
  have hon' : MeasureTheory.IntegrableOn F Work.FTS.EllipticEst.Q0 MeasureTheory.volume := hon
  have hind : MeasureTheory.Integrable (Work.FTS.EllipticEst.Q0.indicator F) MeasureTheory.volume :=
    (MeasureTheory.integrable_indicator_iff hQ0m).mpr hon'
  rwa [Set.indicator_eq_self.mpr hsupp] at hind

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
