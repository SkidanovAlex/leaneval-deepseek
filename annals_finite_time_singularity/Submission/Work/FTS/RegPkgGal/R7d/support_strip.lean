import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.FTS.BSSwirl.lintegral_inv_norm_mul_ball_indicator_le
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PressureOn.omegaSliceRegularPos
import Submission.Work.FTS.RegPkgGal.R7d.chain_rule_along_curve
import Submission.Work.FTS.RegPkgGal.RVocab
import Submission.Work.FTS.Regularity.profFullBounds
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroSliceInt
import Submission.Work.FTS.StrongEps.EpsODEDefs
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.LinPartArith
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.LWP.VorticityAPI
import Submission.Work.R1G.vecResid_eq_scalar_smul
import Submission.Work.SolutionDelivery.Scaling.Main
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.BSSwirl.Main =====
section

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
end
-- ===== merged: Submission.Work.FTS.Physical.RegPkg.integrable_physVort_slice =====
section

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
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Der.rhs_jet_of_parts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.RegPkgGal.Der.rhs_jet_of_parts`

The right-hand side of the fake-time equation,

  `∂_τ g = -𝓛_Γ^T(g) + gRHS(μ̄(τ), λ(τ), F_*+g(τ), Φ(τ), g(τ))`

is the sum of five pieces: the linear term `-𝓛_Γ^T(g)`, the three nonlinear terms `N₀`, `N`, `N_*`
and the coercivity correction `- μ̄(τ)·AK`, where `μ̄(τ) = mubar (N₀(τ)) (N(τ))` is the scalar zero
mode.  This file proves that if each of the four `τ`-families is a `Jet` (bounded and jointly
`α`-Hölder on the strip `[0,S]`) and the scalar `μ̄` is bounded and `α`-Hölder in `τ`, then so is
the whole right-hand side.

The analytic ingredients are `AK α z θ = (Γ(θ)/c)·2z²/(1+z)³` (a function of `(z,θ)` alone, with
both factors bounded and `α`-Hölder) and the `Jet`-closure API; both live in the auxiliary module
`Submission.Work.FTS.RegPkgGal.Der.rhs_jet_aux` (`rhsJet_ak_bounds`, `rhsJet_add`, `rhsJet_mul`,
…).
-/

namespace Work.FTS.RegPkgGal.Der

open scoped Real Topology
open Set Filter MeasureTheory

set_option autoImplicit false

theorem rhs_jet_of_parts {α S : ℝ} {g Φ : Work.FTS.RegPkgGal.Fam} {N₁ N₂ N₃ N₄ : ℝ}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hS : 0 < S)
    (hL : Work.FTS.Regularity.Jet α S N₁
      (fun z θ τ => -(Work.Coercivity.LGammaT (Work.FTS.Regularity.pExp α)
        (Work.FTS.Regularity.gSlice g τ) z θ)))
    (hN₀ : Work.FTS.Regularity.Jet α S N₂
      (fun z θ τ => Work.Construction.N0 (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice g τ) z θ))
    (hN : Work.FTS.Regularity.Jet α S N₃
      (fun z θ τ => Work.Construction.N (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice Φ τ) z θ))
    (hNs : Work.FTS.Regularity.Jet α S N₄
      (fun z θ τ => Work.Construction.Nstar
        (Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α) Φ g τ)
        (Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α) Φ g τ)
        (Work.FTS.Regularity.gSlice g τ) z θ))
    (hmb : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S,
      |Work.Construction.mubar
        (Work.Construction.N0 (Work.FTS.Regularity.pExp α)
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
          (Work.FTS.Regularity.gSlice g τ))
        (Work.Construction.N (Work.FTS.Regularity.pExp α)
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
          (Work.FTS.Regularity.gSlice Φ τ))| ≤ M)
    (hmbh : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
      |Work.Construction.mubar
          (Work.Construction.N0 (Work.FTS.Regularity.pExp α)
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
            (Work.FTS.Regularity.gSlice g τ))
          (Work.Construction.N (Work.FTS.Regularity.pExp α)
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
            (Work.FTS.Regularity.gSlice Φ τ))
        - Work.Construction.mubar
          (Work.Construction.N0 (Work.FTS.Regularity.pExp α)
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ')
            (Work.FTS.Regularity.gSlice g τ'))
          (Work.Construction.N (Work.FTS.Regularity.pExp α)
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ')
            (Work.FTS.Regularity.gSlice Φ τ'))| ≤ M * |τ - τ'| ^ α) :
    ∃ Nc : ℝ, Work.FTS.Regularity.Jet α S Nc
      (fun z θ τ => Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g τ z θ
        + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g τ z θ) := by
  obtain ⟨M₁, hM₁0, hM₁⟩ := hmb
  obtain ⟨M₂, -, hM₂⟩ := hmbh
  set M := max M₁ M₂ with hMdef
  have hM0 : 0 ≤ M := le_trans hM₁0 (le_max_left M₁ M₂)
  -- the scalar zero mode `μ̄(τ)`, together with its two moduli
  set m : ℝ → ℝ := fun τ => Work.Construction.mubar
      (Work.Construction.N0 (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice g τ))
      (Work.Construction.N (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice Φ τ)) with hmdef
  have hm : ∀ τ ∈ Set.Icc 0 S, |m τ| ≤ M := by
    intro τ hτ
    rw [hmdef]
    exact le_trans (hM₁ τ hτ) (le_max_left M₁ M₂)
  have hmh : ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, |m τ - m τ'| ≤ M * |τ - τ'| ^ α := by
    intro τ hτ τ' hτ'
    have h := hM₂ τ hτ τ' hτ'
    have hle : M₂ ≤ M := le_max_right M₁ M₂
    calc |m τ - m τ'| ≤ M₂ * |τ - τ'| ^ α := h
      _ ≤ M * |τ - τ'| ^ α := mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg (abs_nonneg _) _)
  obtain ⟨hAKbdd, hAKh⟩ := rhsJet_ak_bounds hα hα13
  have hprod : Work.FTS.Regularity.Jet α S (M * 10 + M * 100)
      (fun z θ τ => -(m τ * Work.Construction.AK (Work.FTS.Regularity.pExp α) z θ)) :=
    rhsJet_neg (rhsJet_mul hα hM0 (by norm_num) (by norm_num) hm hmh hAKbdd hAKh)
  -- the five pieces, added left-to-right: `-𝓛_Γ^T(g) + N₀ + N + N_* + (-μ̄·AK)`
  have hsum : Work.FTS.Regularity.Jet α S (((N₁ + N₂) + N₃ + N₄) + (M * 10 + M * 100))
      (fun z θ τ => -(Work.Coercivity.LGammaT (Work.FTS.Regularity.pExp α)
            (Work.FTS.Regularity.gSlice g τ) z θ)
          + Work.Construction.N0 (Work.FTS.Regularity.pExp α)
              (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
              (Work.FTS.Regularity.gSlice g τ) z θ
          + Work.Construction.N (Work.FTS.Regularity.pExp α)
              (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
              (Work.FTS.Regularity.gSlice Φ τ) z θ
          + Work.Construction.Nstar
              (Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α) Φ g τ)
              (Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α) Φ g τ)
              (Work.FTS.Regularity.gSlice g τ) z θ
          + -(m τ * Work.Construction.AK (Work.FTS.Regularity.pExp α) z θ)) := by
    have h12 := rhsJet_add hL hN₀
    have h123 := rhsJet_add h12 hN
    have h1234 := rhsJet_add h123 hNs
    exact rhsJet_add h1234 hprod
  refine ⟨((N₁ + N₂) + N₃ + N₄) + (M * 10 + M * 100), ?_⟩
  refine rhsJet_congr (fun z θ τ => ?_) hsum
  simp only [Work.FTS.Galerkin.dynLin, Work.FTS.Galerkin.dynRHS, Work.Construction.gRHS, hmdef]
  rw [show Work.FTS.Galerkin.slice g τ = Work.FTS.Regularity.gSlice g τ from rfl,
    show Work.FTS.Galerkin.slice Φ τ = Work.FTS.Regularity.gSlice Φ τ from rfl]
  ring_nf

end Work.FTS.RegPkgGal.Der
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.R7d.support_strip =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Set Filter
open scoped Topology Real

set_option maxHeartbeats 1600000

namespace Work.FTS.RegPkgGal.R7d



end Work.FTS.RegPkgGal.R7d
end
end
