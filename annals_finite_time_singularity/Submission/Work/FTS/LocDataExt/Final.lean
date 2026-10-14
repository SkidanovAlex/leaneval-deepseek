import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.MinImports
import Mathlib.Tactic.NormNum.Ineq
import Submission.Work.FTS.EllipticEst.Final.ReHome.H2W_slot20_bound
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.Honest.HonSliceSigmaLower
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.LocDataExt.LocG5
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.QangSq6Full
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2W.momentChainAe
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.SolutionDelivery.DatumEuler
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall
-- ===== merged: Submission.Work.FTS.EllipticEst.Final.ReHome.H2W_Step5_s20_Fslot =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.Step5

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false

/-! ## The `(2,0)` angular slot of the source `F` at level `2`

`F` itself (not just `∂_θθΨ`) contributes to the level-`2` top angular slot of `∂_θθΨ`, through
the term `∂_θ²G = ∂_θ²F + α²∂_θ²Φ + α(5+α)∂_θ²Λ` of the source `G = Gsrc α F Ψ`.  This file
provides the *`F`-slot*:

  `∫_z ∫_θ w(z)² (∂_θ²F z θ)² sin(2θ)^{4-γ} ≤ C · HkSq α 2 F`

together with the honesty (integrability) of the `z`-marginal, where `γ = gam α = 1 + α/10`.

The mathematics is the elementary pointwise reduction already isolated in
`Work.FTS.EllipticEst.Mine.sig4_slot_pointwise`: with `s = sin 2θ` and `γ ≤ gam α` (so that
`s^{4-γ} ≤ s^{4-gam α}` on `s ≤ 1`),

  `s² ∂_θ²F = D_θ²F − 2 s cos(2θ) ∂_θF`  ⟹
  `w²(∂_θ²F)²s^{4-γ} ≤ 2 (D_θ²F·Wt)² + 8 (D_θF·Wt)² ≤ 10 · HkIntegrand α 2 F`,

and the two sums on the right are the mixed slots `(i,j) = (2,0)` and `(1,0)` of the level-`2`
integrand.  Integrating against `HkMem α 2 F` gives the bound with constant `10`; the
integrability of the marginal follows from the same pointwise domination once the marginal is
known to be a.e. strongly measurable, which is the continuity of the uncurried integrand on the
open quadrant (`SmoothOpen`).

Everything rests on `[propext, Classical.choice, Quot.sound]`. -/

/-- **Continuity of the `F`-slot integrand on the open quadrant.**  With `F` smooth (all finite
orders) on `(0,∞) × (0,π/2)`, so are `∂_θ²F`, the weight `w`, and therefore the product
`w(z)²(∂_θ²F)²sin(2θ)^{4-γ}` (note `sin(2θ) > 0` on the open quadrant, so the real power is the
honest one). -/
theorem s20_Fslot_cont {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F) (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 *
      ((Work.Spaces.pthIter 2 F p.1 p.2) ^ 2 *
        Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) p.2)) Work.FTS.EllipticEst.Q0 := by
  have hpth : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.pthIter 2 F p.1 p.2))
      Work.FTS.EllipticEst.Q0 := by
    have h : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 F) := by
      have := hF.pth.pth
      exact this
    exact h.continuousOn
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Work.FTS.EllipticEst.Q0 := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
    rw [hfun]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) ?_
    intro p hp
    exact pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0 :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  have hsinne : ∀ p ∈ Work.FTS.EllipticEst.Q0, Real.sin (2 * p.2) ≠ 0 := by
    intro p hp
    obtain ⟨-, h1, h2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
  have hsig : ContinuousOn
      (fun p : ℝ × ℝ => Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) p.2)
      Work.FTS.EllipticEst.Q0 := by
    have h := hsin.rpow_const (p := 4 - Work.Spaces.gam α)
      (fun p hp => Or.inl (hsinne p hp))
    simpa only [Work.FTS.EllipticEst.Mine.sig4, Real.rpow_eq_pow] using h
  exact (hw.pow 2).mul ((hpth.pow 2).mul hsig)

/-- The `F`-slot of the level-`2` top angular slot: `w(z)²(∂_θ²F)²sin(2θ)^{4-γ}` is integrable
over the quadrant and its integral is bounded by `10 · HkSq α 2 F`. -/
theorem s20_Fslot : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.SmoothOpen F → Work.Spaces.HkMem α 2 F →
      MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 *
          ((Work.Spaces.pthIter 2 F z θ) ^ 2 *
            Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ))
        Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 *
          ((Work.Spaces.pthIter 2 F z θ) ^ 2 *
            Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ))
        ≤ C * Work.Spaces.HkSq α 2 F := by
  refine ⟨10, by norm_num, ?_⟩
  intro α F hα hα4 hF hmem
  have hgam2 : Work.Spaces.gam α ≤ 3 / 2 := by rw [Work.Spaces.gam]; linarith
  -- nonnegativity of the angular weight `σ₄` on `Iθ`
  have hsig_nn : ∀ θ ∈ Work.Spaces.Iθ,
      0 ≤ Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ := by
    intro θ hθ
    rw [Work.FTS.EllipticEst.Mine.sig4]
    exact Real.rpow_nonneg (Work.FTS.EllipticEst.Mine.sin_two_nonneg_of_mem_Iθ hθ) _
  have hnn : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      0 ≤ (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter 2 F z θ) ^ 2 *
        Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ) :=
    fun z _ θ hθ => mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (hsig_nn θ hθ))
  -- the pointwise domination by the level-`2` integrand
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter 2 F z θ) ^ 2 *
        Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ)
        ≤ 10 * Work.Spaces.HkIntegrand α 2 F z θ :=
    fun z _ θ hθ =>
      Work.FTS.EllipticEst.Mine.sig4_slot_pointwise α hα (Work.Spaces.gam α) hgam2 le_rfl F z θ hθ
  -- a.e. strong measurability of the `z`-marginal
  have haesmMarg : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 *
        ((Work.Spaces.pthIter 2 F z θ) ^ 2 *
          Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    (Work.Spaces.aesm_of_continuousOn_Qd _ (s20_Fslot_cont hF α)).integral_prod_right'
  -- the inner (`θ`-)bound
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 *
        ((Work.Spaces.pthIter 2 F z θ) ^ 2 *
          Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ))
        ≤ 10 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 2 F z θ) := by
    intro z hz
    have h := MeasureTheory.integral_mono_of_nonneg
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun θ => (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter 2 F z θ) ^ 2 *
        Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ))
      (g := fun θ => 10 * Work.Spaces.HkIntegrand α 2 F z θ)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hnn z hz θ hθ))
      ((hmem.1 z hz).const_mul 10)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hpt z hz θ hθ))
    calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 *
          ((Work.Spaces.pthIter 2 F z θ) ^ 2 *
            Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ))
        ≤ (∫ θ in Work.Spaces.Iθ, 10 * Work.Spaces.HkIntegrand α 2 F z θ) := h
      _ = 10 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 2 F z θ) :=
          MeasureTheory.integral_const_mul 10 _
  -- honesty of the marginal, by the pointwise domination
  have hmargInt : MeasureTheory.Integrable
      (fun z => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 *
        ((Work.Spaces.pthIter 2 F z θ) ^ 2 *
          Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine (hmem.2.const_mul 10).mono' haesmMarg ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    have hmi : 0 ≤ (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 *
        ((Work.Spaces.pthIter 2 F z θ) ^ 2 *
          Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ)) :=
      MeasureTheory.integral_nonneg_of_ae
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hnn z hz θ hθ))
    rw [Real.norm_eq_abs, abs_of_nonneg hmi]
    exact hinner z hz
  -- the integral bound
  have hbound : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 *
        ((Work.Spaces.pthIter 2 F z θ) ^ 2 *
          Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ))
      ≤ 10 * Work.Spaces.HkSq α 2 F := by
    have h := MeasureTheory.integral_mono_of_nonneg
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (f := fun z => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 *
        ((Work.Spaces.pthIter 2 F z θ) ^ 2 *
          Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ))
      (g := fun z => 10 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 2 F z θ))
      (Filter.Eventually.of_forall (fun z => MeasureTheory.integral_nonneg_of_ae
        (by
          refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
          exact mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (hsig_nn θ hθ)))))
      (hmem.2.const_mul 10)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => hinner z hz))
    calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 *
          ((Work.Spaces.pthIter 2 F z θ) ^ 2 *
            Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ))
        ≤ (∫ z in Work.Spaces.Iz, 10 * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 2 F z θ)) := h
      _ = 10 * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 2 F z θ) := MeasureTheory.integral_const_mul 10 _
      _ = 10 * Work.Spaces.HkSq α 2 F := rfl
  exact ⟨hmargInt, hbound⟩

end Work.FTS.EllipticEst.H2W.Step5
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Final.Rep.H2W.slot20_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.slot11_src_int =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `H2W.slot11_src_int`: integrability of the angular derivative of the shifted source

For `0 < α ≤ 1/4`, a datum `h : TT.EllWeakPos α 2 F Ψ` of the weak elliptic class and every
`z > 0`, the function

  `θ ↦ (∂_θ (Gsrc α (D_zF) (D_zΨ)) (z,θ))² · sin(2θ)^{2-γ}`

is integrable on the angular interval `Iθ = [0,π/2]`.

Route.  On the open quadrant `Gsrc α (D_zF) (D_zΨ) = D_zF + α²·D_z(slotA Ψ) + α(5+α)·D_z²Ψ`, where
`slotA Ψ = z²∂_z²Ψ`, and `D_z²Ψ = slotA Ψ + D_zΨ` there; differentiating in `θ` splits
`∂_θ(Gsrc …)` into the four terms `∂_θ(D_zF)`, `α²∂_θ(D_z(slotA Ψ))`,
`α(5+α)∂_θ(slotA Ψ)`, `α(5+α)∂_θ(D_zΨ)`.  Each of their squares against `sin(2θ)^{2-γ}` is
integrable:

* the first two are the `(1,1)`-slots of `HkMem α 2 F` resp. `HkMem α 2 (slotA Ψ)`
  (`Slot11Src.mixed11_Wt_sq_eq`, together with `integrableOn_mixedSummand`);
* the third is the `(1,0)`-slot of `HkMem α 2 (slotA Ψ)` (`Wt_sq_eq`, `mul_sq_rpow_neg`);
* the fourth is controlled by the elementary criterion `integrableOn_deriv_sq_mul_rpow` applied
  to the `i = 1` pure slot of `HkMem α 2 (∂_θ²Ψ)` (`integrableOn_zSummand` +
  `pthIter2_DzIter_comm`).  No endpoint continuity of the slice is needed here: the second
  derivative is already weighted-`L²` with the singular weight `sEta`, and the fundamental
  theorem of calculus on the open interval plus Cauchy–Schwarz (`Mine.cs_interval_le`) bounds the
  first derivative there.
-/

namespace Work.FTS.EllipticEst.H2W

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Iθ" => Work.Spaces.Iθ

/-! ## Elementary `rpow` algebra of the angular weights -/

/-- `sEta θ = sin(2θ)^{-η} ≥ 0` on the angular interval. -/
theorem sEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ Work.FTS.EllipticEst.sEta θ :=
  Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _

/-- `sin(2θ) > 0` on the open angular interval. -/
theorem sin_two_pos_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])


/-- `(Wt α z θ)² = w(z)²·sin(2θ)^{-γ}` on the angular interval. -/
theorem Wt_sq_eq (α : ℝ) (z : ℝ) {θ : ℝ} (hθ : θ ∈ Iθ) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow,
    ← Real.rpow_natCast (Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2))) 2,
    ← Real.rpow_mul hs]
  congr 1
  ring

/-! ## The two product rules relating `D_z Ψ` to the plain derivatives of `Ψ` -/





/-! ## An elementary integrability criterion for the first `θ`-derivative

The only positive-exponent weight `sin(2θ)^c` is bounded, so it is enough to know that the
*second* derivative is weighted-square-integrable with the singular weight `sEta`: the
fundamental theorem of calculus on the open interval, Cauchy–Schwarz (`cs_interval_le`) and the
boundedness of the weight then give a *pointwise* bound on the first derivative. -/



/-- `(w z / sin(2θ)^{η/2})² = w(z)²·sEta θ` on the angular interval. -/
theorem wdivsin_sq (z : ℝ) {θ : ℝ} (hθ : θ ∈ Iθ) :
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  rw [div_pow, ← Real.rpow_natCast (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) 2,
    ← Real.rpow_mul hs (Work.Spaces.eta / 2) ((2 : ℕ) : ℝ),
    show Work.Spaces.eta / 2 * ((2 : ℕ) : ℝ) = Work.Spaces.eta by ring,
    Work.FTS.EllipticEst.sEta, Real.rpow_neg hs, div_eq_mul_inv]






end Work.FTS.EllipticEst.H2W
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.CutEnergyAux.sliceFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop.CutEnergyAux

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Elementary tooling -/

/-- The interval `Iθ = [0,π/2]` and the open interval `(0,π/2)` carry the same restriction of
Lebesgue measure (they differ by the two endpoints, a null set). -/
private theorem restrict_Iθ_eq_Ioo_prv :
    volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  (Measure.restrict_congr_set (by
    rw [Work.Spaces.Iθ]
    exact Ioo_ae_eq_Icc)).symm

/-- `σ = sEta θ = sin(2θ)^{-η}` is nonnegative on `Iθ`. -/
private theorem sEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ :=
  Real.rpow_nonneg
    (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])) _

/-- `F²` is integrable on `Iθ` as soon as `F` is continuous on `(0,π/2)` and `F²σ` is
integrable on `Iθ`: on the open interval `σ ≥ 1`, and the endpoints are null. -/
private theorem integrableOn_sq_of_sigma {F : ℝ → ℝ}
    (hcont : ContinuousOn F (Set.Ioo 0 (Real.pi / 2)))
    (hint : IntegrableOn (fun θ => (F θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    IntegrableOn (fun θ => (F θ) ^ 2) Work.Spaces.Iθ := by
  have hint' : Integrable (fun θ => (F θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (volume.restrict (Set.Ioo 0 (Real.pi / 2))) := by
    simpa only [IntegrableOn, restrict_Iθ_eq_Ioo_prv] using hint
  have hmain : Integrable (fun θ => (F θ) ^ 2)
      (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    Integrable.mono' hint' ((hcont.pow 2).aestronglyMeasurable measurableSet_Ioo) (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact le_mul_of_one_le_right (sq_nonneg _)
        (Work.FTS.EllipticEst.Dispatch.one_le_sEta_D hθ))
  simpa only [IntegrableOn, restrict_Iθ_eq_Ioo_prv] using hmain

/-- `F·H` is integrable on `Iθ` as soon as `F`, `H` are continuous on `(0,π/2)` and `F²σ` and
`H²σ` are integrable on `Iθ` (AM–GM and `σ ≥ 1` on the open interval). -/
private theorem integrableOn_mul_of_sigma {F H : ℝ → ℝ}
    (hFcont : ContinuousOn F (Set.Ioo 0 (Real.pi / 2)))
    (hHcont : ContinuousOn H (Set.Ioo 0 (Real.pi / 2)))
    (hF : IntegrableOn (fun θ => (F θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ)
    (hH : IntegrableOn (fun θ => (H θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    IntegrableOn (fun θ => F θ * H θ) Work.Spaces.Iθ := by
  have hF' : Integrable (fun θ => (F θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (volume.restrict (Set.Ioo 0 (Real.pi / 2))) := by
    simpa only [IntegrableOn, restrict_Iθ_eq_Ioo_prv] using hF
  have hH' : Integrable (fun θ => (H θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (volume.restrict (Set.Ioo 0 (Real.pi / 2))) := by
    simpa only [IntegrableOn, restrict_Iθ_eq_Ioo_prv] using hH
  have hsum : Integrable (fun θ => (F θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      + (H θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    hF'.add hH'
  have hmain : Integrable (fun θ => F θ * H θ)
      (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    Integrable.mono' (hsum) ((hFcont.mul hHcont).aestronglyMeasurable measurableSet_Ioo) (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
        have h1 : (1 : ℝ) ≤ Work.FTS.EllipticEst.sEta θ :=
          Work.FTS.EllipticEst.Dispatch.one_le_sEta_D hθ
        have hAM : |F θ| * |H θ| ≤ ((F θ) ^ 2 + (H θ) ^ 2) / 2 := by
          nlinarith [sq_nonneg (|F θ| - |H θ|), sq_abs (F θ), sq_abs (H θ),
            abs_nonneg (F θ), abs_nonneg (H θ)]
        have hle1 : (F θ) ^ 2 ≤ (F θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
          calc (F θ) ^ 2 = (F θ) ^ 2 * 1 := (mul_one _).symm
            _ ≤ (F θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
                mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
        have hle2 : (H θ) ^ 2 ≤ (H θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
          calc (H θ) ^ 2 = (H θ) ^ 2 * 1 := (mul_one _).symm
            _ ≤ (H θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
                mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
        have hnn : (0 : ℝ) ≤ (F θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
            + (H θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
          add_nonneg (mul_nonneg (sq_nonneg _) (le_trans zero_le_one h1))
            (mul_nonneg (sq_nonneg _) (le_trans zero_le_one h1))
        rw [Real.norm_eq_abs, abs_mul]
        linarith)
  simpa only [IntegrableOn, restrict_Iθ_eq_Ioo_prv] using hmain

/-- The `θ`-slice of a function which is `C^∞` on the open quadrant is continuous on
`(0,π/2)`. -/
private theorem continuousOn_slice_of_smoothOpen {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun θ => F z θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have hmap : MapsTo (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2))
      Work.FTS.EllipticEst.Q0 := fun θ hθ => ⟨hz, hθ⟩
  have hcont : ContinuousOn (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hcomp := hF.continuousOn.comp hcont hmap
  exact hcomp

/-- `((c·A)·B)·c⁻¹ = A·B` for `c ≠ 0`. -/
private theorem mul_eq_mul_inv {c A B : ℝ} (hc : c ≠ 0) : ((c * A) * B) * c⁻¹ = A * B := by
  field_simp

/-- `(c·A)²·(c²)⁻¹ = A²` for `c ≠ 0`. -/
private theorem sq_eq_sq_mul_inv_sq {c A : ℝ} (hc : c ≠ 0) : ((c * A) ^ 2) * (c ^ 2)⁻¹ = A ^ 2 := by
  field_simp

/-! ## The main theorem -/

theorem sliceFacts (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => Work.Elliptic.bslOp α u z θ * u z θ)
          Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ => Work.Elliptic.Lzero u z θ * u z θ)
          Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.pzIter 2 u z θ * u z θ)
          Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.pz u z θ * u z θ)
          Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ => (z * Work.Spaces.pz u z θ) ^ 2)
          Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ => (u z θ) ^ 2) Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pz u z θ) ^ 2)
          Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pzIter 2 u z θ) ^ 2)
          Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ => (G z θ) ^ 2) Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ => (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pthIter 2 u z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
  intro z hz
  have hzpos : 0 < z := hz
  -- ## the smoothness classes
  have hUso : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => h.smooth n)
  have hGso : Work.FTS.EllipticEst.SmoothOpen G :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen (α := α) hUso)
      (fun z θ hz hθ hθ' => h.eq z hz θ hθ hθ')
  -- ## continuity of the slices on the open interval
  have hcnt_u : ContinuousOn (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    continuousOn_slice_of_smoothOpen hUso hzpos
  have hcnt_pz : ContinuousOn (fun θ => Work.Spaces.pz u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    continuousOn_slice_of_smoothOpen (hUso.pz) hzpos
  have hcnt_pz2 : ContinuousOn (fun θ => Work.Spaces.pzIter 2 u z θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    continuousOn_slice_of_smoothOpen (hUso.pzIter 2) hzpos
  have hcnt_B : ContinuousOn (fun θ => Work.Spaces.pthIter 2 u z θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.Endpt.continuousOn_pthIter2_of_strip h.smooth hzpos
  have hcnt_G : ContinuousOn (fun θ => G z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    continuousOn_slice_of_smoothOpen hGso hzpos
  -- ## the five `σ`-weighted honest slices
  have P1 : IntegrableOn (fun θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.Dispatch.slice_sigma_sq_of_hkMem_D
      (Work.FTS.EllipticEst.Dispatch.hkMem_uM α u G h) hzpos
  have P2 : IntegrableOn (fun θ => (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.Dispatch.slice_sigma_sq_of_hkMem_D h.memG hzpos
  have P3 : IntegrableOn
      (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.Dispatch.slice_sigma_sq_of_hkMem_D h.memRad2 hzpos
  have P4 : IntegrableOn
      (fun θ => (z * Work.Spaces.pz u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
    have h4 := Work.FTS.EllipticEst.Dispatch.slice_sigma_sq_of_hkMem_D
      (Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α u G h) hzpos
    simpa only [Work.FTS.EllipticEst.H2W.Ae.grad] using h4
  have P5 : IntegrableOn
      (fun θ => (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.Dispatch.slice_sigma_sq_of_hkMem_D h.memAng2 hzpos
  -- ## the `Lzero` decomposition on the open quadrant
  have hLz : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Elliptic.Lzero u z θ * u z θ
        = G z θ * u z θ + α ^ 2 * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ) * u z θ)
          + (α * (5 + α)) * ((z * Work.Spaces.pz u z θ) * u z θ) := by
    intro θ hθ
    have heq := h.eq z hzpos θ hθ.1 hθ.2
    rw [Work.Elliptic.bslOp_apply] at heq
    have hL : Work.Elliptic.Lzero u z θ
        = G z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ)
          + α * (5 + α) * (z * Work.Spaces.pz u z θ) := by linarith
    rw [hL]; ring
  -- ## the pairings
  -- `G · u`
  have hGu : IntegrableOn (fun θ => G z θ * u z θ) Work.Spaces.Iθ :=
    integrableOn_mul_of_sigma hcnt_G hcnt_u P2 P1
  -- `(z² ∂_z²u) · u` and `(z ∂_zu) · u`
  have hAu : IntegrableOn (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 u z θ) * u z θ)
      Work.Spaces.Iθ :=
    integrableOn_mul_of_sigma (hcnt_pz2.const_mul (z ^ 2)) hcnt_u P3 P1
  have hDu : IntegrableOn (fun θ => (z * Work.Spaces.pz u z θ) * u z θ) Work.Spaces.Iθ :=
    integrableOn_mul_of_sigma (hcnt_pz.const_mul z) hcnt_u P4 P1
  -- squares
  have hD2 : IntegrableOn (fun θ => (z * Work.Spaces.pz u z θ) ^ 2) Work.Spaces.Iθ :=
    integrableOn_sq_of_sigma (hcnt_pz.const_mul z) P4
  have hu2 : IntegrableOn (fun θ => (u z θ) ^ 2) Work.Spaces.Iθ :=
    integrableOn_sq_of_sigma hcnt_u P1
  have hG2 : IntegrableOn (fun θ => (G z θ) ^ 2) Work.Spaces.Iθ :=
    integrableOn_sq_of_sigma hcnt_G P2
  have hA2 : IntegrableOn (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2)
      Work.Spaces.Iθ :=
    integrableOn_sq_of_sigma (hcnt_pz2.const_mul (z ^ 2)) P3
  -- ## the eleven conjuncts
  refine ⟨?_, ?_, ?_, ?_, hD2, hu2, ?_, ?_, hG2, P2, P5⟩
  · -- 1. `bslOp α u · u`
    refine Integrable.congr hGu ?_
    rw [restrict_Iθ_eq_Ioo_prv]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    rw [h.eq z hzpos θ hθ.1 hθ.2]
  · -- 2. `Lzero u · u`
    have hsum : IntegrableOn (fun θ => G z θ * u z θ
        + α ^ 2 * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ) * u z θ)
        + (α * (5 + α)) * ((z * Work.Spaces.pz u z θ) * u z θ)) Work.Spaces.Iθ :=
      (hGu.add (hAu.const_mul (α ^ 2))).add (hDu.const_mul (α * (5 + α)))
    refine Integrable.congr hsum ?_
    rw [restrict_Iθ_eq_Ioo_prv]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact (hLz θ hθ).symm
  · -- 3. `∂_z²u · u`
    have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hzpos)
    have hscaled := hAu.mul_const ((z ^ 2)⁻¹)
    refine Integrable.congr hscaled (Filter.Eventually.of_forall fun θ => ?_)
    exact mul_eq_mul_inv hz2
  · -- 4. `∂_zu · u`
    have hscaled := hDu.mul_const (z⁻¹)
    refine Integrable.congr hscaled (Filter.Eventually.of_forall fun θ => ?_)
    exact mul_eq_mul_inv (ne_of_gt hzpos)
  · -- 7. `(∂_zu)²`
    have hscaled := hD2.mul_const ((z ^ 2)⁻¹)
    refine Integrable.congr hscaled (Filter.Eventually.of_forall fun θ => ?_)
    exact sq_eq_sq_mul_inv_sq (ne_of_gt hzpos)
  · -- 8. `(∂_z²u)²`
    have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hzpos)
    have hscaled := hA2.mul_const (((z ^ 2) ^ 2)⁻¹)
    refine Integrable.congr hscaled (Filter.Eventually.of_forall fun θ => ?_)
    exact sq_eq_sq_mul_inv_sq hz2

end

end Work.FTS.EllipticEst.Prop.CutEnergyAux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.Slot11.shiftThirdInt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT.Slot11

/-- **Integrability of `(∂_θ³(D_zΨ))² · sin(2θ)^{2-gam α}` on the angular slice.**

For `0 < α ≤ 1/4`, a datum `h : TT.EllWeakPos α 2 F Ψ` of the weak elliptic class and every
`z > 0`, the first `IntegrableOn` hypothesis of the PROVED one-dimensional Step-4 estimate
`Work.H2W.sliceStep4Uniform` holds at the shifted slice `u = θ ↦ D_zΨ(z,θ)`, i.e. the
`(i,j) = (1,1)` mixed slot of `HkMem α 2 (∂_θ²Ψ)` is honest after division by `w²`.

Route.  `H2W/slot11_aux.slot11_mixed_eq` (PROVED) gives, for `z > 0` and `θ ∈ Ioo 0 (π/2)`,
`mixed 1 1 (pthIter 2 Ψ) z θ = sin(2θ) · pthIter 3 (DzIter 1 Ψ) z θ`; with
`Wt² = w²·sin(2θ)^{-gam α}` (`Mine.FSlotsTwoD.Wt_sq`), the slot inequality
`(mixed 1 1 f · Wt)² ≤ HkIntegrand α 2 f` (`Spaces.sq_le_HkIntegrand_mixed`) becomes
`w²·(pthIter 3 (DzIter 1 Ψ))²·sin(2θ)^{2-gam α} ≤ HkIntegrand α 2 (pthIter 2 Ψ)` on the open
interval (the `rpow` algebra needs `sin(2θ) > 0`); dividing by `w² ≥ 1` gives the pointwise bound
`(pthIter 3 (DzIter 1 Ψ) z θ)²·sin(2θ)^{2-gam α} ≤ HkIntegrand α 2 (pthIter 2 Ψ) z θ`.
`Integrable.mono'` against `h.memB.1 z hz` (which gives `θ`-integrability of `HkIntegrand α 2
(pthIter 2 Ψ) z ·` for `z ∈ Iz`) closes the claim; the a.e. strong measurability of the left-hand
side is `measurable_deriv`-based (`pthIter` is a total `deriv`), and the pointwise bound is needed
only a.e. on `Iθ` (`Ioo 0 (π/2)` differs from `Iθ` by two points). -/
theorem shiftThirdInt (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pthIter 3 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
  -- The angular slices of `Ψ` are `C^∞` on the open quadrant.
  have hSO : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  -- `HkIntegrand α 2 (∂_θ²Ψ) z ·` is `θ`-integrable on `Iθ` (`z ≥ 0`), the dominating function.
  have hmem : MeasureTheory.Integrable
      (fun θ => Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := h.memB.1 z (Set.mem_Ici.mpr hz.le)
  -- `w z ≥ 1`, hence `(w z)² ≥ 1`: this is what lets us divide the slot inequality by `w²`.
  have hwpos : 1 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
    nlinarith [hz]
  have hw1 : 1 ≤ (Work.Spaces.w z) ^ 2 := by nlinarith [hwpos]
  -- Almost every point of `Iθ` is an interior point, where `sin (2θ) > 0`.
  have hae : ∀ᵐ θ ∂(MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iθ,
      θ ∈ Set.Ioo 0 (Real.pi / 2) := by
    have h' : Set.Icc (0 : ℝ) (Real.pi / 2) =ᵐ[MeasureTheory.volume] Set.Ioo 0 (Real.pi / 2) :=
      (MeasureTheory.Ioo_ae_eq_Icc (μ := (MeasureTheory.volume : Measure ℝ))).symm
    have hIθ : Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) := rfl
    rw [hIθ, MeasureTheory.Measure.restrict_congr_set h']
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
  refine hmem.mono' ?_ ?_
  · -- a.e. strong measurability: `pthIter` is a total `deriv`, and the angular weight is measurable
    have h1 : Measurable
        (fun θ : ℝ => Work.Spaces.pthIter 3 (Work.Spaces.DzIter 1 Ψ) z θ) := by
      have heq : (fun θ : ℝ => Work.Spaces.pthIter 3 (Work.Spaces.DzIter 1 Ψ) z θ)
          = deriv (fun t : ℝ => Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z t) := by
        funext θ; rfl
      rw [heq]; exact measurable_deriv _
    have h2 : Measurable
        (fun θ : ℝ => Work.Spaces.pthIter 3 (Work.Spaces.DzIter 1 Ψ) z θ ^ 2) :=
      h1.pow_const (2 : ℕ)
    have h3 : Measurable
        (fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)) := by
      have hs : Measurable (fun θ : ℝ => Real.sin (2 * θ)) :=
        Real.measurable_sin.comp (measurable_const.mul measurable_id)
      exact hs.pow_const (2 - Work.Spaces.gam α)
    exact (h2.mul h3).aestronglyMeasurable
  · -- the pointwise bound, only needed on the open interval
    filter_upwards [hae] with θ hθ
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hgnn : 0 ≤ (Work.Spaces.pthIter 3 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs.le _)
    rw [Real.norm_eq_abs, abs_of_nonneg hgnn]
    -- the slot inequality, transported to the shifted slice
    have hsq := Work.FTS.EllipticEst.H2W.slot11_sq_eq (α := α) hSO z θ hz hθ.1 hθ.2
    have hle := Work.Spaces.sq_le_HkIntegrand_mixed α 2 (Work.Spaces.pthIter 2 Ψ) z θ 1 1
      (by norm_num) (by norm_num)
    have hb : (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter 3 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α))
        ≤ Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ := by
      rw [← mul_assoc, ← hsq]
      exact hle
    calc (Work.Spaces.pthIter 3 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)
        = 1 * ((Work.Spaces.pthIter 3 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)) := by ring
      _ ≤ (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter 3 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)) :=
          mul_le_mul_of_nonneg_right hw1 hgnn
      _ ≤ Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ := hb

end Work.FTS.EllipticEst.TT.Slot11
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.aeDzDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `TT/AeDzDefs` -- the vocabulary of the `TT.AeDzNorm` proof

The `σ`-masses of a slice (`AeDz.mass`, `AeDz.dzMass`, `AeDz.lzMass`, `AeDz.srcMass`), the
per-`θ` radial integration-by-parts identity `AeDz.perThetaIBP`, the identification of
`HkSq α 0 g` with the `z`-integral of `mass g`, and the coefficient bounds `AeDz.vnCoeffBounds`
for the truncated weight `Vn n · φ`.  Split off from `TT/aeDzNorm.lean` so that the helper
modules delegated from that file (`TT.truncIntegrable`, `TT.truncId`) can import the vocabulary
without importing the final theorem.
-/
namespace Work.FTS.EllipticEst.TT

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

namespace AeDz

/-- The angular weight `σ θ = sin(2θ)^{-η}`. -/
abbrev sig (θ : ℝ) : ℝ := Work.FTS.EllipticEst.sEta θ

/-- The squared radial weight `φ z = w z ²`. -/
abbrev phi (z : ℝ) : ℝ := (Work.Spaces.w z) ^ 2

/-- The `σ`-mass of a `θ`-slice of `g`: `∫_θ (g z θ)² σ θ`. -/
abbrev mass (g : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * sig θ




/-- `σ ≥ 0` on `Iθ`. -/
theorem sig_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ sig θ := by
  rw [sig, Work.FTS.EllipticEst.sEta]
  refine Real.rpow_nonneg ?_ _
  rw [Work.Spaces.Iθ] at hθ
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `1 ≤ σ` on `(0, π/2)`. -/
theorem one_le_sig {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 1 ≤ sig θ := by
  have hs : 0 < Real.sin (2 * θ) := Work.FTS.EllipticEst.Honest.sin_two_pos_of_Iθo hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  rw [sig, Work.FTS.EllipticEst.sEta]
  calc (1 : ℝ) = (1 : ℝ) ^ (-Work.Spaces.eta) := (Real.one_rpow _).symm
    _ ≤ (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) :=
        Real.rpow_le_rpow_of_nonpos hs hs1 (by norm_num [Work.Spaces.eta])



/-- The `θ`-slice of `Lzero` is `Lzero1` applied to the slice. -/
theorem Lzero1_slice_eq (u : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.FTS.EllipticEst.Lzero1 (fun θ' => u z θ') θ = Work.Elliptic.Lzero u z θ := by
  simp only [Work.FTS.EllipticEst.Lzero1, Work.Elliptic.Lzero, Work.Spaces.pthIter_succ,
    Work.Spaces.pthIter_zero, Work.Spaces.pth]


/-! ## `HkSq` in the `mass` notation -/



/-! ## The coefficient bounds for the truncated weight `Vn n · φ` -/



end AeDz

end

end Work.FTS.EllipticEst.TT
end
-- ===== merged: Submission.Work.FTS.LocDataExt.Final =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocDataExt

set_option autoImplicit false
set_option maxHeartbeats 1000000





end Work.FTS.LocDataExt
end
end
