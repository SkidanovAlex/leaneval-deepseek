/-
Copied from `Submission.Work.FTS.EllipticEst.H2W.Step5.s20_Fslot` for `Final/slot20_bound_fts`.
Only the `import` lines are redirected (see `Final/slot20_bound_fts.lean` for why):
the copy of `Mine/TopSlotTwo` (`Final/ReHome/TkKit.lean`) drops the `Mine/ShiftLevelOne`
import and the two declarations at the end of that file that use it, which cuts the
`RPFresh/excess_finite` dependency out of the closure.
-/

import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.Final.ReHome.H2W_slot20_bound
import Submission.Work.FTS.EllipticEst.Mine.FSlotsTwoD
import Submission.Work.FTS.EllipticEst.OpenQDefs

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
