/-
Copyright: work module for the Elgindi finite-time singularity project.

# `TopSlotTwoFts/AHalf`: the level-`2` `A`-slot of the elliptic estimate

Target of this file:

```
∃ C, 0 < C ∧ ∀ α F Ψ, 0 < α → α ≤ 1/4 → TT.EllWeakPos α 2 F Ψ →
  Tk α 2 (fun z θ => z² ∂_z² Ψ z θ) ≤ C · HkSq α 2 F
```

i.e. the *top angular slot* `∫∫(D_θ²(z²∂_z²Ψ)·W)²` of the second radial derivative of `Ψ` is
controlled by the level-`2` energy of the source `F`.

## Route

Write `A = z²∂_z²Ψ = D_z²Ψ - D_zΨ` on the open quadrant (`DzAmgm.Qop_eq_Dz2_sub_Dz`), so that

* `∂_θ²A = ∂_θ²(D_z²Ψ) - ∂_θ²(D_zΨ)` and `∂_θA = ∂_θ(D_z²Ψ - D_zΨ)` (Clairaut);
* the pointwise weight decomposition (`Mine.Tk_pointwise_le_closed`) together with
  `σ₄, σ₂ ≤ sEta` gives
  `(D_θ²A·W)² ≤ 2 (∂_θ²A)² sEta w² + 8 (∂_θA)² sEta w²`;
* the slice Poincaré `H2W.sliceEtaPoincare` applied to the slices `θ ↦ A z θ` (which vanish at
  both endpoints), for a.e. `z`, converts the second summand into the first:
  `∫_θ (∂_θA)² sEta ≤ C ∫_θ (∂_θ²A)² sEta`;
  hence `Tk α 2 A ≤ (2 + 8C) · HkSq α 0 (∂_θ²A)`;
* finally `HkSq α 0 (∂_θ²A) ≤ 2 HkSq α 0 (∂_θ²(D_z²Ψ)) + 2 HkSq α 0 (∂_θ²(D_zΨ))` and each of the
  two is a level-`0` slot of a radially shifted datum, so it is controlled by `HkSq α 2 F`
  (`TopSlotTwoFts.ShiftZeroSlots2`, an instantiation of the paper's Step 3).

The a.e.-in-`z` bookkeeping (integrability of the majorants, a.e. strong measurability of the
slices and of the parameter integrals) is supplied by `TopSlotTwoFts/AHalfInfra.lean`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.remov.EllEstUnifStepAux
import Submission.Work.FTS.EllipticEst.TopSlotTwoFts.ShiftZeroSlots2
import Submission.Work.FTS.EllipticEst.TopSlotTwoFts.AHalfInfra
import Submission.Work.FTS.EllipticEst.TopSlotTwoFts.SliceRegularShiftTwoAe
import Submission.Work.FTS.EllipticEst.H2W.sliceEtaPoincare
import Submission.Work.FTS.EllipticEst.remov.weakSliceRegular
import Submission.Work.FTS.EllipticEst.Cores.Pieces.TL2.weakShiftTwoOne
import Submission.Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm
import Submission.Work.FTS.EllipticEst.Final.Rep.Cores.topSlotB_two
import Submission.Work.FTS.EllipticEst.Mine.SlotDefs
import Submission.Work.FTS.EllipticEst.Final.Rep.Mine.TopSlotTwo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TopSlotTwoFts

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The level-`0` integrand in factored form -/

/-- At level `0` the `ℋ`-integrand factors as `g² sEta w²` (on the closed angular interval). -/
theorem hkIntegrand_zero_eq_mul (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ * (Work.Spaces.w z) ^ 2 := by
  rw [Work.FTS.EllipticEst.Cores.hkIntegrand_zero_eq]
  have hsin : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  by_cases hs : Real.sin (2 * θ) = 0
  · rw [hs, Work.FTS.EllipticEst.sEta, hs]
    have h1 : (0 : ℝ) ^ (Work.Spaces.eta / 2) = 0 :=
      Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)
    have h2 : (0 : ℝ) ^ (-(Work.Spaces.eta)) = 0 :=
      Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)
    rw [h1, h2]
    ring
  · have hspos : 0 < Real.sin (2 * θ) := lt_of_le_of_ne hsin (Ne.symm hs)
    have hsq : Real.sin (2 * θ) ^ (Work.Spaces.eta)
        = (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2 := by
      rw [sq, ← Real.rpow_add hspos]
      ring_nf
    have hse : Work.FTS.EllipticEst.sEta θ
        = ((Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))⁻¹) ^ 2 := by
      rw [Work.FTS.EllipticEst.sEta, Real.rpow_neg hspos.le, hsq, inv_pow]
    rw [hse, div_eq_mul_inv]
    ring

/-! ## The two weights are dominated by `sEta` -/

theorem sig4_le_sEta {α θ : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ ≤ Work.FTS.EllipticEst.sEta θ := by
  have hγ : Work.Spaces.gam α ≤ 3 / 2 := by rw [Work.Spaces.gam]; linarith
  have h0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have h1 : (0 : ℝ) ≤ 4 - Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have h4 : (4 : ℝ) - Work.Spaces.gam α ≠ 0 := by rw [Work.Spaces.gam]; intro hc; linarith
  rw [Work.FTS.EllipticEst.Mine.sig4]
  rcases eq_or_lt_of_le h0 with hz | hpos
  · have hz1 : Real.rpow (0 : ℝ) (4 - Work.Spaces.gam α) = 0 := Real.zero_rpow h4
    rw [← hz, hz1]
    exact Real.rpow_nonneg h0 _
  · have h2 : Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α) ≤ 1 :=
      Real.rpow_le_one h0 (Real.sin_le_one _) h1
    have h3 : 1 ≤ Work.FTS.EllipticEst.sEta θ := by
      rw [Work.FTS.EllipticEst.sEta, Real.rpow_neg hpos.le, ← Real.inv_rpow hpos.le]
      exact Real.one_le_rpow (by rw [one_le_inv₀ hpos]; exact Real.sin_le_one _)
        Work.Spaces.eta_nonneg
    linarith

theorem sig2_le_sEta {α θ : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.EllipticEst.Mine.sig2 (Work.Spaces.gam α) θ ≤ Work.FTS.EllipticEst.sEta θ := by
  have hγ : Work.Spaces.gam α ≤ 3 / 2 := by rw [Work.Spaces.gam]; linarith
  have h0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have h1 : (0 : ℝ) ≤ 2 - Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have h4 : (2 : ℝ) - Work.Spaces.gam α ≠ 0 := by rw [Work.Spaces.gam]; intro hc; linarith
  rw [Work.FTS.EllipticEst.Mine.sig2]
  rcases eq_or_lt_of_le h0 with hz | hpos
  · have hz1 : Real.rpow (0 : ℝ) (2 - Work.Spaces.gam α) = 0 := Real.zero_rpow h4
    rw [← hz, hz1]
    exact Real.rpow_nonneg h0 _
  · have h2 : Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α) ≤ 1 :=
      Real.rpow_le_one h0 (Real.sin_le_one _) h1
    have h3 : 1 ≤ Work.FTS.EllipticEst.sEta θ := by
      rw [Work.FTS.EllipticEst.sEta, Real.rpow_neg hpos.le, ← Real.inv_rpow hpos.le]
      exact Real.one_le_rpow (by rw [one_le_inv₀ hpos]; exact Real.sin_le_one _)
        Work.Spaces.eta_nonneg
    linarith

/-- The level-`0` weight is nonnegative. -/
theorem sEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  exact Real.rpow_nonneg
    (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])) _

/-! ## The pointwise bound -/

/-- `∂_θ²(Aft Ψ) = ∂_θ²(D_z²Ψ) - ∂_θ²(D_zΨ)` on the open quadrant. -/
theorem pthIter2_Aft_eq {Ψ : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pthIter 2 (Aft Ψ) z θ
      = Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ) z θ
        - Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ := by
  simp only [Work.FTS.EllipticEst.Mine.pthIter_eq_iteratedDeriv]
  have hfun : (fun t => Aft Ψ z t)
      =ᶠ[𝓝 θ] ((fun t => Work.Spaces.DzIter 2 Ψ z t)
        - (fun t => Work.Spaces.DzIter 1 Ψ z t)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
    exact Work.FTS.EllipticEst.DzAmgm.Qop_eq_Dz2_sub_Dz hsm hz ht
  have h2 : ContDiffAt ℝ (2 : ℕ∞) (fun t => Work.Spaces.DzIter 2 Ψ z t) θ :=
    (Work.FTS.EllipticEst.DzAmgm.slice_θ_contDiffOn (smoothOpen_DzIter hsm 2) 2 hz).contDiffAt
      (isOpen_Ioo.mem_nhds hθ)
  have h1 : ContDiffAt ℝ (2 : ℕ∞) (fun t => Work.Spaces.DzIter 1 Ψ z t) θ :=
    (Work.FTS.EllipticEst.DzAmgm.slice_θ_contDiffOn (smoothOpen_DzIter hsm 1) 2 hz).contDiffAt
      (isOpen_Ioo.mem_nhds hθ)
  rw [hfun.iteratedDeriv_eq 2, iteratedDeriv_sub h2 h1]

/-- The pointwise bound with `sEta`-weights (hence by the level-`0` integrands of `A`). -/
theorem Aft_pointwise (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) {Ψ : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ) {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.DthIter 2 (Aft Ψ) z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 (Aft Ψ)) z θ
        + 8 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 1 (Aft Ψ)) z θ := by
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h | h
  · rw [← h]
    have hw0 : Work.Spaces.Wt α 0 θ = 0 := by
      rw [Work.Spaces.Wt, Work.Spaces.w]
      norm_num
    rw [hw0, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    have h1 := Work.Spaces.HkIntegrand_nonneg α 0 (Work.Spaces.pthIter 2 (Aft Ψ)) 0 θ
    have h2 := Work.Spaces.HkIntegrand_nonneg α 0 (Work.Spaces.pthIter 1 (Aft Ψ)) 0 θ
    linarith
  · have h2 : ∀ θ' ∈ Set.Ioo 0 (Real.pi / 2),
        DifferentiableAt ℝ (fun t => deriv (fun s => Aft Ψ z s) t) θ' := by
      intro θ' hθ'
      have hcd : ContDiffOn ℝ 2 (fun θ'' => Aft Ψ z θ'') (Set.Ioo 0 (Real.pi / 2)) :=
        smoothOpen_slices (smoothOpen_Aft hsm) h 2
      have h2' : ContDiffOn ℝ 1 (deriv (fun θ'' => Aft Ψ z θ'')) (Set.Ioo 0 (Real.pi / 2)) :=
        hcd.deriv_of_isOpen isOpen_Ioo (by norm_num)
      have h3 : DifferentiableOn ℝ (deriv (fun θ'' => Aft Ψ z θ''))
          (Set.Ioo 0 (Real.pi / 2)) := h2'.differentiableOn (by norm_num)
      exact (h3.differentiableAt (isOpen_Ioo.mem_nhds hθ')).hasDerivAt.differentiableAt
    have hpt := Work.FTS.EllipticEst.Mine.Tk_pointwise_le_closed α hα hα4 (Aft Ψ) z θ hθ h2
    have e4 : deriv (fun θ' => deriv (fun t => Aft Ψ z t) θ') θ
        = Work.Spaces.pthIter 2 (Aft Ψ) z θ := rfl
    have e3 : deriv (fun t => Aft Ψ z t) θ = Work.Spaces.pthIter 1 (Aft Ψ) z θ := rfl
    rw [e4, e3] at hpt
    have h4 : Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ
        ≤ Work.FTS.EllipticEst.sEta θ := sig4_le_sEta hα hα4 hθ
    have h2w : Work.FTS.EllipticEst.Mine.sig2 (Work.Spaces.gam α) θ
        ≤ Work.FTS.EllipticEst.sEta θ := sig2_le_sEta hα hα4 hθ
    have hw2 : (0 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    have hkey4 : 2 * (Work.Spaces.w z) ^ 2
          * ((Work.Spaces.pthIter 2 (Aft Ψ) z θ) ^ 2
            * Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ)
        ≤ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 (Aft Ψ)) z θ := by
      have h4' : (Work.Spaces.pthIter 2 (Aft Ψ) z θ) ^ 2
            * Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ
          ≤ (Work.Spaces.pthIter 2 (Aft Ψ) z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
        mul_le_mul_of_nonneg_left h4 (sq_nonneg _)
      have h5' := mul_le_mul_of_nonneg_right h4' hw2
      rw [hkIntegrand_zero_eq_mul α _ z θ hθ]
      linarith [h5']
    have hkey2 : 8 * (Work.Spaces.w z) ^ 2
          * ((Work.Spaces.pthIter 1 (Aft Ψ) z θ) ^ 2
            * Work.FTS.EllipticEst.Mine.sig2 (Work.Spaces.gam α) θ)
        ≤ 8 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 1 (Aft Ψ)) z θ := by
      have h4' : (Work.Spaces.pthIter 1 (Aft Ψ) z θ) ^ 2
            * Work.FTS.EllipticEst.Mine.sig2 (Work.Spaces.gam α) θ
          ≤ (Work.Spaces.pthIter 1 (Aft Ψ) z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
        mul_le_mul_of_nonneg_left h2w (sq_nonneg _)
      have h5' := mul_le_mul_of_nonneg_right h4' hw2
      rw [hkIntegrand_zero_eq_mul α _ z θ hθ]
      linarith [h5']
    linarith [hpt, hkey4, hkey2]

end

end Work.FTS.EllipticEst.TopSlotTwoFts
