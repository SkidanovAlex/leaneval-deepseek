import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.TT.slot11_le
import Submission.Work.FTS.EllipticEst.TT.truncAux
import Submission.Work.FTS.EllipticEst.TopSlotTwoFts.ShiftZeroSlots2
import Submission.Work.FTS.EllipticEst.remov.weakSliceRegular
import Submission.Work.FTS.LocData.HkIntegrand_zfar_Fstar_le
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgEnv
import Submission.Work.FTS.OpenPkg.Pieces4
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SlotOpen
import Submission.Work.SolutionDelivery.Scaling.vorticityDecay_rescaleDatum
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.mixed_mul_le
-- ===== merged: Submission.Work.FTS.EllipticEst.Final.Rep.TopSlotTwoFts.AHalf =====
section

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
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.levelTopSlotsTwoAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Prop

set_option autoImplicit false
set_option maxHeartbeats 3200000

abbrev Ab (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
abbrev Bb (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 Ψ

/-- `sin (2θ) ≥ 0` on `Iθ`. -/
theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

theorem sin_two_pos_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `(w / s^{η/2})² = w² · s^{-η}` (`η = Work.Spaces.eta`), for `s > 0`. -/
theorem div_rpow_half_sq {wv s : ℝ} (hs : 0 < s) :
    (wv / s ^ (Work.Spaces.eta / 2)) ^ 2 = wv ^ 2 * s ^ (-Work.Spaces.eta) := by
  have h1 : (s ^ (Work.Spaces.eta / 2)) ^ (2 : ℕ) = s ^ Work.Spaces.eta := by
    rw [pow_two, ← Real.rpow_add hs,
      show Work.Spaces.eta / 2 + Work.Spaces.eta / 2 = Work.Spaces.eta from by ring]
  rw [div_eq_mul_inv, mul_pow, inv_pow, h1, ← Real.rpow_neg hs.le Work.Spaces.eta]

/-- `(w / σ^{η/2})² = w² · σ^{-η}` on `Iθ` (including the endpoints, where both sides vanish). -/
theorem div_rpow_half_sq_Iθ {wv θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (wv / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
      = wv ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta) := by
  rcases eq_or_lt_of_le (sin_two_nonneg_Iθ hθ) with h | h
  · rw [h.symm, Real.zero_rpow (by norm_num [Work.Spaces.eta] : Work.Spaces.eta / 2 ≠ 0),
      div_zero, Real.zero_rpow (by norm_num [Work.Spaces.eta] : -Work.Spaces.eta ≠ 0)]
    ring
  · exact div_rpow_half_sq h









end Work.FTS.EllipticEst.Prop
end
end
