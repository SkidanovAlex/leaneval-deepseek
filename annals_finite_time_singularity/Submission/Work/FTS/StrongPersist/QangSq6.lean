import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.H2.WPQ.Interior
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.HkIntegrand_zfar_Fstar_le
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.integral_sin_two_rpow_neg
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS.Vocab
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.WPQ.hardy_slice_Aang
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.SolutionDelivery.DatumEuler
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.BadTermSqBound
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.WProductRule
import Submission.Work.Spaces.aesm_HkIntegrand_quad
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.AuxE2.L12_contDiffOn_four_of_five =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.AuxE2

set_option autoImplicit false
-- `h0 : L₁₂ f 0 = 0` is part of the requested statement (it is used downstream, on the
-- coercivity side) but is not needed for the `C⁴`-regularity proved here.
set_option linter.unusedVariables false



end Work.FTS.CoercivityFix.Transfer.AuxE2
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.slice_abs_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open MeasureTheory Set Filter

/-- The restricted measure on `Iθ = [0,π/2]` is the restriction to the open interval, since the
two endpoints form a null set. -/
private theorem restrict_Iθ_eq_restrict_Ioo_local :
    MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  refine MeasureTheory.Measure.restrict_congr_set ?_
  exact MeasureTheory.Ioo_ae_eq_Icc.symm

/-- The integral of the constant `1` over `Iθ` is `π/2`. -/
private theorem integral_one_Iθ : (∫ _s in Work.Spaces.Iθ, (1 : ℝ)) = Real.pi / 2 := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ Real.pi / 2 by positivity)]
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  ring

/-- The pointwise Cauchy–Schwarz/AM–GM step: on the open angular interval the weight `σθ` is at
least `1`, so `|h| ≤ (h²·σθ + 1)/2` there. -/
private theorem abs_le_half_sq_mul_add {h : ℝ → ℝ} {s : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |h s| ≤ (h s ^ 2 * Work.FTS.EllipticEst.thEta s + 1) / 2 := by
  have hσ : 1 ≤ Work.FTS.EllipticEst.thEta s := one_le_thEta_of_mem_Ioo hs
  have hX2 : 0 ≤ h s ^ 2 := sq_nonneg _
  have h2 : 2 * |h s| ≤ h s ^ 2 + 1 := by
    nlinarith [sq_nonneg (|h s| - 1), sq_abs (h s)]
  nlinarith [h2, hX2, mul_le_mul_of_nonneg_left hσ hX2]

/-- The `L¹`–`L²` bound for an angular slice: `∫_{Iθ}|h| ≤ ½(∫_{Iθ}h²σθ + π/2)`. -/
private theorem integral_abs_le {h : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn
      (fun s : ℝ => h s ^ 2 * Work.FTS.EllipticEst.thEta s) Work.Spaces.Iθ) :
    (∫ s in Work.Spaces.Iθ, |h s|)
      ≤ (1 / 2) * ((∫ s in Work.Spaces.Iθ, h s ^ 2 * Work.FTS.EllipticEst.thEta s)
          + Real.pi / 2) := by
  have hIθ_ne_top : MeasureTheory.volume Work.Spaces.Iθ ≠ ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hInt1 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    MeasureTheory.integrableOn_const hIθ_ne_top (by simp)
  have hInt2 : MeasureTheory.IntegrableOn
      (fun s : ℝ => h s ^ 2 * Work.FTS.EllipticEst.thEta s + 1) Work.Spaces.Iθ :=
    hint.add hInt1
  have hIntG : MeasureTheory.IntegrableOn
      (fun s : ℝ => ((h s ^ 2 * Work.FTS.EllipticEst.thEta s + 1) / 2)) Work.Spaces.Iθ :=
    MeasureTheory.Integrable.div_const hInt2 2
  have hpoint : (fun s : ℝ => |h s|)
      ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun s : ℝ => (h s ^ 2 * Work.FTS.EllipticEst.thEta s + 1) / 2) := by
    rw [restrict_Iθ_eq_restrict_Ioo_local]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
      (fun s hs => abs_le_half_sq_mul_add hs)
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun s => abs_nonneg (h s))) hIntG hpoint
  have hcalc : (∫ s in Work.Spaces.Iθ,
        (h s ^ 2 * Work.FTS.EllipticEst.thEta s + 1) / 2)
      = (1 / 2) * ((∫ s in Work.Spaces.Iθ, h s ^ 2 * Work.FTS.EllipticEst.thEta s)
          + Real.pi / 2) := by
    rw [MeasureTheory.integral_div, MeasureTheory.integral_add hint hInt1, integral_one_Iθ]
    ring
  exact hmono.trans (le_of_eq hcalc)

theorem slice_abs_le {X : ℝ → ℝ → ℝ} {u ε θ : ℝ} (hu : 0 < u) (hε : 0 < ε)
    (hint : MeasureTheory.IntegrableOn
      (fun s : ℝ => X u s ^ 2 * Work.FTS.EllipticEst.thEta s) Work.Spaces.Iθ)
    (haesm : MeasureTheory.AEStronglyMeasurable (fun s : ℝ => X u s)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    (∫ s in Work.Spaces.Iθ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s * |X u s|)
      ≤ (3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹ / 2)
        * ((∫ s in Work.Spaces.Iθ, X u s ^ 2 * Work.FTS.EllipticEst.thEta s) + Real.pi / 2) := by
  -- Write `c := 3 (ε · sMass)⁻¹`, the uniform bound on the kernel.
  set c : ℝ := 3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹ with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]
    exact mul_pos (by norm_num) (inv_pos.mpr (mul_pos hε Work.FTS.EllSol.PkgK5.K5c.sMass_pos))
  have hIθ_ne_top : MeasureTheory.volume Work.Spaces.Iθ ≠ ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hInt1 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    MeasureTheory.integrableOn_const hIθ_ne_top (by simp)
  have hInt2 : MeasureTheory.IntegrableOn
      (fun s : ℝ => X u s ^ 2 * Work.FTS.EllipticEst.thEta s + 1) Work.Spaces.Iθ :=
    hint.add hInt1
  have hIntDom : MeasureTheory.IntegrableOn
      (fun s : ℝ => (X u s ^ 2 * Work.FTS.EllipticEst.thEta s + 1) / 2)
      Work.Spaces.Iθ :=
    MeasureTheory.Integrable.div_const hInt2 2
  -- The dominating function: `|X u| ≤ (X u ² σθ + 1)/2` a.e. on `Iθ`.
  have hle : (fun s : ℝ => |X u s|)
      ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun s : ℝ => (X u s ^ 2 * Work.FTS.EllipticEst.thEta s + 1) / 2) := by
    rw [restrict_Iθ_eq_restrict_Ioo_local]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
      (fun s hs => abs_le_half_sq_mul_add hs)
  -- Integrability of the slice of `X u`, from the hypothesis `hint` and the a.e.-strong
  -- measurability `haesm`.
  have hIntAbs : MeasureTheory.IntegrableOn (fun s : ℝ => |X u s|) Work.Spaces.Iθ :=
    MeasureTheory.Integrable.mono' hIntDom haesm.norm (by
      filter_upwards [hle] with s hs
      simpa only [Real.norm_eq_abs, abs_abs] using hs)
  have hIntcAbs : MeasureTheory.IntegrableOn (fun s : ℝ => c * |X u s|) Work.Spaces.Iθ :=
    MeasureTheory.Integrable.const_mul hIntAbs c
  have hpointKJ : (fun s : ℝ => Work.FTS.EllSol.EllPkgAux.KJ ε θ s * |X u s|)
      ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun s : ℝ => c * |X u s|) :=
    Filter.Eventually.of_forall (fun s =>
      mul_le_mul_of_nonneg_right (by
        rw [hcdef]; exact Work.FTS.EllSol.EllPkgAux.KJ_le hε θ s) (abs_nonneg _))
  have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun s : ℝ => Work.FTS.EllSol.EllPkgAux.KJ ε θ s * |X u s|) :=
    Filter.Eventually.of_forall (fun s =>
      mul_nonneg (Work.FTS.EllSol.EllPkgAux.KJ_nonneg hε θ s) (abs_nonneg _))
  have hmono := MeasureTheory.integral_mono_of_nonneg hnn hIntcAbs hpointKJ
  calc (∫ s in Work.Spaces.Iθ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s * |X u s|)
      ≤ ∫ s in Work.Spaces.Iθ, c * |X u s| := hmono
    _ = c * ∫ s in Work.Spaces.Iθ, |X u s| := MeasureTheory.integral_const_mul c _
    _ ≤ c * ((1 / 2) * ((∫ s in Work.Spaces.Iθ,
          X u s ^ 2 * Work.FTS.EllipticEst.thEta s) + Real.pi / 2)) :=
        mul_le_mul_of_nonneg_left (integral_abs_le hint) hcpos.le
    _ = (3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹ / 2)
        * ((∫ s in Work.Spaces.Iθ, X u s ^ 2 * Work.FTS.EllipticEst.thEta s) + Real.pi / 2) := by
        rw [hcdef]; ring

end Work.FTS.EllSol.EllPkgAux.MollDom
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.slice_deriv_bdd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

set_option maxHeartbeats 800000

theorem slice_deriv_bdd (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    {w : ℝ} (hw : 0 < w) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |deriv (fun s' : ℝ => G w s') s| ≤ M := by
  obtain ⟨hsm, h0, hpi, htr0, htrpi, hdz0, hdzpi, hhon⟩ := hT
  -- ## The `C²`-regularity of the slice and the weighted `L²`-bound on `∂_θ²G`
  have hsmo : (2 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder := by
    simp [Work.Stability.smoothOrder]
  have hf2 : ContDiffOn ℝ 2 (fun θ : ℝ => G w θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (hsm.curry_θ hw).of_le hsmo
  have hInt : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
    have hc : (0 : ℝ) < (Work.Spaces.w w) ^ 2 := by
      rw [Work.Spaces.w]; positivity
    have h0' := hhon.1 w hw
    have hEq : ∀ θ : ℝ, ((Work.Spaces.w w) ^ 2)⁻¹ *
        (Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * (Work.Spaces.w w) ^ 2
          * Work.FTS.EllipticEst.thEta θ)
        = Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * Work.FTS.EllipticEst.thEta θ := by
      intro θ
      rw [show Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * (Work.Spaces.w w) ^ 2
            * Work.FTS.EllipticEst.thEta θ
          = (Work.Spaces.w w) ^ 2 * (Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2
            * Work.FTS.EllipticEst.thEta θ) from by ring]
      exact inv_mul_cancel_left₀ (ne_of_gt hc) _
    rw [show (fun θ : ℝ => Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2
          * Work.FTS.EllipticEst.thEta θ)
        = fun θ : ℝ => ((Work.Spaces.w w) ^ 2)⁻¹ *
          (Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * (Work.Spaces.w w) ^ 2
            * Work.FTS.EllipticEst.thEta θ) from funext (fun θ => (hEq θ).symm)]
    exact h0'.const_mul _
  -- ## The two landmark points and the uniform estimate on compact subintervals
  have hq0 : (0 : ℝ) < Real.pi / 4 := by positivity
  have hq1 : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hkey : ∀ a b : ℝ, 0 < a → a ≤ b → b < Real.pi / 2 → b - a ≤ Real.pi / 4 →
      |∫ t in a..b, deriv (deriv (fun θ' : ℝ => G w θ')) t|
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ,
              (deriv (deriv (fun θ' : ℝ => G w θ')) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          * Real.sqrt (Real.pi / 4) := by
    intro a b ha hab hb hlen
    have hsub : Set.uIcc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
    have hcg : ContinuousOn (deriv (deriv (fun θ' : ℝ => G w θ'))) (Set.uIcc a b) :=
      (Work.FTS.EllSol.c2_continuousOn_deriv_deriv hf2).mono hsub
    have hcs := Work.Spaces.hardyZ_interval_integral_mul_le_sqrt a b hab
      (f := fun t : ℝ => deriv (deriv (fun θ' : ℝ => G w θ')) t)
      (g := fun _ : ℝ => (1 : ℝ)) hcg continuous_const.continuousOn
    have hone : ∫ t in a..b, (1 : ℝ) ^ 2 = b - a := by
      rw [show (1 : ℝ) ^ 2 = 1 by norm_num, intervalIntegral.integral_const]
      simp
    have hsq : ∫ t in a..b, (deriv (deriv (fun θ' : ℝ => G w θ')) t) ^ 2
        ≤ ∫ θ in Work.Spaces.Iθ,
            (deriv (deriv (fun θ' : ℝ => G w θ')) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ :=
      interval_sq_le_Itheta (h := fun θ : ℝ => deriv (deriv (fun θ' : ℝ => G w θ')) θ)
        hInt ha hab hb
    calc |∫ t in a..b, deriv (deriv (fun θ' : ℝ => G w θ')) t|
        = |∫ t in a..b, deriv (deriv (fun θ' : ℝ => G w θ')) t * 1| := by
          congr 1
          exact intervalIntegral.integral_congr (fun t _ => (mul_one _).symm)
      _ ≤ Real.sqrt (∫ t in a..b, (deriv (deriv (fun θ' : ℝ => G w θ')) t) ^ 2)
            * Real.sqrt (∫ t in a..b, (1 : ℝ) ^ 2) := hcs
      _ = Real.sqrt (∫ t in a..b, (deriv (deriv (fun θ' : ℝ => G w θ')) t) ^ 2)
            * Real.sqrt (b - a) := by rw [hone]
      _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ,
              (deriv (deriv (fun θ' : ℝ => G w θ')) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
            * Real.sqrt (Real.pi / 4) :=
          mul_le_mul (Real.sqrt_le_sqrt hsq) (Real.sqrt_le_sqrt hlen)
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- ## The bound
  refine ⟨|deriv (fun θ' : ℝ => G w θ') (Real.pi / 4)|
      + Real.sqrt (∫ θ in Work.Spaces.Iθ,
          (deriv (deriv (fun θ' : ℝ => G w θ')) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        * Real.sqrt (Real.pi / 4), ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ |deriv (fun θ' : ℝ => G w θ') (Real.pi / 4)| := abs_nonneg _
    have h2 : (0 : ℝ) ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ,
          (deriv (deriv (fun θ' : ℝ => G w θ')) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        * Real.sqrt (Real.pi / 4) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    linarith
  · intro s hs
    have hs0 : 0 < s := hs.1
    have hs1 : s < Real.pi / 2 := hs.2
    rcases le_total s (Real.pi / 4) with hle | hge
    · -- ## `s ≤ π/4`: run the fundamental theorem from `s` up to the landmark `π/4`
      have hFTC : ∫ t in s..(Real.pi / 4), deriv (deriv (fun θ' : ℝ => G w θ')) t
          = deriv (fun θ' : ℝ => G w θ') (Real.pi / 4)
            - deriv (fun θ' : ℝ => G w θ') s := by
        refine intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := deriv (fun θ' : ℝ => G w θ'))
          (f' := fun t : ℝ => deriv (deriv (fun θ' : ℝ => G w θ')) t) ?_ ?_
        · intro t ht
          rw [Set.uIcc_of_le hle] at ht
          exact Work.FTS.EllSol.c2_hasDerivAt_deriv hf2
            ⟨lt_of_lt_of_le hs0 ht.1, lt_of_le_of_lt ht.2 hq1⟩
        · exact Work.FTS.EllSol.c2_intervalIntegrable_deriv_deriv hf2 hs0 hle hq1
      have hs_eq : deriv (fun θ' : ℝ => G w θ') s
          = deriv (fun θ' : ℝ => G w θ') (Real.pi / 4)
            + (- ∫ t in s..(Real.pi / 4), deriv (deriv (fun θ' : ℝ => G w θ')) t) := by
        rw [hFTC]; ring
      have hbnd := hkey s (Real.pi / 4) hs0 hle hq1 (by linarith [hs0])
      rw [hs_eq]
      calc |deriv (fun θ' : ℝ => G w θ') (Real.pi / 4)
            + (- ∫ t in s..(Real.pi / 4), deriv (deriv (fun θ' : ℝ => G w θ')) t)|
          ≤ |deriv (fun θ' : ℝ => G w θ') (Real.pi / 4)|
            + |∫ t in s..(Real.pi / 4), deriv (deriv (fun θ' : ℝ => G w θ')) t| := by
            simpa only [abs_neg] using
              abs_add_le (deriv (fun θ' : ℝ => G w θ') (Real.pi / 4))
                (- ∫ t in s..(Real.pi / 4), deriv (deriv (fun θ' : ℝ => G w θ')) t)
        _ ≤ |deriv (fun θ' : ℝ => G w θ') (Real.pi / 4)|
            + Real.sqrt (∫ θ in Work.Spaces.Iθ,
                (deriv (deriv (fun θ' : ℝ => G w θ')) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
              * Real.sqrt (Real.pi / 4) := by linarith [hbnd]
    · -- ## `π/4 ≤ s`: run the fundamental theorem from the landmark `π/4` up to `s`
      have hFTC : ∫ t in (Real.pi / 4)..s, deriv (deriv (fun θ' : ℝ => G w θ')) t
          = deriv (fun θ' : ℝ => G w θ') s
            - deriv (fun θ' : ℝ => G w θ') (Real.pi / 4) := by
        refine intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := deriv (fun θ' : ℝ => G w θ'))
          (f' := fun t : ℝ => deriv (deriv (fun θ' : ℝ => G w θ')) t) ?_ ?_
        · intro t ht
          rw [Set.uIcc_of_le hge] at ht
          exact Work.FTS.EllSol.c2_hasDerivAt_deriv hf2
            ⟨lt_of_lt_of_le hq0 ht.1, lt_of_le_of_lt ht.2 hs1⟩
        · exact Work.FTS.EllSol.c2_intervalIntegrable_deriv_deriv hf2 hq0 hge hs1
      have hs_eq : deriv (fun θ' : ℝ => G w θ') s
          = deriv (fun θ' : ℝ => G w θ') (Real.pi / 4)
            + ∫ t in (Real.pi / 4)..s, deriv (deriv (fun θ' : ℝ => G w θ')) t := by
        rw [hFTC]; ring
      have hbnd := hkey (Real.pi / 4) s hq0 hge hs1 (by linarith [hs1])
      rw [hs_eq]
      calc |deriv (fun θ' : ℝ => G w θ') (Real.pi / 4)
            + ∫ t in (Real.pi / 4)..s, deriv (deriv (fun θ' : ℝ => G w θ')) t|
          ≤ |deriv (fun θ' : ℝ => G w θ') (Real.pi / 4)|
            + |∫ t in (Real.pi / 4)..s, deriv (deriv (fun θ' : ℝ => G w θ')) t| :=
            abs_add_le _ _
        _ ≤ |deriv (fun θ' : ℝ => G w θ') (Real.pi / 4)|
            + Real.sqrt (∫ θ in Work.Spaces.Iθ,
                (deriv (deriv (fun θ' : ℝ => G w θ')) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
              * Real.sqrt (Real.pi / 4) := by linarith [hbnd]

end Work.FTS.EllSol.EllPkgAux.MollDom
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.window_ttIntS_plain_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open MeasureTheory Set Filter
open scoped Real Topology

/-! ## The *unweighted* windowed `ttIntS`

`window_ttIntS_integrable` controls the windowed θ-integral of `(∂_θ²G)²·σθ` (the quantity
`ttIntS` itself, and its weighted angular part).  The present file removes the angular weight
`σθ = sin(2θ)^{-η}` from the *inside* of the θ-integral: on the open interval `(0,π/2)` one has
`σθ ≥ 1`, so the unweighted slice integral is at most the weighted one, and the two differ only
on the null set of the endpoints.  Hence the windowed plain θ-integral is integrable in `t`.

The only non-elementary point is the a.e. strong measurability of
`t ↦ if |log z - t| ≤ δ then ∫_θ (∂_θ²G)(exp t,θ)² else 0`: the *joint* integrand
`(t,θ) ↦ 1_{window}(t)·(∂_θ²G)(exp t,θ)²` is a.e. strongly measurable on the product
(`thSlice_window_aesm`), and the θ-integral of a jointly a.e. strongly measurable function is
a.e. strongly measurable in the remaining variable (`AEStronglyMeasurable.integral_prod_right'`).
Moving the (θ-independent) `if` out of the integral is then pure bookkeeping. -/

/-- **The unweighted angular slice integral is dominated by the weighted one.**  For any datum
`G` and radius `u`, if the `σθ`-weighted square of the second angular derivative is integrable
on `Iθ`, then so is the comparison
`∫_θ (∂_θ²G)² ≤ ∫_θ (∂_θ²G)²·σθ`.  The two sides agree on `(0,π/2)` up to the factor
`σθ ≥ 1`, and the endpoints form a null set. -/
lemma theta_slice_le_weighted (G : ℝ → ℝ → ℝ) (u : ℝ)
    (hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.pth (Work.Spaces.pth G) u θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.pth G) u θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pth (Work.Spaces.pth G) u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
  -- the closed interval `Iθ` carries the same measure as the open one
  have hIθ : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [Work.Spaces.Iθ]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
        (b := Real.pi / 2))).symm
  rw [hIθ]
  refine MeasureTheory.setIntegral_mono_of_nonneg
    (fun θ _ => sq_nonneg _) (fun θ hθ => ?_)
    (hint.mono_set (fun x hx => ⟨hx.1.le, hx.2.le⟩))
  -- on the open interval `σθ ≥ 1`, so `(∂_θ²G)² ≤ (∂_θ²G)²·σθ`
  have h1 : 1 ≤ Work.FTS.EllipticEst.thEta θ := one_le_thEta_of_mem_Ioo hθ
  have hFnn : (0 : ℝ) ≤ (Work.Spaces.pth (Work.Spaces.pth G) u θ) ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg hFnn (sub_nonneg.mpr h1)]

theorem window_ttIntS_plain_integrable (G : ℝ → ℝ → ℝ)
    (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hF : Work.FTS.EllSol.EllPkgAux.FourInts G) (δ z : ℝ) (hδ : 0 < δ) (hz : 0 < z) :
    MeasureTheory.Integrable (fun t : ℝ => if |Real.log z - t| ≤ δ then
        (∫ s in Work.Spaces.Iθ,
          (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2) else 0) := by
  -- the honesty of the angular second derivative at every radius
  have hHon : Work.EllipticEst.Core.i0Aux.SliceHonestOpen G := hT.2.2.2.2.2.2.2
  -- the *weighted* windowed θ-integral is integrable
  obtain ⟨-, hw2⟩ :=
    window_ttIntS_integrable G hT hF δ z hδ hz
  -- a.e. strong measurability: the joint windowed square is AESM on the product, hence so is
  -- its θ-integral
  have hJoint : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => if |Real.log z - p.1| ≤ δ then
        (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp p.1) p.2) ^ 2 else 0)
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    thSlice_window_aesm G hT δ z
  have hCurried := hJoint.integral_prod_right'
  have hconv : (fun t : ℝ => ∫ θ, (if |Real.log z - t| ≤ δ then
        (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) θ) ^ 2 else 0)
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      = fun t : ℝ => if |Real.log z - t| ≤ δ then
          (∫ s in Work.Spaces.Iθ,
            (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2) else 0 := by
    funext t
    by_cases h : |Real.log z - t| ≤ δ
    · rw [ite_eq_left h]
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ite_eq_left h)
    · rw [ite_eq_right h]
      simp [h]
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => if |Real.log z - t| ≤ δ then
        (∫ s in Work.Spaces.Iθ,
          (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2) else 0)
      MeasureTheory.volume :=
    hCurried.congr (Filter.Eventually.of_forall (fun t => congrFun hconv t))
  -- domination by the weighted windowed θ-integral
  refine MeasureTheory.Integrable.mono' hw2 haesm ?_
  filter_upwards with t
  by_cases h : |Real.log z - t| ≤ δ
  · rw [Real.norm_eq_abs, ite_eq_left h, ite_eq_left h]
    have hInt := pth2_slice_integrable G hHon.1 (Real.exp t) (Real.exp_pos t)
    have hcmp := theta_slice_le_weighted G (Real.exp t) hInt
    have hnn : (0 : ℝ) ≤ ∫ s in Work.Spaces.Iθ,
        (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2 :=
      MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun s _ => sq_nonneg _)
    rw [abs_of_nonneg hnn]
    exact hcmp
  · rw [Real.norm_eq_abs, ite_eq_right h, ite_eq_right h]
    simp

end Work.FTS.EllSol.EllPkgAux.MollDom
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Final.AeSigmaUpD =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Final

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

/-- `EllWeakPos` is `AeData` (the pointwise moments imply the a.e. ones; the classes are
otherwise identical). -/
theorem aeData_of_ellWeakPos' {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ) :
    Work.FTS.EllipticEst.H2W.Ae.AeData α Ψ F :=
  ⟨hα, hα4, h.eq, h.zero, h.pi_half, h.smooth, h.memF, h.memA, h.memB,
    (by filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
        exact h.orthPsi z hz),
    (by filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
        exact h.orthF z hz)⟩

/-- **The `σ`-upgrade of the `u`-norm in the a.e. class** (Step 1, the `u`-half): for a datum
`u` of the almost-everywhere class, `HkSq α 0 u ≤ C · L2Sq (∂_θu · w)`.

This is the statement `aeSigmaUp` of `H2W/Ae/aeSigmaUp.lean`.  It is proved here from the
*already proved* slicewise σ-Poincaré upgrade `AeProof.AeSigmaUpgradeU_all` (an inequality of
`∫⁻`-integrals, `AeSigmaUpgradeU_all`), by translating the `∫⁻`-statement into the Bochner
statement `HkSq`/`L2Sq` with `MeasureTheory.integral_eq_lintegral_of_nonneg_ae`. -/
theorem aeSigmaUpD : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.L2Mem (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z) →
      Work.Spaces.HkSq α 0 u
        ≤ C * Work.Spaces.L2Sq (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.FTS.EllipticEst.H2W.AeProof.AeSigmaUpgradeU_all
  refine ⟨C₀, hC₀pos, ?_⟩
  intro α u G hA hL2
  -- ## abbreviations
  set Asl : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    with hAsl
  set Bsl : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2 with hBsl
  set Apr : ℝ → ℝ≥0∞ := fun z => ∫⁻ θ in Work.Spaces.Iθ,
    ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) with hApr
  set Bpr : ℝ → ℝ≥0∞ := fun z => ∫⁻ θ in Work.Spaces.Iθ,
    ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2) with hBpr
  -- ## elementary facts
  have hsEta_nn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Work.FTS.EllipticEst.sEta θ := by
    intro θ hθ
    show 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    exact Real.rpow_nonneg (Work.FTS.EllipticEst.Honest.sin_two_nonneg_of_mem_Iθ hθ) _
  have hAsl_nn : ∀ z, 0 ≤ Asl z := by
    intro z
    rw [hAsl]
    exact setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (hsEta_nn θ hθ))
  have hBsl_nn : ∀ z, 0 ≤ Bsl z := by
    intro z
    rw [hBsl]
    exact setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  -- ## the level-`0` integrand is `w²·(u²σ)`
  have hptid : ∀ z θ, θ ∈ Work.Spaces.Iθ →
      Work.Spaces.HkIntegrand α 0 u z θ
        = (Work.Spaces.w z) ^ 2 * ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    intro z θ hθ
    rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq, mul_pow,
      Work.FTS.EllipticEst.Honest.sq_weight_eq (Work.FTS.EllipticEst.Honest.sin_two_nonneg_of_mem_Iθ hθ)]
    simp only [Work.FTS.EllipticEst.sEta]
    ring
  have hslice : ∀ z, (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
      = (Work.Spaces.w z) ^ 2 * Asl z := by
    intro z
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    exact hptid z θ hθ
  -- ## `HkSq` as a `toReal` of a `lintegral`
  have hHk : Work.Spaces.HkSq α 0 u
      = (∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * Asl z)).toReal := by
    rw [Work.FTS.EllipticEst.HkSq_eq_lintegral α 0 u hA.smooth]
    congr 1
    exact MeasureTheory.lintegral_congr fun z => by rw [hslice z]
  -- ## `L2Sq` as a `toReal` of a `lintegral`
  have hL2pt : (fun z => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2)
      = fun z => (Work.Spaces.w z) ^ 2 * Bsl z := by
    funext z
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    ring
  have hL2mem : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * Bsl z) Work.Spaces.Iz :=
    hL2.2.congr_fun (fun z _ => congr_fun hL2pt z) measurableSet_Ici
  have hL2l : Work.Spaces.L2Sq (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z)
      = (∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * Bsl z)).toReal := by
    rw [Work.Spaces.L2Sq, hL2pt]
    exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (hBsl_nn z))
      hL2mem.aestronglyMeasurable
  -- ## the slicewise measurability of `u²σ`
  have hslice_smooth : ∀ z, 0 < z →
      ContDiffOn ℝ 1 (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) := by
    intro z hz
    have hmap : MapsTo (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun θ hθ => ⟨hz, hθ⟩
    exact (hA.smooth 1).comp (by fun_prop) hmap
  have haesm_slice : ∀ z, 0 < z → AEStronglyMeasurable
      (fun θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    exact ((Work.FTS.EllipticEst.Honest.aesm_of_contDiffOn_Ioo (hslice_smooth z hz)).pow 2).mul
      (Work.FTS.EllipticEst.H2W.Ae.measurable_sEta.aestronglyMeasurable)
  -- ## the slicewise identity `Asl z = (∫⁻ ...).toReal`
  have hAsl_eq : ∀ z, 0 < z → Asl z = (Apr z).toReal := by
    intro z hz
    rw [hAsl, hApr]
    refine MeasureTheory.integral_eq_lintegral_of_nonneg_ae ?_ (haesm_slice z hz)
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (hsEta_nn θ hθ))
  -- ## pointwise domination, a.e. in `z`
  have hdom_ae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * Asl z)
        ≤ ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Apr z := by
    rw [Work.Spaces.Iz, MeasureTheory.ae_restrict_iff' measurableSet_Ici]
    have hne : ∀ᵐ z ∂(MeasureTheory.volume : Measure ℝ), z ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [hne] with z hz hzI
    have hzpos : 0 < z := lt_of_le_of_ne hzI (Ne.symm hz)
    rw [ENNReal.ofReal_mul (sq_nonneg (Work.Spaces.w z))]
    refine mul_le_mul_of_nonneg_left ?_ bot_le
    rw [hAsl_eq z hzpos]
    exact ENNReal.ofReal_toReal_le
  have hstepA : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * Asl z))
      ≤ ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Apr z :=
    MeasureTheory.lintegral_mono_ae hdom_ae
  -- ## the proved slicewise upgrade
  have hup : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Apr z)
      ≤ ENNReal.ofReal C₀ * (∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Bpr z) :=
    hC₀ α u G hA
  -- ## the two `∫⁻`-expressions agree with the Bochner ones
  have hint2 : ∀ z, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pth u z θ) ^ 2) Work.Spaces.Iθ := by
    intro z hz
    have hwz : Work.Spaces.w z ≠ 0 := by
      rw [Work.Spaces.w]; positivity
    have hint : MeasureTheory.Integrable
        (fun θ => (Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hL2.1 z (le_of_lt hz)
    have hdiv : MeasureTheory.Integrable
        (fun θ => (Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2 / (Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hint.div_const _
    have haeeq : (fun θ => (Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2
          / (Work.Spaces.w z) ^ 2) =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun θ => (Work.Spaces.pth u z θ) ^ 2) := by
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => ?_)
      field_simp
    exact hdiv.congr haeeq
  have hBsl_eq : ∀ z, 0 < z → Bsl z = (Bpr z).toReal := by
    intro z hz
    rw [hBsl, hBpr]
    refine MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun θ => sq_nonneg _) (hint2 z hz).aestronglyMeasurable
  have hBpr_ne : ∀ z, 0 < z → Bpr z ≠ ⊤ := by
    intro z hz
    rw [hBpr]
    exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable (hint2 z hz).aestronglyMeasurable
      (Filter.Eventually.of_forall fun θ => sq_nonneg _)).mpr (hint2 z hz)
  have hCeq_ae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Bpr z
        = ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * Bsl z) := by
    rw [Work.Spaces.Iz, MeasureTheory.ae_restrict_iff' measurableSet_Ici]
    have hne : ∀ᵐ z ∂(MeasureTheory.volume : Measure ℝ), z ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [hne] with z hz hzI
    have hzpos : 0 < z := lt_of_le_of_ne hzI (Ne.symm hz)
    rw [hBsl_eq z hzpos, ENNReal.ofReal_mul (sq_nonneg (Work.Spaces.w z)),
      ENNReal.ofReal_toReal (hBpr_ne z hzpos)]
  have hstepC : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Bpr z)
      = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * Bsl z) :=
    MeasureTheory.lintegral_congr_ae hCeq_ae
  -- ## finiteness of the right-hand side
  have hYne : (∫⁻ z in Work.Spaces.Iz,
      ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * Bsl z)) ≠ ⊤ := by
    refine (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      hL2mem.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (hBsl_nn z))).mpr hL2mem
  have hBne : (∫⁻ z in Work.Spaces.Iz,
      ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Bpr z) ≠ ⊤ := by
    rw [hstepC]; exact hYne
  have hBne' : ENNReal.ofReal C₀ * (∫⁻ z in Work.Spaces.Iz,
      ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Bpr z) ≠ ⊤ := by
    rw [hstepC]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hYne
  have hAne : (∫⁻ z in Work.Spaces.Iz,
      ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Apr z) ≠ ⊤ :=
    ne_top_of_le_ne_top hBne' hup
  -- ## assembly
  calc Work.Spaces.HkSq α 0 u
      = (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * Asl z)).toReal := hHk
    _ ≤ (∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Apr z).toReal :=
        ENNReal.toReal_mono hAne hstepA
    _ ≤ (ENNReal.ofReal C₀ * ∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Bpr z).toReal :=
        ENNReal.toReal_mono hBne' hup
    _ = C₀ * (∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Bpr z).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC₀pos.le]
    _ = C₀ * Work.Spaces.L2Sq (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z) := by
        rw [hstepC, ← hL2l]

end Work.FTS.EllipticEst.Final
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.ESW.ShiftWeak =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT.ESW.Shift

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Tools -/

/-- **The source of the weak class is `C^∞` on the open quadrant.**  On `Q0` it agrees with
`bslOp α Ψ`, which is `C^∞` there by `SmoothOpen_bslOp_of_smoothOpen`. -/
theorem SmoothOpen_of_bslOp_eq {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (heq : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Ψ z θ = F z θ) :
    Work.FTS.EllipticEst.SmoothOpen F :=
  Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hΨ) heq

/-- The shifted mixed slots: for `f` of class `C^∞` on the open quadrant and `(z,θ)` in the open
quadrant, `D_z^j D_θ^i (D_z f) = D_z^{j+1} D_θ^i f`. -/
theorem mixed_Dz_shift_eq {j i : ℕ} (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hg : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ = Work.Spaces.mixed (j + 1) i f z θ := by
  have hcomm : Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i f)))
      (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz f))) Work.FTS.EllipticEst.remov.Step.Qd :=
    Work.FTS.EllipticEst.DzAmgm.DthIterDzCommOpen f hg i
  have hpt : (z, θ) ∈ Work.FTS.EllipticEst.remov.Step.Qd := ⟨hz, hθ⟩
  have hcongr : Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
      = Work.Spaces.DzIter j (Work.Spaces.Dz (Work.Spaces.DthIter i f)) z θ :=
    Work.FTS.EllipticEst.remov.Step.DzIter_congr_of_isOpen Work.FTS.EllipticEst.remov.Step.isOpen_Qd hcomm.symm j hpt
  show Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
    = Work.Spaces.DzIter (j + 1) (Work.Spaces.DthIter i f) z θ
  rw [hcongr, Work.FTS.EllipticEst.remov.Step.DzIter_Dz j (Work.Spaces.DthIter i f)]

/-- **The pointwise `D_z`-shift bound on the open quadrant.**  Every slot of
`HkIntegrand α (k-1) (D_z f)` is a slot of `HkIntegrand α k f` (up to the commutation of `D_z`
with `D_θ^i`), and each single slot is dominated by the whole integrand; counting `k` radial and
`k·k` mixed slots gives the factor `k + k²`. -/
theorem HkIntegrand_Dz_shift_le (α : ℝ) {k : ℕ} (hk : 1 ≤ k) (f : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hg : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ
      ≤ ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α k f z θ :=
    Work.Spaces.HkIntegrand_nonneg α k f z θ
  have hZ : Work.FTS.EllipticEst.remov.Step.Zsum (k - 1) (Work.Spaces.Dz f) z θ
      ≤ (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
    have hterm : ∀ i ∈ Finset.range k,
        (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Work.FTS.EllipticEst.remov.Step.Zu z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α k f z θ := by
      intro i hi
      have hik : i + 1 ≤ k := by
        have := Finset.mem_range.mp hi
        omega
      rw [Work.FTS.EllipticEst.remov.Step.DzIter_Dz i f]
      exact Work.Spaces.sq_le_HkIntegrand_z α k f z θ (i + 1) hik
    have h1 : Work.FTS.EllipticEst.remov.Step.Zsum (k - 1) (Work.Spaces.Dz f) z θ
        = ∑ i ∈ Finset.range k,
            (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Work.FTS.EllipticEst.remov.Step.Zu z θ) ^ 2 := by
      unfold Work.FTS.EllipticEst.remov.Step.Zsum
      exact Finset.sum_congr (by rw [show k - 1 + 1 = k from by omega])
        (fun i _ => rfl)
    rw [h1]
    calc (∑ i ∈ Finset.range k,
          (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Work.FTS.EllipticEst.remov.Step.Zu z θ) ^ 2)
        ≤ ∑ _i ∈ Finset.range k, Work.Spaces.HkIntegrand α k f z θ :=
          Finset.sum_le_sum hterm
      _ = (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hM : Work.FTS.EllipticEst.remov.Step.Msum α (k - 1) (Work.Spaces.Dz f) z θ
      ≤ ((k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
    rw [Work.FTS.EllipticEst.remov.Step.Msum_eq_rows, show k - 1 + 1 = k from by omega]
    have hterm : ∀ i ∈ Finset.range k,
        (∑ j ∈ Finset.range (k - i),
          (if 1 ≤ i then (Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
      intro i hi
      have hstep : (∑ j ∈ Finset.range (k - i),
          (if 1 ≤ i then (Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ ∑ _j ∈ Finset.range (k - i), Work.Spaces.HkIntegrand α k f z θ := by
        refine Finset.sum_le_sum (fun j hj => ?_)
        by_cases hi1 : 1 ≤ i
        · rw [if_pos hi1]
          rw [mixed_Dz_shift_eq f hz hθ hg]
          have hj' : i + (j + 1) ≤ k := by
            have := Finset.mem_range.mp hj
            omega
          exact Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ i (j + 1) hi1 hj'
        · rw [if_neg hi1]
          exact hHnn
      refine le_trans hstep ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hcast : ((k - i : ℕ) : ℝ) ≤ (k : ℝ) := by
        have : k - i ≤ k := by omega
        exact_mod_cast this
      have hci : (0 : ℝ) ≤ ((k - i : ℕ) : ℝ) := by positivity
      nlinarith [hHnn, hcast, hci]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    have hsum : (∑ _i ∈ Finset.range k, (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ)
        = ((k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    exact hsum.le
  rw [Work.FTS.EllipticEst.remov.Step.HkIntegrand_eq α k f z θ] at hZ hM ⊢
  rw [Work.FTS.EllipticEst.remov.Step.HkIntegrand_eq α (k - 1) (Work.Spaces.Dz f) z θ]
  have hnn : 0 ≤ Work.FTS.EllipticEst.remov.Step.Zsum k f z θ + Work.FTS.EllipticEst.remov.Step.Msum α k f z θ :=
    Work.Spaces.HkIntegrand_nonneg α k f z θ
  nlinarith [hZ, hM, hnn]

/-- **Membership form of the `D_z`-shift**: if `f` is `C^∞` on the open quadrant and in
`ℋ^k` (`k ≥ 1`), then `D_z f ∈ ℋ^{k-1}`. -/
theorem HkMem_Dz_shift {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α (k - 1) (Work.Spaces.Dz f) := by
  refine Work.FTS.EllipticEst.TT.ESW.HkMem_of_majorant_ae α (k - 1) (f := Work.Spaces.Dz f)
    (M := fun z θ => ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ)
    ?_ ?_ ?_ ?_
  · exact (Work.FTS.EllipticEst.SmoothOpen.Dz hf).continuousOn_HkIntegrand α (k - 1)
  · intro z hz
    exact (hmem.1 z hz).const_mul _
  · show MeasureTheory.Integrable
      (fun z => ∫ θ in Work.Spaces.Iθ,
        ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz)
    simpa only [MeasureTheory.integral_const_mul] using hmem.2.const_mul _
  · intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hz0
    · subst h0
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
      exact Filter.Eventually.of_forall fun θ _ => by
        rw [Work.FTS.LocData.HkIntegrand_zero_fst α (k - 1) (Work.Spaces.Dz f) θ,
          Work.FTS.LocData.HkIntegrand_zero_fst α k f θ, mul_zero]
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
      exact Filter.Eventually.of_forall fun θ hθ =>
        HkIntegrand_Dz_shift_le α hk f hz0 hθ hf

/-- **`∂_z` commutes with `∂_θ²` on the open quadrant**: Clairaut's theorem applied twice. -/
theorem pz_pthIter_two_comm {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.AgreeOnQ
      (Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ))
      (Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ)) := by
  intro z θ hz hθ hlt
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hlt⟩
  have hcd : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      ContDiffAt ℝ 2 (Function.uncurry Ψ) (z', θ') := fun z' θ' hz' hθ' hlt' =>
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall Ψ).mp hΨ 2).contDiffAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz', hθ', hlt'⟩))
  have hcd_pth : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pth Ψ)) (z, θ) :=
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.pth Ψ)).mp
      (Work.FTS.EllipticEst.SmoothOpen.pth hΨ) 2).contDiffAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)
  have h1 : Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth Ψ)) z θ
      = Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth Ψ)) z θ :=
    Work.Spaces.pz_pth_comm (f := Work.Spaces.pth Ψ) hcd_pth
  have hagree : Work.FTS.EllipticEst.AgreeOnQ (Work.Spaces.pz (Work.Spaces.pth Ψ))
      (Work.Spaces.pth (Work.Spaces.pz Ψ)) :=
    fun z' θ' hz' hθ' hlt' => Work.Spaces.pz_pth_comm (f := Ψ) (hcd z' θ' hz' hθ' hlt')
  have h2 : Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth Ψ)) z θ
      = Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pz Ψ)) z θ :=
    Work.Spaces.pth_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0
      (fun p hp => by
        obtain ⟨z', θ'⟩ := p
        exact hagree z' θ' hp.1 hp.2.1 hp.2.2) hmem
  show Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ
      = Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) z θ
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
  exact h1.trans h2

/-- **`D_z` commutes with `∂_θ²` on the open quadrant.** -/
theorem Dz_pthIter_two_comm {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.AgreeOnQ (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ))
      (Work.Spaces.pthIter 2 (Work.Spaces.Dz Ψ)) := by
  have hplain := pz_pthIter_two_comm hΨ
  have hmul : Work.Spaces.pth (Work.Spaces.Dz Ψ)
      = fun z θ => z * Work.Spaces.pth (Work.Spaces.pz Ψ) z θ := by
    funext z θ
    show deriv (fun θ' => z * Work.Spaces.pz Ψ z θ') θ
      = z * deriv (fun θ' => Work.Spaces.pz Ψ z θ') θ
    rw [deriv_const_mul_field]
  have hstep : Work.Spaces.pthIter 2 (Work.Spaces.Dz Ψ)
      = fun z θ => z * Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) z θ := by
    have h2 : Work.Spaces.pthIter 2 (Work.Spaces.Dz Ψ)
        = Work.Spaces.pth (fun z θ => z * Work.Spaces.pth (Work.Spaces.pz Ψ) z θ) := by
      rw [← hmul]
      simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
    rw [h2]
    funext z θ
    show deriv (fun θ' => z * Work.Spaces.pth (Work.Spaces.pz Ψ) z θ') θ
      = z * deriv (fun θ' => Work.Spaces.pth (Work.Spaces.pz Ψ) z θ') θ
    rw [deriv_const_mul_field]
  intro z θ hz hθ hlt
  show z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ
      = Work.Spaces.pthIter 2 (Work.Spaces.Dz Ψ) z θ
  rw [hstep, hplain z θ hz hθ hlt]

/-! ## The shift -/

/-- **The assembly of the shift, given the two moment conditions.**  All nine fields of
`EllWeakPos α (k-1) (D_z F) (D_z Ψ)` are produced here except the two moment conditions, which
are supplied as explicit hypotheses. -/
theorem EllWeakPos_DzIter_one_shift_of_moments {α : ℝ} {k : ℕ} (hk : 1 ≤ k)
    {F Ψ : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ)
    (hmomF : ∀ z, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter 1 F) z = 0)
    (hmomΨ : ∀ z, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z = 0) :
    Work.FTS.EllipticEst.TT.EllWeakPos α (k - 1)
      (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) := by
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.TT.EllWeakPos.smoothOpen h
  have hSF : Work.FTS.EllipticEst.SmoothOpen F :=
    SmoothOpen_of_bslOp_eq hSΨ (fun z θ hz hθ hlt => h.1 z hz θ hθ hlt)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Work.FTS.EllipticEst.TT.bslOp_DzIter_eq α F Ψ 1 h.smooth h.1
  · exact Work.FTS.EllipticEst.TT.DzIter_zero_at_zero Ψ 1 h.zero
  · exact Work.FTS.EllipticEst.TT.DzIter_zero_at_pi_half Ψ 1 h.pi_half
  · exact hmomF
  · exact hmomΨ
  · intro n
    exact (Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.DzIter 1 Ψ)).mp
      (Work.FTS.EllipticEst.TT.EllWeakPos.smoothOpen_DzIter h 1) n
  · have hmem : Work.Spaces.HkMem α (k - 1) (Work.Spaces.Dz F) :=
      HkMem_Dz_shift hk hSF h.memF
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using hmem
  · have hG : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
      Work.FTS.EllipticEst.TT.ESW.SmoothOpen_zsq_mul (Work.FTS.EllipticEst.SmoothOpen.pzIter hSΨ 2)
    have hmem : Work.Spaces.HkMem α (k - 1)
        (Work.Spaces.Dz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
      HkMem_Dz_shift hk hG h.memA
    have hEqOn := Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm Ψ hSΨ 1 0
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α (k - 1) hmem ?_
    intro z hz θ hθ
    exact (hEqOn (show ((z, θ) : ℝ × ℝ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)
      from ⟨hz, hθ⟩)).symm
  · have hmem : Work.Spaces.HkMem α (k - 1)
        (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ)) :=
      HkMem_Dz_shift hk (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hSΨ 2) h.memB
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α (k - 1) hmem ?_
    intro z hz θ hθ
    exact Dz_pthIter_two_comm hSΨ z θ hz hθ.1 hθ.2
  · -- `ℋ^{k-1}`-honesty of the diagonal second-order term of the shifted datum:
    -- `z ∂_z∂_θθ(D_zΨ) = D_z (D_z ∂_θθΨ)`, and `∂_θθ` commutes with `D_z`.
    have hZ : Work.Spaces.HkMem α (k - 1)
        (Work.Spaces.Dz (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ))) :=
      HkMem_Dz_shift hk
        (Work.FTS.EllipticEst.SmoothOpen.Dz
          (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hSΨ 2))
        h.memZPth2
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α (k - 1) hZ ?_
    intro z hz θ hθ
    show Work.Spaces.Dz (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ)) z θ
      = z * Work.Spaces.pz (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) z θ
    have hpe : Work.Spaces.pz (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) z θ
        = Work.Spaces.pz (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) z θ :=
      Work.Spaces.pz_congr_of_isOpen (isOpen_Ioi.prod isOpen_Ioo)
        (Work.EllipticEst.H2W.pthIter2_DzIter_comm hSΨ 1) ⟨hz, hθ⟩
    rw [hpe, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
    rfl


/-- **The shift, for `2 ≤ k`** — the instance needed by the induction step of `prop:Hk` (the
shifted data are consumed at level `k-1 ≥ 2`) and by the level-`2` assembly.  Both moment
conditions are available from proved lemmas: the `F`-half from `Fstar_DzIter_one_F_ge_two`
(which needs `k ≥ 2`) and the `Ψ`-half from `Mine.FstarDzOnePsi`. -/
theorem EllWeakPos_DzIter_one_shift_of_two_le {α : ℝ} {k : ℕ} (hk : 2 ≤ k)
    {F Ψ : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    Work.FTS.EllipticEst.TT.EllWeakPos α (k - 1)
      (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) :=
  EllWeakPos_DzIter_one_shift_of_moments (by omega) h
    (Work.FTS.EllipticEst.remov.Fstar_DzIter_one_F_ge_two hk h)
    (Work.FTS.EllipticEst.Mine.FstarDzOnePsi α (by omega) F Ψ h)

end Work.FTS.EllipticEst.TT.ESW.Shift
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.ESW.SourceAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT.ESW

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-!
# `source_le` — auxiliary lemmas

This module contains the verified auxiliary lemmas used by `ESW.source_le` (and by the
delegated pieces `ESW.srcA` / `ESW.srcH`): the smoothness of the data on the open quadrant, the
triangular comparison for the top plain angular derivative (`reverse_expansion_sq`), and the
pointwise/integrated top-slot bounds together with the `F`-piece `srcF`.

The top plain angular slot of the source `Gsl α F Ψ = F + α²Asl Ψ + α(5+α)·DzIter 1 Ψ` of the
sliced equation is dominated by `C·HkSq α k F`, for `k ≥ 3`, `0 < α ≤ 1/4`, under the two
level-`(k-1)` bounds on `(Asl Ψ, Bsl Ψ)` and on `(Asl (D_zΨ), Bsl (D_zΨ))`.

## Route

Write `A := Asl Ψ = z²∂_z²Ψ`, `B := Bsl Ψ = ∂_θ²Ψ`, `h := DzIter 1 Ψ = z∂_zΨ`.  Pointwise,

  `∂_θ^kG = ∂_θ^kF + α²∂_θ^kA + α(5+α)∂_θ^kh`  hence
  `(∂_θ^kG)² ≤ 3((∂_θ^kF)² + α⁴(∂_θ^kA)² + α²(5+α)²(∂_θ^kh)²)`.

* **`F`-part** (`srcF`): the plain top slot of a smooth datum is dominated pointwise (a.e. in
  `θ`) by its `H^k`-integrand (`slot_pointwise_HkIntegrand`, whose engine is the sharp chain
  `dthChain_core`: `(sin(2θ)^k ∂_θ^k v)² ≤ C Σ_{r∈Icc 1 k}(D_θ^r v)²`); the passage to the
  integral is `theta_slice_mono` + `z_integral_mono_const`, and `HkMem α k F` (a field of
  `EllWeakPos`) supplies the honesty.
* **`A`-part** (`srcA`): the same pointwise bound with `v = A` gives
  `α⁴∫∫(∂_θ^kA)²w²σ^{2k-γ} ≤ C α⁴ HkSq α k A`; the level-`k` norm of `A` is then reduced by
  `HkSq_step_le` to `HkSq α (k-1) A` (hypothesis H1), to `HkSq α (k-1) (D_z A)` (which is
  `HkSq α (k-1) (Asl (D_zΨ))`, hypothesis H2) and to the single top angular slot `Tk α k A`
  (`A_top_slot_bound`).
* **`h`-part** (`srcH`): the triangular comparison `σ^{j-2}|∂_θ^jh| ≤ K(|D_θ^{j-2}h''| +
  Σ_{r<j-2}σ^r|∂_θ^{r+2}h|)` (reading off the `r = j-2` coefficient `dthCoef (j-2) (j-2) = σ^{j-2}`
  of the exact expansion `DthIter_expansion_local`, and bounding the others by
  `DthCoef_sin_pow_bound`) expresses the `η`-weighted plain slots of `h` in terms of the
  `η`-weighted `D_θ`-slots of `h'' = ∂_θ²h = D_z B`, which are dominated by the `γ`-weighted
  slots of `B` (hypothesis H1) because `σ^{-η} ≤ σ^{-γ}` pointwise.

The `A`-part is the only place where a genuine `H^k` elliptic input is used
(`A_top_slot_bound`, a proved lemma of the sibling directory); the `h`-part is proved here by
the triangular comparison above.
-/

/-! ## Smoothness of the data on the open quadrant -/

/-- `tan` is `C^∞` on the open quadrant (its singularities are at `π/2 + ℤπ`). -/
private theorem contDiffOn_tan_snd (n : ℕ) :
    ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.tan p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  intro p hp
  have hcos : Real.cos p.2 ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hp.2.1, Real.pi_pos], hp.2.2⟩)
  exact (((Real.contDiffAt_tan.mpr hcos).comp p contDiffAt_snd)).contDiffWithinAt




/-- `bslOp α Ψ` is `C^∞` on the open quadrant. -/
theorem contDiffOn_bslOp {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hΨ : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry (Work.Elliptic.bslOp α Ψ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  set Q : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) with hQ
  have h1 : ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pzIter 2 Ψ)) Q :=
    (Work.FTS.EllipticEst.SmoothOpen.pzIter
      (Work.FTS.EllipticEst.smoothOpen_of_forall hΨ) 2).forall n
  have h2 : ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pzIter 1 Ψ)) Q :=
    (Work.FTS.EllipticEst.SmoothOpen.pzIter
      (Work.FTS.EllipticEst.smoothOpen_of_forall hΨ) 1).forall n
  have h3 : ContDiffOn ℝ n (Function.uncurry Ψ) Q := hΨ n
  have h4 : ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pthIter 2 Ψ)) Q :=
    (Work.FTS.EllipticEst.SmoothOpen.pth
      (Work.FTS.EllipticEst.SmoothOpen.pth
        (Work.FTS.EllipticEst.smoothOpen_of_forall hΨ))).forall n
  have h5 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.tan θ * Ψ z θ) :=
    Work.FTS.EllipticEst.smoothOpen_of_forall
      (fun m => (contDiffOn_tan_snd m).mul (hΨ m))
  have h6 : ContDiffOn ℝ n
      (Function.uncurry (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ))) Q :=
    h5.pth.forall n
  have h3c : ContDiffOn ℝ n (fun p : ℝ × ℝ => (6 : ℝ) * Ψ p.1 p.2) Q :=
    contDiffOn_const.mul h3
  have h7 : ContDiffOn ℝ n (Function.uncurry (fun z θ =>
      -((α ^ 2) * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ)) Q := by
    have hp : ContDiffOn ℝ n (fun p : ℝ × ℝ => -((α ^ 2) * p.1 ^ 2)) Q := by fun_prop
    exact (hp.mul h1).congr (fun p _ => rfl)
  have h8 : ContDiffOn ℝ n (Function.uncurry (fun z θ =>
      -((α * (5 + α)) * z) * Work.Spaces.pzIter 1 Ψ z θ)) Q := by
    have hp : ContDiffOn ℝ n (fun p : ℝ × ℝ => -((α * (5 + α)) * p.1)) Q := by fun_prop
    exact (hp.mul h2).congr (fun p _ => rfl)
  have hL : ContDiffOn ℝ n (Function.uncurry (Work.Elliptic.Lzero Ψ)) Q := by
    rw [show Work.Elliptic.Lzero Ψ = fun z θ =>
        -(Work.Spaces.pthIter 2 Ψ z θ)
          + Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - 6 * Ψ z θ from rfl]
    exact (h4.neg.add h6).sub h3c
  have := (h7.add h8).add hL
  refine this.congr (fun p _ => ?_)
  simp only [Function.uncurry, Work.Elliptic.bslOp_apply, Work.Spaces.pzIter_succ,
    Work.Spaces.pzIter_zero]
  ring_nf

/-- `F` is `C^∞` on the open quadrant: it agrees there with `bslOp α Ψ`. -/
theorem contDiffOn_of_weak {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (hwk : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry F)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hbs : ContDiffOn ℝ n (Function.uncurry (Work.Elliptic.bslOp α Ψ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := contDiffOn_bslOp hwk.smooth n
  refine hbs.congr (fun p hp => ?_)
  have h := hwk.eq p.1 hp.1 p.2 hp.2.1 hp.2.2
  simp only [Function.uncurry]
  exact h.symm

/-! ## The pointwise and integrated top-slot bounds -/

/-- **The pointwise top-slot bound**: the top plain slot of a smooth datum is dominated, a.e.
in `θ`, by its `H^k`-integrand.  (`slot_pointwise_HkIntegrand` at `m = k`.) -/
theorem slot_top_le_HkIntegrand (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (v : ℝ → ℝ → ℝ), 0 < α →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry v)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
      ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter k v z θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - Work.Spaces.gam α))
          ≤ C * Work.Spaces.HkIntegrand α k v z θ := by
  obtain ⟨C, hC, h⟩ := Work.FTS.EllipticEst.remov.selfdth.slot_pointwise_HkIntegrand k (by omega)
  exact ⟨C, hC, fun α v hα hv => h α v k le_rfl hα hv⟩

/-- **The integrated top-slot bound**: the top plain slot of a datum in `H^k` is dominated by
`HkSq α k v`. -/
theorem slot_top_integral_le (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (v : ℝ → ℝ → ℝ), 0 < α →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry v)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
      Work.Spaces.HkMem α k v →
      (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
          ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k v z θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - Work.Spaces.gam α))
        ≤ C * Work.Spaces.HkSq α k v := by
  obtain ⟨C, hC, hpt⟩ := slot_top_le_HkIntegrand k hk
  refine ⟨C, hC, fun α v hα hv hmem => ?_⟩
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 *
          ((Work.Spaces.pthIter k v z θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - Work.Spaces.gam α)))
        ≤ ∫ θ in Work.Spaces.Iθ, C * Work.Spaces.HkIntegrand α k v z θ := by
    intro z hz
    have h0 := Work.FTS.EllipticEst.remov.selfdth.theta_slice_mono (K := k) (m := k) (v := v)
      (z := z) (C := C) hC.le (hmem.1 z hz) (hpt α v hα hv z hz)
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    exact h0
  exact Work.FTS.EllipticEst.remov.selfdth.z_integral_mono_const (K := k) (m := k) (v := v)
    (C := C) hC.le hmem.2
    ((MeasureTheory.ae_restrict_mem measurableSet_Ici).mono (fun z hz => hslice z hz))

/-! ## The `F`-piece -/

theorem srcF (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
          ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k F z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
        ≤ C * Work.Spaces.HkSq α k F := by
  obtain ⟨C, hC, h⟩ := slot_top_integral_le k hk
  exact ⟨C, hC, fun α F Ψ hα _ hwk =>
    h α F hα (contDiffOn_of_weak hwk) hwk.memF⟩

/-! ## The triangular comparison for the `h`-part -/

/-- Iterates of `∂_θ` compose. -/
theorem pthIter_add_local (m n : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter (m + n) f = Work.Spaces.pthIter m (Work.Spaces.pthIter n f) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.succ_add, Work.Spaces.pthIter_succ, ih, Work.Spaces.pthIter_succ]





end

end Work.FTS.EllipticEst.TT.ESW
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.aShiftSlotAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem slot11_eq (A : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed 1 1 A z θ
      = Real.sin (2 * θ) * Work.Spaces.Dz (Work.Spaces.pth A) z θ := by
  simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
    Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero, Work.Spaces.Dth, Work.Spaces.Dz,
    Work.Spaces.pth, Work.Spaces.pz]
  rw [deriv_const_mul_field]
  ring

/-- `(s^a)² = s^{2a}` for `s ≥ 0`. -/
theorem rpow_sq_eq {s a : ℝ} (hs : 0 ≤ s) : (s ^ a) ^ (2 : ℕ) = s ^ (2 * a) := by
  rw [← Real.rpow_natCast (s ^ a) 2, ← Real.rpow_mul hs]
  ring_nf

/-- `s² · s^{-γ} = s^{2-γ}` for `s ≥ 0` and `2 - γ ≠ 0`. -/
theorem sq_mul_rpow_neg {s γ : ℝ} (hs : 0 ≤ s) (h2 : (2 : ℝ) - γ ≠ 0) :
    s ^ (2 : ℝ) * s ^ (-γ) = s ^ (2 - γ) := by
  rcases eq_or_lt_of_le hs with h | h
  · rw [← h]
    by_cases hγ : γ = 0
    · subst hγ
      rw [show (-(0 : ℝ)) = 0 by norm_num, Real.rpow_zero, mul_one,
        Real.zero_rpow (by norm_num : (2 : ℝ) ≠ 0),
        Real.zero_rpow (by norm_num : (2 : ℝ) - 0 ≠ 0)]
    · rw [Real.zero_rpow (by norm_num : (2 : ℝ) ≠ 0),
        Real.zero_rpow (by simpa using hγ), zero_mul, Real.zero_rpow h2]
  · rw [← Real.rpow_add h]
    ring_nf

/-- **The pointwise weight identity of the slot.** -/
theorem slot11_sq_eq (α : ℝ) (A : ℝ → ℝ → ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.mixed 1 1 A z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.Dz (Work.Spaces.pth A) z θ
          * (Real.sin (2 * θ)) ^ ((2 - Work.Spaces.gam α) / 2) * Work.Spaces.w z) ^ 2 := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  rw [slot11_eq, Work.Spaces.Wt, Work.Spaces.wTheta]
  have h1 : (Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2))) ^ (2 : ℕ)
      = Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) := by
    rw [rpow_sq_eq hs]
    ring_nf
  have h2 : (Real.sin (2 * θ) ^ ((2 - Work.Spaces.gam α) / 2)) ^ (2 : ℕ)
      = Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α) := by
    rw [rpow_sq_eq hs]
    ring_nf
  have hgam2 : (2 : ℝ) - Work.Spaces.gam α ≠ 0 := by
    rw [Work.Spaces.gam]
    intro hc
    linarith
  have h3 : Real.sin (2 * θ) ^ (2 : ℕ)
        * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))
      = Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α) := by
    rw [← Real.rpow_natCast (Real.sin (2 * θ)) 2]
    exact sq_mul_rpow_neg hs hgam2
  calc (Real.sin (2 * θ) * Work.Spaces.Dz (Work.Spaces.pth A) z θ
        * (Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2)))) ^ 2
      = Real.sin (2 * θ) ^ (2 : ℕ) * (Work.Spaces.Dz (Work.Spaces.pth A) z θ) ^ 2
          * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2))) ^ (2 : ℕ) := by
        ring
    _ = Real.sin (2 * θ) ^ (2 : ℕ) * (Work.Spaces.Dz (Work.Spaces.pth A) z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) := by rw [h1]
    _ = Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α)
          * (Work.Spaces.Dz (Work.Spaces.pth A) z θ) ^ 2 * (Work.Spaces.w z) ^ 2 := by
        rw [← h3]; ring
    _ = (Work.Spaces.Dz (Work.Spaces.pth A) z θ
          * Real.sin (2 * θ) ^ ((2 - Work.Spaces.gam α) / 2) * Work.Spaces.w z) ^ 2 := by
        rw [← h2]; ring


/-- The zero function is honest in `ℋ⁰`. -/
theorem HkMem_zero_fun (α : ℝ) : Work.Spaces.HkMem α 0 (fun _ _ : ℝ => (0 : ℝ)) := by
  refine ⟨fun z _ => ?_, ?_⟩
  · have hz : (fun θ : ℝ => Work.Spaces.HkIntegrand α 0 (fun _ _ : ℝ => (0 : ℝ)) z θ)
        = fun _ : ℝ => (0 : ℝ) := by
      funext θ
      rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq]
      ring
    rw [hz]
    exact integrableOn_zero
  · have hz : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (fun _ _ : ℝ => (0 : ℝ)) z θ) = fun _ : ℝ => (0 : ℝ) := by
      funext z
      have h1 : (fun θ : ℝ => Work.Spaces.HkIntegrand α 0 (fun _ _ : ℝ => (0 : ℝ)) z θ)
          = fun _ : ℝ => (0 : ℝ) := by
        funext θ
        rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq]
        ring
      rw [h1, integral_zero]
    rw [hz]
    exact integrableOn_zero

/-- The level-`0` `ℋ`-square is the `L²`-square against the level-`0` weight. -/
theorem HkSq_zero_eq_L2Sq (α : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 g = Work.Spaces.L2Sq (fun z θ => g z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) := by
  rw [Work.Spaces.HkSq, Work.Spaces.L2Sq]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
  rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq]

/-- The level-`0` `ℋ`-square of the zero function vanishes. -/
theorem HkSq_zero_fun (α : ℝ) : Work.Spaces.HkSq α 0 (fun _ _ : ℝ => (0 : ℝ)) = 0 := by
  rw [Work.Spaces.HkSq]
  have h : ∀ z : ℝ, (∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 (fun _ _ : ℝ => (0 : ℝ)) z θ) = 0 := by
    intro z
    have h1 : (fun θ : ℝ => Work.Spaces.HkIntegrand α 0 (fun _ _ : ℝ => (0 : ℝ)) z θ)
        = fun _ : ℝ => (0 : ℝ) := by
      funext θ
      rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq]
      ring
    rw [h1, integral_zero]
  simp only [h, integral_zero]



/-! ## The `D_z²` slot split and the source slot, for the `Aof`/`Gof` datum -/

end Work.FTS.EllipticEst.TT
open Work.FTS.EllipticEst.H2W

namespace Work.FTS.EllipticEst.TT




end Work.FTS.EllipticEst.TT

open Work.FTS.EllipticEst.H2W

namespace Work.FTS.EllipticEst.TT

abbrev nr := Work.FTS.EllipticEst.H2W.Ae.nrm


end Work.FTS.EllipticEst.TT
end
end
-- ===== merged: Submission.Work.FTS.H2.HQ.BadMemQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.HQ

open MeasureTheory Set Filter
open scoped Real Topology
open Work.Spaces
open Work.FTS.LocData (SmoothQuad)

set_option maxHeartbeats 800000

/-- The `L2Mem` half of the bad-term package of the interior product rule `HProdQ`: given the
a.e.-in-`θ` norm-domination of the bad-term integrand `(D_z³f · D_θg · Wt)²` by the product
`badU α f z · badV α g θ` of the two one-dimensional Hardy bounds, together with the
integrability of the two dominating functions, the weighted product is square integrable in the
iterated sense (every angular slice integrable, and the resulting function of `z` integrable). -/
theorem BadMemQ (α : ℝ) (f g : ℝ → ℝ → ℝ)
    (hf : Work.FTS.LocData.SmoothQuad f) (hg : Work.FTS.LocData.SmoothQuad g)
    (hUint : MeasureTheory.Integrable (Work.Spaces.badU α f)
      (MeasureTheory.volume.restrict Work.Spaces.Iz))
    (hVint : MeasureTheory.Integrable (Work.Spaces.badV α g)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hdom : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), ∀ z ∈ Work.Spaces.Iz,
      ‖(Work.Spaces.DzIter 3 f z θ * Work.Spaces.Dth g z θ * Work.Spaces.Wt α z θ) ^ 2‖
        ≤ Work.Spaces.badU α f z * Work.Spaces.badV α g θ) :
    Work.Spaces.L2Mem (fun z θ => Work.Spaces.DzIter 3 f z θ * Work.Spaces.Dth g z θ
        * Work.Spaces.Wt α z θ) := by
  -- The joint strong measurability of the squared weighted product and that of every angular
  -- slice, supplied by the interior glue (`SmoothQuad` is closed under `D_z^3` and `D_θ`).
  have haesm := aesm_sq_prod_quad α (A := DzIter 3 f) (B := Dth g) (hf.DzIter 3) (hg.DthIter 1)
  -- The a.e.-in-`θ` domination, restricted to a fixed `z ∈ Iz`.
  have hdom' : ∀ z ∈ Iz, ∀ᵐ θ ∂(volume.restrict Iθ),
      ‖(DzIter 3 f z θ * Dth g z θ * Wt α z θ) ^ 2‖ ≤ badU α f z * badV α g θ :=
    fun z hz => hdom.mono fun θ hθ => hθ z hz
  constructor
  · -- Every angular slice is integrable, by domination by the (integrable) `θ ↦ badV α g θ`.
    intro z hz
    refine MeasureTheory.Integrable.mono' (hVint.const_mul (badU α f z)) (haesm.2 z hz) ?_
    filter_upwards [hdom' z hz] with θ hθ
    simpa only [Real.norm_of_nonneg (sq_nonneg (DzIter 3 f z θ * Dth g z θ * Wt α z θ))]
      using hθ
  · -- The iterated integral is integrable: its `z`-value is bounded by
    -- `badU α f z * ∫_θ badV α g`, and `badU α f` is integrable.
    refine MeasureTheory.Integrable.mono'
      (hUint.mul_const (∫ θ in Iθ, badV α g θ)) haesm.1.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Iz from measurableSet_Ici)] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
    calc ∫ θ in Iθ, (DzIter 3 f z θ * Dth g z θ * Wt α z θ) ^ 2
        ≤ ∫ θ in Iθ, badU α f z * badV α g θ := by
          refine MeasureTheory.integral_mono_ae
            (MeasureTheory.Integrable.mono'
              (hVint.const_mul (badU α f z)) (haesm.2 z hz) ?_)
            (hVint.const_mul (badU α f z)) ?_
          · filter_upwards [hdom' z hz] with θ hθ
            simpa only [Real.norm_of_nonneg
              (sq_nonneg (DzIter 3 f z θ * Dth g z θ * Wt α z θ))] using hθ
          · filter_upwards [hdom' z hz] with θ hθ
            simpa only [Real.norm_of_nonneg
              (sq_nonneg (DzIter 3 f z θ * Dth g z θ * Wt α z θ))] using hθ
      _ = badU α f z * ∫ θ in Iθ, badV α g θ := MeasureTheory.integral_const_mul _ _

end Work.FTS.H2.HQ
end
-- ===== merged: Submission.Work.FTS.H2.HQ.MsummandQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.HQ

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open Work.Spaces
open Work.FTS.LocData (SmoothQuad)

/-! ## The weight `Wt` vanishes on the boundary lines

`RegQ` constrains `f` only on the *open* quadrant, so all the pointwise estimates below
have to be taken where the weight `Wt α z θ = w z · sin(2θ)^{-γ/2}` does not vanish.
On the two lines `θ = 0`, `θ = π/2` and on `z = 0` the weight is `0` (Lean's totalised
division and `Real.zero_rpow`), which is exactly what makes the pointwise estimates at
those lines trivial: both sides of each of them vanish. -/

/-- `Wt α 0 θ = 0`: the radial weight vanishes at `z = 0`. -/
private theorem Wt_zero_left (α θ : ℝ) : Wt α 0 θ = 0 := by
  simp [Wt, w]

/-- `Wt α z 0 = 0` for `α > 0`: the angular weight vanishes at `θ = 0`. -/
private theorem Wt_zero_theta_zero (α z : ℝ) (hα : 0 < α) : Wt α z 0 = 0 := by
  have hgam : 0 < gam α := by rw [gam]; linarith
  have hexp : -(gam α / 2) ≠ 0 := by linarith
  rw [Wt, wTheta, show Real.sin (2 * 0) = 0 by norm_num, Real.zero_rpow hexp, mul_zero]

/-- `Wt α z (π/2) = 0` for `α > 0`: the angular weight vanishes at `θ = π/2`. -/
private theorem Wt_zero_theta_pi (α z : ℝ) (hα : 0 < α) : Wt α z (π / 2) = 0 := by
  have hgam : 0 < gam α := by rw [gam]; linarith
  have hexp : -(gam α / 2) ≠ 0 := by linarith
  rw [Wt, wTheta, show 2 * (π / 2) = π by ring, Real.sin_pi, Real.zero_rpow hexp, mul_zero]

/-- The weight vanishes on the boundary of the closed quadrant. -/
private theorem Wt_eq_zero_of_boundary (α z θ : ℝ) (hα : 0 < α) (hz : z ∈ Iz) (hθ : θ ∈ Iθ)
    (h : ¬ (0 < z ∧ 0 < θ ∧ θ < π / 2)) : Wt α z θ = 0 := by
  by_cases hz0 : z = 0
  · subst hz0
    exact Wt_zero_left α θ
  · have hzpos : 0 < z := lt_of_le_of_ne (Set.mem_Ici.mp hz) (Ne.symm hz0)
    have hθ' : θ = 0 ∨ θ = π / 2 := by
      rcases Set.mem_Icc.mp hθ with ⟨h1, h2⟩
      by_contra hc
      push_neg at hc
      exact h ⟨hzpos, lt_of_le_of_ne h1 (Ne.symm hc.1), lt_of_le_of_ne h2 hc.2⟩
    rcases hθ' with rfl | rfl
    · exact Wt_zero_theta_zero α z hα
    · exact Wt_zero_theta_pi α z hα

/-! ## The pointwise `L^∞`-bound of the factor of order `≤ 2` -/

/-- The square of the pointwise `L^∞`-bound of the factor of total order `≤ 2`:
`Cf/(γ-1)·|f|²_{ℋ⁴}`, exactly the right hand side of `PwBd.bound`. -/
private def PWBQ (α : ℝ) (f : ℝ → ℝ → ℝ) (Cf : ℝ) : ℝ := Cf / (gam α - 1) * HkSq α 4 f

/-- `PWBQ` is nonnegative for `α > 0` and `Cf ≥ 0`. -/
private theorem PWBQ_nonneg {α Cf : ℝ} (hα : 0 < α) (hC : 0 ≤ Cf) (f : ℝ → ℝ → ℝ) :
    0 ≤ PWBQ α f Cf := by
  rw [PWBQ]
  exact mul_nonneg (div_nonneg hC (by linarith [one_lt_gam hα])) (HkSq_nonneg α 4 f)

/-- The pointwise `L^∞`-bound of `PwBd`, in the `PWBQ` shape. -/
private theorem PWBQ_bound {α Cf : ℝ} {f : ℝ → ℝ → ℝ} (hb : PwBd α f Cf)
    {b a : ℕ} (hab : a + b ≤ 2) {z θ : ℝ} (hz : 0 < z) (hθ1 : 0 < θ) (hθ2 : θ < π / 2) :
    (mixed b a f z θ) ^ 2 ≤ PWBQ α f Cf :=
  hb.bound b a hab z hz θ hθ1 hθ2

/-! ## The combinatorial case analysis -/

/-- For the pairs `(a,b)` occurring in the Leibniz expansion of `mixed j i (f g)` (so that
`a ≤ i`, `b ≤ j`) with `1 ≤ i`, `i + j ≤ 4` and `(j,i) ≠ (3,1)`, at least one of the two
factors has total order `≤ 2` while the *other* one carries a `θ`-derivative of order
`≥ 1`.  This is what makes the paper's "all other terms can be treated as `D_θ^4(fg)`"
precise: the exceptional configurations are exactly `(j,i) = (3,1)` with `a = 0, b = 3`
or `a = 1, b = 0`. -/
private lemma msum_orders {i j a b : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ 4)
    (hne : ¬ (j = 3 ∧ i = 1)) (hai : a ≤ i) (hbj : b ≤ j) :
    (1 ≤ a ∧ (i - a) + (j - b) ≤ 2) ∨ (1 ≤ i - a ∧ a + b ≤ 2) := by
  by_cases hc : 1 ≤ a
  · by_cases hd : (i - a) + (j - b) ≤ 2
    · exact Or.inl ⟨hc, hd⟩
    · refine Or.inr ⟨?_, by omega⟩
      by_contra h
      push_neg at h
      omega
  · push_neg at hc
    exact Or.inr ⟨by omega, by omega⟩

/-! ## Cauchy–Schwarz on the Leibniz expansion -/

/-- Leibniz expansion of `D_z^j D_θ^i (f g)`, followed by Cauchy–Schwarz: the squared
weighted summand is bounded by `6400` times the sum over the expansion pairs of the
squared weighted pieces.  The constant is very generous: `25` for the cardinality of the
index set `(i+1)(j+1)` and `256 = 4^{i+j}` for the squared binomial coefficients.

The `RegQ` Leibniz rule `mixed_mul_eq_quad` is only available for `0 < θ < π/2`; at the
two lines `θ = 0`, `θ = π/2` both sides of the inequality vanish because the weight
`Wt α z θ` does, so the estimate holds for every `θ ∈ Iθ`. -/
private lemma expansion_cs (α : ℝ) (hα : 0 < α) (i j : ℕ) (hij : i + j ≤ 4)
    (f g : ℝ → ℝ → ℝ) (hf : SmoothQuad f) (hg : SmoothQuad g) :
    ∀ z ∈ Iz, ∀ θ ∈ Iθ,
      (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2
        ≤ 6400 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            (mixed b a f z θ * Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2 := by
  intro z hz θ hθ
  by_cases hθi : θ ∈ Set.Ioo 0 (π / 2)
  · set s : Finset (ℕ × ℕ) := Finset.range (i + 1) ×ˢ Finset.range (j + 1) with hs
    set X : ℕ × ℕ → ℝ := fun p => (i.choose p.1 : ℝ) * (j.choose p.2 : ℝ)
        * ((mixed p.2 p.1 f z θ * Wt α z θ) * mixed (j - p.2) (i - p.1) g z θ) with hX
    set Y : ℕ × ℕ → ℝ := fun p => (mixed p.2 p.1 f z θ * Wt α z θ) ^ 2
        * (mixed (j - p.2) (i - p.1) g z θ) ^ 2 with hY
    -- the exact Leibniz expansion, with the weight distributed
    have hexp : mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ = ∑ p ∈ s, X p := by
      have h1 : mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ
          = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              ((i.choose a : ℝ) * (j.choose b : ℝ))
                * ((mixed b a f z θ * Wt α z θ) * mixed (j - b) (i - a) g z θ) := by
        rw [mixed_mul_eq_quad j i f g hf hg z hz θ hθi]
        simp only [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun a ha => ?_)
        refine Finset.sum_congr rfl (fun b hb => ?_)
        ring
      rw [h1, hs, Finset.sum_product]
    -- the Cauchy–Schwarz step
    have hcard : ((s.card : ℕ) : ℝ) ≤ 25 := by
      have h25 : s.card ≤ 25 := by
        rw [hs, Finset.card_product, Finset.card_range, Finset.card_range]
        have hi5 : i + 1 ≤ 5 := by omega
        have hj5 : j + 1 ≤ 5 := by omega
        calc (i + 1) * (j + 1) ≤ 5 * 5 := Nat.mul_le_mul hi5 hj5
          _ = 25 := rfl
      exact_mod_cast h25
    have hcoef : ∀ p ∈ s, X p ^ 2 ≤ 256 * Y p := by
      intro p hp
      rw [hs, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
      have hc16 : (i.choose p.1 : ℝ) * (j.choose p.2 : ℝ) ≤ 16 := by
        have h1 : (i.choose p.1 : ℝ) ≤ 2 ^ i := by
          exact_mod_cast Nat.choose_le_two_pow i p.1
        have h2 : (j.choose p.2 : ℝ) ≤ 2 ^ j := by
          exact_mod_cast Nat.choose_le_two_pow j p.2
        calc (i.choose p.1 : ℝ) * (j.choose p.2 : ℝ)
            ≤ 2 ^ i * 2 ^ j := mul_le_mul h1 h2 (by positivity) (by positivity)
          _ = 2 ^ (i + j) := by rw [← pow_add]
          _ ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) (by omega)
          _ = 16 := by norm_num
      have hid : X p ^ 2 = ((i.choose p.1 : ℝ) * (j.choose p.2 : ℝ)) ^ 2 * Y p := by
        simp only [hX, hY]; ring
      have hYnn : 0 ≤ Y p := by simp only [hY]; positivity
      rw [hid]
      calc ((i.choose p.1 : ℝ) * (j.choose p.2 : ℝ)) ^ 2 * Y p
          ≤ 16 ^ 2 * Y p :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hc16 2) hYnn
        _ = 256 * Y p := by norm_num
    have hYsum : ∑ p ∈ s, Y p = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        (mixed b a f z θ * Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2 := by
      rw [hs, Finset.sum_product]
    have hYnn : 0 ≤ ∑ p ∈ s, Y p :=
      Finset.sum_nonneg (fun p _ => by simp only [hY]; positivity)
    have hX2nn : 0 ≤ ∑ p ∈ s, X p ^ 2 := Finset.sum_nonneg (fun p _ => sq_nonneg _)
    have hbound : (∑ p ∈ s, X p) ^ 2 ≤ 6400 * ∑ p ∈ s, Y p := by
      calc (∑ p ∈ s, X p) ^ 2 ≤ (s.card : ℝ) * ∑ p ∈ s, X p ^ 2 :=
            sq_sum_le_card_mul_sum_sq
        _ ≤ 25 * ∑ p ∈ s, X p ^ 2 := mul_le_mul_of_nonneg_right hcard hX2nn
        _ ≤ 25 * (256 * ∑ p ∈ s, Y p) :=
            mul_le_mul_of_nonneg_left
              (by
                calc ∑ p ∈ s, X p ^ 2 ≤ ∑ p ∈ s, 256 * Y p := Finset.sum_le_sum hcoef
                  _ = 256 * ∑ p ∈ s, Y p := by rw [Finset.mul_sum])
              (by norm_num)
        _ = 6400 * ∑ p ∈ s, Y p := by ring
    calc (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2
        = (∑ p ∈ s, X p) ^ 2 := by rw [hexp]
      _ ≤ 6400 * ∑ p ∈ s, Y p := hbound
      _ = 6400 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              (mixed b a f z θ * Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2 := by
          rw [hYsum]
  · have hW : Wt α z θ = 0 :=
      Wt_eq_zero_of_boundary α z θ hα hz hθ (fun hc => hθi hc.2)
    have hL : (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2 = 0 := by
      rw [hW]; ring
    have hR : 0 ≤ 6400 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        (mixed b a f z θ * Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2 := by
      refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun a _ => ?_)
      exact Finset.sum_nonneg fun b _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
    rw [hL]; exact hR

/-! ## The majorant attached to a pair `(a,b)` of the Leibniz expansion -/

/-- The majorant of a single pair `(a,b)` of the Leibniz expansion of `mixed j i (f g)`:
whichever of the two factors has total order `≤ 2` is pulled out into its pointwise
`L^∞`-bound `PWBQ`, and the other one keeps its weighted `L²`-norm.

The two branches are `(a,b)` with `1 ≤ a` and `(i-a) + (j-b) ≤ 2` (the `g`-factor is
pulled out, with constant `Cg`; the `f`-factor is a weighted mixed derivative with
`1 ≤ a`), resp. the complementary situation (`msum_orders` guarantees that at least one
branch applies for every pair occurring in the expansion, under the hypotheses of
`MsummandQ`). -/
private def MAJ (α : ℝ) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ) (j i a b : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => if 1 ≤ a ∧ (i - a) + (j - b) ≤ 2
    then PWBQ α g Cg * (mixed b a f z θ * Wt α z θ) ^ 2
    else PWBQ α f Cf * (mixed (j - b) (i - a) g z θ * Wt α z θ) ^ 2

/-- The majorant is nonnegative. -/
private lemma MAJ_nonneg {α Cf Cg : ℝ} (hα : 0 < α) (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (f g : ℝ → ℝ → ℝ) (j i a b : ℕ) (z θ : ℝ) :
    0 ≤ MAJ α f g Cf Cg j i a b z θ := by
  rw [MAJ]
  split
  · exact mul_nonneg (PWBQ_nonneg hα hCg g) (sq_nonneg _)
  · exact mul_nonneg (PWBQ_nonneg hα hCf f) (sq_nonneg _)

/-- The pointwise domination of a pair of the Leibniz expansion by its majorant. -/
private lemma MAJ_pw_le (α : ℝ) (hα : 0 < α) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ)
    (hCfb : PwBd α f Cf) (hCgb : PwBd α g Cg)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) (hne : ¬ (j = 3 ∧ i = 1))
    {a b : ℕ} (hai : a ≤ i) (hbj : b ≤ j) {z θ : ℝ} (hz : z ∈ Iz) (hθ : θ ∈ Iθ) :
    (mixed b a f z θ * Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2
      ≤ MAJ α f g Cf Cg j i a b z θ := by
  by_cases hgen : 0 < z ∧ 0 < θ ∧ θ < π / 2
  · obtain ⟨hzpos, hθ1, hθ2⟩ := hgen
    by_cases hc : 1 ≤ a ∧ (i - a) + (j - b) ≤ 2
    · have hB : (mixed (j - b) (i - a) g z θ) ^ 2 ≤ PWBQ α g Cg :=
        PWBQ_bound hCgb hc.2 hzpos hθ1 hθ2
      have hnn : 0 ≤ (mixed b a f z θ * Wt α z θ) ^ 2 := sq_nonneg _
      rw [MAJ, if_pos hc]
      calc (mixed b a f z θ * Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2
          = (mixed (j - b) (i - a) g z θ) ^ 2 * (mixed b a f z θ * Wt α z θ) ^ 2 := by ring
        _ ≤ PWBQ α g Cg * (mixed b a f z θ * Wt α z θ) ^ 2 :=
            mul_le_mul_of_nonneg_right hB hnn
    · have h2 : 1 ≤ i - a ∧ a + b ≤ 2 := by
        rcases msum_orders hi hij hne hai hbj with h | h
        · exact absurd h hc
        · exact h
      have hA : (mixed b a f z θ) ^ 2 ≤ PWBQ α f Cf :=
        PWBQ_bound hCfb h2.2 hzpos hθ1 hθ2
      rw [MAJ, if_neg hc]
      calc (mixed b a f z θ * Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2
          = (mixed b a f z θ) ^ 2 * (Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2 := by
            rw [mul_pow]
        _ ≤ PWBQ α f Cf * (Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hA (sq_nonneg _)) (sq_nonneg _)
        _ = PWBQ α f Cf * (mixed (j - b) (i - a) g z θ * Wt α z θ) ^ 2 := by
            rw [mul_pow]; ring
  · have hW : Wt α z θ = 0 :=
      Wt_eq_zero_of_boundary α z θ hα hz hθ (fun hc => hgen hc)
    have h0 : (mixed b a f z θ * Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2 = 0 := by
      rw [hW]; ring
    rw [h0]
    exact MAJ_nonneg hα hCfb.nonneg hCgb.nonneg f g j i a b z θ

/-! ## Integrability of the majorant -/

/-- A finite sum of functions integrable on a set is integrable on that set. -/
private theorem integrableOn_finsetSum {ι : Type*} {s : Set ℝ} {φ : ι → ℝ → ℝ} (t : Finset ι)
    (h : ∀ i ∈ t, IntegrableOn (φ i) s) : IntegrableOn (fun x => ∑ i ∈ t, φ i x) s := by
  classical
  induction t using Finset.induction with
  | empty =>
      simpa using (integrableOn_zero :
        IntegrableOn (fun _ : ℝ => (0 : ℝ)) s (μ := volume))
  | insert a t ha ih =>
      have hfun : (fun x => ∑ i ∈ insert a t, φ i x)
          = (fun x => φ a x) + (fun x => ∑ i ∈ t, φ i x) := by
        funext x; rw [Finset.sum_insert ha]; rfl
      rw [hfun]
      exact (h a (Finset.mem_insert_self a t)).add
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- The `θ`-slice of the majorant is integrable. -/
private lemma MAJ_integrableOn_theta (α : ℝ) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ) (j i a b : ℕ)
    (hfsq : SmoothQuad f) (hmemf : HkMem α 4 f) (hgsq : SmoothQuad g) (hmemg : HkMem α 4 g)
    (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hi : 1 ≤ i) (hij : i + j ≤ 4) (hne : ¬ (j = 3 ∧ i = 1)) (hai : a ≤ i) (hbj : b ≤ j)
    {z : ℝ} (hz : z ∈ Iz) :
    IntegrableOn (fun θ => MAJ α f g Cf Cg j i a b z θ) Iθ := by
  by_cases hc : 1 ≤ a ∧ (i - a) + (j - b) ≤ 2
  · have hab : a + b ≤ 4 := by omega
    have h1 : IntegrableOn (fun θ => (mixed b a f z θ * Wt α z θ) ^ 2) Iθ :=
      integrableOn_slice_mixed_Wt_sq α f hfsq hmemf b a hc.1 hab hz
    have h2 := h1.const_mul (PWBQ α g Cg)
    exact MeasureTheory.IntegrableOn.congr_fun h2
      (fun θ _ => by simp only [MAJ]; rw [if_pos hc]) measurableSet_Icc
  · have h2' : 1 ≤ i - a ∧ a + b ≤ 2 := by
      rcases msum_orders hi hij hne hai hbj with h | h
      · exact absurd h hc
      · exact h
    have hab : (i - a) + (j - b) ≤ 4 := by omega
    have h1 : IntegrableOn (fun θ => (mixed (j - b) (i - a) g z θ * Wt α z θ) ^ 2) Iθ :=
      integrableOn_slice_mixed_Wt_sq α g hgsq hmemg (j - b) (i - a) h2'.1 hab hz
    have h2 := h1.const_mul (PWBQ α f Cf)
    exact MeasureTheory.IntegrableOn.congr_fun h2
      (fun θ _ => by simp only [MAJ]; rw [if_neg hc]) measurableSet_Icc

/-- `L2Mem` for a weighted mixed derivative of order between `1` and `4`. -/
private theorem L2Mem_mixed_Wt_qd (α : ℝ) (u : ℝ → ℝ → ℝ) (hu : SmoothQuad u)
    (hmem : HkMem α 4 u) (b a : ℕ) (ha : 1 ≤ a) (hab : a + b ≤ 4) :
    L2Mem (fun z θ => mixed b a u z θ * Wt α z θ) := by
  constructor
  · intro z hz
    exact integrableOn_slice_mixed_Wt_sq α u hu hmem b a ha hab hz
  · exact (bt_prod_integrable_quad α u hu hmem b a ha hab).1.integral_prod_left

/-- Integrability in `z` of the angular integral of the majorant. -/
private lemma MAJ_integrableOn_z (α : ℝ) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ) (j i a b : ℕ)
    (hfsq : SmoothQuad f) (hmemf : HkMem α 4 f) (hgsq : SmoothQuad g) (hmemg : HkMem α 4 g)
    (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hi : 1 ≤ i) (hij : i + j ≤ 4) (hne : ¬ (j = 3 ∧ i = 1)) (hai : a ≤ i) (hbj : b ≤ j) :
    IntegrableOn (fun z => ∫ θ in Iθ, MAJ α f g Cf Cg j i a b z θ) Iz := by
  by_cases hc : 1 ≤ a ∧ (i - a) + (j - b) ≤ 2
  · have hab : a + b ≤ 4 := by omega
    have h1 : IntegrableOn (fun z => ∫ θ in Iθ, (mixed b a f z θ * Wt α z θ) ^ 2) Iz :=
      (L2Mem_mixed_Wt_qd α f hfsq hmemf b a hc.1 hab).2
    have h2 := h1.const_mul (PWBQ α g Cg)
    refine MeasureTheory.IntegrableOn.congr_fun h2 ?_ measurableSet_Ici
    intro z hz
    show PWBQ α g Cg * ∫ θ in Iθ, (mixed b a f z θ * Wt α z θ) ^ 2
        = ∫ θ in Iθ, MAJ α f g Cf Cg j i a b z θ
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    simp only [MAJ]
    rw [if_pos hc]
  · have h2' : 1 ≤ i - a ∧ a + b ≤ 2 := by
      rcases msum_orders hi hij hne hai hbj with h | h
      · exact absurd h hc
      · exact h
    have hab : (i - a) + (j - b) ≤ 4 := by omega
    have h1 : IntegrableOn
        (fun z => ∫ θ in Iθ, (mixed (j - b) (i - a) g z θ * Wt α z θ) ^ 2) Iz :=
      (L2Mem_mixed_Wt_qd α g hgsq hmemg (j - b) (i - a) h2'.1 hab).2
    have h2 := h1.const_mul (PWBQ α f Cf)
    refine MeasureTheory.IntegrableOn.congr_fun h2 ?_ measurableSet_Ici
    intro z hz
    show PWBQ α f Cf * ∫ θ in Iθ, (mixed (j - b) (i - a) g z θ * Wt α z θ) ^ 2
        = ∫ θ in Iθ, MAJ α f g Cf Cg j i a b z θ
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    simp only [MAJ]
    rw [if_neg hc]

/-! ## Strong measurability of the weighted summand -/

/-- The squared weighted mixed derivative of a `SmoothQuad` function is a.e. strongly
measurable on every angular slice, for every `z ∈ Iz` (at `z = 0` the function vanishes
identically). -/
private lemma aesm_slice_mixed_qd (α : ℝ) {u : ℝ → ℝ → ℝ} (hu : SmoothQuad u) (j i : ℕ)
    {z : ℝ} (hz : z ∈ Iz) :
    AEStronglyMeasurable (fun θ => (mixed j i u z θ * Wt α z θ) ^ 2) (volume.restrict Iθ) := by
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hpos
  · subst h0
    have hzero : (fun θ => (mixed j i u 0 θ * Wt α 0 θ) ^ 2) = fun _ => (0 : ℝ) := by
      funext θ; rw [Wt_zero_left]; ring
    rw [hzero]
    exact aestronglyMeasurable_const
  · exact aesm_slice_mixed_Wt_sq α u hu j i hpos

/-! ## The per-pair integral bound -/

/-- The integral of the majorant of a single pair of the Leibniz expansion. -/
private lemma MAJ_pair_integral_le (α : ℝ) (hα : 0 < α) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ)
    (hfsq : SmoothQuad f) (hmemf : HkMem α 4 f) (hgsq : SmoothQuad g) (hmemg : HkMem α 4 g)
    (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) (hne : ¬ (j = 3 ∧ i = 1))
    {a b : ℕ} (hai : a ≤ i) (hbj : b ≤ j) :
    (∫ z in Iz, ∫ θ in Iθ, MAJ α f g Cf Cg j i a b z θ)
      ≤ (Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by
  have hγ : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  by_cases hc : 1 ≤ a ∧ (i - a) + (j - b) ≤ 2
  · have hab : a + b ≤ 4 := by omega
    have hInt : (∫ z in Iz, ∫ θ in Iθ, MAJ α f g Cf Cg j i a b z θ)
        = PWBQ α g Cg * ∫ z in Iz, ∫ θ in Iθ, (mixed b a f z θ * Wt α z θ) ^ 2 := by
      simp only [MAJ, if_pos hc, MeasureTheory.integral_const_mul]
    rw [hInt]
    have hstep : (∫ z in Iz, ∫ θ in Iθ, (mixed b a f z θ * Wt α z θ) ^ 2) ≤ HkSq α 4 f :=
      L2Sq_mixed_le_HkSq α 4 f hmemf a b hc.1 hab
    have hCg' : Cg ≤ Cf + Cg := by linarith
    calc PWBQ α g Cg * ∫ z in Iz, ∫ θ in Iθ, (mixed b a f z θ * Wt α z θ) ^ 2
        ≤ PWBQ α g Cg * HkSq α 4 f :=
          mul_le_mul_of_nonneg_left hstep (PWBQ_nonneg hα hCg g)
      _ ≤ (Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by
          rw [PWBQ]
          calc Cg / (gam α - 1) * HkSq α 4 g * HkSq α 4 f
              = (Cg * (gam α - 1)⁻¹) * (HkSq α 4 g * HkSq α 4 f) := by ring
            _ ≤ ((Cf + Cg) * (gam α - 1)⁻¹) * (HkSq α 4 g * HkSq α 4 f) :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hCg' (inv_nonneg.mpr hγ.le))
                  (mul_nonneg (HkSq_nonneg α 4 g) (HkSq_nonneg α 4 f))
            _ = (Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by ring
  · have h2' : 1 ≤ i - a ∧ a + b ≤ 2 := by
      rcases msum_orders hi hij hne hai hbj with h | h
      · exact absurd h hc
      · exact h
    have hab : (i - a) + (j - b) ≤ 4 := by omega
    have hInt : (∫ z in Iz, ∫ θ in Iθ, MAJ α f g Cf Cg j i a b z θ)
        = PWBQ α f Cf * ∫ z in Iz, ∫ θ in Iθ,
            (mixed (j - b) (i - a) g z θ * Wt α z θ) ^ 2 := by
      simp only [MAJ, if_neg hc, MeasureTheory.integral_const_mul]
    rw [hInt]
    have hstep : (∫ z in Iz, ∫ θ in Iθ, (mixed (j - b) (i - a) g z θ * Wt α z θ) ^ 2)
        ≤ HkSq α 4 g :=
      L2Sq_mixed_le_HkSq α 4 g hmemg (i - a) (j - b) h2'.1 hab
    have hCf' : Cf ≤ Cf + Cg := by linarith
    calc PWBQ α f Cf * ∫ z in Iz, ∫ θ in Iθ, (mixed (j - b) (i - a) g z θ * Wt α z θ) ^ 2
        ≤ PWBQ α f Cf * HkSq α 4 g :=
          mul_le_mul_of_nonneg_left hstep (PWBQ_nonneg hα hCf f)
      _ ≤ (Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by
          rw [PWBQ]
          calc Cf / (gam α - 1) * HkSq α 4 f * HkSq α 4 g
              = (Cf * (gam α - 1)⁻¹) * (HkSq α 4 f * HkSq α 4 g) := by ring
            _ ≤ ((Cf + Cg) * (gam α - 1)⁻¹) * (HkSq α 4 f * HkSq α 4 g) :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hCf' (inv_nonneg.mpr hγ.le))
                  (mul_nonneg (HkSq_nonneg α 4 f) (HkSq_nonneg α 4 g))
            _ = (Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by ring

/-- **The "middle" mixed summands of the interior product rule `HProdQ`.**

For `f, g` in the interior class `Work.FTS.Nonlin.RegQ α 4` and pointwise `L^∞`-bound packages
`PwBd α f Cf`, `PwBd α g Cg`, every weighted mixed slot of the product with `1 ≤ i`,
`i + j ≤ 4`, except the exceptional pair `(j,i) = (3,1)` (which is `BadsummandQ`), satisfies
`L2Mem (mixed j i (f g) · Wt α)` and
`L2Sq (mixed j i (f g) · Wt α) ≤ C/(γ-1)·(Cf+Cg)·|f|²_{ℋ⁴}·|g|²_{ℋ⁴}`.

This is `Work.Spaces.HProductRule_Msummand` (proved) with `Spaces.SmoothNbhd` (analyticity on a
neighbourhood of the closed quadrant) replaced by `SmoothQuad`, `VanishTheta` dropped, the decay
hypotheses dropped, and the pointwise `L^∞`-bound of order `≤ 2` supplied abstractly by `PwBd`
(instead of `Work.Spaces.MixedSqPointwiseBound`).  Route: copy the proof of
`Submission/Work/Spaces/HProductRule_Msummand.lean`:
* `Work.FTS.H2.HQ.mixed_mul_eq_quad` replaces `Work.Spaces.mixed_mul_eq` — note that the
  `RegQ` version is *only* available for `0 < θ < π/2` (the `SmoothQuad` Leibniz is interior),
  so the pointwise step `expansion_cs`/`hpoint` must be stated with
  `∀ᵐ θ ∂(volume.restrict Iθ)` (use `ae_restrict_mem measurableSet_Ioo`) rather than for all
  `θ ∈ Iθ`; at `θ = 0, π/2` and at `z = 0` both sides of every pointwise inequality used here
  vanish because the weights `Wt α z θ = w z · sin(2θ)^{-γ/2}` do (in Lean `w 0 = 0` and
  `(sin 0)^c = 0` by totalised division/`Real.zero_rpow`), so this loses nothing;
* `Work.FTS.H2.HQ.integrableOn_slice_mixed_Wt_sq`, `Work.FTS.H2.HQ.aesm_mixed_Wt_sq_prod_quad`,
  `Work.FTS.H2.HQ.aesm_slice_mixed_Wt_sq`, `Work.FTS.H2.HQ.bt_prod_integrable_quad` (in
  `HQ/Glue.lean`) replace `Work.Spaces.mixed_sq_integrableOn`, `Work.Spaces.aesm_mixed_Wt_sq_prod`
  and `Work.Spaces.bt_prod_integrable`, and `Work.FTS.LocData.smoothQuad_mul` gives
  `SmoothQuad (f·g)`;
* `Work.Spaces.L2Sq_mixed_le_HkSq` and `Work.Spaces.sq_le_HkIntegrand_mixed` are pure and are
  reused unchanged;
* the arithmetic is as in `HProductRule_Msummand`, with `PwBd.bound` (and `PwBd.nonneg`)
  supplying the two `PWB` values, so the final constant is again some absolute `C`. -/
theorem MsummandQ : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : Work.FTS.Galerkin.Fn)
    (Cf Cg : ℝ), 0 < α → α ≤ 1 → Work.FTS.Nonlin.RegQ α 4 f → Work.FTS.Nonlin.RegQ α 4 g →
    Work.FTS.H2.HQ.PwBd α f Cf → Work.FTS.H2.HQ.PwBd α g Cg →
    ∀ (j i : ℕ), 1 ≤ i → i + j ≤ 4 → ¬ (j = 3 ∧ i = 1) →
      Work.Spaces.L2Mem (fun z θ => Work.Spaces.mixed j i (fun z θ => f z θ * g z θ) z θ
          * Work.Spaces.Wt α z θ)
      ∧ Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed j i (fun z θ => f z θ * g z θ) z θ
          * Work.Spaces.Wt α z θ)
        ≤ C / (Work.Spaces.gam α - 1) * (Cf + Cg) * Work.Spaces.HkSq α 4 f
            * Work.Spaces.HkSq α 4 g := by
  refine ⟨10 ^ 12, by norm_num, ?_⟩
  intro α f g Cf Cg hα hα1 hregf hregg hCfb hCgb j i hi hij hne
  obtain ⟨hfsq, hmemf, _⟩ := hregf
  obtain ⟨hgsq, hmemg, _⟩ := hregg
  have hγ : (0 : ℝ) < gam α - 1 := by rw [gam_sub_one]; linarith
  have hCf : 0 ≤ Cf := hCfb.nonneg
  have hCg : 0 ≤ Cg := hCgb.nonneg
  have hsmFG : SmoothQuad (fun z θ => f z θ * g z θ) :=
    Work.FTS.LocData.smoothQuad_mul hfsq hgsq
  -- the pointwise bound
  have hpoint : ∀ z ∈ Iz, ∀ θ ∈ Iθ,
      (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2
        ≤ 6400 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            MAJ α f g Cf Cg j i a b z θ := by
    intro z hz θ hθ
    have hcs := expansion_cs α hα i j hij f g hfsq hgsq z hz θ hθ
    have hterm : ∀ a ∈ Finset.range (i + 1), ∀ b ∈ Finset.range (j + 1),
        (mixed b a f z θ * Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2
          ≤ MAJ α f g Cf Cg j i a b z θ := by
      intro a ha b hb
      rw [Finset.mem_range] at ha hb
      exact MAJ_pw_le α hα f g Cf Cg hCfb hCgb j i hi hij hne
        (by omega) (by omega) hz hθ
    calc (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2
        ≤ 6400 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            (mixed b a f z θ * Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2 := hcs
      _ ≤ 6400 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            MAJ α f g Cf Cg j i a b z θ := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact Finset.sum_le_sum fun a ha =>
            Finset.sum_le_sum fun b hb => hterm a ha b hb
  -- integrability of the majorant sums
  have hsumθ_int : ∀ z ∈ Iz, IntegrableOn (fun θ => ∑ a ∈ Finset.range (i + 1),
      ∑ b ∈ Finset.range (j + 1), MAJ α f g Cf Cg j i a b z θ) Iθ := by
    intro z hz
    exact integrableOn_finsetSum _ fun a ha => integrableOn_finsetSum _ fun b hb =>
      MAJ_integrableOn_theta α f g Cf Cg j i a b hfsq hmemf hgsq hmemg hCf hCg hi hij hne
        (by have := Finset.mem_range.mp ha; omega)
        (by have := Finset.mem_range.mp hb; omega) hz
  have hsumz_int : IntegrableOn (fun z => ∑ a ∈ Finset.range (i + 1),
      ∑ b ∈ Finset.range (j + 1), ∫ θ in Iθ, MAJ α f g Cf Cg j i a b z θ) Iz := by
    exact integrableOn_finsetSum _ fun a ha => integrableOn_finsetSum _ fun b hb =>
      MAJ_integrableOn_z α f g Cf Cg j i a b hfsq hmemf hgsq hmemg hCf hCg hi hij hne
        (by have := Finset.mem_range.mp ha; omega)
        (by have := Finset.mem_range.mp hb; omega)
  -- integrability of the angular slices of the target
  have hIntTheta : ∀ z ∈ Iz, IntegrableOn
      (fun θ => (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2) Iθ := by
    intro z hz
    refine Integrable.mono' ((hsumθ_int z hz).const_mul 6400)
      (aesm_slice_mixed_qd α hsmFG j i hz) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hpoint z hz θ hθ
  -- the (pointwise in `z`) domination of the angular integral
  have hdom : ∀ z ∈ Iz, (∫ θ in Iθ,
        (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2)
      ≤ 6400 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          ∫ θ in Iθ, MAJ α f g Cf Cg j i a b z θ := by
    intro z hz
    have h2 : IntegrableOn (fun θ => 6400 * ∑ a ∈ Finset.range (i + 1),
        ∑ b ∈ Finset.range (j + 1), MAJ α f g Cf Cg j i a b z θ) Iθ :=
      (hsumθ_int z hz).const_mul 6400
    calc ∫ θ in Iθ, (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2
        ≤ ∫ θ in Iθ, 6400 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            MAJ α f g Cf Cg j i a b z θ :=
          integral_mono_ae (hIntTheta z hz) h2
            (ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => hpoint z hz θ hθ)
      _ = 6400 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            ∫ θ in Iθ, MAJ α f g Cf Cg j i a b z θ := by
          rw [MeasureTheory.integral_const_mul]
          congr 1
          rw [MeasureTheory.integral_finsetSum _ (fun a ha =>
            integrableOn_finsetSum _ fun b hb => MAJ_integrableOn_theta α f g Cf Cg j i a b
              hfsq hmemf hgsq hmemg hCf hCg hi hij hne
              (by have := Finset.mem_range.mp ha; omega)
              (by have := Finset.mem_range.mp hb; omega) hz)]
          refine Finset.sum_congr rfl fun a ha => ?_
          rw [MeasureTheory.integral_finsetSum _ fun b hb =>
            MAJ_integrableOn_theta α f g Cf Cg j i a b hfsq hmemf hgsq hmemg hCf hCg
              hi hij hne
              (by have := Finset.mem_range.mp ha; omega)
              (by have := Finset.mem_range.mp hb; omega) hz]
  -- integrability of the outer integral of the target
  have hOuterInt : IntegrableOn
      (fun z => ∫ θ in Iθ, (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2) Iz := by
    have hmaj : IntegrableOn (fun z => 6400 * ∑ a ∈ Finset.range (i + 1),
        ∑ b ∈ Finset.range (j + 1), ∫ θ in Iθ, MAJ α f g Cf Cg j i a b z θ) Iz :=
      hsumz_int.const_mul 6400
    refine Integrable.mono' hmaj ?_ ?_
    · have hAESM := aesm_mixed_Wt_sq_prod_quad α (fun z θ => f z θ * g z θ) hsmFG j i
      simpa only [Function.uncurry] using hAESM.integral_prod_right'
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
      rw [Real.norm_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
      exact hdom z hz
  refine ⟨⟨hIntTheta, hOuterInt⟩, ?_⟩
  rw [L2Sq]
  -- the per-pair integral bound
  have hXnn : (0 : ℝ) ≤ (Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g :=
    mul_nonneg (mul_nonneg (div_nonneg (by linarith) hγ.le) (HkSq_nonneg α 4 f))
      (HkSq_nonneg α 4 g)
  have hTerg : ∀ a ∈ Finset.range (i + 1), ∀ b ∈ Finset.range (j + 1),
      (∫ z in Iz, ∫ θ in Iθ, MAJ α f g Cf Cg j i a b z θ)
        ≤ (Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by
    intro a ha b hb
    exact MAJ_pair_integral_le α hα f g Cf Cg hfsq hmemf hgsq hmemg hCf hCg j i hi hij hne
      (by have := Finset.mem_range.mp ha; omega) (by have := Finset.mem_range.mp hb; omega)
  calc ∫ z in Iz, ∫ θ in Iθ, (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2
      ≤ ∫ z in Iz, 6400 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          ∫ θ in Iθ, MAJ α f g Cf Cg j i a b z θ :=
        setIntegral_mono_of_nonneg
          (fun z hz => integral_nonneg fun θ => sq_nonneg _)
          (fun z hz => hdom z hz) (hsumz_int.const_mul 6400)
    _ = 6400 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          ∫ z in Iz, ∫ θ in Iθ, MAJ α f g Cf Cg j i a b z θ := by
        rw [MeasureTheory.integral_const_mul]
        congr 1
        rw [MeasureTheory.integral_finsetSum _ (fun a ha => integrableOn_finsetSum _
          fun b hb => MAJ_integrableOn_z α f g Cf Cg j i a b hfsq hmemf hgsq hmemg hCf hCg
            hi hij hne
            (by have := Finset.mem_range.mp ha; omega)
            (by have := Finset.mem_range.mp hb; omega))]
        refine Finset.sum_congr rfl fun a ha => ?_
        rw [MeasureTheory.integral_finsetSum _ fun b hb =>
          MAJ_integrableOn_z α f g Cf Cg j i a b hfsq hmemf hgsq hmemg hCf hCg hi hij hne
            (by have := Finset.mem_range.mp ha; omega)
            (by have := Finset.mem_range.mp hb; omega)]
    _ ≤ 6400 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          ((Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hTerg a ha b hb
    _ = 6400 * ((((i + 1) * (j + 1) : ℕ) : ℝ)
          * ((Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g)) := by
        rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul,
          Finset.card_range, Finset.card_range]
        push_cast
        ring
    _ ≤ 6400 * (25 * ((Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g)) := by
        have hcard25 : ((((i + 1) * (j + 1) : ℕ)) : ℝ) ≤ 25 := by
          have h5 : (i + 1) * (j + 1) ≤ 25 := by
            have hi5 : i + 1 ≤ 5 := by omega
            have hj5 : j + 1 ≤ 5 := by omega
            calc (i + 1) * (j + 1) ≤ 5 * 5 := Nat.mul_le_mul hi5 hj5
              _ = 25 := rfl
          exact_mod_cast h5
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard25 hXnn)
          (by norm_num)
    _ = (160000 : ℝ) * ((Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g) := by ring
    _ ≤ 10 ^ 12 * ((Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g) :=
        mul_le_mul_of_nonneg_right (by norm_num) hXnn
    _ = 10 ^ 12 / (gam α - 1) * (Cf + Cg) * HkSq α 4 f * HkSq α 4 g := by ring

end Work.FTS.H2.HQ
end
end
-- ===== merged: Submission.Work.FTS.H2.WProdQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2

open scoped Real Topology
open Set MeasureTheory Filter


end Work.FTS.H2
end
-- ===== merged: Submission.Work.FTS.OpenPkg.Qang_sq_leQ_gen_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.OpenPkg

set_option autoImplicit false

/-- **Cauchy–Schwarz in `θ` for the angular moment, in the open-quadrant class.**

For `SmoothOpen g`, `HkMem α k g`, `j ≤ k` and `z > 0`,

  `(Qang g j z)² ≤ (∫_θ Ktheta θ²)·(∫_θ (D_z^j g z θ)²)`,

where `Qang g j z = ∫_θ Ktheta θ · D_z^j g z θ dθ`.

This is `Work.FTS.CoercivityFix.Transfer.E1Norm.Qang_sq_leQ_gen`
(`Submission/Work/FTS/CoercivityFix/Transfer/E1Norm/Qang_sq_w_sq_le_HkSq.lean`, in the
*interior* class `Work.FTS.LocData.SmoothQuad g`, i.e. `C^∞` on `z > -1`) with the hypothesis
weakened to the open-quadrant class `Work.FTS.EllipticEst.SmoothOpen g` (`C^∞` on the open
quadrant `z > 0`, `0 < θ < π/2`).  That sibling proof uses the smoothness hypothesis *only*
through the continuity of the angular slice `θ ↦ D_z^j g z θ` on `(0,π/2)`, which it obtains as
`((hsm.DzIter j).curry_θ hzIoi).continuousOn` with `hzIoi : z ∈ Set.Ioi (-1)`;
`Work.FTS.EllipticEst.SmoothOpen.DzIter` and `Work.FTS.EllipticEst.SmoothOpen.curry_θ` supply
exactly the same two facts for the weaker class (`curry_θ` at `z ∈ Set.Ioi 0`).  Everything else
is unchanged: `Iθ = Icc 0 (π/2)` is replaced by the full-measure open interval
`Ioo 0 (π/2)` (`MeasureTheory.Ioo_ae_eq_Icc`), the `θ`-slice of `D_z^j g` is dominated by the
`ℋ^k`-integrand via `Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq` (already general in the level
`k`, and this is the only use of `hmem`), `Ktheta²` is integrable by continuity on the compact
closure, and the inequality is the standard Cauchy–Schwarz for the Bochner integral
(`MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg` with `p = q = 2`).

Route: copy the proof of `E1Norm.Qang_sq_leQ_gen` verbatim and change the single use of the
smoothness hypothesis as described.  Note the level `k` must stay general: the consumer needs
`HkMem α n g` with `i ≤ n` for arbitrary `n`, and `sq_DzIter_le_HkIntegrand_div_w_sq` is what
makes that possible. -/
theorem Qang_sq_leQ_gen_open (α : ℝ) (g : ℝ → ℝ → ℝ) (hO : Work.FTS.EllipticEst.SmoothOpen g)
    {k : ℕ} (hmem : Work.Spaces.HkMem α k g) (j : ℕ) (hj : j ≤ k) {z : ℝ} (hz : 0 < z) :
    (Work.Elliptic.Qang g j z) ^ 2 ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
      * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2) := by
  -- `Iθ = Icc 0 (π/2)` and the open interval `Ioo 0 (π/2)` differ by the two endpoints, a null
  -- set: every integral below can be taken over the open interval, where the `θ`-slice of
  -- `D_z^j g` is continuous (`SmoothOpen` only gives smoothness on the *open* quadrant).
  have hIoo : (Set.Icc (0 : ℝ) (π / 2)) =ᵐ[volume] (Set.Ioo (0 : ℝ) (π / 2)) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm
  have hQeq : Work.Elliptic.Qang g j z
      = ∫ θ in Set.Ioo (0 : ℝ) (π / 2),
          Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ := by
    rw [Work.Elliptic.Qang]
    exact MeasureTheory.setIntegral_congr_set hIoo
  have hKeq : (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
      = ∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2 :=
    MeasureTheory.setIntegral_congr_set hIoo
  have hAeq : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2)
      = ∫ θ in Set.Ioo (0 : ℝ) (π / 2), (Work.Spaces.DzIter j g z θ) ^ 2 :=
    MeasureTheory.setIntegral_congr_set hIoo
  -- the `θ`-slice of `D_z^j g` at `z > 0` is continuous on `(0,π/2)`
  have hAcont : ContinuousOn (fun θ => Work.Spaces.DzIter j g z θ)
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    ((hO.DzIter j).curry_θ hz).continuousOn
  -- `Ktheta` is continuous everywhere (hence on `Iθ` and on `Ioo 0 (π/2)`)
  have hKcont : Continuous (fun θ => Work.Elliptic.Ktheta θ) := by
    unfold Work.Elliptic.Ktheta
    fun_prop
  -- integrability of `Ktheta²` on the open interval (continuity on the compact closure)
  have hK2int : IntegrableOn (fun θ => Work.Elliptic.Ktheta θ ^ 2)
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    ((hKcont.pow 2).continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Set.Ioo_subset_Icc_self
  -- integrability of `HkIntegrand α k g z ·`, transported from `hmem` to the open interval
  have hHkint : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k g z θ)
      (Set.Ioo (0 : ℝ) (π / 2)) := by
    change Integrable (fun θ => Work.Spaces.HkIntegrand α k g z θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2)))
    rw [← MeasureTheory.Measure.restrict_congr_set hIoo]
    simpa only [Work.Spaces.Iθ, IntegrableOn] using hmem.1 z (le_of_lt hz)
  -- a.e. strong measurability of the `θ`-slice
  have hAesm : AEStronglyMeasurable (fun θ => |Work.Spaces.DzIter j g z θ|)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
    simpa only [Real.norm_eq_abs] using (hAcont.aestronglyMeasurable measurableSet_Ioo).norm
  -- integrability of `(D_z^j g z ·)²`: dominated by the `ℋ^k`-integrand on the open interval
  have hA2int : IntegrableOn (fun θ => |Work.Spaces.DzIter j g z θ| ^ 2)
      (Set.Ioo (0 : ℝ) (π / 2)) := by
    refine hHkint.mono' (hAesm.pow 2) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_abs]
    -- the pure `D_z`-slot is dominated by the whole `ℋ^k`-integrand (the radial weight
    -- `w` is `≥ 1` on `(0,∞)`)
    have h1 := Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq α k g j hj hz hθ
    exact le_trans h1 (div_le_self (Work.Spaces.HkIntegrand_nonneg α k g z θ)
      (one_le_pow₀ (Work.Elliptic.one_le_w hz)))
  have hKesm : AEStronglyMeasurable (fun θ => |Work.Elliptic.Ktheta θ|)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
    simpa only [Real.norm_eq_abs] using hKcont.aestronglyMeasurable.norm
  have hKabs : IntegrableOn (fun θ => |Work.Elliptic.Ktheta θ| ^ 2)
      (Set.Ioo (0 : ℝ) (π / 2)) := by
    simpa only [sq_abs] using hK2int
  -- `L²`-membership of the two factors (`p = q = 2`)
  have hKmem : MemLp (fun θ => |Work.Elliptic.Ktheta θ|) (ENNReal.ofReal 2)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    exact (MeasureTheory.memLp_two_iff_integrable_sq hKesm).mpr hKabs
  have hAmem : MemLp (fun θ => |Work.Spaces.DzIter j g z θ|) (ENNReal.ofReal 2)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    exact (MeasureTheory.memLp_two_iff_integrable_sq hAesm).mpr hA2int
  -- Cauchy–Schwarz for the Bochner integral (`p = q = 2`, both factors nonnegative)
  have hcs := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict (Set.Ioo (0 : ℝ) (π / 2)))
    (p := 2) (q := 2) (f := fun θ => |Work.Elliptic.Ktheta θ|)
    (g := fun θ => |Work.Spaces.DzIter j g z θ|)
    (by norm_num [Real.holderConjugate_iff])
    (Filter.Eventually.of_forall fun θ => abs_nonneg _)
    (Filter.Eventually.of_forall fun θ => abs_nonneg _) hKmem hAmem
  have hnQ : |∫ θ in Set.Ioo (0 : ℝ) (π / 2),
        Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ|
      ≤ ∫ θ in Set.Ioo (0 : ℝ) (π / 2),
          |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter j g z θ| := by
    have h := MeasureTheory.norm_integral_le_integral_norm
      (μ := volume.restrict (Set.Ioo (0 : ℝ) (π / 2)))
      (fun θ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ)
    simpa only [Real.norm_eq_abs, abs_mul] using h
  have hKIsq : (∫ θ in Set.Ioo (0 : ℝ) (π / 2), |Work.Elliptic.Ktheta θ| ^ (2 : ℝ))
      = ∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2 :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by
      simp only [Real.rpow_two, sq_abs])
  have hAIsq : (∫ θ in Set.Ioo (0 : ℝ) (π / 2), |Work.Spaces.DzIter j g z θ| ^ (2 : ℝ))
      = ∫ θ in Set.Ioo (0 : ℝ) (π / 2), (Work.Spaces.DzIter j g z θ) ^ 2 :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by
      simp only [Real.rpow_two, sq_abs])
  have hK0 : 0 ≤ ∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2 :=
    MeasureTheory.integral_nonneg (fun θ => sq_nonneg _)
  have hA0 : 0 ≤ ∫ θ in Set.Ioo (0 : ℝ) (π / 2), (Work.Spaces.DzIter j g z θ) ^ 2 :=
    MeasureTheory.integral_nonneg (fun θ => sq_nonneg _)
  have hmain : (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
        Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ) ^ 2
      ≤ (∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2)
        * (∫ θ in Set.Ioo (0 : ℝ) (π / 2), (Work.Spaces.DzIter j g z θ) ^ 2) := by
    calc (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
          Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ) ^ 2
        = |∫ θ in Set.Ioo (0 : ℝ) (π / 2),
            Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ| ^ 2 := by rw [sq_abs]
      _ ≤ (Real.sqrt (∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2)
            * Real.sqrt (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                (Work.Spaces.DzIter j g z θ) ^ 2)) ^ 2 := by
          apply pow_le_pow_left₀ (abs_nonneg _)
          calc |∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ|
              ≤ ∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                  |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter j g z θ| := hnQ
            _ ≤ (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                    |Work.Elliptic.Ktheta θ| ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
                * (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                    |Work.Spaces.DzIter j g z θ| ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hcs
            _ = Real.sqrt (∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2)
                * Real.sqrt (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                    (Work.Spaces.DzIter j g z θ) ^ 2) := by
                rw [hKIsq, hAIsq, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
      _ = (∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2)
          * (∫ θ in Set.Ioo (0 : ℝ) (π / 2), (Work.Spaces.DzIter j g z θ) ^ 2) := by
          rw [mul_pow, Real.sq_sqrt hK0, Real.sq_sqrt hA0]
  rw [hQeq, hKeq, hAeq]
  exact hmain

end Work.FTS.OpenPkg
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.QangSq6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Null-set bookkeeping (the two ends of `Iz`, the two angular endpoints) -/

private theorem Iz_ae_eq_Ioi : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
  (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm

private theorem Iθ_ae_eq_Ioo : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
  (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm

/-- `w²` is continuous on `(0,∞)`. -/
private theorem continuousOn_w_sq :
    ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) := by
  have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      = fun z : ℝ => (((1 + z) ^ 2 / z ^ 2) ^ 2) := by
    funext z; rw [Work.Spaces.w]
  rw [hfun]
  exact (ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
    (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))).pow 2

/-! ## The pointwise slot domination at an arbitrary order `k` -/

/-- **A single pure `D_z`-slot of the `ℋ^k`-integrand dominates the square of the iterate, on
the open quadrant.**  On `z > 0` and `0 < θ < π/2` one has `w(z) ≥ 1` and
`sin(2θ)^{-η} ≥ 1`, so the weighted slot `(D_z^j g · w/sin(2θ)^{η/2})²` of the integrand
dominates the unweighted square: `(D_z^j g)² ≤ HkIntegrand α k g` for `j ≤ k`.

This is `Work.Elliptic.sq_DzIter_le_HkIntegrand_Qd` (the case `k = 4`) with `4 ↦ k`. -/
private theorem sq_DzIter_le_HkIntegrand_k (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) {j : ℕ}
    (hj : j ≤ k) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    (Work.Spaces.DzIter j g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k g z θ := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hw := Work.Elliptic.one_le_w hz
  have hsinp := Work.Elliptic.one_le_sin_two_rpow_neg_eta hθ0 hθ1
  have hw2 : (1 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := by nlinarith
  have hstep : (Work.Spaces.DzIter j g z θ) ^ 2
      ≤ (Work.Spaces.DzIter j g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    calc (Work.Spaces.DzIter j g z θ) ^ 2
        = (Work.Spaces.DzIter j g z θ) ^ 2 * 1 * 1 := by ring
      _ ≤ (Work.Spaces.DzIter j g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hw2 (sq_nonneg _)) hsinp ?_ (by positivity)
          positivity
  have heq : (Work.Spaces.DzIter j g z θ * (Work.Spaces.w z
        / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.DzIter j g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    have hs : 0 ≤ Real.sin (2 * θ) := hsin.le
    have hsq : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
        = Real.sin (2 * θ) ^ (Work.Spaces.eta) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
      norm_num
    rw [mul_pow, div_pow, hsq, div_eq_mul_inv, ← Real.rpow_neg hs (Work.Spaces.eta)]
    ring
  rw [← heq] at hstep
  exact le_trans hstep (Work.Spaces.sq_le_HkIntegrand_z α k g z θ j hj)

/-! ## The weighted slot, with the full weight `w²` -/

/-- On the open quadrant, `(D_z^i g)²·w²` is dominated by the `ℋ^k`-integrand (`i ≤ k`).
Immediate from `Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq` (which gives
`(D_z^i g)² ≤ HkIntegrand/w²`) after multiplying by `w² > 0`. -/
private theorem DzIter_sq_w_sq_le_HkIntegrand_k (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) {i : ℕ}
    (hi : i ≤ k) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Work.Spaces.DzIter i g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ Work.Spaces.HkIntegrand α k g z θ := by
  have h1 := Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq α k g i hi hz hθ
  have hw : 0 < (Work.Spaces.w z) ^ 2 := pow_pos (Work.FTS.H2.w_pos hz) 2
  rw [le_div_iff₀ hw] at h1
  exact h1

/-! ## Cauchy–Schwarz in `θ` at an arbitrary order `k` -/

/-- **Cauchy–Schwarz in `θ` for the angular moment, at an arbitrary order `k`.**  For a datum
which is `C^∞` on the open quadrant and lies in `ℋ^k`, and for `j ≤ k` and `z > 0`,

  `(Qang g j z)² ≤ (∫_θ Kθ(θ)² dθ)·∫_θ (D_z^j g z θ)² dθ`,

with the `α`-independent constant `∫_θ Kθ²`.

This is `Work.FTS.H2.Qang_sq_leQ` / `Work.FTS.OpenPkg.QangOpen.Qang_sq_leQ_open` with the fixed
order `4` replaced by `k`: the `θ`-integrals are taken over the open interval `(0,π/2)` (the
endpoints are null), where both factors are continuous and square-integrable, and the standard
`L²`-Cauchy–Schwarz (`MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`) applies. -/
private theorem Qang_sq_le_k (α : ℝ) (g : ℝ → ℝ → ℝ)
    (hO : Work.FTS.EllipticEst.SmoothOpen g) {k : ℕ} (hmem : Work.Spaces.HkMem α k g)
    (j : ℕ) (hj : j ≤ k) {z : ℝ} (hz : 0 < z) :
    (Work.Elliptic.Qang g j z) ^ 2 ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
      * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2) := by
  have hIoo : (Set.Icc (0 : ℝ) (π / 2)) =ᵐ[volume] (Set.Ioo (0 : ℝ) (π / 2)) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm
  have hQeq : Work.Elliptic.Qang g j z
      = ∫ θ in Set.Ioo (0 : ℝ) (π / 2),
          Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ := by
    rw [Work.Elliptic.Qang]
    exact MeasureTheory.setIntegral_congr_set hIoo
  have hKeq : (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
      = ∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2 :=
    MeasureTheory.setIntegral_congr_set hIoo
  have hAeq : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2)
      = ∫ θ in Set.Ioo (0 : ℝ) (π / 2), (Work.Spaces.DzIter j g z θ) ^ 2 :=
    MeasureTheory.setIntegral_congr_set hIoo
  -- the `θ`-slice of `D_z^j g` at `z > 0` is continuous on `(0,π/2)`
  have hAcont : ContinuousOn (fun θ => Work.Spaces.DzIter j g z θ)
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    ((hO.DzIter j).curry_θ hz).continuousOn
  have hKcont : Continuous (fun θ => Work.Elliptic.Ktheta θ) := by
    unfold Work.Elliptic.Ktheta
    fun_prop
  have hK2int : IntegrableOn (fun θ => Work.Elliptic.Ktheta θ ^ 2)
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    ((hKcont.pow 2).continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Set.Ioo_subset_Icc_self
  -- integrability of `HkIntegrand α k g z ·`, transported from `hmem` to the open interval
  have hHkint : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k g z θ)
      (Set.Ioo (0 : ℝ) (π / 2)) := by
    change Integrable (fun θ => Work.Spaces.HkIntegrand α k g z θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2)))
    rw [← MeasureTheory.Measure.restrict_congr_set hIoo]
    simpa only [Work.Spaces.Iθ, IntegrableOn] using hmem.1 z (le_of_lt hz)
  have hAesm : AEStronglyMeasurable (fun θ => |Work.Spaces.DzIter j g z θ|)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
    simpa only [Real.norm_eq_abs] using (hAcont.aestronglyMeasurable measurableSet_Ioo).norm
  have hA2int : IntegrableOn (fun θ => |Work.Spaces.DzIter j g z θ| ^ 2)
      (Set.Ioo (0 : ℝ) (π / 2)) := by
    refine hHkint.mono' (hAesm.pow 2) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_abs]
    exact sq_DzIter_le_HkIntegrand_k α k g hj hz hθ.1 hθ.2
  have hKesm : AEStronglyMeasurable (fun θ => |Work.Elliptic.Ktheta θ|)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
    simpa only [Real.norm_eq_abs] using hKcont.aestronglyMeasurable.norm
  have hKabs : IntegrableOn (fun θ => |Work.Elliptic.Ktheta θ| ^ 2)
      (Set.Ioo (0 : ℝ) (π / 2)) := by
    simpa only [sq_abs] using hK2int
  have hKmem : MemLp (fun θ => |Work.Elliptic.Ktheta θ|) (ENNReal.ofReal 2)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    exact (MeasureTheory.memLp_two_iff_integrable_sq hKesm).mpr hKabs
  have hAmem : MemLp (fun θ => |Work.Spaces.DzIter j g z θ|) (ENNReal.ofReal 2)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    exact (MeasureTheory.memLp_two_iff_integrable_sq hAesm).mpr hA2int
  have hcs := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict (Set.Ioo (0 : ℝ) (π / 2)))
    (p := 2) (q := 2) (f := fun θ => |Work.Elliptic.Ktheta θ|)
    (g := fun θ => |Work.Spaces.DzIter j g z θ|)
    (by norm_num [Real.holderConjugate_iff])
    (Filter.Eventually.of_forall fun θ => abs_nonneg _)
    (Filter.Eventually.of_forall fun θ => abs_nonneg _) hKmem hAmem
  have hnQ : |∫ θ in Set.Ioo (0 : ℝ) (π / 2),
        Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ|
      ≤ ∫ θ in Set.Ioo (0 : ℝ) (π / 2),
          |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter j g z θ| := by
    have h := MeasureTheory.norm_integral_le_integral_norm
      (μ := volume.restrict (Set.Ioo (0 : ℝ) (π / 2)))
      (fun θ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ)
    simpa only [Real.norm_eq_abs, abs_mul] using h
  have hKIsq : (∫ θ in Set.Ioo (0 : ℝ) (π / 2), |Work.Elliptic.Ktheta θ| ^ (2 : ℝ))
      = ∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2 :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by
      simp only [Real.rpow_two, sq_abs])
  have hAIsq : (∫ θ in Set.Ioo (0 : ℝ) (π / 2), |Work.Spaces.DzIter j g z θ| ^ (2 : ℝ))
      = ∫ θ in Set.Ioo (0 : ℝ) (π / 2), (Work.Spaces.DzIter j g z θ) ^ 2 :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by
      simp only [Real.rpow_two, sq_abs])
  have hK0 : 0 ≤ ∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2 :=
    MeasureTheory.integral_nonneg (fun θ => sq_nonneg _)
  have hA0 : 0 ≤ ∫ θ in Set.Ioo (0 : ℝ) (π / 2), (Work.Spaces.DzIter j g z θ) ^ 2 :=
    MeasureTheory.integral_nonneg (fun θ => sq_nonneg _)
  have hmain : (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
        Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ) ^ 2
      ≤ (∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2)
        * (∫ θ in Set.Ioo (0 : ℝ) (π / 2), (Work.Spaces.DzIter j g z θ) ^ 2) := by
    calc (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
          Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ) ^ 2
        = |∫ θ in Set.Ioo (0 : ℝ) (π / 2),
            Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ| ^ 2 := by rw [sq_abs]
      _ ≤ (Real.sqrt (∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2)
            * Real.sqrt (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                (Work.Spaces.DzIter j g z θ) ^ 2)) ^ 2 := by
          apply pow_le_pow_left₀ (abs_nonneg _)
          calc |∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ|
              ≤ ∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                  |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter j g z θ| := hnQ
            _ ≤ (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                    |Work.Elliptic.Ktheta θ| ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
                * (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                    |Work.Spaces.DzIter j g z θ| ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hcs
            _ = Real.sqrt (∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2)
                * Real.sqrt (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                    (Work.Spaces.DzIter j g z θ) ^ 2) := by
                rw [hKIsq, hAIsq, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
      _ = (∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2)
          * (∫ θ in Set.Ioo (0 : ℝ) (π / 2), (Work.Spaces.DzIter j g z θ) ^ 2) := by
          rw [mul_pow, Real.sq_sqrt hK0, Real.sq_sqrt hA0]
  rw [hQeq, hKeq, hAeq]
  exact hmain

/-! ## A.e. strong measurability of the angular moment -/

/-- `z ↦ Qang g i z` is a.e. strongly measurable on `Iz` (no integrability needed): it is the
`θ`-integral of the jointly continuous `(z,θ) ↦ Kθ(θ)·D_z^i g z θ` on the open quadrant
(`AEStronglyMeasurable.integral_prod_right'`). -/
private theorem aesm_Qang (i : ℕ) {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) :
    AEStronglyMeasurable (fun z : ℝ => Work.Elliptic.Qang g i z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have h := (Work.Spaces.aesm_of_continuousOn_Qd
    (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 * Work.Spaces.DzIter i g p.1 p.2)
    (Work.FTS.OpenPkg.QangOpen.continuousOn_Ktheta_DzIter_open hO i)).integral_prod_right'
  simpa only [Work.Elliptic.Qang] using h

/-! ## The level-six bound -/

theorem QangSq6 {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 6 g) :
    ∀ i : ℕ, i ≤ 5 →
      MeasureTheory.IntegrableOn (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
          Work.Spaces.Iz ∧
        (∫ z in Work.Spaces.Iz, (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
          ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α 6 g := by
  intro i hi
  have hi6 : i ≤ 6 := by omega
  have hK0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 :=
    MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  -- ## the pointwise (in `z > 0`) bound
  have hpt : ∀ z : ℝ, 0 < z →
      (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ) := by
    intro z hz
    have hCS := Qang_sq_le_k α g hO hmem i hi6 hz
    have hslice : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g z θ) ^ 2)
          * (Work.Spaces.w z) ^ 2
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ := by
      have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          (Work.Spaces.DzIter i g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            ≤ Work.Spaces.HkIntegrand α 6 g z θ := by
        rw [MeasureTheory.Measure.restrict_congr_set Iθ_ae_eq_Ioo]
        exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
          (fun θ hθ => DzIter_sq_w_sq_le_HkIntegrand_k α 6 g hi6 hz hθ)
      have hmono := MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (hmem.1 z (le_of_lt hz)) hae
      simpa only [MeasureTheory.integral_mul_const] using hmono
    calc (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g z θ) ^ 2))
            * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_right hCS (sq_nonneg _)
      _ = (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g z θ) ^ 2)
                * (Work.Spaces.w z) ^ 2) := by ring
      _ ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ) :=
          mul_le_mul_of_nonneg_left hslice hK0
  -- ## the bound holds almost everywhere on `Iz`
  have hle : (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      (fun z => (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ)) := by
    rw [MeasureTheory.Measure.restrict_congr_set Iz_ae_eq_Ioi]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hpt
  -- ## a.e. strong measurability
  have haesm : AEStronglyMeasurable
      (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hQ := aesm_Qang i hO
    have hw : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      rw [MeasureTheory.Measure.restrict_congr_set Iz_ae_eq_Ioi]
      exact continuousOn_w_sq.aestronglyMeasurable measurableSet_Ioi
    exact (hQ.pow 2).mul hw
  -- ## the dominating function is integrable
  have hdom : MeasureTheory.Integrable
      (fun z => (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hmem.2.const_mul _
  refine ⟨?_, ?_⟩
  · refine MeasureTheory.Integrable.mono' hdom haesm ?_
    filter_upwards [hle] with z hz
    rwa [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  · have hmono := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      hdom hle
    rw [MeasureTheory.integral_const_mul] at hmono
    exact hmono.trans (le_of_eq rfl)

end Work.FTS.StrongPersist
end
end
