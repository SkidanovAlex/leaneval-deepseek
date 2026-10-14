import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Interval.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.H2.Transport1Aux
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.OpenPkg.ProdOpen.Tools1d
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.LWP.Main
import Submission.Work.LWP.VorticityAPI
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.SolutionDelivery.DatumEuler
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.mixed_sq_integrableOn
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.thD_reindex
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.Cutoff
import Submission.Work.Stability.holderWith_of_dist_le
-- ===== merged: Submission.Work.ConstructionInstance.A0_holder =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Topology NNReal ENNReal

namespace Work.ConstructionInstance


/-- `|s₁ ^ (3β) - s₂ ^ (3β)| ≤ 3^β S^(2β) d^β` for `0 ≤ s₁,s₂ ≤ S` and `|s₁ - s₂| ≤ d`.

This is the elementary Hölder estimate for `t ↦ t^{3β}`: `t^{3β} = (t³)^β`, the cube is
`3S²`-Lipschitz on `[0,S]`, and `t ↦ t^β` is `β`-Hölder on `[0,∞)` (`A0_rpow_sub_le`). -/
private lemma rho_pow_diff_le {β s₁ s₂ S d : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (h1 : 0 ≤ s₁) (h2 : 0 ≤ s₂) (hS1 : s₁ ≤ S) (hS2 : s₂ ≤ S) (hd : |s₁ - s₂| ≤ d) :
    |s₁ ^ (3 * β) - s₂ ^ (3 * β)| ≤ 3 ^ β * S ^ (2 * β) * d ^ β := by
  have hd0 : 0 ≤ d := le_trans (abs_nonneg _) hd
  have hS0 : 0 ≤ S := le_trans h1 hS1
  have hpow : s₁ ^ (3 * β) = (s₁ ^ 3) ^ β := by
    rw [← Real.rpow_natCast s₁ 3]
    exact Real.rpow_mul h1 3 β
  have hpow' : s₂ ^ (3 * β) = (s₂ ^ 3) ^ β := by
    rw [← Real.rpow_natCast s₂ 3]
    exact Real.rpow_mul h2 3 β
  have hcub : |s₁ ^ 3 - s₂ ^ 3| ≤ 3 * S ^ 2 * d := by
    have hfac : s₁ ^ 3 - s₂ ^ 3 = (s₁ - s₂) * (s₁ ^ 2 + s₁ * s₂ + s₂ ^ 2) := by ring
    rw [hfac, abs_mul]
    have hkey : s₁ ^ 2 + s₁ * s₂ + s₂ ^ 2 ≤ 3 * S ^ 2 := by nlinarith [hS1, hS2, h1, h2]
    have hkey0 : (0:ℝ) ≤ s₁ ^ 2 + s₁ * s₂ + s₂ ^ 2 := by positivity
    calc |s₁ - s₂| * |s₁ ^ 2 + s₁ * s₂ + s₂ ^ 2|
        = |s₁ - s₂| * (s₁ ^ 2 + s₁ * s₂ + s₂ ^ 2) := by rw [abs_of_nonneg hkey0]
      _ ≤ d * (3 * S ^ 2) := mul_le_mul hd hkey hkey0 hd0
      _ = 3 * S ^ 2 * d := by ring
  calc |s₁ ^ (3 * β) - s₂ ^ (3 * β)|
      = |(s₁ ^ 3) ^ β - (s₂ ^ 3) ^ β| := by rw [hpow, hpow']
    _ ≤ |s₁ ^ 3 - s₂ ^ 3| ^ β := A0_rpow_sub_le hβ hβ1 (by positivity) (by positivity)
    _ ≤ (3 * S ^ 2 * d) ^ β := Real.rpow_le_rpow (abs_nonneg _) hcub hβ.le
    _ = 3 ^ β * S ^ (2 * β) * d ^ β := by
        have h1' : (3 * S ^ 2 * d : ℝ) = 3 * (S ^ 2 * d) := by ring
        rw [h1', Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) (by positivity : (0:ℝ) ≤ S ^ 2 * d),
          Real.mul_rpow (by positivity : (0:ℝ) ≤ S ^ 2) hd0,
          ← Real.rpow_natCast S 2, ← Real.rpow_mul hS0]
        ring

/-! ### the case `4 d < S` -/


lemma A0_holder_caseB {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {x y : R3}
    (hd : 4 * ‖x - y‖ < max (Work.Cyl.rho x) (Work.Cyl.rho y)) :
    |A0 β x - A0 β y| ≤ 3170304 * ‖x - y‖ ^ β := by
  set d : ℝ := ‖x - y‖ with hddef
  set S : ℝ := max (Work.Cyl.rho x) (Work.Cyl.rho y) with hSdef
  set rx : ℝ := Work.Cyl.rho x with hrxdef
  set ry : ℝ := Work.Cyl.rho y with hrydef
  have hd0 : 0 ≤ d := by rw [hddef]; exact norm_nonneg _
  have hSd : 4 * d < S := by simpa [← hddef, ← hSdef] using hd
  have hSpos : 0 < S := by linarith
  have hrx0 : 0 ≤ rx := by rw [hrxdef]; exact Work.Cyl.rho_nonneg x
  have hry0 : 0 ≤ ry := by rw [hrydef]; exact Work.Cyl.rho_nonneg y
  have hrxS : rx ≤ S := by rw [hrxdef, hSdef]; exact le_max_left _ _
  have hryS : ry ≤ S := by rw [hrydef, hSdef]; exact le_max_right _ _
  have hdiff : |rx - ry| ≤ d := by
    have h1 : |rx - ry| = |‖x‖ - ‖y‖| := by
      rw [hrxdef, hrydef, Work.Cyl.rho_eq_norm, Work.Cyl.rho_eq_norm]
    rw [h1, hddef]; exact abs_norm_sub_norm_le x y
  have hS4 : S / 4 ≤ min rx ry := by
    have h1 : S - min rx ry = |ry - rx| := by rw [hSdef]; exact max_sub_min_eq_abs rx ry
    have h2 : |ry - rx| = |rx - ry| := abs_sub_comm _ _
    have h3 : min rx ry = S - |rx - ry| := by linarith
    have h4 : |rx - ry| ≤ S / 4 := by linarith
    linarith
  have hsm0 : 0 < min rx ry := lt_of_lt_of_le (by positivity) hS4
  have hAx : A0 β x = 2 * Pall x ^ β / (1 + rx ^ (3 * β)) ^ 2 := by
    rw [hrxdef]; exact A0_eq_Pall β x
  have hAy : A0 β y = 2 * Pall y ^ β / (1 + ry ^ (3 * β)) ^ 2 := by
    rw [hrydef]; exact A0_eq_Pall β y
  have hUx1 : 1 ≤ 1 + rx ^ (3 * β) := by
    have := Real.rpow_nonneg hrx0 (3 * β); linarith
  have hUy1 : 1 ≤ 1 + ry ^ (3 * β) := by
    have := Real.rpow_nonneg hry0 (3 * β); linarith
  have hPx0 : 0 ≤ Pall x := Pall_nonneg x
  have hPy0 : 0 ≤ Pall y := Pall_nonneg y
  have hPxβ : 0 ≤ Pall x ^ β := Real.rpow_nonneg hPx0 β
  have hPyβ : 0 ≤ Pall y ^ β := Real.rpow_nonneg hPy0 β
  have hdβ0 : 0 ≤ d ^ β := Real.rpow_nonneg hd0 β
  have h3β0 : (0:ℝ) ≤ 3 ^ β := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 3) β
  have h9β0 : (0:ℝ) ≤ (4 : ℝ) ^ (9 * β) :=
    Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 4) (9 * β)
  have h6β0 : (0:ℝ) ≤ (4 : ℝ) ^ (6 * β) :=
    Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 4) (6 * β)
  have hdecomp : A0 β x - A0 β y
      = 2 * Pall x ^ β * (1 / (1 + rx ^ (3 * β)) ^ 2 - 1 / (1 + ry ^ (3 * β)) ^ 2)
        + 2 * (Pall x ^ β - Pall y ^ β) / (1 + ry ^ (3 * β)) ^ 2 := by
    rw [hAx, hAy]
    field_simp
    ring
  have htri : |A0 β x - A0 β y|
      ≤ 2 * Pall x ^ β * |1 / (1 + rx ^ (3 * β)) ^ 2 - 1 / (1 + ry ^ (3 * β)) ^ 2|
        + 2 * |Pall x ^ β - Pall y ^ β| / (1 + ry ^ (3 * β)) ^ 2 := by
    rw [hdecomp]
    refine (abs_add_le _ _).trans (le_of_eq ?_)
    have h1 : |2 * Pall x ^ β * (1 / (1 + rx ^ (3 * β)) ^ 2 - 1 / (1 + ry ^ (3 * β)) ^ 2)|
        = 2 * Pall x ^ β
          * |1 / (1 + rx ^ (3 * β)) ^ 2 - 1 / (1 + ry ^ (3 * β)) ^ 2| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_nonneg hPxβ]
    have h2 : |2 * (Pall x ^ β - Pall y ^ β) / (1 + ry ^ (3 * β)) ^ 2|
        = 2 * |Pall x ^ β - Pall y ^ β| / (1 + ry ^ (3 * β)) ^ 2 := by
      rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
        abs_of_pos (by positivity : (0:ℝ) < (1 + ry ^ (3 * β)) ^ 2)]
    rw [h1, h2]
  have hPxS : Pall x ^ β ≤ S ^ (3 * β) := by
    have h1 : Pall x ≤ S ^ 3 := by
      refine le_trans (Pall_le_rho_cube x) ?_
      rw [← hrxdef]
      exact pow_le_pow_left₀ hrx0 hrxS 3
    calc Pall x ^ β ≤ (S ^ 3) ^ β := Real.rpow_le_rpow hPx0 h1 hβ.le
      _ = S ^ (3 * β) := by
          rw [← Real.rpow_natCast S 3]
          exact (Real.rpow_mul hSpos.le 3 β).symm
  have hPP : |Pall x ^ β - Pall y ^ β| ≤ 3 ^ β * S ^ (2 * β) * d ^ β := by
    have hPd : |Pall x - Pall y| ≤ 3 * S ^ 2 * d := by
      have h := A0_Pall_diff x y
      rw [hSdef, hddef]
      exact h
    calc |Pall x ^ β - Pall y ^ β| ≤ |Pall x - Pall y| ^ β := A0_rpow_sub_le hβ hβ1 hPx0 hPy0
      _ ≤ (3 * S ^ 2 * d) ^ β := Real.rpow_le_rpow (abs_nonneg _) hPd hβ.le
      _ = 3 ^ β * S ^ (2 * β) * d ^ β := by
          have h1 : (3 * S ^ 2 * d : ℝ) = 3 * (S ^ 2 * d) := by ring
          rw [h1, Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3)
                (by positivity : (0:ℝ) ≤ S ^ 2 * d),
            Real.mul_rpow (by positivity : (0:ℝ) ≤ S ^ 2) hd0,
            ← Real.rpow_natCast S 2, ← Real.rpow_mul hSpos.le]
          ring
  have hUU : |(1 + rx ^ (3 * β)) - (1 + ry ^ (3 * β))| ≤ 3 ^ β * S ^ (2 * β) * d ^ β := by
    have h := rho_pow_diff_le hβ hβ1 hrx0 hry0 hrxS hryS hdiff
    have he : (1 + rx ^ (3 * β)) - (1 + ry ^ (3 * β)) = rx ^ (3 * β) - ry ^ (3 * β) := by ring
    rwa [he]
  have hminU : min (1 + rx ^ (3 * β)) (1 + ry ^ (3 * β)) = 1 + min rx ry ^ (3 * β) := by
    rcases le_total rx ry with h | h
    · have h2 : 1 + rx ^ (3 * β) ≤ 1 + ry ^ (3 * β) := by
        have h0 : rx ^ (3 * β) ≤ ry ^ (3 * β) :=
          Real.rpow_le_rpow hrx0 h (by linarith : (0:ℝ) ≤ 3 * β)
        linarith
      rw [min_eq_left h2, min_eq_left h]
    · have h2 : 1 + ry ^ (3 * β) ≤ 1 + rx ^ (3 * β) := by
        have h0 : ry ^ (3 * β) ≤ rx ^ (3 * β) :=
          Real.rpow_le_rpow hry0 h (by linarith : (0:ℝ) ≤ 3 * β)
        linarith
      rw [min_eq_right h2, min_eq_right h]
  have hinv : |1 / (1 + rx ^ (3 * β)) ^ 2 - 1 / (1 + ry ^ (3 * β)) ^ 2|
      ≤ 2 * (3 ^ β * S ^ (2 * β) * d ^ β) / (1 + min rx ry ^ (3 * β)) ^ 3 := by
    have h := A0_inv_sq_sub_le hUx1 hUy1
    rw [hminU] at h
    refine h.trans ?_
    have hM0 : (0:ℝ) < (1 + min rx ry ^ (3 * β)) ^ 3 := by positivity
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hUU (by norm_num : (0:ℝ) ≤ 2)) hM0.le
  have hterm1 : 2 * Pall x ^ β * |1 / (1 + rx ^ (3 * β)) ^ 2 - 1 / (1 + ry ^ (3 * β)) ^ 2|
      ≤ 3145728 * d ^ β := by
    have hstep : 2 * Pall x ^ β * |1 / (1 + rx ^ (3 * β)) ^ 2 - 1 / (1 + ry ^ (3 * β)) ^ 2|
        ≤ 2 * S ^ (3 * β) * (2 * (3 ^ β * S ^ (2 * β) * d ^ β)
            * (1 / (1 + min rx ry ^ (3 * β)) ^ 3)) := by
      have h1 : 2 * Pall x ^ β * |1 / (1 + rx ^ (3 * β)) ^ 2 - 1 / (1 + ry ^ (3 * β)) ^ 2|
          ≤ 2 * S ^ (3 * β) * (2 * (3 ^ β * S ^ (2 * β) * d ^ β)
              / (1 + min rx ry ^ (3 * β)) ^ 3) := by
        refine mul_le_mul (by linarith) hinv (abs_nonneg _) (by positivity)
      calc 2 * Pall x ^ β * |1 / (1 + rx ^ (3 * β)) ^ 2 - 1 / (1 + ry ^ (3 * β)) ^ 2|
          ≤ 2 * S ^ (3 * β) * (2 * (3 ^ β * S ^ (2 * β) * d ^ β)
              / (1 + min rx ry ^ (3 * β)) ^ 3) := h1
        _ = 2 * S ^ (3 * β) * (2 * (3 ^ β * S ^ (2 * β) * d ^ β)
              * (1 / (1 + min rx ry ^ (3 * β)) ^ 3)) := by
            simp only [div_eq_mul_inv, one_mul]
    rcases le_total S 1 with hS1 | hS1
    · have hS3 : S ^ (3 * β) ≤ 1 := Real.rpow_le_one hSpos.le hS1 (by linarith)
      have hS2 : S ^ (2 * β) ≤ 1 := Real.rpow_le_one hSpos.le hS1 (by linarith)
      have hS3β0 : (0:ℝ) ≤ S ^ (3 * β) := Real.rpow_nonneg hSpos.le _
      have hS2β0 : (0:ℝ) ≤ S ^ (2 * β) := Real.rpow_nonneg hSpos.le _
      have hM3 : 1 / (1 + min rx ry ^ (3 * β)) ^ 3 ≤ 1 := by
        rw [div_le_one (by positivity : (0:ℝ) < (1 + min rx ry ^ (3 * β)) ^ 3)]
        have h0 : (0:ℝ) ≤ min rx ry ^ (3 * β) := Real.rpow_nonneg hsm0.le _
        calc (1:ℝ) = 1 ^ 3 := by ring
          _ ≤ (1 + min rx ry ^ (3 * β)) ^ 3 :=
              pow_le_pow_left₀ (show (0:ℝ) ≤ 1 by norm_num) (by linarith) 3
      have hM30 : (0:ℝ) ≤ 1 / (1 + min rx ry ^ (3 * β)) ^ 3 := by positivity
      have hprod : S ^ (3 * β) * S ^ (2 * β) * (1 / (1 + min rx ry ^ (3 * β)) ^ 3) ≤ 1 := by
        calc S ^ (3 * β) * S ^ (2 * β) * (1 / (1 + min rx ry ^ (3 * β)) ^ 3)
            ≤ 1 * 1 * 1 := by
              refine mul_le_mul ?_ hM3 hM30 (by norm_num)
              exact mul_le_mul hS3 hS2 hS2β0 (by norm_num)
          _ = 1 := by norm_num
      have hkey : 2 * S ^ (3 * β) * (2 * (3 ^ β * S ^ (2 * β) * d ^ β)
          * (1 / (1 + min rx ry ^ (3 * β)) ^ 3)) ≤ 4 * 3 ^ β * d ^ β := by
        calc 2 * S ^ (3 * β) * (2 * (3 ^ β * S ^ (2 * β) * d ^ β)
              * (1 / (1 + min rx ry ^ (3 * β)) ^ 3))
            = (S ^ (3 * β) * S ^ (2 * β) * (1 / (1 + min rx ry ^ (3 * β)) ^ 3))
                * (4 * 3 ^ β * d ^ β) := by ring
          _ ≤ 1 * (4 * 3 ^ β * d ^ β) := mul_le_mul_of_nonneg_right hprod (by positivity)
          _ = 4 * 3 ^ β * d ^ β := by ring
      calc 2 * Pall x ^ β * |1 / (1 + rx ^ (3 * β)) ^ 2 - 1 / (1 + ry ^ (3 * β)) ^ 2|
          ≤ 2 * S ^ (3 * β) * (2 * (3 ^ β * S ^ (2 * β) * d ^ β)
              * (1 / (1 + min rx ry ^ (3 * β)) ^ 3)) := hstep
        _ ≤ 4 * 3 ^ β * d ^ β := hkey
        _ ≤ 3145728 * d ^ β := by
            have h3β : (3:ℝ) ^ β ≤ 3 := by
              have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3) hβ1
              rwa [Real.rpow_one] at h
            have hcoef : (4:ℝ) * 3 ^ β ≤ 4 * 3 := by linarith
            calc 4 * 3 ^ β * d ^ β ≤ 4 * 3 * d ^ β := mul_le_mul_of_nonneg_right hcoef hdβ0
              _ ≤ 3145728 * d ^ β := mul_le_mul_of_nonneg_right (by norm_num) hdβ0
    · have hM3 : 1 / (1 + min rx ry ^ (3 * β)) ^ 3 ≤ 4 ^ (9 * β) / S ^ (9 * β) := by
        have h1 : (S / 4) ^ (9 * β) ≤ (min rx ry) ^ (9 * β) :=
          Real.rpow_le_rpow (by positivity) hS4 (by linarith)
        have h5 : (min rx ry) ^ (9 * β) ≤ (1 + min rx ry ^ (3 * β)) ^ 3 := by
          have h6 : min rx ry ^ (3 * β) ≤ 1 + min rx ry ^ (3 * β) := by
            have h0 : (0:ℝ) ≤ min rx ry ^ (3 * β) := Real.rpow_nonneg hsm0.le _
            linarith
          calc (min rx ry) ^ (9 * β) = ((min rx ry) ^ (3 * β)) ^ 3 := by
                rw [← Real.rpow_natCast ((min rx ry) ^ (3 * β)) 3, ← Real.rpow_mul hsm0.le]
                congr 1
                ring
            _ ≤ (1 + min rx ry ^ (3 * β)) ^ 3 :=
                pow_le_pow_left₀ (Real.rpow_nonneg hsm0.le _) h6 3
        have h6 : (S / 4) ^ (9 * β) ≤ (1 + min rx ry ^ (3 * β)) ^ 3 := le_trans h1 h5
        have h7 : 0 < (S / 4) ^ (9 * β) := Real.rpow_pos_of_pos (by positivity) _
        have h8 := one_div_le_one_div_of_le h7 h6
        have h9 : 1 / ((S / 4) ^ (9 * β)) = 4 ^ (9 * β) / S ^ (9 * β) := by
          rw [Real.div_rpow hSpos.le (by norm_num : (0:ℝ) ≤ 4) (9 * β)]
          field_simp
        rw [← h9]
        exact h8
      have hkey0 : S ^ (3 * β) * S ^ (2 * β) * ((4:ℝ) ^ (9 * β) / S ^ (9 * β)) ≤ 4 ^ (9 * β) := by
        have h5 : S ^ (3 * β) * S ^ (2 * β) = S ^ (5 * β) := by
          rw [← Real.rpow_add hSpos]
          congr 1
          ring
        rw [h5]
        have hr : S ^ (5 * β) / S ^ (9 * β) ≤ 1 := by
          rw [div_le_one (Real.rpow_pos_of_pos hSpos _)]
          exact Real.rpow_le_rpow_of_exponent_le hS1 (by linarith)
        calc S ^ (5 * β) * (4 ^ (9 * β) / S ^ (9 * β))
            = 4 ^ (9 * β) * (S ^ (5 * β) / S ^ (9 * β)) := by
              rw [div_eq_mul_inv, div_eq_mul_inv]; ring
          _ ≤ 4 ^ (9 * β) * 1 := mul_le_mul_of_nonneg_left hr h9β0
          _ = 4 ^ (9 * β) := mul_one _
      have hkey : 2 * S ^ (3 * β) * (2 * (3 ^ β * S ^ (2 * β) * d ^ β)
          * (4 ^ (9 * β) / S ^ (9 * β))) ≤ 4 * 3 ^ β * 4 ^ (9 * β) * d ^ β := by
        have h4 : (0:ℝ) ≤ 4 * 3 ^ β * d ^ β := by positivity
        have h := mul_le_mul_of_nonneg_right hkey0 h4
        calc 2 * S ^ (3 * β) * (2 * (3 ^ β * S ^ (2 * β) * d ^ β)
              * (4 ^ (9 * β) / S ^ (9 * β)))
            = (S ^ (3 * β) * S ^ (2 * β) * (4 ^ (9 * β) / S ^ (9 * β)))
                * (4 * 3 ^ β * d ^ β) := by ring
          _ ≤ 4 ^ (9 * β) * (4 * 3 ^ β * d ^ β) := h
          _ = 4 * 3 ^ β * 4 ^ (9 * β) * d ^ β := by ring
      calc 2 * Pall x ^ β * |1 / (1 + rx ^ (3 * β)) ^ 2 - 1 / (1 + ry ^ (3 * β)) ^ 2|
          ≤ 2 * S ^ (3 * β) * (2 * (3 ^ β * S ^ (2 * β) * d ^ β)
              * (1 / (1 + min rx ry ^ (3 * β)) ^ 3)) := hstep
        _ ≤ 2 * S ^ (3 * β) * (2 * (3 ^ β * S ^ (2 * β) * d ^ β)
              * (4 ^ (9 * β) / S ^ (9 * β))) := by
            have h0 : (0:ℝ) ≤ 2 * S ^ (3 * β) := by positivity
            have h1 : (0:ℝ) ≤ 2 * (3 ^ β * S ^ (2 * β) * d ^ β) := by positivity
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hM3 h1) h0
        _ ≤ 4 * 3 ^ β * 4 ^ (9 * β) * d ^ β := hkey
        _ ≤ 3145728 * d ^ β := by
            have h3β : (3:ℝ) ^ β ≤ 3 := by
              have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3) hβ1
              rwa [Real.rpow_one] at h
            have h49 : (4:ℝ) ^ (9 * β) ≤ 262144 := by
              calc (4:ℝ) ^ (9 * β) ≤ (4:ℝ) ^ (9:ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 4) (by linarith)
                _ = 262144 := by norm_num
            have hcoef : (4:ℝ) * 3 ^ β * 4 ^ (9 * β) ≤ 3145728 := by
              have h1 : (4:ℝ) * 3 ^ β ≤ 4 * 3 := by linarith
              have h2 : (4:ℝ) * 3 ^ β * 4 ^ (9 * β) ≤ 4 * 3 * 262144 :=
                mul_le_mul h1 h49 h9β0 (by norm_num : (0:ℝ) ≤ 4 * 3)
              linarith
            exact mul_le_mul_of_nonneg_right hcoef hdβ0
  have hterm2 : 2 * |Pall x ^ β - Pall y ^ β| / (1 + ry ^ (3 * β)) ^ 2 ≤ 24576 * d ^ β := by
    have hstep : 2 * |Pall x ^ β - Pall y ^ β| / (1 + ry ^ (3 * β)) ^ 2
        ≤ 2 * (3 ^ β * S ^ (2 * β) * d ^ β) / (1 + ry ^ (3 * β)) ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hPP (by norm_num : (0:ℝ) ≤ 2))
        (by positivity)
    rcases le_total S 1 with hS1 | hS1
    · have hS2 : S ^ (2 * β) ≤ 1 := Real.rpow_le_one hSpos.le hS1 (by linarith)
      have hS2β0 : (0:ℝ) ≤ S ^ (2 * β) := Real.rpow_nonneg hSpos.le _
      have hden : 1 / (1 + ry ^ (3 * β)) ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity : (0:ℝ) < (1 + ry ^ (3 * β)) ^ 2)]
        have h0 : (0:ℝ) ≤ ry ^ (3 * β) := Real.rpow_nonneg hry0 _
        calc (1:ℝ) = 1 ^ 2 := by ring
          _ ≤ (1 + ry ^ (3 * β)) ^ 2 :=
              pow_le_pow_left₀ (show (0:ℝ) ≤ 1 by norm_num) (by linarith) 2
      have hden0 : (0:ℝ) ≤ 1 / (1 + ry ^ (3 * β)) ^ 2 := by positivity
      have hprod : S ^ (2 * β) * (1 / (1 + ry ^ (3 * β)) ^ 2) ≤ 1 := by
        calc S ^ (2 * β) * (1 / (1 + ry ^ (3 * β)) ^ 2) ≤ 1 * 1 :=
              mul_le_mul hS2 hden hden0 (by norm_num)
          _ = 1 := by norm_num
      have hkey : 2 * (3 ^ β * S ^ (2 * β) * d ^ β) * (1 / (1 + ry ^ (3 * β)) ^ 2)
          ≤ 6 * d ^ β := by
        calc 2 * (3 ^ β * S ^ (2 * β) * d ^ β) * (1 / (1 + ry ^ (3 * β)) ^ 2)
            = (S ^ (2 * β) * (1 / (1 + ry ^ (3 * β)) ^ 2)) * (2 * 3 ^ β * d ^ β) := by ring
          _ ≤ 1 * (2 * 3 ^ β * d ^ β) := mul_le_mul_of_nonneg_right hprod (by positivity)
          _ = 2 * 3 ^ β * d ^ β := by ring
          _ ≤ 6 * d ^ β := by
              have h3β : (3:ℝ) ^ β ≤ 3 := by
                have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3) hβ1
                rwa [Real.rpow_one] at h
              have hcoef : (2:ℝ) * 3 ^ β ≤ 2 * 3 := by linarith
              calc 2 * 3 ^ β * d ^ β ≤ 2 * 3 * d ^ β := mul_le_mul_of_nonneg_right hcoef hdβ0
                _ = 6 * d ^ β := by ring
      calc 2 * |Pall x ^ β - Pall y ^ β| / (1 + ry ^ (3 * β)) ^ 2
          ≤ 2 * (3 ^ β * S ^ (2 * β) * d ^ β) / (1 + ry ^ (3 * β)) ^ 2 := hstep
        _ = 2 * (3 ^ β * S ^ (2 * β) * d ^ β) * (1 / (1 + ry ^ (3 * β)) ^ 2) := by
            simp only [div_eq_mul_inv, one_mul]
        _ ≤ 6 * d ^ β := hkey
        _ ≤ 24576 * d ^ β := mul_le_mul_of_nonneg_right (by norm_num) hdβ0
    · have hden : 1 / (1 + ry ^ (3 * β)) ^ 2 ≤ 4 ^ (6 * β) / S ^ (6 * β) := by
        have h1 : (S / 4) ^ (6 * β) ≤ ry ^ (6 * β) :=
          Real.rpow_le_rpow (by positivity) (le_trans hS4 (min_le_right rx ry)) (by linarith)
        have h6 : ry ^ (6 * β) ≤ (1 + ry ^ (3 * β)) ^ 2 := by
          have h7 : ry ^ (3 * β) ≤ 1 + ry ^ (3 * β) := by
            have h0 : (0:ℝ) ≤ ry ^ (3 * β) := Real.rpow_nonneg hry0 _
            linarith
          calc ry ^ (6 * β) = (ry ^ (3 * β)) ^ 2 := by
                rw [← Real.rpow_natCast (ry ^ (3 * β)) 2, ← Real.rpow_mul hry0]
                congr 1
                ring
            _ ≤ (1 + ry ^ (3 * β)) ^ 2 :=
                pow_le_pow_left₀ (Real.rpow_nonneg hry0 _) h7 2
        have h7 : (S / 4) ^ (6 * β) ≤ (1 + ry ^ (3 * β)) ^ 2 := le_trans h1 h6
        have h8 : 0 < (S / 4) ^ (6 * β) := Real.rpow_pos_of_pos (by positivity) _
        have h9 := one_div_le_one_div_of_le h8 h7
        have h10 : 1 / ((S / 4) ^ (6 * β)) = 4 ^ (6 * β) / S ^ (6 * β) := by
          rw [Real.div_rpow hSpos.le (by norm_num : (0:ℝ) ≤ 4) (6 * β)]
          field_simp
        rw [← h10]
        exact h9
      have hkey0 : S ^ (2 * β) * ((4:ℝ) ^ (6 * β) / S ^ (6 * β)) ≤ 4 ^ (6 * β) := by
        have hr : S ^ (2 * β) / S ^ (6 * β) ≤ 1 := by
          rw [div_le_one (Real.rpow_pos_of_pos hSpos _)]
          exact Real.rpow_le_rpow_of_exponent_le hS1 (by linarith)
        calc S ^ (2 * β) * (4 ^ (6 * β) / S ^ (6 * β))
            = 4 ^ (6 * β) * (S ^ (2 * β) / S ^ (6 * β)) := by
              rw [div_eq_mul_inv, div_eq_mul_inv]; ring
          _ ≤ 4 ^ (6 * β) * 1 := mul_le_mul_of_nonneg_left hr h6β0
          _ = 4 ^ (6 * β) := mul_one _
      have hkey : 2 * (3 ^ β * S ^ (2 * β) * d ^ β) * (4 ^ (6 * β) / S ^ (6 * β))
          ≤ 2 * 3 ^ β * 4 ^ (6 * β) * d ^ β := by
        have h4 : (0:ℝ) ≤ 2 * 3 ^ β * d ^ β := by positivity
        have h := mul_le_mul_of_nonneg_right hkey0 h4
        calc 2 * (3 ^ β * S ^ (2 * β) * d ^ β) * (4 ^ (6 * β) / S ^ (6 * β))
            = (S ^ (2 * β) * ((4:ℝ) ^ (6 * β) / S ^ (6 * β))) * (2 * 3 ^ β * d ^ β) := by ring
          _ ≤ 4 ^ (6 * β) * (2 * 3 ^ β * d ^ β) := h
          _ = 2 * 3 ^ β * 4 ^ (6 * β) * d ^ β := by ring
      have h3β : (3:ℝ) ^ β ≤ 3 := by
        have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3) hβ1
        rwa [Real.rpow_one] at h
      have h46 : (4:ℝ) ^ (6 * β) ≤ 4096 := by
        calc (4:ℝ) ^ (6 * β) ≤ (4:ℝ) ^ (6:ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 4) (by linarith)
          _ = 4096 := by norm_num
      calc 2 * |Pall x ^ β - Pall y ^ β| / (1 + ry ^ (3 * β)) ^ 2
          ≤ 2 * (3 ^ β * S ^ (2 * β) * d ^ β) / (1 + ry ^ (3 * β)) ^ 2 := hstep
        _ = 2 * (3 ^ β * S ^ (2 * β) * d ^ β) * (1 / (1 + ry ^ (3 * β)) ^ 2) := by
            simp only [div_eq_mul_inv, one_mul]
        _ ≤ 2 * (3 ^ β * S ^ (2 * β) * d ^ β) * (4 ^ (6 * β) / S ^ (6 * β)) := by
            have h0 : (0:ℝ) ≤ 2 * (3 ^ β * S ^ (2 * β) * d ^ β) := by positivity
            exact mul_le_mul_of_nonneg_left hden h0
        _ ≤ 2 * 3 ^ β * 4 ^ (6 * β) * d ^ β := hkey
        _ ≤ 24576 * d ^ β := by
            have hcoef : (2:ℝ) * 3 ^ β * 4 ^ (6 * β) ≤ 24576 := by
              have h1 : (2:ℝ) * 3 ^ β ≤ 2 * 3 := by linarith
              have h2 : (2:ℝ) * 3 ^ β * 4 ^ (6 * β) ≤ 2 * 3 * 4096 :=
                mul_le_mul h1 h46 h6β0 (by norm_num : (0:ℝ) ≤ 2 * 3)
              linarith
            exact mul_le_mul_of_nonneg_right hcoef hdβ0
  calc |A0 β x - A0 β y|
      ≤ 2 * Pall x ^ β * |1 / (1 + rx ^ (3 * β)) ^ 2 - 1 / (1 + ry ^ (3 * β)) ^ 2|
        + 2 * |Pall x ^ β - Pall y ^ β| / (1 + ry ^ (3 * β)) ^ 2 := htri
    _ ≤ 3145728 * d ^ β + 24576 * d ^ β := add_le_add hterm1 hterm2
    _ = 3170304 * d ^ β := by ring
    _ = 3170304 * ‖x - y‖ ^ β := by rw [hddef]

theorem A0_holder {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∃ C : NNReal, ∀ x y : Work.ConstructionInstance.R3,
      |Work.ConstructionInstance.A0 β x - Work.ConstructionInstance.A0 β y|
        ≤ (C : ℝ) * ‖x - y‖ ^ β := by
  refine ⟨3200000, ?_⟩
  intro x y
  show |A0 β x - A0 β y| ≤ (3200000 : ℝ) * ‖x - y‖ ^ β
  have hd0 : 0 ≤ ‖x - y‖ := norm_nonneg _
  have hdβ0 : (0:ℝ) ≤ ‖x - y‖ ^ β := Real.rpow_nonneg hd0 β
  by_cases hdbig : 1 ≤ ‖x - y‖
  · have h1 : |A0 β x - A0 β y| ≤ 1 := by
      have hx := A0_le_half β hβ x
      have hy := A0_le_half β hβ y
      have hx0 := A0_nonneg β x
      have hy0 := A0_nonneg β y
      rw [abs_sub_le_iff]
      exact ⟨by linarith, by linarith⟩
    have h2 : (1:ℝ) ≤ ‖x - y‖ ^ β := Real.one_le_rpow hdbig hβ.le
    have h3 : (1:ℝ) * ‖x - y‖ ^ β ≤ 3200000 * ‖x - y‖ ^ β :=
      mul_le_mul_of_nonneg_right (by norm_num) hdβ0
    linarith
  · push_neg at hdbig
    by_cases hA : max (Work.Cyl.rho x) (Work.Cyl.rho y) ≤ 4 * ‖x - y‖
    · have hx2 : |x 2| ≤ 4 * ‖x - y‖ := by
        refine le_trans (Work.Cyl.abs_axial_le_rho x) ?_
        exact le_trans (le_max_left _ _) hA
      have hy2 : |y 2| ≤ 4 * ‖x - y‖ := by
        refine le_trans (Work.Cyl.abs_axial_le_rho y) ?_
        exact le_trans (le_max_right _ _) hA
      have hbx : |x 2| ^ β ≤ 4 ^ β * ‖x - y‖ ^ β := by
        have hpow4 : (4 * ‖x - y‖) ^ β = 4 ^ β * ‖x - y‖ ^ β :=
          Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hd0
        rw [← hpow4]
        exact Real.rpow_le_rpow (abs_nonneg _) hx2 hβ.le
      have hby : |y 2| ^ β ≤ 4 ^ β * ‖x - y‖ ^ β := by
        have hpow4 : (4 * ‖x - y‖) ^ β = 4 ^ β * ‖x - y‖ ^ β :=
          Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hd0
        rw [← hpow4]
        exact Real.rpow_le_rpow (abs_nonneg _) hy2 hβ.le
      have hxax := A0_le_ax β hβ x
      have hyax := A0_le_ax β hβ y
      have hx0 := A0_nonneg β x
      have hy0 := A0_nonneg β y
      have h4β : (4:ℝ) ^ β ≤ 4 := by
        calc (4:ℝ) ^ β ≤ 4 ^ (1:ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 4) hβ1
          _ = 4 := Real.rpow_one 4
      have hfinal : 4 * 4 ^ β * ‖x - y‖ ^ β ≤ 3200000 * ‖x - y‖ ^ β := by
        have h1 : 4 * 4 ^ β * ‖x - y‖ ^ β ≤ 4 * 4 * ‖x - y‖ ^ β :=
          mul_le_mul_of_nonneg_right (by linarith [h4β]) hdβ0
        have h2 : (4:ℝ) * 4 * ‖x - y‖ ^ β ≤ 3200000 * ‖x - y‖ ^ β :=
          mul_le_mul_of_nonneg_right (by norm_num) hdβ0
        linarith
      calc |A0 β x - A0 β y| ≤ A0 β x + A0 β y := by
            rw [abs_sub_le_iff]; exact ⟨by linarith, by linarith⟩
        _ ≤ 2 * |x 2| ^ β + 2 * |y 2| ^ β := by linarith
        _ ≤ 2 * (4 ^ β * ‖x - y‖ ^ β) + 2 * (4 ^ β * ‖x - y‖ ^ β) := by linarith
        _ = 4 * 4 ^ β * ‖x - y‖ ^ β := by ring
        _ ≤ 3200000 * ‖x - y‖ ^ β := hfinal
    · push_neg at hA
      have hcaseB := A0_holder_caseB hβ hβ1 hA
      calc |A0 β x - A0 β y| ≤ 3170304 * ‖x - y‖ ^ β := hcaseB
        _ ≤ 3200000 * ‖x - y‖ ^ β := mul_le_mul_of_nonneg_right (by norm_num) hdβ0

end Work.ConstructionInstance
end
end
-- ===== merged: Submission.Work.ConstructionInstance.ProfileData =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.ConstructionInstance

/-- **The profile/modulation interface**: the perturbation of the self-similar profile, the
modulation, and the two geometric parameters — everything the interface needs *before* the
vorticity is defined. -/
structure ProfileData (α : NNReal) where
  /-- `0 < α` (the Hölder exponent of the challenge) -/
  hα : 0 < (α : ℝ)
  /-- the perturbation `g` of the self-similar profile `F = F_* + g` -/
  g : ℝ → ℝ → ℝ
  /-- `g` vanishes on the two angular boundaries -/
  hvt : Work.Spaces.VanishTheta g
  /-- the smoothness class consumed by the profile estimates -/
  hsmooth : Work.Spaces.SmoothNbhd g
  /-- `g` vanishes at `z = 0` -/
  hquad0 : ∀ θ : ℝ, g 0 θ = 0
  /-- `∂_z g` vanishes at `z = 0` -/
  hquad : ∀ θ : ℝ, Work.Spaces.pz g 0 θ = 0
  /-- the `L^∞` constant of `g` -/
  Cg : ℝ
  /-- `Cg ≥ 0` -/
  hCg : 0 ≤ Cg
  /-- the `z`-decay of `g` (the hypothesis of the radial Hardy inequality) -/
  hdec : Work.Spaces.DecayInZ 2 g
  /-- `g ∈ ℋ²` (the a-priori bound of the construction's fixed point) -/
  hmem : Work.Spaces.HkMem (profExp α) 2 g
  /-- the `ℋ²`-bound, which yields `|g| ≤ Cg` (`abs_le_of_linf_H2`) -/
  hCgbig : 100 / Real.sqrt (Work.Spaces.gam (profExp α) - 1)
    * Work.Spaces.HkNorm (profExp α) 2 g ≤ Cg
  /-- the uniform angular vanishing of the perturbation -/
  Cv : ℝ
  /-- `Cv ≥ 0` -/
  hCv : 0 ≤ Cv
  /-- `|g z θ| ≤ Cv·Γ(α,θ)` -/
  hvan : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |g z θ| ≤ Cv * Gamma (α : ℝ) θ
  /-- the uniform radial modulus of the perturbation -/
  Lg : ℝ
  /-- `Lg ≥ 0` -/
  hLg : 0 ≤ Lg
  /-- the radial modulus -/
  hzk : ∀ z z' θ : ℝ, 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ →
    |g z θ - g z' θ| ≤ Lg * |z - z'| ^ (α : ℝ)
  /-- the uniform angular modulus of the perturbation -/
  Lθ : ℝ
  /-- `Lθ ≥ 0` -/
  hLθ : 0 ≤ Lθ
  /-- the angular modulus -/
  hzth : ∀ z θ θ' : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
    |g z θ - g z θ'| ≤ Lθ * |θ - θ'| ^ (α : ℝ)
  /-- the `𝒲^{1,∞}`-bound on `z ∂_z g` -/
  Cg' : ℝ
  /-- `z ∂_z g` is bounded on the closed quadrant -/
  hg2 : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |z * Work.Spaces.pz g z θ| ≤ Cg'
  /-- the `z`-differentiability of the profile -/
  hgdiff : ∀ z θ : ℝ, 0 < z →
    HasDerivAt (fun z' => profile (profExp α) g z' θ)
      (Work.Spaces.pz (profile (profExp α) g) z θ) z
  /-- the smallness `Cg ≤ c₀star α` of the perturbation (`St5`) -/
  hsmall : Cg ≤ profExp α * Work.Spaces.Gam (profExp α) (Real.pi / 4)
    / (4 * Work.Spaces.c (profExp α))
  /-- measurability of the scalar profile in the physical variables -/
  hmeasP : MeasureTheory.AEStronglyMeasurable
    (fun x : R3 => profile (profExp α) g (Work.Cyl.Rc (profExp α) x) (Work.Cyl.theta x))
    MeasureTheory.volume
  /-- the paper's regime `α ≤ 1/3` -/
  hα13 : (α : ℝ) ≤ 1 / 3
  /-- the blow-up time -/
  T : ℝ
  /-- `T > 0` -/
  hT : 0 < T
  /-- the modulation -/
  lam : ℝ → ℝ
  /-- `λ̄ > 0` before the maximal time -/
  hlam : ∀ t ∈ preWindow T, 0 < lam t
  /-- **the normalisation `λ̄(0) = 1`** of the design (`s = -ln λ̄`): it is what makes the ansatz at
  `t = 0` reproduce the `St1` datum `ω₀ = χ(ρ/L)·omegaS`, i.e. makes the datum of the maximal
  solution consistent with the pointwise ansatz (finding G) -/
  hlam0 : lam 0 = 1
  /-- the rate constant -/
  K : ℝ
  /-- `K ≥ 0` -/
  hK : 0 ≤ K
  /-- the design's normalisation `K ≤ 1/2` -/
  hK12 : K ≤ 1 / 2
  /-- `λ̄` is differentiable before the maximal time -/
  hlamdif : ∀ t ∈ preWindow T, HasDerivAt lam (deriv lam t) t
  /-- the rate bound `|λ̄'| ≤ K` -/
  hlamd : ∀ t ∈ preWindow T, |deriv lam t| ≤ K
  /-- `λ̄(t) ≤ 2(T-t)` -/
  hlam_le : ∀ t ∈ Set.Ico 0 T, lam t ≤ 2 * (T - t)
  /-- `(T-t)/2 ≤ λ̄(t)` -/
  hlam_low : ∀ t ∈ Set.Ico 0 T, (T - t) / 2 ≤ lam t
  /-- the `St1` cut-off parameter -/
  L : ℝ
  /-- `L > 0` -/
  hL : 0 < L
  /-- the cut-off is transparent at the `St5` witness: `(2T)^{1/p} ≤ L` -/
  hLbig : (2 * T) ^ (1 / profExp α) ≤ L
  /-- the self-similar `L^∞` constant -/
  M : ℝ
  /-- `M ≥ 0` -/
  hM : 0 ≤ M
  /-- `M` dominates the profile box -/
  hMprof : 20 * profExp α + Cg ≤ M
  /-- the self-similar `L^∞` constant of `∂ₜω` -/
  M₁ : ℝ
  /-- `M₁ ≥ 0` -/
  hM₁ : 0 ≤ M₁
  /-- `M₁` dominates the derived `∂ₜω` bound -/
  hM₁big : K * (20 * profExp α + Cg + Cg') ≤ M₁
  /-- the support radius -/
  R : ℝ
  /-- `R ≥ 0` -/
  hR : 0 ≤ R
  /-- the support radius covers the cut-off -/
  hRbig : 2 * L ≤ R

/-! ## The explicit `St5` constant -/

/-- **The explicit `St5` constant** `c₀ = p·Γ(p/4)/(4c(p))` with `p = profExp α`: it is half the
profile's value at the point `(z,θ) = (1,π/4)`, and it is positive.  Taking it as a *definition*
rather than a field removes the fields `c₀`, `hc₀` from the residual interface (the `St5` lower
bound then follows from the smallness `Cg ≤ c₀` of the perturbation). -/
def c₀star (α : NNReal) : ℝ :=
  3 * Work.Spaces.Gam (profExp α) (Real.pi / 4) / (4 * Work.Spaces.c (profExp α))

theorem c₀star_pos {α : NNReal} (hα : 0 < (α : ℝ)) (hα13 : (α : ℝ) ≤ 1 / 3) :
    0 < c₀star α := by
  have hp : 0 < profExp α := profExp_pos hα
  have hp1 : profExp α ≤ 1 := by rw [profExp]; linarith
  have hc := (Work.Spaces.c_bounds (profExp α) hp hp1).1
  have hcpos : 0 < Work.Spaces.c (profExp α) := by linarith
  have hGam : 0 < Work.Spaces.Gam (profExp α) (Real.pi / 4) := by
    rw [Work.Spaces.Gam]
    refine Real.rpow_pos_of_pos ?_ _
    rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
    norm_num
  rw [c₀star]
  positivity

end Work.ConstructionInstance
end
end
-- ===== merged: Submission.Work.ConstructionInstance.bddDt_selfSimVort =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- **The `∂ₜ` box for the constructed (cut) self-similar vorticity.**

The cut field is `selfSimVort p g L lam x t = χ(ρ(x)/L) • U x t`, where
`U x t = λ̄(t)⁻¹ • omegaSz p g (ρ(x)^p/λ̄(t)) x` is the *uncut* self-similar field.  Since the
cut-off factor `χ(ρ(x)/L)` does not depend on `t`, differentiating in `t` just multiplies the
derivative of `U` by `χ(ρ(x)/L)`; and `|χ| ≤ 1`.  Hence the box for the cut field follows from the
box for the uncut one (which is `lam_sq_timeDeriv_le_Ioo`, proved by the chain rule
`dasdt(λ̄⁻¹F(c/λ̄)) = -λ̄'(F + (c/λ̄)∂_zF)/λ̄²` and `|F + z∂_zF| ≤ 20p + Cg + Cg'`). -/
theorem bddDt_selfSimVort {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ}
    {Cg Cg' K : ℝ}
    (hgbdd : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |g z θ| ≤ Cg)
    (hg2 : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |z * Work.Spaces.pz g z θ| ≤ Cg')
    (hgdiff : ∀ z θ : ℝ, 0 < z →
      HasDerivAt (fun z' => Work.ConstructionInstance.profile p g z' θ)
        (Work.Spaces.pz (Work.ConstructionInstance.profile p g) z θ) z)
    {L : ℝ} {lam : ℝ → ℝ} {T : ℝ} (hK : 0 ≤ K)
    (hlam : ∀ t ∈ Work.ConstructionInstance.preWindow T, 0 < lam t)
    (hlamdif : ∀ t ∈ Work.ConstructionInstance.preWindow T, HasDerivAt lam (deriv lam t) t)
    (hlamd : ∀ t ∈ Work.ConstructionInstance.preWindow T, |deriv lam t| ≤ K)
    {t : ℝ} (ht : t ∈ Work.ConstructionInstance.preWindow T) (y : Work.ConstructionInstance.R3) :
    (lam t) ^ 2 * ‖FiniteTimeSingularity.timeDeriv
      (Work.ConstructionInstance.selfSimVort p g L lam) y t‖ ≤ K * (20 * p + Cg + Cg') := by
  have hI0 : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hCg : 0 ≤ Cg := le_trans (abs_nonneg _) (hgbdd 0 0 le_rfl hI0)
  have hCg' : 0 ≤ Cg' := by simpa using hg2 0 0 le_rfl hI0
  have hsum : 0 ≤ 20 * p + Cg + Cg' := by linarith
  have hlt : 0 < lam t := hlam t ht
  by_cases hrad : Work.Cyl.radial y = 0
  · -- on the symmetry axis the field vanishes identically
    have he0 : Work.Cyl.eTheta y = 0 := by
      rw [Work.Cyl.eTheta, hrad, div_zero, zero_smul]
    have hω0 : selfSimVort p g L lam y = fun _ => 0 := by
      funext s
      rw [selfSimVort_apply, omegaSz_apply, he0, smul_zero, smul_zero, smul_zero]
    rw [FiniteTimeSingularity.timeDeriv, hω0, deriv_const, norm_zero, mul_zero]
    exact mul_nonneg hK hsum
  · have hy : y ≠ 0 := by
      intro h0
      exact hrad (by rw [h0, Work.Cyl.radial_eq_zero_iff]; exact ⟨rfl, rfl⟩)
    have hρpos : 0 < Work.Cyl.rho y := by rw [Work.Cyl.rho_pos_iff]; exact hy
    set c : ℝ := Work.Cyl.rho y ^ p with hc
    set θ : ℝ := Work.Cyl.theta y with hθdef
    set e : R3 := Work.Cyl.eTheta y with he
    set a : ℝ := Work.Stability.chi (Work.Cyl.rho y / L) with ha
    have ha0 : 0 ≤ a := by rw [ha]; exact Work.Stability.chi_nonneg _
    have ha1 : |a| ≤ 1 := by
      rw [abs_of_nonneg ha0, ha]; exact Work.Stability.chi_le_one _
    have hcpos : 0 < c := by rw [hc]; exact Real.rpow_pos_of_pos hρpos p
    have hzpos : 0 < c / lam t := div_pos hcpos hlt
    have hlt2 : (0 : ℝ) < (lam t) ^ 2 := by positivity
    have hθabs : |θ| ≤ Real.pi / 2 := by
      rw [hθdef, abs_le]
      exact ⟨le_of_lt (Real.neg_pi_div_two_lt_arctan _),
        le_of_lt (Real.arctan_lt_pi_div_two _)⟩
    have hD4 := profile_add_z_pz_abs_le hp hp1 hgbdd hg2 hgdiff hzpos hθabs
    -- the scalar chain rule for `s ↦ λ̄(s)⁻¹ · F(c/λ̄(s))`
    have hφ : HasDerivAt (fun s => (lam s)⁻¹ * profile p g (c / lam s) θ)
        (-(deriv lam t * (profile p g (c / lam t) θ
          + (c / lam t) * Work.Spaces.pz (profile p g) (c / lam t) θ) / (lam t) ^ 2)) t :=
      hasDerivAt_inv_mul_comp (F := fun z' => profile p g z' θ) (hlamdif t ht) (ne_of_gt hlt)
        (hgdiff (c / lam t) θ hzpos)
    set X : ℝ := -(deriv lam t * (profile p g (c / lam t) θ
      + (c / lam t) * Work.Spaces.pz (profile p g) (c / lam t) θ) / (lam t) ^ 2) with hXdef
    -- the cut field is `χ(ρ(y)/L) = a` times the uncut one
    have hcut : selfSimVort p g L lam y
        = fun s => (a * ((lam s)⁻¹ * profile p g (c / lam s) θ)) • e := by
      funext s
      rw [selfSimVort_apply, ← ha, omegaSz_apply, ← hc, ← hθdef, ← he]
      rw [smul_smul, smul_smul]
      congr 1
      ring
    have hderivG : HasDerivAt (selfSimVort p g L lam y) ((a * X) • e) t := by
      rw [hcut, hXdef]
      exact (hφ.const_mul a).smul_const e
    have hdt : FiniteTimeSingularity.timeDeriv (selfSimVort p g L lam) y t
        = (a * X) • e := by
      rw [FiniteTimeSingularity.timeDeriv]
      exact hderivG.deriv
    rw [hdt, norm_smul, Real.norm_eq_abs, he, Work.Cyl.norm_eTheta y hrad, mul_one, abs_mul]
    have hkey : (lam t) ^ 2 * |X| = |deriv lam t * (profile p g (c / lam t) θ
        + (c / lam t) * Work.Spaces.pz (profile p g) (c / lam t) θ)| := by
      rw [hXdef, abs_neg, abs_div, abs_of_pos hlt2]
      rw [abs_mul]
      field_simp
    calc (lam t) ^ 2 * (|a| * |X|)
        = |a| * ((lam t) ^ 2 * |X|) := by ring
      _ ≤ 1 * ((lam t) ^ 2 * |X|) := mul_le_mul_of_nonneg_right ha1 (by positivity)
      _ = |deriv lam t * (profile p g (c / lam t) θ
            + (c / lam t) * Work.Spaces.pz (profile p g) (c / lam t) θ)| := by
            rw [one_mul, hkey]
      _ ≤ K * (20 * p + Cg + Cg') := by
            rw [abs_mul]
            exact mul_le_mul (hlamd t ht) hD4 (abs_nonneg _) hK

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.div_selfSimVort =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

set_option linter.unusedVariables false

noncomputable section

open FiniteTimeSingularity Work.Cyl

/-! ## The cut-off factor `χ(ρ/L)` has vanishing derivative along `e_θ` -/

/-- `ρ` is even along the line `t ↦ x + t • e_θ(x)` (`rho_add_smul_eTheta`), hence so is the
cut-off factor `χ(ρ/L)`; its directional derivative at `x` along `e_θ` therefore vanishes. -/
lemma fderiv_chi_rho_div_eTheta {L : ℝ} {x : R3} (hr : 0 < Work.Cyl.radial x) :
    fderiv ℝ (fun y : R3 => Work.Stability.chi (Work.Cyl.rho y / L)) x (Work.Cyl.eTheta x) = 0 := by
  have hdiff : DifferentiableAt ℝ (fun y : R3 => Work.Cyl.rho y / L) x := by
    simpa only [div_eq_mul_inv] using
      (Work.Cyl.differentiableAt_rho_of_radial_pos x hr).mul_const L⁻¹
  have hF : DifferentiableAt ℝ
      (fun y : R3 => Work.Stability.chi (Work.Cyl.rho y / L)) x :=
    ((Work.Stability.chi_contDiff.differentiable (by simp)).differentiableAt).comp x hdiff
  rw [Work.Cyl.fderiv_apply_eq_deriv_line _ x _ hF]
  refine deriv_zero_of_even (fun t => ?_)
  rw [Work.ConstructionInstance.rho_add_smul_eTheta x hr (-t),
    Work.ConstructionInstance.rho_add_smul_eTheta x hr t, neg_sq]

/-! ## The coordinate-line vanishing on the axis and on the plane -/

/-- On the axis (`radial x = 0`) and on the plane `x₃ = 0` (`axial x = 0`) the `i`-th coordinate
of the constructed vorticity vanishes along the `i`-th coordinate line through `x`, at every time
`t`.  Only the first conjunct `g z 0 = 0` of `VanishTheta` and `p ≠ 0` are used: on the axis the
`i`-th coordinate of `e_θ` vanishes at the shifted point, and in the plane the angle `θ` vanishes
at the shifted point (for `i ≠ 2`), where the profile vanishes, while for `i = 2` the axial
component of `e_θ` vanishes. -/
lemma selfSimVort_coord_line_eq_zero {p : ℝ} (hp : p ≠ 0) {g : ℝ → ℝ → ℝ}
    (hg0 : ∀ z : ℝ, g z 0 = 0) {L : ℝ} {lam : ℝ → ℝ} {x : R3}
    (hx : Work.Cyl.radial x = 0 ∨ Work.Cyl.axial x = 0) (i : Fin 3) (s t : ℝ) :
    (selfSimVort p g L lam (x + s • Work.Cyl.basisVec i) t) i = 0 := by
  have hcoord : (selfSimVort p g L lam (x + s • Work.Cyl.basisVec i) t) i
      = (lam t)⁻¹ * (Work.Stability.chi (Work.Cyl.rho (x + s • Work.Cyl.basisVec i) / L)
          * (profile p g (Work.Cyl.rho (x + s • Work.Cyl.basisVec i) ^ p / lam t)
              (Work.Cyl.theta (x + s • Work.Cyl.basisVec i))
            * (Work.Cyl.eTheta (x + s • Work.Cyl.basisVec i)).ofLp i)) := by
    rw [selfSimVort_apply, omegaSz_apply]
    simp only [PiLp.smul_apply, smul_eq_mul]
  calc (selfSimVort p g L lam (x + s • Work.Cyl.basisVec i) t) i
      = (lam t)⁻¹ * (Work.Stability.chi (Work.Cyl.rho (x + s • Work.Cyl.basisVec i) / L)
          * (profile p g (Work.Cyl.rho (x + s • Work.Cyl.basisVec i) ^ p / lam t)
              (Work.Cyl.theta (x + s • Work.Cyl.basisVec i))
            * (Work.Cyl.eTheta (x + s • Work.Cyl.basisVec i)).ofLp i)) := hcoord
    _ = 0 := by
        simp [selfSim_profile_eTheta_coord_eq_zero hp hg0 hx i s]

/-! ## The main theorem -/

theorem div_selfSimVort {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ}
    (hvt : Work.Spaces.VanishTheta g) (hsmooth : Work.Spaces.SmoothNbhd g) {L : ℝ} (hL : 0 < L)
    {lam : ℝ → ℝ} {t : ℝ} (ht : 0 < lam t) :
    ∀ x : Work.ConstructionInstance.R3,
      FiniteTimeSingularity.div
        (fun y => Work.ConstructionInstance.selfSimVort p g L lam y t) x = 0 := by
  intro x
  have hsf : Work.Stability.SmoothFar g := Work.Stability.SmoothFar.of_smoothNbhd hsmooth
  -- the field is the cut-off factor times the uncut self-similar swirl field
  have hfield : (fun y : R3 => selfSimVort p g L lam y t)
      = (fun y : R3 => Work.Stability.chi (Work.Cyl.rho y / L))
        • (fun y : R3 => (lam t)⁻¹ • omegaSz p g (Work.Cyl.rho y ^ p / lam t) y) := by
    funext y
    rw [selfSimVort_apply]
    exact smul_comm (lam t)⁻¹ (Work.Stability.chi (Work.Cyl.rho y / L))
      (omegaSz p g (Work.Cyl.rho y ^ p / lam t) y)
  by_cases hgen : 0 < Work.Cyl.radial x ∧ Work.Cyl.axial x ≠ 0
  · -- off the axis and off the plane: the cut swirl field
    have hr : 0 < Work.Cyl.radial x := hgen.1
    have hρpos : 0 < Work.Cyl.rho x := lt_of_lt_of_le hr (Work.Cyl.radial_le_rho x)
    have hθ0 : Work.Cyl.theta x ≠ 0 := by
      intro h
      have h1 : Work.Cyl.axial x / Work.Cyl.radial x = 0 := by
        rw [← Real.arctan_eq_zero_iff]
        exact h
      rcases div_eq_zero_iff.mp h1 with h2 | h2
      · exact hgen.2 h2
      · exact absurd h2 (ne_of_gt hr)
    have hz : -1 < Work.Cyl.rho x ^ p / lam t := by
      have hpos : 0 < Work.Cyl.rho x ^ p / lam t :=
        div_pos (Real.rpow_pos_of_pos hρpos p) ht
      linarith
    have hθmem : Work.Cyl.theta x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩
    have hF2 : Work.Cyl.DiffAt2 (profile p g) (Work.Cyl.rho x ^ p / lam t) (Work.Cyl.theta x) :=
      (contDiffAt_uncurry_profile hsf hz hθmem hθ0).differentiableAt (by norm_num)
    -- differentiability of the cut-off factor and of the uncut swirl field at `x`
    have hFdiff : DifferentiableAt ℝ
        (fun y : R3 => Work.Stability.chi (Work.Cyl.rho y / L)) x := by
      have hdiff : DifferentiableAt ℝ (fun y : R3 => Work.Cyl.rho y / L) x := by
        simpa only [div_eq_mul_inv] using
          (Work.Cyl.differentiableAt_rho_of_radial_pos x hr).mul_const L⁻¹
      exact ((Work.Stability.chi_contDiff.differentiable (by simp)).differentiableAt).comp x hdiff
    have hVdiff : DifferentiableAt ℝ
        (fun y : R3 => (lam t)⁻¹ • omegaSz p g (Work.Cyl.rho y ^ p / lam t) y) x := by
      have hA := selfSim_scalar_differentiableAt (p := p) (c := lam t) (g := g) hr hF2
      have hE := differentiableAt_eTheta x hr
      have heq : (fun y : R3 => (lam t)⁻¹ • omegaSz p g (Work.Cyl.rho y ^ p / lam t) y)
          = (fun y : R3 => (lam t)⁻¹ * profile p g (Work.Cyl.rho y ^ p / lam t)
              (Work.Cyl.theta y)) • Work.Cyl.eTheta := by
        funext y
        simp [omegaSz_apply, smul_smul]
      rw [heq]
      exact hA.smul hE
    have hdivV : FiniteTimeSingularity.div
        (fun y : R3 => (lam t)⁻¹ • omegaSz p g (Work.Cyl.rho y ^ p / lam t) y) x = 0 :=
      div_selfSim_field hp hp1 hvt hsf ht x
    rw [hfield]
    rw [div_smul_eq _ _ x hFdiff hVdiff]
    rw [hdivV, mul_zero, zero_add]
    -- the only remaining term is `(fderiv (χ(ρ/L)) x) (v x)`, and `v x` is parallel to `e_θ`
    rw [omegaSz_apply, smul_smul, map_smul]
    rw [fderiv_chi_rho_div_eTheta hr]
    exact smul_zero _
  · -- on the axis or on the plane: differentiate along the coordinate lines, or not at all
    have hcase : Work.Cyl.radial x = 0 ∨ Work.Cyl.axial x = 0 := by
      rcases not_and_or.mp hgen with h | h
      · exact Or.inl (le_antisymm (not_lt.mp h) (Work.Cyl.radial_nonneg x))
      · exact Or.inr (not_not.mp h)
    by_cases hd : DifferentiableAt ℝ (fun y : R3 => selfSimVort p g L lam y t) x
    · rw [Work.Cyl.div_eq_sum_partials (fun y : R3 => selfSimVort p g L lam y t) x hd]
      refine Finset.sum_eq_zero fun i _ => ?_
      have hline : (fun s : ℝ => ((fun y : R3 => selfSimVort p g L lam y t)
          (x + s • Work.Cyl.basisVec i)).ofLp i) = fun _ : ℝ => 0 :=
        funext fun s => selfSimVort_coord_line_eq_zero hp.ne' hvt.1 hcase i s t
      rw [hline]
      simp
    · rw [FiniteTimeSingularity.div, fderiv_zero_of_not_differentiableAt hd]
      simp

end

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.exists_profile_abs_le_mul_z =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- **The `F_*` part of the profile is `O(z)`**: for `0 < p ≤ 1`, `z ≥ 0` and `θ ∈ [0,π/2]`,

  `|F_*(z,θ)| ≤ 20 z`.

Indeed `F_*(z,θ) = p·(Γ(θ)/c(p))·2z/(1+z)²` with `Γ(θ) ≤ 1`, `c(p) ≥ 1/10` and
`2z/(1+z)² ≤ 2z` for `z ≥ 0`. -/
theorem Fstar_abs_le_mul_z {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {z : ℝ} (hz : 0 ≤ z)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Construction.Fstar p z θ| ≤ 20 * z := by
  have hc := (Work.Spaces.c_bounds p hp hp1).1
  have hcpos : 0 < Work.Spaces.c p := by linarith
  have hG := Work.Spaces.Gam_bounds p θ hp hθ
  have hden : (0 : ℝ) < (1 + z) ^ 2 := by positivity
  have hq0 : 0 ≤ Work.Spaces.Gam p θ / Work.Spaces.c p := div_nonneg hG.1 hcpos.le
  have hq1 : Work.Spaces.Gam p θ / Work.Spaces.c p ≤ 10 := by
    rw [div_le_iff₀ hcpos]; nlinarith [hG.2]
  have hfrac0 : 0 ≤ 2 * z / (1 + z) ^ 2 := by positivity
  have hfrac1 : 2 * z / (1 + z) ^ 2 ≤ 2 * z := by
    rw [div_le_iff₀ hden]
    nlinarith [sq_nonneg z, hz, sq_nonneg (1 + z)]
  have hpc : p * (Work.Spaces.Gam p θ / Work.Spaces.c p) ≤ 10 := by
    have := mul_le_mul hp1 hq1 hq0 (by norm_num : (0 : ℝ) ≤ 1)
    linarith
  have hval : Work.Construction.Fstar p z θ
      = p * (Work.Spaces.Gam p θ / Work.Spaces.c p) * (2 * z / (1 + z) ^ 2) := by
    rw [Work.Construction.Fstar, Work.FM.Fstar]
  rw [hval, abs_of_nonneg (mul_nonneg (mul_nonneg hp.le hq0) hfrac0)]
  calc p * (Work.Spaces.Gam p θ / Work.Spaces.c p) * (2 * z / (1 + z) ^ 2)
      ≤ 10 * (2 * z) := mul_le_mul hpc hfrac1 hfrac0 (by norm_num)
    _ = 20 * z := by ring

theorem exists_profile_abs_le_mul_z {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ}
    (hquad0 : ∀ θ : ℝ, g 0 θ = 0) (hsmooth : Work.Spaces.SmoothNbhd g) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℝ, z ∈ Set.Icc (0 : ℝ) 1 → ∀ θ : ℝ,
      |θ| ≤ Real.pi / 2 → |Work.ConstructionInstance.profile p g z θ| ≤ K * z := by
  have hsm2 : ContDiffOn ℝ 2 (Function.uncurry g)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)) := hsmooth.of_le (by norm_num)
  obtain ⟨K1, hK1, hK1b⟩ := g_z_linear_bound hquad0 hsm2
  refine ⟨K1 + 20, by linarith, ?_⟩
  intro z hz θ hθ
  have hz0 : 0 ≤ z := hz.1
  have hsplit : (K1 + 20) * z = K1 * z + 20 * z := by ring
  rw [hsplit]
  have hkey : ∀ φ : ℝ, φ ∈ Work.Spaces.Iθ →
      |Work.Construction.Fstar p z φ + g z φ| ≤ K1 * z + 20 * z := by
    intro φ hφ
    calc |Work.Construction.Fstar p z φ + g z φ|
        ≤ |Work.Construction.Fstar p z φ| + |g z φ| := abs_add_le _ _
      _ ≤ 20 * z + K1 * z :=
          add_le_add (Fstar_abs_le_mul_z hp hp1 hz0 hφ) (hK1b φ hφ z hz)
      _ = K1 * z + 20 * z := by ring
  rcases le_or_gt 0 θ with hθ0 | hθ0
  · have hθmem : θ ∈ Work.Spaces.Iθ :=
      ⟨hθ0, by rw [abs_of_nonneg hθ0] at hθ; exact hθ⟩
    rw [profile_of_nonneg hθ0]
    exact hkey θ hθmem
  · have hθmem : -θ ∈ Work.Spaces.Iθ :=
      ⟨by linarith, by rw [abs_of_neg hθ0] at hθ; exact hθ⟩
    rw [profile_of_neg (not_le.mpr hθ0), abs_neg]
    exact hkey (-θ) hθmem

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.exists_psiField_eq_biotSavart =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ConstructionInstance

open FiniteTimeSingularity MeasureTheory Filter
open scoped Topology

/-! ## The right half plane in `ℝ² = ℝ × ℝ` -/




/-! ## Derivatives of curried functions along the coordinate directions -/



/-! ## Derivatives of `p ↦ p.1 * f p.1 p.2` -/



/-! ## The scalar multiplication form of `fderiv` -/


/-! ## Symmetry of a bilinear form on `ℝ × ℝ` from its `(e₀,e₁)`-entry -/


/-! ## The Poincaré step: a primitive for the meridian 1-form -/



end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.hasDerivAt_selfSimVort_slice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- **The time slice of the constructed (cut) self-similar vorticity is differentiable in `t`.**

The cut field is `selfSimVort p g L lam x t = χ(ρ(x)/L) • U x t`, where
`U x t = λ̄(t)⁻¹ • omegaSz p g (ρ(x)^p/λ̄(t)) x` is the *uncut* self-similar field.  Since the
cut-off factor and the frame `e_θ(x)` do not depend on `t`, the derivative in `t` is obtained from
the scalar chain rule `hasDerivAt_inv_mul_comp` for `s ↦ λ̄(s)⁻¹ · F(c/λ̄(s))`; equivalently, the
field is `s ↦ (a * ((lam s)⁻¹ * profile p g (c / lam s) θ)) • e` for the constants
`a = χ(ρ(y)/L)`, `c = ρ(y)^p`, `θ = θ(y)` and the constant vector `e = e_θ(y)`.

On the symmetry axis (`radial y = 0`) the frame vector `e_θ(y)` vanishes, so the field is
identically `0`. -/
theorem hasDerivAt_selfSimVort_slice {p : ℝ} {g : ℝ → ℝ → ℝ} {L : ℝ} {lam : ℝ → ℝ} {T : ℝ}
    (hgdiff : ∀ z θ : ℝ, 0 < z →
      HasDerivAt (fun z' => Work.ConstructionInstance.profile p g z' θ)
        (Work.Spaces.pz (Work.ConstructionInstance.profile p g) z θ) z)
    (hlam : ∀ t ∈ Work.ConstructionInstance.preWindow T, 0 < lam t)
    (hlamdif : ∀ t ∈ Work.ConstructionInstance.preWindow T, HasDerivAt lam (deriv lam t) t)
    {t : ℝ} (ht : t ∈ Work.ConstructionInstance.preWindow T) (y : Work.ConstructionInstance.R3) :
    HasDerivAt (fun s : ℝ => Work.ConstructionInstance.selfSimVort p g L lam y s)
      (FiniteTimeSingularity.timeDeriv
        (Work.ConstructionInstance.selfSimVort p g L lam) y t) t := by
  have hlt : 0 < lam t := hlam t ht
  by_cases hrad : Work.Cyl.radial y = 0
  · -- on the symmetry axis the field vanishes identically
    have he0 : Work.Cyl.eTheta y = 0 := by
      rw [Work.Cyl.eTheta, hrad, div_zero, zero_smul]
    have hω0 : selfSimVort p g L lam y = fun _ => 0 := by
      funext s
      rw [selfSimVort_apply, omegaSz_apply, he0, smul_zero, smul_zero, smul_zero]
    rw [FiniteTimeSingularity.timeDeriv, hω0, deriv_const]
    exact hasDerivAt_const t 0
  · have hy : y ≠ 0 := by
      intro h0
      exact hrad (by rw [h0, Work.Cyl.radial_eq_zero_iff]; exact ⟨rfl, rfl⟩)
    have hρpos : 0 < Work.Cyl.rho y := by rw [Work.Cyl.rho_pos_iff]; exact hy
    set c : ℝ := Work.Cyl.rho y ^ p with hc
    set θ : ℝ := Work.Cyl.theta y with hθdef
    set e : R3 := Work.Cyl.eTheta y with he
    set a : ℝ := Work.Stability.chi (Work.Cyl.rho y / L) with ha
    have hcpos : 0 < c := by rw [hc]; exact Real.rpow_pos_of_pos hρpos p
    have hzpos : 0 < c / lam t := div_pos hcpos hlt
    -- the scalar chain rule for `s ↦ λ̄(s)⁻¹ · F(c/λ̄(s))`
    have hφ : HasDerivAt (fun s => (lam s)⁻¹ * profile p g (c / lam s) θ)
        (-(deriv lam t * (profile p g (c / lam t) θ
          + (c / lam t) * Work.Spaces.pz (profile p g) (c / lam t) θ) / (lam t) ^ 2)) t :=
      hasDerivAt_inv_mul_comp (F := fun z' => profile p g z' θ) (hlamdif t ht) (ne_of_gt hlt)
        (hgdiff (c / lam t) θ hzpos)
    -- the cut field is `χ(ρ(y)/L) = a` times the uncut scalar part, along the constant vector `e`
    have hcut : selfSimVort p g L lam y
        = fun s => (a * ((lam s)⁻¹ * profile p g (c / lam s) θ)) • e := by
      funext s
      rw [selfSimVort_apply, ← ha, omegaSz_apply, ← hc, ← hθdef, ← he]
      rw [smul_smul, smul_smul]
      congr 1
      ring
    have hderivG : HasDerivAt (selfSimVort p g L lam y)
        ((a * (-(deriv lam t * (profile p g (c / lam t) θ
          + (c / lam t) * Work.Spaces.pz (profile p g) (c / lam t) θ)
            / (lam t) ^ 2))) • e) t := by
      rw [hcut]
      exact (hφ.const_mul a).smul_const e
    rw [FiniteTimeSingularity.timeDeriv, hderivG.deriv]
    exact hderivG

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.holder_gComp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Set Metric
open scoped Topology

namespace Work.ConstructionInstance

/-! ## Elementary metric and trigonometric facts -/

/-- `ρ = ‖·‖` is `1`-Lipschitz on `ℝ³`. -/
lemma abs_rho_sub_rho_le_dist (x y : R3) :
    |Work.Cyl.rho x - Work.Cyl.rho y| ≤ dist x y := by
  rw [Work.Cyl.rho_eq_norm x, Work.Cyl.rho_eq_norm y, dist_eq_norm]
  exact abs_norm_sub_norm_le x y

/-- `max ρ ≤ min ρ + dist`. -/
lemma max_rho_le_min_rho_add_dist (x y : R3) :
    max (Work.Cyl.rho x) (Work.Cyl.rho y)
      ≤ min (Work.Cyl.rho x) (Work.Cyl.rho y) + dist x y := by
  have h := abs_rho_sub_rho_le_dist x y
  rcases le_total (Work.Cyl.rho x) (Work.Cyl.rho y) with hle | hle
  · have h' : -(Work.Cyl.rho x - Work.Cyl.rho y) ≤ dist x y := by
      rw [abs_of_nonpos (by linarith : Work.Cyl.rho x - Work.Cyl.rho y ≤ 0)] at h
      exact h
    rw [min_eq_left hle, max_eq_right hle]
    linarith
  · have h' : Work.Cyl.rho x - Work.Cyl.rho y ≤ dist x y := by
      rw [abs_of_nonneg (by linarith : 0 ≤ Work.Cyl.rho x - Work.Cyl.rho y)] at h
      exact h
    rw [min_eq_right hle, max_eq_left hle]
    linarith

/-- `|θ x| ∈ [0, π/2]`. -/
lemma abs_theta_mem_Iθ (x : R3) : |Work.Cyl.theta x| ∈ Work.Spaces.Iθ := by
  refine ⟨abs_nonneg _, ?_⟩
  rw [abs_le]
  exact ⟨le_of_lt (Real.neg_pi_div_two_lt_arctan _), le_of_lt (Real.arctan_lt_pi_div_two _)⟩

/-! ## `rpow` arithmetic -/

/-- For `1 ≤ a ≤ b` and `0 < s ≤ 1`: `b^s - a^s ≤ s (b - a)`. -/
lemma rpow_sub_le_mul_of_one_le {s a b : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (ha : 1 ≤ a) (hab : a ≤ b) : b ^ s - a ^ s ≤ s * (b - a) := by
  have ha0 : 0 < a := lt_of_lt_of_le one_pos ha
  have h := rpow_sub_le_mul hs hs1 ha0 hab
  have h1 : a ^ (s - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ha (by linarith)
  calc b ^ s - a ^ s ≤ s * a ^ (s - 1) * (b - a) := h
    _ ≤ s * 1 * (b - a) := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        exact mul_le_mul_of_nonneg_left h1 hs.le
    _ = s * (b - a) := by ring

/-- Two-sided form: for `a, b ≥ 1` and `0 < s ≤ 1`, `|a^s - b^s| ≤ s |a - b|`. -/
lemma abs_rpow_sub_le_mul_of_one_le {s a b : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (ha : 1 ≤ a) (hb : 1 ≤ b) : |a ^ s - b ^ s| ≤ s * |a - b| := by
  rcases le_total a b with h | h
  · have hle : a ^ s ≤ b ^ s := Real.rpow_le_rpow (by linarith) h hs.le
    have h' := rpow_sub_le_mul_of_one_le hs hs1 ha h
    rw [abs_of_nonpos (by linarith : a ^ s - b ^ s ≤ 0),
      abs_of_nonpos (by linarith : a - b ≤ 0)]
    linarith
  · have hle : b ^ s ≤ a ^ s := Real.rpow_le_rpow (by linarith) h hs.le
    have h' := rpow_sub_le_mul_of_one_le hs hs1 hb h
    rw [abs_of_nonneg (by linarith : 0 ≤ a ^ s - b ^ s),
      abs_of_nonneg (by linarith : 0 ≤ a - b)]
    linarith

/-- The near-origin radial bound: for `2d ≤ ρ` and `d ≤ 1`, `ρ^{3α}/ρ · d ≤ 2^{3α-1} d^α`. -/
lemma rho_pow_div_mul_le {α ρ d : ℝ} (hα : 0 < α) (h31 : 3 * α ≤ 1) (hd : 0 < d) (hd1 : d ≤ 1)
    (hρd : 2 * d ≤ ρ) : ρ ^ (3 * α) / ρ * d ≤ 2 ^ (3 * α - 1) * d ^ α := by
  have hρ : 0 < ρ := lt_of_lt_of_le (by linarith) hρd
  have h1 : 3 * α - 1 ≤ 0 := by linarith
  calc ρ ^ (3 * α) / ρ * d = ρ ^ (3 * α - 1) * d := by
        rw [Real.rpow_sub_one hρ.ne']
    _ ≤ (2 * d) ^ (3 * α - 1) * d := by
        apply mul_le_mul_of_nonneg_right _ hd.le
        exact Real.rpow_le_rpow_of_nonpos (by linarith) hρd h1
    _ = 2 ^ (3 * α - 1) * (d ^ (3 * α - 1) * d) := by
        rw [Real.mul_rpow (by norm_num) hd.le]
        ring
    _ = 2 ^ (3 * α - 1) * d ^ (3 * α) := by
        rw [← Real.rpow_add_one hd.ne']
        congr 1
        ring
    _ ≤ 2 ^ (3 * α - 1) * d ^ α := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)
        exact Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)

/-! ## Two elementary inequalities between the three quantities `ρ x`, `ρ y`, `dist x y` -/

lemma abs_sub_le_abs_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  have := abs_add_le a (-b)
  simpa [sub_eq_add_neg] using this

/-! ## The main theorem -/

/-- The perturbation composite `ĝ : x ↦ g (ρ x ^ (3α)) (|θ x|)` is `α`-Hölder on `ℝ³`.

Scalar core of `holder_omegaS_of_data`: on the closed half space `x₃ ≥ 0` the self-similar
vorticity is `ω x = (3α / c(3α)) • omegaStar α x + ĝ x • e_θ x` (the first term by
`Gamma_mul_Fstar_eq_Aom`), so this Hölder bound (together with the vanishing bound
`gComp_abs_le`) is what `holder_smul_eTheta` consumes for the perturbation.

Intended proof (all constants may depend on `α`, `Cv`, `Lg`, `Lθ` and a free `δ > 0`):

* WLOG `x₃, y₃ ≥ 0` (both `ρ x ^ (3α)` and `|θ x|` are even in `x₃`), and WLOG `‖x-y‖ < 1`
  (`|g| ≤ Cv` from `hvan` and `Γ ≤ 1` gives the trivial bound otherwise).
* `hsm` (`C²` on an open set containing `[0,δ]×[0,π/2]`), `hquad0`, `hquad1` and `hvt` give
  uniform Taylor bounds for `0 ≤ z ≤ δ`, `θ ∈ [0,π/2]`:
  `|g z θ| ≤ K z²`, `|∂_θ g (z,θ)| ≤ K z²`, `|∂_z g (z,θ)| ≤ K z`
  (`g(0,θ) = 0` makes `∂_θ g (0,θ) = 0`, and `∂_z g (0,θ) = 0` makes `∂_z ∂_θ g (0,θ) = 0`).
* `z = ρ^{3α}` is `(3α)`-Hölder and, on `ρ ≥ δ`, `3αδ^{3α-1}`-Lipschitz (`3α ≤ 1`); `θ` has
  `|∇θ| = 1/ρ` off the axis, while `g z 0 = g z (π/2) = 0` kills the axis/plane singularities
  (`|π/2 - |θ|| = arcsin (r/ρ) ≤ 2r/ρ`, `||θ|| = arccos (r/ρ)`); `r = Cyl.radial`, `ρ = Cyl.rho`.
* split on `d = ‖x-y‖ ≤ ρ_min/2` (`ρ_min = min (ρ x) (ρ y)`) vs `d > ρ_min/2`:
  for `d > ρ_min/2` one has `ρ_max < 3d` so the sup bound `|ĝ| ≤ Cv` (far from the origin) resp.
  `|ĝ| ≤ K ρ^{6α}` (near the origin) closes it; for `d ≤ ρ_min/2` bound
  `|ĝ x - ĝ y| ≤ Lg |z x - z y|^α + Lθ |θ x - θ y|^α` (using `hzk`, `hzth` at the intermediate
  points), with the local gradients (`ρ ≥ ρ_min/2` on the segment) giving
  `|Δz| ≤ 3α ρ_min^{3α-1} d ≤ C d` resp. `|Δθ| ≤ C d/ρ_min ≤ C d` — and for `ρ_min ≤ δ`
  replacing the radial part by the Taylor bound `K ρ_min^{6α-1} d`. -/
theorem holder_gComp {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1/3) {g : ℝ → ℝ → ℝ}
    {Cv Lg Lθ : ℝ} (hCv : 0 ≤ Cv) (hLg : 0 ≤ Lg) (hLθ : 0 ≤ Lθ)
    (hvt : Work.Spaces.VanishTheta g)
    (hquad0 : ∀ θ : ℝ, g 0 θ = 0)
    (hquad1 : ∀ θ : ℝ, Work.Spaces.pz g 0 θ = 0)
    (hvan : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ| ≤ Cv * Work.ConstructionInstance.Gamma α θ)
    (hzk : ∀ z z' θ : ℝ, 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ →
      |g z θ - g z' θ| ≤ Lg * |z - z'| ^ α)
    (hzth : ∀ z θ θ' : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
      |g z θ - g z θ'| ≤ Lθ * |θ - θ'| ^ α)
    (hsm : ContDiffOn ℝ 2 (Function.uncurry g)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1))) :
    Holder ⟨α, hα.le⟩ (fun x : R3 => g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|)) := by
  have h3α : 0 < 3 * α := by linarith
  have h3α1 : 3 * α ≤ 1 := by linarith
  -- the Taylor bounds at the origin, and the resulting slice-Lipschitz bounds
  obtain ⟨K, hK0, hK⟩ := g_taylor_bounds hsm hquad0 hquad1
  have hzK : ∀ z θ : ℝ, 0 ≤ z → z ≤ 2 → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.pz g z θ| ≤ K * z :=
    fun z θ hz h2 hθ => (hK z θ hz h2 hθ).2.1
  have hthK : ∀ z θ : ℝ, 0 ≤ z → z ≤ 2 → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.pth g z θ| ≤ K * z :=
    fun z θ hz h2 hθ => (hK z θ hz h2 hθ).2.2
  obtain ⟨hslicez, hsliceθ⟩ := g_slice_lipschitz hsm hzK hthK
  -- the two global bounds of the composite
  have hsup : ∀ z : R3, |g (Work.Cyl.rho z ^ (3 * α)) (psi z)| ≤ Cv := by
    intro z
    have hθ := psi_mem_Iθ z
    have h1 := hvan (Work.Cyl.rho z ^ (3 * α)) (psi z)
      (Real.rpow_nonneg (Work.Cyl.rho_nonneg z) _) hθ
    have h2 : Gamma α (psi z) ≤ 1 := Gamma_le_one hα.le hθ
    have h3 : 0 ≤ Gamma α (psi z) := Gamma_nonneg hθ
    nlinarith [hCv]
  have hquadbound : ∀ z : R3, Work.Cyl.rho z ≤ 2 →
      |g (Work.Cyl.rho z ^ (3 * α)) (psi z)| ≤ K * (Work.Cyl.rho z) ^ (6 * α) := by
    intro z hz
    have hρ0 := Work.Cyl.rho_nonneg z
    have hZ0 : 0 ≤ Work.Cyl.rho z ^ (3 * α) := Real.rpow_nonneg hρ0 _
    have hZ2 : Work.Cyl.rho z ^ (3 * α) ≤ 2 := by
      calc Work.Cyl.rho z ^ (3 * α) ≤ 2 ^ (3 * α) := Real.rpow_le_rpow hρ0 hz h3α.le
        _ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h3α1
        _ = 2 := Real.rpow_one 2
    have h1 := (hK _ _ hZ0 hZ2 (psi_mem_Iθ z)).1
    have h2 : (Work.Cyl.rho z ^ (3 * α)) ^ 2 = (Work.Cyl.rho z) ^ (6 * α) := by
      rw [← Real.rpow_natCast (Work.Cyl.rho z ^ (3 * α)) 2, ← Real.rpow_mul hρ0]
      congr 1
      ring
    calc |g (Work.Cyl.rho z ^ (3 * α)) (psi z)|
        ≤ K * (Work.Cyl.rho z ^ (3 * α)) ^ 2 := h1
      _ = K * (Work.Cyl.rho z) ^ (6 * α) := by rw [h2]
  -- the Hölder constant
  set C : ℝ := 2 * Cv + (2 * Cv * (3/2) ^ α
      + (2 * K * 3 ^ (6 * α) + ((Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α)
      + (K * (3/2) * 3 ^ α * (3/2) ^ (2 * α)
      + K * (3/2) ^ (3 * α) * (4 * Real.pi) * 2 ^ (3 * α - 1))))) with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  have hC1 : 2 * Cv ≤ C := by
    rw [hCdef]
    linarith [show (0:ℝ) ≤ 2 * Cv * (3/2) ^ α
      + (2 * K * 3 ^ (6 * α) + ((Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α)
      + (K * (3/2) * 3 ^ α * (3/2) ^ (2 * α)
      + K * (3/2) ^ (3 * α) * (4 * Real.pi) * 2 ^ (3 * α - 1)))) by positivity]
  have hC2 : 2 * Cv * (3/2) ^ α ≤ C := by
    rw [hCdef]
    linarith [show (0:ℝ) ≤ 2 * Cv
      + (2 * K * 3 ^ (6 * α) + ((Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α)
      + (K * (3/2) * 3 ^ α * (3/2) ^ (2 * α)
      + K * (3/2) ^ (3 * α) * (4 * Real.pi) * 2 ^ (3 * α - 1)))) by positivity]
  have hC3 : 2 * K * 3 ^ (6 * α) ≤ C := by
    rw [hCdef]
    linarith [show (0:ℝ) ≤ 2 * Cv
      + (2 * Cv * (3/2) ^ α + ((Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α)
      + (K * (3/2) * 3 ^ α * (3/2) ^ (2 * α)
      + K * (3/2) ^ (3 * α) * (4 * Real.pi) * 2 ^ (3 * α - 1)))) by positivity]
  have hC4 : Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α ≤ C := by
    rw [hCdef]
    linarith [show (0:ℝ) ≤ 2 * Cv + (2 * Cv * (3/2) ^ α + (2 * K * 3 ^ (6 * α)
      + (K * (3/2) * 3 ^ α * (3/2) ^ (2 * α)
      + K * (3/2) ^ (3 * α) * (4 * Real.pi) * 2 ^ (3 * α - 1)))) by positivity]
  have hC5 : K * (3/2) * 3 ^ α * (3/2) ^ (2 * α) ≤ C := by
    rw [hCdef]
    linarith [show (0:ℝ) ≤ 2 * Cv + (2 * Cv * (3/2) ^ α + (2 * K * 3 ^ (6 * α)
      + ((Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α)
      + K * (3/2) ^ (3 * α) * (4 * Real.pi) * 2 ^ (3 * α - 1)))) by positivity]
  have hC6 : K * (3/2) ^ (3 * α) * (4 * Real.pi) * 2 ^ (3 * α - 1) ≤ C := by
    rw [hCdef]
    linarith [show (0:ℝ) ≤ 2 * Cv + (2 * Cv * (3/2) ^ α + (2 * K * 3 ^ (6 * α)
      + ((Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α)
      + K * (3/2) * 3 ^ α * (3/2) ^ (2 * α)))) by positivity]
  have hC56 : K * (3/2) ^ (3 * α) * (4 * Real.pi) * 2 ^ (3 * α - 1)
      + K * (3/2) * 3 ^ α * (3/2) ^ (2 * α) ≤ C := by
    rw [hCdef]
    linarith [show (0:ℝ) ≤ 2 * Cv + (2 * Cv * (3/2) ^ α + (2 * K * 3 ^ (6 * α)
      + (Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α))) by positivity]
  refine ⟨⟨C, hCnn⟩, ?_⟩
  refine Work.Stability.holderWith_of_dist_le (fun x y => ?_)
  rw [Real.dist_eq, g_psi_eq hquad0 hvt x, g_psi_eq hquad0 hvt y]
  show |g (Work.Cyl.rho x ^ (3 * α)) (psi x) - g (Work.Cyl.rho y ^ (3 * α)) (psi y)|
      ≤ C * dist x y ^ α
  by_cases hxy : x = y
  · subst hxy
    simp only [dist_self, sub_self, abs_zero]
    positivity
  have hdpos : 0 < dist x y := dist_pos.mpr hxy
  have hdnn : 0 ≤ dist x y := dist_nonneg
  have htri : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := abs_sub_le_abs_add
  rcases le_or_gt 1 (dist x y) with hd1 | hd1
  · -- far away (or exactly at distance one): the sup bound suffices
    have h1 : (1 : ℝ) ≤ dist x y ^ α := Real.one_le_rpow hd1 hα.le
    calc |g (Work.Cyl.rho x ^ (3 * α)) (psi x) - g (Work.Cyl.rho y ^ (3 * α)) (psi y)|
        ≤ |g (Work.Cyl.rho x ^ (3 * α)) (psi x)|
          + |g (Work.Cyl.rho y ^ (3 * α)) (psi y)| := htri _ _
      _ ≤ 2 * Cv := by linarith [hsup x, hsup y]
      _ ≤ C * dist x y ^ α := by
          calc 2 * Cv ≤ C := hC1
            _ = C * 1 := by ring
            _ ≤ C * dist x y ^ α := by
                simpa using mul_le_mul_of_nonneg_left h1 hCnn
  · rcases le_or_gt (min (Work.Cyl.rho x) (Work.Cyl.rho y)) (2 * dist x y) with hfar | hnear
    · -- the radii are not large compared with `d`: use the two pointwise bounds
      have hmax3 : max (Work.Cyl.rho x) (Work.Cyl.rho y) ≤ 3 * dist x y := by
        have := max_rho_le_min_rho_add_dist x y
        linarith
      by_cases hsmall : max (Work.Cyl.rho x) (Work.Cyl.rho y) ≤ 2
      · -- both radii at most two: the quadratic vanishing of `g` at `z = 0`
        have hρx2 : Work.Cyl.rho x ≤ 2 := le_trans (le_max_left _ _) hsmall
        have hρy2 : Work.Cyl.rho y ≤ 2 := le_trans (le_max_right _ _) hsmall
        have hρx3 : Work.Cyl.rho x ≤ 3 * dist x y := le_trans (le_max_left _ _) hmax3
        have hρy3 : Work.Cyl.rho y ≤ 3 * dist x y := le_trans (le_max_right _ _) hmax3
        have hpow : dist x y ^ (6 * α) ≤ dist x y ^ α :=
          Real.rpow_le_rpow_of_exponent_ge hdpos (le_of_lt hd1) (by linarith)
        calc |g (Work.Cyl.rho x ^ (3 * α)) (psi x) - g (Work.Cyl.rho y ^ (3 * α)) (psi y)|
            ≤ |g (Work.Cyl.rho x ^ (3 * α)) (psi x)|
              + |g (Work.Cyl.rho y ^ (3 * α)) (psi y)| := htri _ _
          _ ≤ K * (Work.Cyl.rho x) ^ (6 * α) + K * (Work.Cyl.rho y) ^ (6 * α) :=
              add_le_add (hquadbound x hρx2) (hquadbound y hρy2)
          _ ≤ K * (3 * dist x y) ^ (6 * α) + K * (3 * dist x y) ^ (6 * α) := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left
                  (Real.rpow_le_rpow (Work.Cyl.rho_nonneg x) hρx3 (by linarith)) hK0
              · exact mul_le_mul_of_nonneg_left
                  (Real.rpow_le_rpow (Work.Cyl.rho_nonneg y) hρy3 (by linarith)) hK0
          _ = 2 * K * 3 ^ (6 * α) * dist x y ^ (6 * α) := by
              rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hdnn]; ring
          _ ≤ 2 * K * 3 ^ (6 * α) * dist x y ^ α :=
              mul_le_mul_of_nonneg_left hpow (by positivity)
          _ ≤ C * dist x y ^ α := by
              exact mul_le_mul_of_nonneg_right hC3 (Real.rpow_nonneg hdnn α)
      · -- both radii large: then `d > 2/3` and the sup bound suffices
        have hd23 : 2 / 3 ≤ dist x y := by
          have := max_rho_le_min_rho_add_dist x y
          linarith [not_le.mp hsmall, hfar]
        have h1 : (1 : ℝ) ≤ (3 / 2) ^ α * dist x y ^ α := by
          have h2 : (3 / 2 : ℝ) ^ α * (2 / 3) ^ α = 1 := by
            rw [← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3 / 2) (by norm_num : (0:ℝ) ≤ 2 / 3),
              show (3:ℝ)/2 * (2/3) = 1 by ring, Real.one_rpow]
          have h3 : (2 / 3 : ℝ) ^ α ≤ dist x y ^ α :=
            Real.rpow_le_rpow (by norm_num) hd23 hα.le
          have h4 : 0 ≤ (3 / 2 : ℝ) ^ α := Real.rpow_nonneg (by norm_num) _
          calc (1 : ℝ) = (3 / 2 : ℝ) ^ α * (2 / 3) ^ α := h2.symm
            _ ≤ (3 / 2 : ℝ) ^ α * dist x y ^ α := mul_le_mul_of_nonneg_left h3 h4
        calc |g (Work.Cyl.rho x ^ (3 * α)) (psi x) - g (Work.Cyl.rho y ^ (3 * α)) (psi y)|
            ≤ |g (Work.Cyl.rho x ^ (3 * α)) (psi x)|
              + |g (Work.Cyl.rho y ^ (3 * α)) (psi y)| := htri _ _
          _ ≤ 2 * Cv := by linarith [hsup x, hsup y]
          _ = 2 * Cv * 1 := by ring
          _ ≤ 2 * Cv * ((3 / 2) ^ α * dist x y ^ α) :=
              mul_le_mul_of_nonneg_left h1 (by linarith)
          _ = 2 * Cv * (3 / 2) ^ α * dist x y ^ α := by ring
          _ ≤ C * dist x y ^ α := by
              exact mul_le_mul_of_nonneg_right hC2 (Real.rpow_nonneg hdnn α)
    · -- close together and away from the origin
      have hρmin2d : 2 * dist x y < min (Work.Cyl.rho x) (Work.Cyl.rho y) := hnear
      have hρminpos : 0 < min (Work.Cyl.rho x) (Work.Cyl.rho y) :=
        lt_of_lt_of_le (by linarith [dist_nonneg (x := x) (y := y)]) (le_of_lt hρmin2d)
      have hminx : min (Work.Cyl.rho x) (Work.Cyl.rho y) ≤ Work.Cyl.rho x := min_le_left _ _
      have hminy : min (Work.Cyl.rho x) (Work.Cyl.rho y) ≤ Work.Cyl.rho y := min_le_right _ _
      have hρxmax : Work.Cyl.rho x ≤ max (Work.Cyl.rho x) (Work.Cyl.rho y) := le_max_left _ _
      have hρymax : Work.Cyl.rho y ≤ max (Work.Cyl.rho x) (Work.Cyl.rho y) := le_max_right _ _
      have hmax32 : max (Work.Cyl.rho x) (Work.Cyl.rho y)
          ≤ 3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2 := by
        have := max_rho_le_min_rho_add_dist x y
        linarith
      have hpsi : |psi x - psi y|
          ≤ 4 * Real.pi * dist x y / min (Work.Cyl.rho x) (Work.Cyl.rho y) :=
        psi_sub_le x y hρminpos hminx hminy
      have hpsi_nn : 0 ≤ |psi x - psi y| := abs_nonneg _
      have hZx0 : 0 ≤ Work.Cyl.rho x ^ (3 * α) := Real.rpow_nonneg (Work.Cyl.rho_nonneg x) _
      have hZy0 : 0 ≤ Work.Cyl.rho y ^ (3 * α) := Real.rpow_nonneg (Work.Cyl.rho_nonneg y) _
      have hsplit : |g (Work.Cyl.rho x ^ (3 * α)) (psi x)
            - g (Work.Cyl.rho y ^ (3 * α)) (psi y)|
          ≤ |g (Work.Cyl.rho x ^ (3 * α)) (psi x) - g (Work.Cyl.rho x ^ (3 * α)) (psi y)|
            + |g (Work.Cyl.rho x ^ (3 * α)) (psi y)
                - g (Work.Cyl.rho y ^ (3 * α)) (psi y)| := by
        have := abs_add_le
          (g (Work.Cyl.rho x ^ (3 * α)) (psi x) - g (Work.Cyl.rho x ^ (3 * α)) (psi y))
          (g (Work.Cyl.rho x ^ (3 * α)) (psi y) - g (Work.Cyl.rho y ^ (3 * α)) (psi y))
        rwa [show g (Work.Cyl.rho x ^ (3 * α)) (psi x)
              - g (Work.Cyl.rho x ^ (3 * α)) (psi y)
            + (g (Work.Cyl.rho x ^ (3 * α)) (psi y) - g (Work.Cyl.rho y ^ (3 * α)) (psi y))
            = g (Work.Cyl.rho x ^ (3 * α)) (psi x)
              - g (Work.Cyl.rho y ^ (3 * α)) (psi y) from by ring] at this
      by_cases hB1 : 1 ≤ min (Work.Cyl.rho x) (Work.Cyl.rho y)
      · -- both points at radius at least one: `hzk`/`hzth` and the Lipschitz bound for `psi`
        have hρx1 : 1 ≤ Work.Cyl.rho x := le_trans hB1 hminx
        have hρy1 : 1 ≤ Work.Cyl.rho y := le_trans hB1 hminy
        have hZd : |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)| ≤ 3 * α * dist x y := by
          calc |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)|
              ≤ 3 * α * |Work.Cyl.rho x - Work.Cyl.rho y| :=
                abs_rpow_sub_le_mul_of_one_le h3α h3α1 hρx1 hρy1
            _ ≤ 3 * α * dist x y :=
                mul_le_mul_of_nonneg_left (abs_rho_sub_rho_le_dist x y) h3α.le
        have hdψ : |psi x - psi y| ≤ 4 * Real.pi * dist x y := by
          rw [le_div_iff₀ hρminpos] at hpsi
          have h1 : |psi x - psi y|
              ≤ |psi x - psi y| * min (Work.Cyl.rho x) (Work.Cyl.rho y) :=
            le_mul_of_one_le_right (abs_nonneg _) hB1
          linarith
        calc |g (Work.Cyl.rho x ^ (3 * α)) (psi x) - g (Work.Cyl.rho y ^ (3 * α)) (psi y)|
            ≤ |g (Work.Cyl.rho x ^ (3 * α)) (psi x) - g (Work.Cyl.rho x ^ (3 * α)) (psi y)|
              + |g (Work.Cyl.rho x ^ (3 * α)) (psi y)
                  - g (Work.Cyl.rho y ^ (3 * α)) (psi y)| := hsplit
          _ ≤ Lθ * |psi x - psi y| ^ α + Lg * |Work.Cyl.rho x ^ (3 * α)
                - Work.Cyl.rho y ^ (3 * α)| ^ α :=
              add_le_add (hzth _ _ _ hZx0 (psi_mem_Iθ x) (psi_mem_Iθ y))
                (hzk _ _ _ hZx0 hZy0 (psi_mem_Iθ y))
          _ ≤ Lθ * (4 * Real.pi * dist x y) ^ α + Lg * (3 * α * dist x y) ^ α := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left
                  (Real.rpow_le_rpow hpsi_nn hdψ hα.le) hLθ
              · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hZd hα.le) hLg
          _ = (Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α) * dist x y ^ α := by
              rw [Real.mul_rpow (by positivity : (0:ℝ) ≤ 4 * Real.pi) hdnn,
                Real.mul_rpow (by linarith : (0:ℝ) ≤ 3 * α) hdnn]
              ring
          _ ≤ C * dist x y ^ α := by
              exact mul_le_mul_of_nonneg_right hC4 (Real.rpow_nonneg hdnn α)
      · -- both points at radius below one: the slice bounds of the Taylor expansion
        have hρmin1 : min (Work.Cyl.rho x) (Work.Cyl.rho y) < 1 := lt_of_not_ge hB1
        have hmax2 : max (Work.Cyl.rho x) (Work.Cyl.rho y) ≤ 2 := by linarith
        have hρx32 : Work.Cyl.rho x ≤ 3 / 2 := by
          have := le_trans hρxmax hmax32
          linarith
        have hρy32 : Work.Cyl.rho y ≤ 3 / 2 := by
          have := le_trans hρymax hmax32
          linarith
        have hZx2 : Work.Cyl.rho x ^ (3 * α) ≤ 2 := by
          calc Work.Cyl.rho x ^ (3 * α) ≤ (2 : ℝ) ^ (3 * α) :=
                Real.rpow_le_rpow (Work.Cyl.rho_nonneg x) (le_trans hρxmax hmax2) h3α.le
            _ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h3α1
            _ = 2 := Real.rpow_one 2
        have hZy2 : Work.Cyl.rho y ^ (3 * α) ≤ 2 := by
          calc Work.Cyl.rho y ^ (3 * α) ≤ (2 : ℝ) ^ (3 * α) :=
                Real.rpow_le_rpow (Work.Cyl.rho_nonneg y) (le_trans hρymax hmax2) h3α.le
            _ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h3α1
            _ = 2 := Real.rpow_one 2
        have hZx32 : Work.Cyl.rho x ^ (3 * α) ≤ 3 / 2 := by
          calc Work.Cyl.rho x ^ (3 * α) ≤ (3 / 2 : ℝ) ^ (3 * α) :=
                Real.rpow_le_rpow (Work.Cyl.rho_nonneg x) hρx32 h3α.le
            _ ≤ (3 / 2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h3α1
            _ = 3 / 2 := Real.rpow_one (3 / 2)
        have hZy32 : Work.Cyl.rho y ^ (3 * α) ≤ 3 / 2 := by
          calc Work.Cyl.rho y ^ (3 * α) ≤ (3 / 2 : ℝ) ^ (3 * α) :=
                Real.rpow_le_rpow (Work.Cyl.rho_nonneg y) hρy32 h3α.le
            _ ≤ (3 / 2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h3α1
            _ = 3 / 2 := Real.rpow_one (3 / 2)
        have hmaxZ : max (Work.Cyl.rho x ^ (3 * α)) (Work.Cyl.rho y ^ (3 * α)) ≤ 3 / 2 :=
          max_le hZx32 hZy32
        have hZxle : Work.Cyl.rho x ^ (3 * α)
            ≤ (3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2) ^ (3 * α) :=
          Real.rpow_le_rpow (Work.Cyl.rho_nonneg x) (le_trans hρxmax hmax32) h3α.le
        have hZd : |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)|
            ≤ 3 ^ α * (3 / 2) ^ (2 * α) * dist x y ^ α :=
          A0_rho_pow_diff (β := α) hα (le_trans hα13 (by norm_num)) (Work.Cyl.rho_nonneg x)
            (Work.Cyl.rho_nonneg y) hρx32 hρy32 (abs_rho_sub_rho_le_dist x y)
        have hzslice := hslicez (Work.Cyl.rho x ^ (3 * α)) (Work.Cyl.rho y ^ (3 * α)) (psi y)
          hZx0 hZx2 hZy0 hZy2 (psi_mem_Iθ y)
        have hθslice := hsliceθ (Work.Cyl.rho x ^ (3 * α)) (psi x) (psi y)
          hZx0 hZx2 (psi_mem_Iθ x) (psi_mem_Iθ y)
        -- the two gradient steps
        have hstep1 : K * (Work.Cyl.rho x ^ (3 * α)) * |psi x - psi y|
            ≤ K * ((3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2) ^ (3 * α)
              * (4 * Real.pi * dist x y / min (Work.Cyl.rho x) (Work.Cyl.rho y))) := by
          have h1 : K * (Work.Cyl.rho x ^ (3 * α))
              ≤ K * (3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2) ^ (3 * α) :=
            mul_le_mul_of_nonneg_left hZxle hK0
          calc K * (Work.Cyl.rho x ^ (3 * α)) * |psi x - psi y|
              ≤ K * (3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2) ^ (3 * α)
                * |psi x - psi y| := mul_le_mul_of_nonneg_right h1 hpsi_nn
            _ = K * ((3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2) ^ (3 * α)
                * |psi x - psi y|) := by ring
            _ ≤ K * ((3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2) ^ (3 * α)
                * (4 * Real.pi * dist x y / min (Work.Cyl.rho x) (Work.Cyl.rho y))) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ K)
                exact mul_le_mul_of_nonneg_left hpsi (by positivity)
        have hstep2 : K * max (Work.Cyl.rho x ^ (3 * α)) (Work.Cyl.rho y ^ (3 * α))
              * |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)|
            ≤ K * ((3 / 2) * (3 ^ α * (3 / 2) ^ (2 * α) * dist x y ^ α)) := by
          have h1 : K * max (Work.Cyl.rho x ^ (3 * α)) (Work.Cyl.rho y ^ (3 * α))
              ≤ K * (3 / 2) := mul_le_mul_of_nonneg_left hmaxZ hK0
          calc K * max (Work.Cyl.rho x ^ (3 * α)) (Work.Cyl.rho y ^ (3 * α))
                * |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)|
              ≤ K * (3 / 2) * |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)| :=
                mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
            _ = K * ((3 / 2) * |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)|) := by ring
            _ ≤ K * ((3 / 2) * (3 ^ α * (3 / 2) ^ (2 * α) * dist x y ^ α)) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ K)
                exact mul_le_mul_of_nonneg_left hZd (by positivity)
        have hstep1' : (3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2) ^ (3 * α)
              * (4 * Real.pi * dist x y / min (Work.Cyl.rho x) (Work.Cyl.rho y))
            ≤ (3 / 2) ^ (3 * α) * 4 * Real.pi * (2 ^ (3 * α - 1) * dist x y ^ α) := by
          have h1 : (3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2) ^ (3 * α)
              = (3 / 2) ^ (3 * α) * min (Work.Cyl.rho x) (Work.Cyl.rho y) ^ (3 * α) := by
            rw [show 3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2
                = 3 / 2 * min (Work.Cyl.rho x) (Work.Cyl.rho y) by ring,
              Real.mul_rpow (by norm_num) hρminpos.le]
          rw [h1]
          have h2 := rho_pow_div_mul_le hα h3α1 hdpos (le_of_lt hd1) (le_of_lt hρmin2d)
          have h3 : (3 / 2) ^ (3 * α) * min (Work.Cyl.rho x) (Work.Cyl.rho y) ^ (3 * α)
                * (4 * Real.pi * dist x y / min (Work.Cyl.rho x) (Work.Cyl.rho y))
              = (3 / 2) ^ (3 * α) * 4 * Real.pi
                * (min (Work.Cyl.rho x) (Work.Cyl.rho y) ^ (3 * α)
                  / min (Work.Cyl.rho x) (Work.Cyl.rho y) * dist x y) := by ring
          rw [h3]
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
        calc |g (Work.Cyl.rho x ^ (3 * α)) (psi x) - g (Work.Cyl.rho y ^ (3 * α)) (psi y)|
            ≤ |g (Work.Cyl.rho x ^ (3 * α)) (psi x) - g (Work.Cyl.rho x ^ (3 * α)) (psi y)|
              + |g (Work.Cyl.rho x ^ (3 * α)) (psi y)
                  - g (Work.Cyl.rho y ^ (3 * α)) (psi y)| := hsplit
          _ ≤ K * (Work.Cyl.rho x ^ (3 * α)) * |psi x - psi y|
              + K * max (Work.Cyl.rho x ^ (3 * α)) (Work.Cyl.rho y ^ (3 * α))
                * |Work.Cyl.rho x ^ (3 * α) - Work.Cyl.rho y ^ (3 * α)| :=
              add_le_add hθslice hzslice
          _ ≤ K * ((3 * min (Work.Cyl.rho x) (Work.Cyl.rho y) / 2) ^ (3 * α)
                * (4 * Real.pi * dist x y / min (Work.Cyl.rho x) (Work.Cyl.rho y)))
              + K * ((3 / 2) * (3 ^ α * (3 / 2) ^ (2 * α) * dist x y ^ α)) :=
              add_le_add hstep1 hstep2
          _ ≤ K * ((3 / 2) ^ (3 * α) * 4 * Real.pi * (2 ^ (3 * α - 1) * dist x y ^ α))
              + K * ((3 / 2) * (3 ^ α * (3 / 2) ^ (2 * α) * dist x y ^ α)) := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left hstep1' hK0
              · exact le_refl _
          _ = (K * (3 / 2) ^ (3 * α) * (4 * Real.pi) * 2 ^ (3 * α - 1)
                + K * (3 / 2) * 3 ^ α * (3 / 2) ^ (2 * α)) * dist x y ^ α := by ring_nf
          _ ≤ C * dist x y ^ α :=
              mul_le_mul_of_nonneg_right hC56 (Real.rpow_nonneg hdnn α)

end Work.ConstructionInstance
end
end
-- ===== merged: Submission.Work.ConstructionInstance.profile_continuousAt_pi_half =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Filter Topology Set
open scoped Topology

namespace Work.ConstructionInstance

/-- **Continuity of the profile at `θ = π/2`.**

Near `θ = π/2` the sign condition `0 ≤ θ` holds everywhere (as `π/2 > 0`), so the odd
extension defining `profile` never uses its negative branch there: `profile p g` agrees, on a
neighbourhood of `(z, π/2)`, with `F_*(z,θ) + g(z,θ)`.  Both summands are continuous there —
`g` because `SmoothNbhd g` is smoothness on an *open* neighbourhood of the quadrant, and
`F_*` because it is the product of the smooth radial factor `Work.FM.Fstar` with the angular
factor `Γ(θ) = (sin θ · cos²θ)^{p/3}`, which is continuous at `θ = π/2` since the base vanishes
there and the exponent `p/3` is positive (`Real.continuousAt_rpow_const` at base `0`). -/
theorem profile_continuousAt_pi_half {p : ℝ} (hp : 0 < p) {g : ℝ → ℝ → ℝ}
    (hvt : Work.Spaces.VanishTheta g) (hsmooth : Work.Spaces.SmoothNbhd g) {z : ℝ}
    (hz : -1 < z) :
    ContinuousAt (Function.uncurry (Work.ConstructionInstance.profile p g)) (z, Real.pi / 2) := by
  have _ := hvt
  -- `(z, π/2)` lies in the open neighbourhood on which `g` is smooth.
  have hset : (z, Real.pi / 2) ∈ Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1) := by
    refine ⟨hz, by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  -- Continuity of `g` at `(z, π/2)` from smoothness on the open set.
  have hgcont : ContinuousAt (Function.uncurry g) (z, Real.pi / 2) :=
    hsmooth.continuousOn.continuousAt
      ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds hset)
  -- Continuity of the angular factor `Γ(θ) = (sin θ cos²θ)^{p/3}` at `θ = π/2`.
  have hbase : ContinuousAt (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) (Real.pi / 2) :=
    (Real.continuous_sin.continuousAt).mul ((Real.continuous_cos.continuousAt).pow 2)
  have hGam : ContinuousAt (fun θ : ℝ => Work.Spaces.Gam p θ) (Real.pi / 2) := by
    have h := hbase.rpow continuousAt_const (Or.inr (by positivity : (0:ℝ) < p / 3))
    simpa [Work.Spaces.Gam] using h
  -- Continuity of the smooth radial factor `z ↦ 2z/(1+z)²` at `z`.
  have hFz : ContinuousAt (fun z : ℝ => Work.FM.Fstar z) z :=
    (Work.FM.hasDerivAt_Fstar z hz).continuousAt
  -- Continuity of the uncurried `F_*` at `(z, π/2)`.
  have hFcont : ContinuousAt (fun q : ℝ × ℝ => Work.Construction.Fstar p q.1 q.2)
      (z, Real.pi / 2) := by
    have h1 : ContinuousAt (fun q : ℝ × ℝ => Work.Spaces.Gam p q.2) (z, Real.pi / 2) :=
      ContinuousAt.comp (f := fun q : ℝ × ℝ => q.2) (x := (z, Real.pi / 2)) hGam
        continuous_snd.continuousAt
    have h2 : ContinuousAt (fun q : ℝ × ℝ => Work.Spaces.Gam p q.2 / Work.Spaces.c p)
        (z, Real.pi / 2) := h1.div_const _
    have h3 : ContinuousAt (fun q : ℝ × ℝ => Work.FM.Fstar q.1) (z, Real.pi / 2) :=
      ContinuousAt.comp (f := fun q : ℝ × ℝ => q.1) (x := (z, Real.pi / 2)) hFz
        continuous_fst.continuousAt
    have h4 : ContinuousAt
        (fun q : ℝ × ℝ => p * (Work.Spaces.Gam p q.2 / Work.Spaces.c p) * Work.FM.Fstar q.1)
        (z, Real.pi / 2) := (continuousAt_const.mul h2).mul h3
    simpa [Work.Construction.Fstar] using h4
  have hcomb : ContinuousAt
      (fun q : ℝ × ℝ => Work.Construction.Fstar p q.1 q.2 + g q.1 q.2) (z, Real.pi / 2) :=
    hFcont.add hgcont
  -- On the neighbourhood `{θ > 0}` the profile uses its positive branch.
  have hU : {q : ℝ × ℝ | (0:ℝ) < q.2} ∈ 𝓝 (z, Real.pi / 2) :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds (by norm_num [Real.pi_pos])
  have hEv : Function.uncurry (Work.ConstructionInstance.profile p g) =ᶠ[𝓝 (z, Real.pi / 2)]
      (fun q : ℝ × ℝ => Work.Construction.Fstar p q.1 q.2 + g q.1 q.2) := by
    filter_upwards [hU] with q hq
    exact profile_of_nonneg (le_of_lt hq)
  exact hcomb.congr hEv.symm

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.profile_continuousAt_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- **Continuity of the profile at `θ = 0`.**  For `0 < p`, a perturbation `g` vanishing on the
angular boundaries (`VanishTheta`) and smooth near the closed quadrant (`SmoothNbhd`), the profile
`F = F_* + g` (extended oddly in `θ`) is continuous at `(z,0)` for every `z > -1`.

Both branches of the odd extension agree at `θ = 0` because `F_*(z,0) = Γ(0)·… = 0` (`p ≠ 0`) and
`g z 0 = 0`; the reflected branch `θ ↦ -(F_*(z,-θ) + g(z,-θ))` is continuous as the composition of
the (continuous) reflection `θ ↦ -θ` with the profile.  Only the *restricted* continuity of the two
branches is used, on the closed halves `{θ ≥ 0}` and `{θ ≤ 0}`, which cover the plane. -/
theorem profile_continuousAt_zero {p : ℝ} (hp : 0 < p) {g : ℝ → ℝ → ℝ}
    (hvt : Work.Spaces.VanishTheta g) (hsmooth : Work.Spaces.SmoothNbhd g) {z : ℝ}
    (hz : -1 < z) :
    ContinuousAt (Function.uncurry (Work.ConstructionInstance.profile p g)) (z, 0) := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hg0 : ∀ z' : ℝ, g z' 0 = 0 := hvt.1
  have hF0 : ∀ z' : ℝ, Work.Construction.Fstar p z' 0 = 0 :=
    fun z' => Fstar_zero_theta hp0 z'
  -- The "positive branch" `A(z,θ) = F_*(z,θ) + g(z,θ)` is continuous at `(z,0)`.
  have hGam : Continuous (fun q : ℝ × ℝ => Work.Spaces.Gam p q.2) := by
    unfold Work.Spaces.Gam
    exact (Real.continuous_rpow_const (by positivity : (0 : ℝ) ≤ p / 3)).comp
      ((Real.continuous_sin.comp continuous_snd).mul
        ((Real.continuous_cos.comp continuous_snd).pow 2))
  have hFst : ContinuousAt (fun q : ℝ × ℝ => Work.FM.Fstar q.1) (z, 0) :=
    ContinuousAt.comp (x := (z, 0)) (g := Work.FM.Fstar) (f := fun q : ℝ × ℝ => q.1)
      (Work.FM.hasDerivAt_Fstar z hz).continuousAt
      (continuous_fst.continuousAt : ContinuousAt (fun q : ℝ × ℝ => q.1) (z, 0))
  have hFcont : ContinuousAt (fun q : ℝ × ℝ => Work.Construction.Fstar p q.1 q.2) (z, 0) :=
    ((continuousAt_const.mul (hGam.continuousAt.div_const (Work.Spaces.c p))).mul hFst)
  have hgcont : ContinuousAt (fun q : ℝ × ℝ => g q.1 q.2) (z, 0) :=
    hsmooth.continuousOn.continuousAt
      ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds
        ⟨hz, by constructor <;> linarith [Real.pi_pos]⟩)
  have hAcont : ContinuousAt
      (fun q : ℝ × ℝ => Work.Construction.Fstar p q.1 q.2 + g q.1 q.2) (z, 0) :=
    hFcont.add hgcont
  -- The reflection `q ↦ (q.1, -q.2)`.
  have hPhicont : Continuous (fun q : ℝ × ℝ => (q.1, -q.2)) := by fun_prop
  -- The reflected branch `q ↦ -(F_*(q) + g(q))` (with the sign flip) is continuous at `(z,0)`.
  have hnegcont : ContinuousAt
      (fun q : ℝ × ℝ => -(Work.Construction.Fstar p q.1 (-q.2) + g q.1 (-q.2))) (z, 0) := by
    have hA0 : ContinuousAt
        (fun q : ℝ × ℝ => Work.Construction.Fstar p q.1 q.2 + g q.1 q.2) (z, -0) := by
      simpa using hAcont
    have hcomp := ContinuousAt.comp (x := (z, 0))
      (g := fun q : ℝ × ℝ => Work.Construction.Fstar p q.1 q.2 + g q.1 q.2)
      (f := fun q : ℝ × ℝ => (q.1, -q.2)) hA0 hPhicont.continuousAt
    have hrefl : ((fun q : ℝ × ℝ => Work.Construction.Fstar p q.1 q.2 + g q.1 q.2)
        ∘ (fun q : ℝ × ℝ => (q.1, -q.2)))
        = fun q : ℝ × ℝ => Work.Construction.Fstar p q.1 (-q.2) + g q.1 (-q.2) := by
      ext q; rfl
    rw [hrefl] at hcomp
    exact hcomp.neg
  -- The profile equals `A` on the closed half `{θ ≥ 0}`.
  have hs1 : ContinuousWithinAt (Function.uncurry (profile p g))
      {q : ℝ × ℝ | 0 ≤ q.2} (z, 0) :=
    hAcont.continuousWithinAt.congr
      (fun y hy => profile_of_nonneg hy)
      (profile_of_nonneg le_rfl)
  -- The profile equals `-(A ∘ reflect)` on the closed half `{θ ≤ 0}`.
  have hs2 : ContinuousWithinAt (Function.uncurry (profile p g))
      {q : ℝ × ℝ | q.2 ≤ 0} (z, 0) := by
    refine hnegcont.continuousWithinAt.congr (fun y hy => ?_) ?_
    · obtain ⟨a, b⟩ := y
      by_cases h : 0 ≤ b
      · have hb : b = 0 := le_antisymm hy h
        subst hb
        rw [Function.uncurry_apply_pair, profile_of_nonneg (le_refl (0 : ℝ)), hF0 a, hg0 a]
        simp [hF0 a, hg0 a]
      · exact profile_of_neg h
    · rw [Function.uncurry_apply_pair, profile_of_nonneg (le_refl (0 : ℝ)), hF0 z, hg0 z]
      simp [hF0 z, hg0 z]
  have hcover : {q : ℝ × ℝ | 0 ≤ q.2} ∪ {q : ℝ × ℝ | q.2 ≤ 0} = Set.univ := by
    ext q
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact le_total 0 q.2
  have hunion : ContinuousWithinAt (Function.uncurry (profile p g))
      ({q : ℝ × ℝ | 0 ≤ q.2} ∪ {q : ℝ × ℝ | q.2 ≤ 0}) (z, 0) :=
    continuousWithinAt_union.mpr ⟨hs1, hs2⟩
  rw [hcover] at hunion
  exact (continuousWithinAt_univ _ _).1 hunion

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.HkIntegrand_radial_sin =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cert

theorem HkIntegrand_radial_sin (α : ℝ) (k : ℕ) (R : ℝ → ℝ) (z θ : ℝ)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α k (fun z θ => R z * Real.sin (2 * θ)) z θ
      = Work.FTS.EllipticEst.Cert.HkExp α k R z θ := by
  rw [Work.Spaces.HkIntegrand, HkExp]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Work.FTS.EllipticEst.DzIter_fstarSin_eq]
    exact Work.FTS.EllipticEst.FstarHkOpen.zTerm_eq_on (Work.FTS.EllipticEst.radIter R i z)
      z θ hθ
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [if_pos hc, if_pos hc, Work.FTS.EllipticEst.mixed_fstarSin_eq]
      exact Work.FTS.EllipticEst.FstarHkOpen.mixedTerm_eq_on α
        (Work.FTS.EllipticEst.radIter R j z) z (Work.FTS.EllipticEst.sinProf i) θ hθ
    · rw [if_neg hc, if_neg hc]

end Work.FTS.EllipticEst.Cert
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.integral_HkExp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert

/-- Linearity of the integral over `Iθ` against a *fixed* angular profile `f`, for a finite
sum whose coefficients are independent of `θ`. -/
lemma integral_sum_mul_const (s : Finset ℕ) (c : ℕ → ℝ) (f : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, ∑ i ∈ s, c i * f θ)
      = (∑ i ∈ s, c i) * ∫ θ in Work.Spaces.Iθ, f θ := by
  have hfun : (fun θ => ∑ i ∈ s, c i * f θ) = fun θ => (∑ i ∈ s, c i) * f θ := by
    funext θ; exact (Finset.sum_mul s c (f θ)).symm
  rw [hfun, integral_const_mul]

/-- Linearity of the integral over `Iθ` for a finite sum of `if p i then c i * f θ else 0`,
where the proposition `p i` does not depend on `θ`: the sum can be integrated termwise. -/
lemma integral_sum_ite_mul_const (s : Finset ℕ) (p : ℕ → Prop) [DecidablePred p]
    (c : ℕ → ℝ) (f : ℝ → ℝ) (hf : IntegrableOn f Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, ∑ i ∈ s, (if p i then c i * f θ else 0))
      = ∑ i ∈ s, (if p i then c i * (∫ θ in Work.Spaces.Iθ, f θ) else 0) := by
  rw [MeasureTheory.integral_finset_sum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hp : p i
    · simp only [hp, ite_true]; rw [integral_const_mul]
    · simp only [hp]; simp
  · intro i _
    by_cases hp : p i
    · simp only [hp]; exact hf.integrable.const_mul _
    · simp only [hp]; exact integrable_zero _ _ _

/-- The two-index version of `integral_sum_ite_mul_const`: a double finite sum whose
`(i,j)`-term is `if p i j then c i j * g i θ else 0`, with the angular profile `g i`
depending only on the outer index. -/
lemma integral_sum2_ite_mul_const (s : Finset ℕ) (p : ℕ → ℕ → Prop) [DecidableRel p]
    (c : ℕ → ℕ → ℝ) (g : ℕ → ℝ → ℝ) (hg : ∀ i, IntegrableOn (g i) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, ∑ i ∈ s, ∑ j ∈ s, (if p i j then c i j * g i θ else 0))
      = ∑ i ∈ s, ∑ j ∈ s, (if p i j then c i j * (∫ θ in Work.Spaces.Iθ, g i θ) else 0) := by
  rw [MeasureTheory.integral_finset_sum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_sum_ite_mul_const s (p i) (c i) (g i) (hg i)]
  · intro i _
    refine integrable_finset_sum _ fun j _ => ?_
    by_cases hp : p i j
    · simp only [hp]; exact (hg i).integrable.const_mul _
    · simp only [hp]; exact integrable_zero _ _ _

/-- The purely algebraic rearrangement used at the end of `integral_HkExp`: the explicit
`θ`-integral of the separated `ℋ^k`-integrand equals `W` times the boxed separated
expression, with the radial weight `W` pulled out of both sums and the coefficients of the
second (mixed) double sum moved next to the angular integrals. -/
lemma HkExp_algebra (S : Finset ℕ) (W Z : ℝ) (a A : ℕ → ℝ) (p : ℕ → ℕ → Prop)
    [DecidableRel p] :
    (∑ i ∈ S, a i * W) * Z + ∑ i ∈ S, ∑ j ∈ S, (if p i j then a j * W * A i else 0)
      = W * (Z * ∑ i ∈ S, a i + ∑ i ∈ S, ∑ j ∈ S, (if p i j then a j else 0) * A i) := by
  have h1 : (∑ i ∈ S, a i * W) * Z = W * (Z * ∑ i ∈ S, a i) := by
    rw [← Finset.sum_mul]; ring
  have hinner : ∀ i, (∑ j ∈ S, (if p i j then a j * W * A i else 0))
      = W * ((∑ j ∈ S, (if p i j then a j else 0)) * A i) := by
    intro i
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hp : p i j <;> simp [hp] <;> ring
  have h2 : (∑ i ∈ S, ∑ j ∈ S, (if p i j then a j * W * A i else 0))
      = W * (∑ i ∈ S, (∑ j ∈ S, (if p i j then a j else 0)) * A i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => hinner i
  rw [h1, h2]
  simp only [Finset.sum_mul]
  ring

theorem integral_HkExp (α : ℝ) (k : ℕ) (R : ℝ → ℝ) (z : ℝ)
    (hZ : MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.Cert.angZ θ)
      Work.Spaces.Iθ)
    (hA : ∀ i : ℕ, MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.FTS.EllipticEst.Cert.angA α i θ) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Cert.HkExp α k R z θ)
      = (Work.Spaces.w z) ^ 2 *
          ((∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Cert.angZ θ)
              * (∑ i ∈ Finset.range (k + 1),
                  (Work.FTS.EllipticEst.radIter R i z) ^ 2)
            + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                (if 1 ≤ i ∧ i + j ≤ k then
                    (Work.FTS.EllipticEst.radIter R j z) ^ 2 else 0)
                  * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Cert.angA α i θ)) := by
  simp only [HkExp]
  have hI1 : Integrable (fun θ : ℝ => ∑ i ∈ Finset.range (k + 1),
      (Work.FTS.EllipticEst.radIter R i z) ^ 2 * (Work.Spaces.w z) ^ 2 * angZ θ)
      (volume.restrict Work.Spaces.Iθ) := by
    refine integrable_finset_sum _ fun i _ => ?_
    exact hZ.const_mul _
  have hI2 : Integrable (fun θ : ℝ => ∑ i ∈ Finset.range (k + 1),
      ∑ j ∈ Finset.range (k + 1),
      if 1 ≤ i ∧ i + j ≤ k then
        (Work.FTS.EllipticEst.radIter R j z) ^ 2 * (Work.Spaces.w z) ^ 2 * angA α i θ
      else 0)
      (volume.restrict Work.Spaces.Iθ) := by
    refine integrable_finset_sum _ fun i _ => ?_
    refine integrable_finset_sum _ fun j _ => ?_
    by_cases hp : 1 ≤ i ∧ i + j ≤ k
    · simp only [hp]; exact (hA i).const_mul _
    · simp only [hp]; exact integrable_zero _ _ _
  rw [MeasureTheory.integral_add hI1 hI2]
  rw [integral_sum_mul_const]
  rw [integral_sum2_ite_mul_const _ (fun i j => 1 ≤ i ∧ i + j ≤ k) _ _ (fun i => hA i)]
  exact HkExp_algebra _ _ _ _ _ _

end Work.FTS.EllipticEst.Cert
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.DzAmgm.Scratch =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.DzAmgm

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Step 1: the identity between the two forms of the pure angular weight -/

/-- On the angular interval `Iθ`, the pure summand of `HkIntegrand` written with the division
`w z / sin(2θ)^{η/2}` equals the same summand written with the product `w z · angZ θ`
(`angZ θ = sin(2θ)^{-η/2}`).  At the two endpoints both sides vanish. -/
theorem mul_angZ_eq_mul_div (z θ x : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    x * Work.Spaces.w z * angZ θ
      = x * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) := by
  rcases eq_or_ne (Real.sin (2 * θ)) 0 with h | h
  · have hη : ((-(Work.Spaces.eta / 2)) : ℝ) ≠ 0 := by
      rw [Work.Spaces.eta]; norm_num
    have hη2 : ((Work.Spaces.eta / 2) : ℝ) ≠ 0 := by
      rw [Work.Spaces.eta]; norm_num
    have hzero : angZ θ = 0 := by rw [angZ, h, Real.zero_rpow hη]
    rw [hzero, mul_zero, h, Real.zero_rpow hη2, div_zero, mul_zero]
  · have hnn : 0 ≤ Real.sin (2 * θ) := by
      rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
      exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    rw [angZ, div_eq_mul_inv, Real.rpow_neg hnn]
    ring

/-! ## Step 2: a.e. strong measurability of the `z`-slices -/

/-- The `z`-slice of a function continuous on the open quadrant is a.e. strongly measurable on
`Iz = [0,∞)`. -/
theorem aesm_zs (g : ℝ × ℝ → ℝ)
    (hg : ContinuousOn g (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    MeasureTheory.AEStronglyMeasurable (fun z => g (z, θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hcont : ContinuousOn (fun z : ℝ => g (z, θ)) (Set.Ioi 0) :=
    hg.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun z hz => ⟨hz, hθ⟩)
  have h1 : MeasureTheory.AEStronglyMeasurable (fun z : ℝ => g (z, θ))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    hcont.aestronglyMeasurable measurableSet_Ioi
  have hset : (Set.Ioi (0 : ℝ)) =ᵐ[MeasureTheory.volume] Work.Spaces.Iz := by
    rw [Work.Spaces.Iz]; exact MeasureTheory.Ioi_ae_eq_Ici
  have hmeas : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.restrict_congr_set hset.symm
  rw [hmeas]
  exact h1

/-! ## Step 3: splitting a finite sum out of the double `lintegral` -/

/-- **Splitting a finite sum of summands continuous on the open quadrant.**  For a finite family
of real functions continuous on `Q0`, the double (`θ`-then-`z`) `lintegral` of the finite sum of
their `ofReal`-lifts is the sum of the individual double `lintegral`s.  Both `ℒ²`-measurability
inputs come from the continuity on `Q0` (the `z`-slices for the inner integral and the joint
a.e. strong measurability for the partial `θ`-integral). -/
theorem lintegral_sum_split {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℝ → ℝ)
    (hF : ∀ m ∈ s, ContinuousOn (fun p : ℝ × ℝ => F m p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz, ∑ m ∈ s, ENNReal.ofReal (F m z θ))
      = ∑ m ∈ s, ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal (F m z θ) := by
  classical
  -- a.e. angle in the open interval
  have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
    have hset : MeasureTheory.volume.restrict Work.Spaces.Iθ
        = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
      refine MeasureTheory.Measure.restrict_congr_set ?_
      rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc.symm
    rw [hset]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
  -- the inner integral splits for a.e. angle
  have hsplit : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (∫⁻ z in Work.Spaces.Iz, ∑ m ∈ s, ENNReal.ofReal (F m z θ))
        = ∑ m ∈ s, ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (F m z θ) := by
    filter_upwards [hae] with θ hθ
    exact MeasureTheory.lintegral_finsetSum' s fun m hm =>
      ((aesm_zs _ (hF m hm) hθ).aemeasurable.ennreal_ofReal)
  -- the partial `z`-integrals are a.e. strongly measurable in `θ`
  have hθmeas : ∀ m ∈ s, AEMeasurable
      (fun θ => ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (F m z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro m hm
    have huncurry : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (F m p.1 p.2))
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      ((Work.Spaces.aesm_of_continuousOn_Qd _ (hF m hm)).aemeasurable).ennreal_ofReal
    exact huncurry.lintegral_prod_left'
  rw [MeasureTheory.lintegral_congr_ae hsplit]
  exact MeasureTheory.lintegral_finsetSum' s hθmeas

/-! ## Step 4: domain conversions -/

theorem lintegral_Iθ_eq_Ioo (f : ℝ → ℝ≥0∞) :
    ∫⁻ θ in Work.Spaces.Iθ, f θ = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), f θ := by
  have h : MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2))
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm
  rw [Work.Spaces.Iθ, h]

theorem lintegral_Iz_eq_Ioi (f : ℝ → ℝ≥0∞) :
    ∫⁻ z in Work.Spaces.Iz, f z = ∫⁻ z in Set.Ioi (0 : ℝ), f z := by
  have h : MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioi_ae_eq_Ici.symm
  rw [Work.Spaces.Iz, h]

/-- The double integral over `Iθ × Iz` equals the double integral over the open quadrant
(angular variable first). -/
theorem lintegral_prod_eq_open (F : ℝ → ℝ → ℝ≥0∞) :
    (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz, F θ z)
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ), F θ z := by
  rw [lintegral_Iθ_eq_Ioo]
  refine lintegral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  exact lintegral_Iz_eq_Ioi _

/-- The reverse direction of the previous lemma. -/
theorem lintegral_open_eq_prod (F : ℝ → ℝ → ℝ≥0∞) :
    (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ), F θ z)
      = ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz, F θ z :=
  (lintegral_prod_eq_open F).symm

/-- The pure summand in the `angZ`-form equals the summand of `HkIntegrand` (division form). -/
theorem pure_ofReal_eq (f : ℝ → ℝ → ℝ) (m : ℕ) (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    ENNReal.ofReal ((Work.Spaces.DzIter m f z θ * Work.Spaces.w z * angZ θ) ^ 2)
      = ENNReal.ofReal ((Work.Spaces.DzIter m f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
  have h1 : Work.Spaces.DzIter m f z θ * Work.Spaces.w z * angZ θ
      = Work.Spaces.DzIter m f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) :=
    mul_angZ_eq_mul_div z θ (Work.Spaces.DzIter m f z θ) hθ
  have h2 : (Work.Spaces.DzIter m f z θ * Work.Spaces.w z * angZ θ) ^ 2
      = (Work.Spaces.DzIter m f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [h1]
  rw [h2]

/-- The mixed summand in the `w · angM`-form equals the summand of `HkIntegrand` (using `Wt`). -/
theorem mixed_ofReal_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (i j : ℕ) (z θ : ℝ) :
    ENNReal.ofReal ((Work.Spaces.mixed j i f z θ * Work.Spaces.w z * angM α θ) ^ 2)
      = ENNReal.ofReal ((Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
  have h1 : Work.Spaces.mixed j i f z θ * Work.Spaces.w z * angM α θ
      = Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ := by
    rw [mul_assoc]; rfl
  have h2 : (Work.Spaces.mixed j i f z θ * Work.Spaces.w z * angM α θ) ^ 2
      = (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
    rw [h1]
  rw [h2]

/-! ## Step 5: the termwise Agmon–Nirenberg estimate -/

/-- **Termwise AM–GM, pure summands.**  Applying `TermAMGMLintegral` with `V = D_z^m f`,
`wth = angZ` and rewriting `D_z (D_z^m f) = D_z^{m+1} f`,
`z²∂_z²(D_z^m f) = D_z^m (z²∂_z²f)` (`ZsqPz2Comm`) gives the termwise estimate for `TZ`. -/
theorem TZ_termwise (C1 : ℝ) (hC1 : 0 < C1)
    (hgen : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ), SmoothOpen V →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ wth θ) →
      ENNReal.ofReal (α ^ 2) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2))
        ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))
            + (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2)))) :
    ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (f : ℝ → ℝ → ℝ), SmoothOpen f → ∀ (m : ℕ),
      ENNReal.ofReal (α ^ 2) * TZ f (m + 1)
        ≤ ENNReal.ofReal (C1 ^ 2) *
            (ENNReal.ofReal (α ^ 4) * TZ (zsqPz2 f) m + TZ f m) := by
  intro α hα hα1 f hf m
  have hang : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ angZ θ := fun θ hθ =>
    angZ_nonneg_of_mem (by rw [Work.Spaces.Iθ]; exact ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have h := hgen α hα hα1 (Work.Spaces.DzIter m f) angZ (hf.DzIter m) hang
  -- the first factor of the left-hand integrand
  have hL : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.Dz (Work.Spaces.DzIter m f) z θ * Work.Spaces.w z
          * angZ θ) ^ 2))
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.DzIter (m + 1) f z θ * Work.Spaces.w z * angZ θ) ^ 2) := by
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    rw [Work.Spaces.DzIter_succ]
  -- the second-derivative factor of the right-hand side
  have hR2 : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter m f) z θ
          * Work.Spaces.w z * angZ θ) ^ 2))
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.DzIter m (zsqPz2 f) z θ * Work.Spaces.w z * angZ θ) ^ 2) := by
    refine lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    refine lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    have hcomm := ZsqPz2Comm f hf m 0 (show (z, θ) ∈ Q0 from ⟨hz, hθ⟩)
    have h1 : z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter m f) z θ
        = Work.Spaces.DzIter m (zsqPz2 f) z θ := hcomm
    rw [h1]
  rw [hL, hR2] at h
  rw [lintegral_open_eq_prod] at h
  rw [lintegral_open_eq_prod] at h
  rw [lintegral_open_eq_prod] at h
  exact h

/-- **Termwise AM–GM, mixed summands.**  Applying `TermAMGMLintegral` with
`V = D_z^j D_θ^i f`, `wth = angM α` and rewriting `D_z (D_z^j D_θ^i f) = D_z^{j+1} D_θ^i f`,
`z²∂_z²(D_z^j D_θ^i f) = D_z^j D_θ^i (z²∂_z²f)` (`ZsqPz2Comm`) gives the termwise estimate. -/
theorem TM_termwise (C1 : ℝ) (hC1 : 0 < C1)
    (hgen : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ), SmoothOpen V →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ wth θ) →
      ENNReal.ofReal (α ^ 2) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2))
        ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))
            + (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2)))) :
    ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (f : ℝ → ℝ → ℝ), SmoothOpen f → ∀ (i j : ℕ),
      ENNReal.ofReal (α ^ 2) * TM α f i (j + 1)
        ≤ ENNReal.ofReal (C1 ^ 2) *
            (ENNReal.ofReal (α ^ 4) * TM α (zsqPz2 f) i j + TM α f i j) := by
  intro α hα hα1 f hf i j
  have hang : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ angM α θ := fun θ hθ =>
    angM_nonneg_of_mem (by rw [Work.Spaces.Iθ]; exact ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have h := hgen α hα hα1 (Work.Spaces.mixed j i f) (angM α) (hf.mixed j i) hang
  have hL : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.Dz (Work.Spaces.mixed j i f) z θ * Work.Spaces.w z
          * angM α θ) ^ 2))
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.mixed (j + 1) i f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    have hdz : Work.Spaces.Dz (Work.Spaces.mixed j i f)
        = Work.Spaces.mixed (j + 1) i f := by
      simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ]
    rw [hdz]
    exact mixed_ofReal_eq α f i (j + 1) z θ
  have hR2 : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.mixed j i f) z θ
          * Work.Spaces.w z * angM α θ) ^ 2))
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.mixed j i (zsqPz2 f) z θ * Work.Spaces.Wt α z θ) ^ 2) := by
    refine lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    refine lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    have hcomm := ZsqPz2Comm f hf j i (show (z, θ) ∈ Q0 from ⟨hz, hθ⟩)
    have h1 : z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.mixed j i f) z θ
        = Work.Spaces.mixed j i (zsqPz2 f) z θ := hcomm
    rw [h1, mixed_ofReal_eq α (zsqPz2 f) i j z θ]
  have hR3 : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.mixed j i f z θ * Work.Spaces.w z * angM α θ) ^ 2))
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    exact mixed_ofReal_eq α f i j z θ
  rw [hL, hR2, hR3] at h
  rw [lintegral_open_eq_prod] at h
  rw [lintegral_open_eq_prod] at h
  rw [lintegral_open_eq_prod] at h
  exact h

/-! ## Step 6: the pure/mixed parts of `HkIntegrand` -/

/-- The pure (`D_z`-) part of `HkIntegrand α k g`, as a real function. -/
def purePart (g : ℝ → ℝ → ℝ) (k : ℕ) (z θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i g z θ
    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2

/-- The mixed part of `HkIntegrand α k g`, as a real function. -/
def mixedPart (α : ℝ) (g : ℝ → ℝ → ℝ) (k : ℕ) (z θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
    (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2
      else 0)

theorem HkIntegrand_eq_parts (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k g z θ = purePart g k z θ + mixedPart α g k z θ := rfl

theorem purePart_nonneg (g : ℝ → ℝ → ℝ) (k : ℕ) (z θ : ℝ) : 0 ≤ purePart g k z θ :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

theorem mixedPart_nonneg (α : ℝ) (g : ℝ → ℝ → ℝ) (k : ℕ) (z θ : ℝ) : 0 ≤ mixedPart α g k z θ :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by split_ifs <;> simp [sq_nonneg]

theorem continuousOn_Wt (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Q0 := by
  have hsinpos : ∀ p ∈ Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, h0, h1⟩ := mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Q0 := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
    rw [hfun]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt (mem_Q0.mp hp).1))
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.w p.1
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by funext p; rfl
  rw [hfun]
  refine hw.mul ?_
  exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))

theorem continuousOn_pureTerm (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g) (i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.DzIter i g p.1 p.2
      * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2) Q0 :=
  (((hg.DzIter i).continuousOn).mul continuousOn_wdivsin_Q0).pow 2

theorem continuousOn_mixedTerm (α : ℝ) (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g) (k i j : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ =>
      (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i g p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2
        else 0)) Q0 := by
  by_cases hc : 1 ≤ i ∧ i + j ≤ k
  · simp only [if_pos hc]
    exact (((hg.mixed j i).continuousOn).mul (continuousOn_Wt α)).pow 2
  · simp only [if_neg hc]
    exact continuousOn_const


/-- a.e. angles lie in the open interval. -/
theorem ae_mem_Ioo_theta : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
    θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  have hset : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    refine MeasureTheory.Measure.restrict_congr_set ?_
    rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc.symm
  rw [hset]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- a.e. radii are positive. -/
theorem ae_mem_Ioi_z : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
    z ∈ Set.Ioi (0 : ℝ) := by
  have hset : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
    refine MeasureTheory.Measure.restrict_congr_set ?_
    rw [Work.Spaces.Iz]; exact MeasureTheory.Ioi_ae_eq_Ici.symm
  rw [hset]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioi

/-- The family of summands of `HkIntegrand α k g`, indexed by `ℕ ⊕ (ℕ × ℕ)`
(pure indices on the left, mixed indices on the right). -/
def termFamily (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) : ℕ ⊕ (ℕ × ℕ) → ℝ → ℝ → ℝ
  | Sum.inl i => fun z θ => (Work.Spaces.DzIter i g z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
  | Sum.inr p => fun z θ => (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then
      (Work.Spaces.mixed p.2 p.1 g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)

theorem continuousOn_termFamily (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g)
    (σ : ℕ ⊕ (ℕ × ℕ)) :
    ContinuousOn (fun p : ℝ × ℝ => termFamily α k g σ p.1 p.2) Q0 := by
  rcases σ with i | p
  · exact continuousOn_pureTerm g hg i
  · exact continuousOn_mixedTerm α g hg k p.1 p.2

/-- Summing over a disjoint sum of finsets. -/
theorem sum_disjSum_eq {α β M : Type*} [AddCommMonoid M] (s : Finset α) (t : Finset β)
    (f : α ⊕ β → M) :
    (∑ σ ∈ s.disjSum t, f σ) = (∑ a ∈ s, f (Sum.inl a)) + (∑ b ∈ t, f (Sum.inr b)) := by
  rw [← Finset.map_inl_disjUnion_map_inr, Finset.sum_disjUnion, Finset.sum_map, Finset.sum_map]
  simp only [Function.Embedding.inl_apply, Function.Embedding.inr_apply]

/-- `ofReal` of a finite sum of nonnegative reals, in one index. -/
theorem ofReal_sum_range (k : ℕ) (h : ℕ → ℝ) (hh : ∀ i, 0 ≤ h i) :
    (∑ i ∈ Finset.range (k + 1), ENNReal.ofReal (h i))
      = ENNReal.ofReal (∑ i ∈ Finset.range (k + 1), h i) := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hh i)]

/-- `ofReal` of a finite double sum of nonnegative reals. -/
theorem ofReal_sum_range₂ (k : ℕ) (h : ℕ → ℕ → ℝ) (hh : ∀ i j, 0 ≤ h i j) :
    (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1), ENNReal.ofReal (h i j))
      = ENNReal.ofReal (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1), h i j) := by
  have hinner : ∀ i, (∑ j ∈ Finset.range (k + 1), ENNReal.ofReal (h i j))
      = ENNReal.ofReal (∑ j ∈ Finset.range (k + 1), h i j) := fun i =>
    ofReal_sum_range k (h i) (hh i)
  rw [Finset.sum_congr rfl (fun i _ => hinner i)]
  exact ofReal_sum_range k (fun i => ∑ j ∈ Finset.range (k + 1), h i j)
    (fun i => Finset.sum_nonneg fun j _ => hh i j)

/-- The sum of the `ofReal`-lifts of the summand family is the `ofReal` of `HkIntegrand`. -/
theorem sum_termFamily (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    (∑ σ ∈ (Finset.range (k + 1)).disjSum
        ((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))),
        ENNReal.ofReal (termFamily α k g σ z θ))
      = ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ) := by
  rw [sum_disjSum_eq]
  have hpure : (∑ a ∈ Finset.range (k + 1), ENNReal.ofReal
        (termFamily α k g (Sum.inl a) z θ)) = ENNReal.ofReal (purePart g k z θ) := by
    simp only [termFamily, purePart]
    exact ofReal_sum_range k _ (fun a => sq_nonneg _)
  have hmixed : (∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)), ENNReal.ofReal
        (termFamily α k g (Sum.inr p) z θ)) = ENNReal.ofReal (mixedPart α g k z θ) := by
    rw [Finset.sum_product]
    simp only [termFamily, mixedPart]
    exact ofReal_sum_range₂ k _ (fun i j => by split_ifs <;> simp [sq_nonneg])
  rw [hpure, hmixed, ← ENNReal.ofReal_add (purePart_nonneg g k z θ)
    (mixedPart_nonneg α g k z θ), ← HkIntegrand_eq_parts]

/-- **Decomposition of `LkSq` into its individual summands.**  The honest `lintegral` of the
`H^k`-integrand of `g` is the sum of the honest sizes of its pure and mixed summands. -/
theorem LkSq_eq_sum (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g) :
    LkSq α k g
      = (∑ i ∈ Finset.range (k + 1), TZ g i)
        + ∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α g p.1 p.2 else 0) := by
  classical
  have hsplit := lintegral_sum_split
    ((Finset.range (k + 1)).disjSum ((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))))
    (termFamily α k g) (fun σ _ => continuousOn_termFamily α k g hg σ)
  have hLHS : (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz,
        ∑ σ ∈ (Finset.range (k + 1)).disjSum
          ((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))),
          ENNReal.ofReal (termFamily α k g σ z θ)) = LkSq α k g := by
    show (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz,
        ∑ σ ∈ (Finset.range (k + 1)).disjSum
          ((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))),
          ENNReal.ofReal (termFamily α k g σ z θ))
      = ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ)
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    exact sum_termFamily α k g z θ
  rw [hLHS] at hsplit
  rw [hsplit]
  rw [sum_disjSum_eq]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    show (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
        (termFamily α k g (Sum.inl i) z θ)) = TZ g i
    rw [TZ]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_mem_Ioo_theta] with θ hθ
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    exact (pure_ofReal_eq g i z θ (by
      rw [Work.Spaces.Iθ]; exact ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)).symm
  · refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hc : 1 ≤ p.1 ∧ p.1 + p.2 ≤ k
    · rw [if_pos hc]
      show (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
        (termFamily α k g (Sum.inr p) z θ)) = TM α g p.1 p.2
      rw [TM]
      refine lintegral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [termFamily, if_pos hc]
    · rw [if_neg hc]
      have hzero : (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
          (termFamily α k g (Sum.inr p) z θ)) = 0 := by
        have hterm : termFamily α k g (Sum.inr p) = fun _ _ => (0 : ℝ) := by
          funext z θ; simp only [termFamily, if_neg hc]
        rw [hterm]
        simp
      rw [hzero]

/-! ## Step 7: re-indexing `TZ` and `TM` of `D_z f` -/

theorem DzIter_succ_eq (m : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter (m + 1) f = Work.Spaces.DzIter m (Work.Spaces.Dz f) := by
  rw [Work.Spaces.DzIter_add_right m 1 f]
  rfl

/-- `z²∂_z² h = D_z² h − D_z h` on the open quadrant, for `h` smooth there. -/
theorem zsqPz2_eq_sub (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    zsqPz2 g z θ = Work.Spaces.DzIter 2 g z θ - Work.Spaces.Dz g z θ := by
  have h1 : DifferentiableAt ℝ (fun z' => g z' θ) z := (hg.hasDerivAt_slice hθ hz).differentiableAt
  have h2 : DifferentiableAt ℝ (fun z' => Work.Spaces.pz g z' θ) z :=
    (hg.hasDerivAt_slice_pzIter 1 hθ hz).differentiableAt
  simpa only [zsqPz2] using Work.FTS.EllipticEst.zsq_pzIter2_eq g h1 h2


theorem TZ_Dz (f : ℝ → ℝ → ℝ) (i : ℕ) :
    TZ (Work.Spaces.Dz f) i = TZ f (i + 1) := by
  simp only [TZ]
  refine lintegral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  rw [DzIter_succ_eq]

theorem TM_Dz_of_comm (α : ℝ) (f : ℝ → ℝ → ℝ)
    (hcomm : ∀ (a : ℕ) (z θ : ℝ), (z, θ) ∈ Q0 →
      Work.Spaces.DthIter a (Work.Spaces.Dz f) z θ
        = Work.Spaces.Dz (Work.Spaces.DthIter a f) z θ) (a b : ℕ) :
    TM α (Work.Spaces.Dz f) a b = TM α f a (b + 1) := by
  simp only [TM]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_mem_Ioo_theta] with θ hθ
  refine lintegral_congr_ae ?_
  filter_upwards [ae_mem_Ioi_z] with z hz
  have hpoint : Work.Spaces.DthIter a (Work.Spaces.Dz f) z θ
      = Work.Spaces.Dz (Work.Spaces.DthIter a f) z θ := hcomm a z θ ⟨hz, hθ⟩
  have hcongr : Work.Spaces.DzIter b (Work.Spaces.DthIter a (Work.Spaces.Dz f)) z θ
      = Work.Spaces.DzIter b (Work.Spaces.Dz (Work.Spaces.DthIter a f)) z θ :=
    SmoothOpen.DzIter_congr (F := Work.Spaces.DthIter a (Work.Spaces.Dz f))
      (G := Work.Spaces.Dz (Work.Spaces.DthIter a f))
      (fun z' θ' hz' h1 h2 => hcomm a z' θ' ⟨hz', ⟨h1, h2⟩⟩) b z θ hz hθ.1 hθ.2
  have hgoal : Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ
      = Work.Spaces.mixed (b + 1) a f z θ := by
    simp only [Work.Spaces.mixed] at hcongr ⊢
    rw [hcongr, DzIter_succ_eq]
  rw [hgoal]

/-- Distributing a constant over a conditionally-defined finite sum of pairs. -/
theorem sum_ite_mul_split {s : Finset (ℕ × ℕ)} {k : ℕ} (B Cc : ℝ≥0∞)
    (x y : ℕ × ℕ → ℝ≥0∞) :
    (∑ p ∈ s, (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then B * (Cc * x p + y p) else 0))
      = (B * Cc) * (∑ p ∈ s, (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then x p else 0))
        + B * (∑ p ∈ s, (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then y p else 0)) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hc : 1 ≤ p.1 ∧ p.1 + p.2 ≤ k
  · rw [if_pos hc, if_pos hc, if_pos hc]; ring
  · rw [if_neg hc, if_neg hc, if_neg hc]; ring

/-! ## Step 8: the main `LkSq` inequality -/

/-! ## Step 8: the main `LkSq` inequality -/

/-- The second radial derivative of a smooth-on-the-quadrant function is smooth. -/
theorem SmoothOpen_zsqPz2 (f : ℝ → ℝ → ℝ) (hf : SmoothOpen f) : SmoothOpen (zsqPz2 f) := by
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1 ^ 2) Q0 := by
    fun_prop
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 f p.1 p.2) Q0 := hf.pzIter 2
  have h3 := h1.mul h2
  have hfun : Function.uncurry (zsqPz2 f)
      = fun p : ℝ × ℝ => p.1 ^ 2 * Work.Spaces.pzIter 2 f p.1 p.2 := by
    funext p; rfl
  rw [SmoothOpen, hfun]
  exact h3


/-- **The `θ`-integrated radial interpolation for `D_z f`, at the level of the honest
`lintegral`s.** -/
theorem LkSq_Dz_le (C1 : ℝ) (hC1 : 0 < C1)
    (hgen : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ), SmoothOpen V →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ wth θ) →
      ENNReal.ofReal (α ^ 2) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2))
        ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))
            + (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2)))) :
    ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (k : ℕ) (f : ℝ → ℝ → ℝ),
      (∀ (a : ℕ) (z θ : ℝ), (z, θ) ∈ Q0 →
        Work.Spaces.DthIter a (Work.Spaces.Dz f) z θ
          = Work.Spaces.Dz (Work.Spaces.DthIter a f) z θ) →
      SmoothOpen f →
      ENNReal.ofReal (α ^ 2) * LkSq α k (Work.Spaces.Dz f)
        ≤ ENNReal.ofReal (C1 ^ 2) *
            (ENNReal.ofReal (α ^ 4) * LkSq α k (zsqPz2 f) + LkSq α k f) := by
  intro α hα hα1 k f hcomm hf
  have hDz : SmoothOpen (Work.Spaces.Dz f) := hf.Dz
  have hQ : SmoothOpen (zsqPz2 f) := SmoothOpen_zsqPz2 f hf
  have hdec : LkSq α k (Work.Spaces.Dz f)
      = (∑ i ∈ Finset.range (k + 1), TZ f (i + 1))
        + ∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α f p.1 (p.2 + 1) else 0) := by
    rw [LkSq_eq_sum α k (Work.Spaces.Dz f) hDz]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => TZ_Dz f i
    · refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hc : 1 ≤ p.1 ∧ p.1 + p.2 ≤ k
      · rw [if_pos hc, if_pos hc, TM_Dz_of_comm α f hcomm p.1 p.2]
      · rw [if_neg hc, if_neg hc]
  have hdecQ : LkSq α k (zsqPz2 f)
      = (∑ i ∈ Finset.range (k + 1), TZ (zsqPz2 f) i)
        + ∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α (zsqPz2 f) p.1 p.2 else 0) :=
    LkSq_eq_sum α k (zsqPz2 f) hQ
  have hdecf : LkSq α k f
      = (∑ i ∈ Finset.range (k + 1), TZ f i)
        + ∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α f p.1 p.2 else 0) :=
    LkSq_eq_sum α k f hf
  -- the termwise bounds
  have hT : ∀ i ∈ Finset.range (k + 1), ENNReal.ofReal (α ^ 2) * TZ f (i + 1)
      ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * TZ (zsqPz2 f) i + TZ f i) :=
    fun i _ => TZ_termwise C1 hC1 hgen α hα hα1 f hf i
  have hM : ∀ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
      (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then ENNReal.ofReal (α ^ 2) * TM α f p.1 (p.2 + 1) else 0)
        ≤ ENNReal.ofReal (C1 ^ 2) *
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then
              ENNReal.ofReal (α ^ 4) * TM α (zsqPz2 f) p.1 p.2 + TM α f p.1 p.2 else 0) := by
    intro p _
    by_cases hc : 1 ≤ p.1 ∧ p.1 + p.2 ≤ k
    · rw [if_pos hc, if_pos hc]
      exact TM_termwise C1 hC1 hgen α hα hα1 f hf p.1 p.2
    · rw [if_neg hc, if_neg hc, mul_zero]
  -- the two sums
  have hS1le : ENNReal.ofReal (α ^ 2) * (∑ i ∈ Finset.range (k + 1), TZ f (i + 1))
      ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * (∑ i ∈ Finset.range (k + 1), TZ (zsqPz2 f) i)
            + (∑ i ∈ Finset.range (k + 1), TZ f i)) := by
    rw [Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum hT) (le_of_eq ?_)
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.mul_sum]
  have hS2le : ENNReal.ofReal (α ^ 2)
        * (∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α f p.1 (p.2 + 1) else 0))
      ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4)
              * (∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
                  (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α (zsqPz2 f) p.1 p.2 else 0))
            + (∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
                  (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α f p.1 p.2 else 0))) := by
    rw [Finset.mul_sum]
    have hstep : (∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
          ENNReal.ofReal (α ^ 2) *
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α f p.1 (p.2 + 1) else 0))
        = ∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k
              then ENNReal.ofReal (α ^ 2) * TM α f p.1 (p.2 + 1) else 0) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hc : 1 ≤ p.1 ∧ p.1 + p.2 ≤ k
      · rw [if_pos hc, if_pos hc]
      · rw [if_neg hc, if_neg hc, mul_zero]
    rw [hstep]
    refine le_trans (Finset.sum_le_sum hM) (le_of_eq ?_)
    have hflat : ∀ p : ℕ × ℕ,
        ENNReal.ofReal (C1 ^ 2) * (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then
            ENNReal.ofReal (α ^ 4) * TM α (zsqPz2 f) p.1 p.2 + TM α f p.1 p.2 else 0)
          = (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then ENNReal.ofReal (C1 ^ 2) *
                (ENNReal.ofReal (α ^ 4) * TM α (zsqPz2 f) p.1 p.2 + TM α f p.1 p.2)
              else 0) := by
      intro p; by_cases hc : 1 ≤ p.1 ∧ p.1 + p.2 ≤ k <;> simp [hc]
    rw [Finset.sum_congr rfl (fun p _ => hflat p)]
    rw [sum_ite_mul_split (k := k) (ENNReal.ofReal (C1 ^ 2)) (ENNReal.ofReal (α ^ 4))
      (fun p => TM α (zsqPz2 f) p.1 p.2) (fun p => TM α f p.1 p.2)]
    rw [mul_add]
    ring
  -- combine
  rw [hdec, mul_add]
  refine le_trans (add_le_add hS1le hS2le) (le_of_eq ?_)
  rw [hdecQ, hdecf]
  ring

/-! ## Step 9: the bridges between `HkSq` and `LkSq` -/

/-- The `ofReal` of a Bochner integral of a nonnegative function is dominated by the
`lintegral` of the `ofReal`-lift. -/
theorem ofReal_integral_le_lintegral (s : Set ℝ) (u : ℝ → ℝ) (hu : ∀ θ, 0 ≤ u θ) :
    ENNReal.ofReal (∫ θ in s, u θ) ≤ ∫⁻ θ in s, ENNReal.ofReal (u θ) := by
  by_cases hg : IntegrableOn u s
  · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg (Filter.Eventually.of_forall hu)]
  · rw [MeasureTheory.integral_undef hg]; simp

/-- The uncurried `H^k`-integrand is a.e. strongly measurable for the product of the restricted
measures (in either order). -/
theorem aesm_HkIntegrand_prod (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g) :
    AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k g p.1 p.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
  ((Work.Spaces.aesm_of_continuousOn_Qd _ (hg.continuousOn_HkIntegrand α k)).aemeasurable).ennreal_ofReal

theorem HkSq_forall_smooth (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
  fun n => (smoothOpen_iff_forall g).mp hg n

/-- `LkSq` written as the `z`-integral of the `ofReal` of the `θ`-integral. -/
theorem LkSq_eq_theta_integral (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g)
    (hmem : Work.Spaces.HkMem α k g) :
    LkSq α k g = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ) := by
  have hswap : (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ))
      = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ) :=
    MeasureTheory.lintegral_lintegral_swap
      ((aesm_HkIntegrand_prod α k g hg).prod_swap)
  have heq : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ))
      = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ) := by
    refine lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iz from
      measurableSet_Ici)] with z hz
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hmem.1 z hz)
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k g z θ)).symm
  rw [LkSq, hswap, heq]


/-- Honesty of `LkSq` from `HkMem`. -/
theorem LkSq_lt_top (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g)
    (hmem : Work.Spaces.HkMem α k g) : LkSq α k g < ⊤ := by
  rw [LkSq_eq_theta_integral α k g hg hmem]
  exact MeasureTheory.Integrable.lintegral_lt_top hmem.2

/-- Under honesty (`HkMem`), `LkSq` is the `ofReal` of `HkSq`. -/
theorem LkSq_eq_ofReal_HkSq (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g)
    (hmem : Work.Spaces.HkMem α k g) :
    LkSq α k g = ENNReal.ofReal (Work.Spaces.HkSq α k g) := by
  have hforall := HkSq_forall_smooth g hg
  rw [LkSq_eq_theta_integral α k g hg hmem,
    Work.FTS.EllipticEst.HkSq_eq_lintegral α k g hforall]
  have hA : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)) < ⊤ := by
    rw [← LkSq_eq_theta_integral α k g hg hmem]
    exact LkSq_lt_top α k g hg hmem
  exact (ENNReal.ofReal_toReal (ne_of_lt hA)).symm

/-- `√(x+y) ≤ √x + √y` for nonnegative reals. -/
theorem sqrt_add_le_sqrt (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have h : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by
    have h1 := Real.sq_sqrt hx
    have h2 := Real.sq_sqrt hy
    have h3 : 0 ≤ Real.sqrt x * Real.sqrt y := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith
  calc Real.sqrt (x + y) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt x + Real.sqrt y := Real.sqrt_sq (by positivity)

/-! ## Step 10: from the `LkSq` inequality to the norm inequality -/

/-- The commutation hypothesis of `LkSq_Dz_le`, from the coprime theorem
`DthIterDzCommOpen`. -/
theorem comm_hyp (f : ℝ → ℝ → ℝ) (hf : SmoothOpen f) :
    ∀ (a : ℕ) (z θ : ℝ), (z, θ) ∈ Q0 →
      Work.Spaces.DthIter a (Work.Spaces.Dz f) z θ
        = Work.Spaces.Dz (Work.Spaces.DthIter a f) z θ :=
  fun a z θ h => (DthIterDzCommOpen f hf a h).symm

/-- Finiteness of `LkSq (D_z f)` from the `LkSq` inequality. -/
theorem LkSq_Dz_lt_top (C1 : ℝ) (hC1 : 0 < C1)
    (hgen : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ), SmoothOpen V →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ wth θ) →
      ENNReal.ofReal (α ^ 2) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2))
        ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))
            + (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2))))
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (f : ℝ → ℝ → ℝ) (hf : SmoothOpen f)
    (hmf : Work.Spaces.HkMem α k f) (hmQ : Work.Spaces.HkMem α k (zsqPz2 f)) :
    LkSq α k (Work.Spaces.Dz f) < ⊤ := by
  have hQfin : LkSq α k (zsqPz2 f) < ⊤ := LkSq_lt_top α k _ (SmoothOpen_zsqPz2 f hf) hmQ
  have hffin : LkSq α k f < ⊤ := LkSq_lt_top α k f hf hmf
  have h := LkSq_Dz_le C1 hC1 hgen α hα hα1 k f (comm_hyp f hf) hf
  have hfin : ENNReal.ofReal (C1 ^ 2) *
      (ENNReal.ofReal (α ^ 4) * LkSq α k (zsqPz2 f) + LkSq α k f) < ⊤ := by
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hQfin, hffin⟩
  have hlt : ENNReal.ofReal (α ^ 2) * LkSq α k (Work.Spaces.Dz f) < ⊤ := lt_of_le_of_lt h hfin
  have hpos : ENNReal.ofReal (α ^ 2) ≠ 0 := by
    simpa using (ENNReal.ofReal_pos.mpr (by positivity : (0 : ℝ) < α ^ 2)).ne'
  rcases ENNReal.mul_lt_top_iff.mp hlt with ⟨-, h2⟩ | h0 | h0
  · exact h2
  · exact absurd h0 hpos
  · exact lt_top_iff_ne_top.mpr (by simp [h0])
/-- **The norm inequality**, given the honesty of `D_z f`. -/
theorem HkNorm_Dz_le_of (C1 : ℝ) (hC1 : 0 < C1)
    (hgen : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ), SmoothOpen V →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ wth θ) →
      ENNReal.ofReal (α ^ 2) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2))
        ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))
            + (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2))))
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (f : ℝ → ℝ → ℝ) (hf : SmoothOpen f)
    (hmf : Work.Spaces.HkMem α k f) (hmQ : Work.Spaces.HkMem α k (zsqPz2 f))
    (hmDz : Work.Spaces.HkMem α k (Work.Spaces.Dz f)) :
    α * Work.Spaces.HkNorm α k (Work.Spaces.Dz f)
      ≤ C1 * (Work.Spaces.HkNorm α k f + α ^ 2 * Work.Spaces.HkNorm α k (zsqPz2 f)) := by
  have hDzSm : SmoothOpen (Work.Spaces.Dz f) := hf.Dz
  have hQSm : SmoothOpen (zsqPz2 f) := SmoothOpen_zsqPz2 f hf
  have hDzfin := LkSq_Dz_lt_top C1 hC1 hgen α hα hα1 k f hf hmf hmQ
  have hQfin : LkSq α k (zsqPz2 f) < ⊤ := LkSq_lt_top α k _ hQSm hmQ
  have hffin : LkSq α k f < ⊤ := LkSq_lt_top α k f hf hmf
  -- (★) in terms of `HkSq`
  have h := LkSq_Dz_le C1 hC1 hgen α hα hα1 k f (comm_hyp f hf) hf
  rw [LkSq_eq_ofReal_HkSq α k (Work.Spaces.Dz f) hDzSm hmDz,
    LkSq_eq_ofReal_HkSq α k (zsqPz2 f) hQSm hmQ,
    LkSq_eq_ofReal_HkSq α k f hf hmf] at h
  have hnn : 0 ≤ Work.Spaces.HkSq α k (Work.Spaces.Dz f) :=
    Work.Spaces.HkSq_nonneg α k _
  have hnnQ : 0 ≤ Work.Spaces.HkSq α k (zsqPz2 f) := Work.Spaces.HkSq_nonneg α k _
  have hnnf : 0 ≤ Work.Spaces.HkSq α k f := Work.Spaces.HkSq_nonneg α k f
  have hL : ENNReal.ofReal (α ^ 2) * ENNReal.ofReal (Work.Spaces.HkSq α k (Work.Spaces.Dz f))
      = ENNReal.ofReal (α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz f)) := by
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ α ^ 2)]
  have hR : ENNReal.ofReal (C1 ^ 2) * (ENNReal.ofReal (α ^ 4) *
        ENNReal.ofReal (Work.Spaces.HkSq α k (zsqPz2 f)) + ENNReal.ofReal (Work.Spaces.HkSq α k f))
      = ENNReal.ofReal (C1 ^ 2 * (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f)
          + Work.Spaces.HkSq α k f)) := by
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ C1 ^ 2),
      ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f)) hnnf,
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ α ^ 4)]
  rw [hL, hR] at h
  have hsq : α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz f)
      ≤ C1 ^ 2 * (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f) + Work.Spaces.HkSq α k f) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  -- take square roots
  have hsqrt : α * Real.sqrt (Work.Spaces.HkSq α k (Work.Spaces.Dz f))
      ≤ C1 * Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f) + Work.Spaces.HkSq α k f) := by
    have h1 : α * Real.sqrt (Work.Spaces.HkSq α k (Work.Spaces.Dz f))
        = Real.sqrt (α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz f)) := by
      rw [Real.sqrt_mul (sq_nonneg α), Real.sqrt_sq hα.le]
    have h2 : C1 * Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f) + Work.Spaces.HkSq α k f)
        = Real.sqrt (C1 ^ 2 * (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f)
            + Work.Spaces.HkSq α k f)) := by
      rw [Real.sqrt_mul (sq_nonneg C1), Real.sqrt_sq hC1.le]
    rw [h1, h2]
    exact Real.sqrt_le_sqrt hsq
  have hf1 : Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f))
      = α ^ 2 * Work.Spaces.HkNorm α k (zsqPz2 f) := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ α ^ 4), Work.Spaces.HkNorm,
      show Real.sqrt (α ^ 4) = α ^ 2 by
        rw [show α ^ 4 = (α ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity : (0 : ℝ) ≤ α ^ 2)]]
  have hadd : Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f) + Work.Spaces.HkSq α k f)
      ≤ α ^ 2 * Work.Spaces.HkNorm α k (zsqPz2 f) + Work.Spaces.HkNorm α k f := by
    calc Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f) + Work.Spaces.HkSq α k f)
        ≤ Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f))
          + Real.sqrt (Work.Spaces.HkSq α k f) :=
          sqrt_add_le_sqrt _ _ (by positivity) (Work.Spaces.HkSq_nonneg α k f)
      _ = α ^ 2 * Work.Spaces.HkNorm α k (zsqPz2 f) + Work.Spaces.HkNorm α k f := by
          rw [hf1]
          rfl
  calc α * Real.sqrt (Work.Spaces.HkSq α k (Work.Spaces.Dz f))
      ≤ C1 * Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f) + Work.Spaces.HkSq α k f) := hsqrt
    _ ≤ C1 * (α ^ 2 * Work.Spaces.HkNorm α k (zsqPz2 f) + Work.Spaces.HkNorm α k f) :=
        mul_le_mul_of_nonneg_left hadd (le_of_lt hC1)
    _ = C1 * (Work.Spaces.HkNorm α k f + α ^ 2 * Work.Spaces.HkNorm α k (zsqPz2 f)) := by ring

/-! ## Step 11: pointwise decomposition of the `H^k`-integrand of `D_z f` -/

/-- `D_z² X = z²∂_z²X + D_z X` on the open quadrant. -/
theorem DzIter_two_decomp (X : ℝ → ℝ → ℝ) (hX : SmoothOpen X) :
    Set.EqOn (Function.uncurry (fun z θ => Work.Spaces.DzIter 2 X z θ
        - (zsqPz2 X z θ + Work.Spaces.Dz X z θ))) (fun _ : ℝ × ℝ => (0 : ℝ)) Q0 := by
  intro y hy
  obtain ⟨hz, hθ⟩ := hy
  have h := zsqPz2_eq_sub X hX hz hθ
  show Work.Spaces.DzIter 2 X y.1 y.2
    - (zsqPz2 X y.1 y.2 + Work.Spaces.Dz X y.1 y.2) = 0
  rw [h]; ring








/-- The second `HkMem` conjunct of `g`, from the finiteness of `LkSq α k g`. -/
theorem integrableOn_sliceIntegral_of_LkSq_lt_top (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ)
    (hg : SmoothOpen g) (h : LkSq α k g < ⊤) :
    MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k g z θ) Work.Spaces.Iz := by
  have hprod : AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k g p.1 p.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    aesm_HkIntegrand_prod α k g hg
  have hfin : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ)) < ⊤ := by
    rw [← MeasureTheory.lintegral_lintegral_swap (hprod.prod_swap)]
    exact h
  have hA : AEMeasurable (fun z => ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hprod.lintegral_prod_right'
  have hint : MeasureTheory.Integrable (fun z => (∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ)).toReal)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    MeasureTheory.integrable_toReal_of_lintegral_ne_top hA (ne_of_lt hfin)
  refine hint.congr ?_
  filter_upwards [ae_mem_Ioi_z] with z hz
  exact (MeasureTheory.integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k g z θ)
    (Work.Spaces.aesm_slice_of_continuousOn_Qd _
      (hg.continuousOn_HkIntegrand α k) hz)).symm

end Work.FTS.EllipticEst.DzAmgm
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Endpt.Lzero1_slice_mul_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Endpt

set_option autoImplicit false

/-- The `θ`-slice of `Lzero1 (fun θ' => Ψ z θ')` multiplied by the kernel `sinθcos²θ` is
integrable, assuming the slice and its derivative are bounded.

Pointwise on `(0, π/2)` (where `Real.cos θ ≠ 0`),
`(Lzero1 u θ) * sinθcos²θ = -(u'' θ) * sinθcos²θ + sin θ * u θ + sin²θ cos θ * u' θ
 - 6 * u θ * sinθcos²θ` (from `(tan·u)' = (1/cos²)·u + tan·u'` and
`sinθcos²θ/cos²θ = sinθ`, `tanθ·sinθcos²θ = sin²θcosθ`). The last three terms are bounded by
`7 * C` since `|u| ≤ C`, `|u'| ≤ C` and the angular factors lie in `[0,1]`; the `u''`-term is
dominated by `(u'' θ · w z / sin(2θ)^{η/2})² + 1` via
`Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted`, which is integrable by `hmB` (divided by
`w z ≠ 0`). Needed: `deriv`-rewriting of `(tan · u)'` (via `deriv_mul` and `Real.deriv_tan`),
the a.e. equality `pthIter 2 Ψ z · = deriv (deriv (Ψ z ·))` on `Iθ` (definitional), and
a.e.-strong measurability of the slice (from `hsm`). -/
theorem Lzero1_slice_mul_integrable {α : ℝ} {Ψ : ℝ → ℝ → ℝ} {z C : ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hmB : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ)) (hz : 0 < z)
    (hC : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), |Ψ z θ| ≤ C ∧ |deriv (fun θ' => Ψ z θ') θ| ≤ C) :
    MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.EllipticEst.Lzero1 (fun θ' => Ψ z θ') θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ := by
  -- the slice `θ ↦ Ψ z θ` is `C²` on the open interval, with continuous first two derivatives
  obtain ⟨hslice2, hdu_cont, hddu_cont⟩ := slice_regularity_of_uncurry hz hsm
  -- `C` is nonnegative because the open interval is nonempty
  have hC0 : 0 ≤ C :=
    le_trans (abs_nonneg _) (hC (Real.pi / 4) ⟨by linarith [Real.pi_pos],
      by linarith [Real.pi_pos]⟩).1
  -- the pointwise identity on the open interval
  have hpoint : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 (fun θ' => Ψ z θ') θ * Work.Elliptic.sinCos2 θ
        = -(deriv (deriv (fun θ' => Ψ z θ')) θ) * Work.Elliptic.sinCos2 θ
          + Real.sin θ * (fun θ' => Ψ z θ') θ
          + (Real.sin θ) ^ 2 * Real.cos θ * deriv (fun θ' => Ψ z θ') θ
          - 6 * (fun θ' => Ψ z θ') θ * Work.Elliptic.sinCos2 θ := by
    intro θ hθ
    exact Lzero1_mul_sinCos2_eq hθ
      ((hslice2.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num))
  -- continuity on the open interval of the explicit form, hence a.e. strong measurability
  have hcont_sc : ContinuousOn (fun θ : ℝ => Work.Elliptic.sinCos2 θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    unfold Work.Elliptic.sinCos2
    fun_prop
  have hu_cont : ContinuousOn (fun θ' => Ψ z θ') (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hslice2.continuousOn
  have hcontG : ContinuousOn (fun θ : ℝ =>
      -(deriv (deriv (fun θ' => Ψ z θ')) θ) * Work.Elliptic.sinCos2 θ
        + Real.sin θ * (fun θ' => Ψ z θ') θ
        + (Real.sin θ) ^ 2 * Real.cos θ * deriv (fun θ' => Ψ z θ') θ
        - 6 * (fun θ' => Ψ z θ') θ * Work.Elliptic.sinCos2 θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h1 : ContinuousOn (fun θ : ℝ =>
        -(deriv (deriv (fun θ' => Ψ z θ')) θ) * Work.Elliptic.sinCos2 θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hddu_cont.neg.mul hcont_sc
    have h2 : ContinuousOn (fun θ : ℝ => Real.sin θ * (fun θ' => Ψ z θ') θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := Real.continuous_sin.continuousOn.mul hu_cont
    have h3 : ContinuousOn (fun θ : ℝ =>
        (Real.sin θ) ^ 2 * Real.cos θ * deriv (fun θ' => Ψ z θ') θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      ((Real.continuous_sin.continuousOn.pow 2).mul Real.continuous_cos.continuousOn).mul hdu_cont
    have h4 : ContinuousOn (fun θ : ℝ => 6 * (fun θ' => Ψ z θ') θ * Work.Elliptic.sinCos2 θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (continuousOn_const.mul hu_cont).mul hcont_sc
    exact ((h1.add h2).add h3).sub h4
  have hcontF : ContinuousOn
      (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 (fun θ' => Ψ z θ') θ * Work.Elliptic.sinCos2 θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hcontG.congr hpoint
  have haesm : AEStronglyMeasurable
      (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 (fun θ' => Ψ z θ') θ * Work.Elliptic.sinCos2 θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hcontF.aestronglyMeasurable measurableSet_Ioo
  -- the dominating function is integrable on `Iθ`
  have hsq : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (Work.Spaces.pthIter 2 Ψ z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) Work.Spaces.Iθ :=
    (hmB.1 z hz.le).congr_fun (fun θ _ => by simp [Work.Spaces.HkIntegrand]) measurableSet_Icc
  have hGint : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (Work.Spaces.pthIter 2 Ψ z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1 + 8 * C)
      Work.Spaces.Iθ := by
    have h1 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
      MeasureTheory.integrableOn_const Work.FTS.EllipticEst.remov.ws_vol_Iθ_ne_top
    have h8 : MeasureTheory.IntegrableOn (fun _ : ℝ => 8 * C) Work.Spaces.Iθ :=
      MeasureTheory.integrableOn_const Work.FTS.EllipticEst.remov.ws_vol_Iθ_ne_top
    exact (hsq.add h1).add h8
  have hGintIoo : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (Work.Spaces.pthIter 2 Ψ z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1 + 8 * C)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hGint.mono_set Set.Ioo_subset_Icc_self
  -- the pointwise bound on the open interval
  have hbound : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ‖Work.FTS.EllipticEst.Lzero1 (fun θ' => Ψ z θ') θ * Work.Elliptic.sinCos2 θ‖
        ≤ (Work.Spaces.pthIter 2 Ψ z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1 + 8 * C := by
    intro θ hθ
    have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    obtain ⟨hΨ, hdΨ⟩ := hC θ hθ
    rw [Real.norm_eq_abs, hpoint θ hθ]
    -- the `u''`-term, absorbed by the weighted `L²` square
    have hA : |-(deriv (deriv (fun θ' => Ψ z θ')) θ) * Work.Elliptic.sinCos2 θ|
        ≤ (Work.Spaces.pthIter 2 Ψ z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1 := by
      rw [neg_mul, abs_neg]
      exact Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
        (f := fun θ' => deriv (deriv (fun θ'' => Ψ z θ'')) θ') hz hθIθ
    -- the three bounded terms
    have hB : |Real.sin θ * (fun θ' => Ψ z θ') θ| ≤ C := by
      rw [abs_mul]
      calc |Real.sin θ| * |(fun θ' => Ψ z θ') θ| ≤ 1 * C :=
            mul_le_mul (Real.abs_sin_le_one θ) hΨ (abs_nonneg _) (by norm_num)
        _ = C := by ring
    have hCc : |(Real.sin θ) ^ 2 * Real.cos θ * deriv (fun θ' => Ψ z θ') θ| ≤ C := by
      rw [abs_mul, abs_mul, abs_pow]
      have hs1 : |Real.sin θ| ^ 2 ≤ 1 := by
        nlinarith [abs_nonneg (Real.sin θ), Real.abs_sin_le_one θ]
      have hc1 : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
      calc |Real.sin θ| ^ 2 * |Real.cos θ| * |deriv (fun θ' => Ψ z θ') θ|
          ≤ 1 * 1 * C := by
            refine mul_le_mul (mul_le_mul hs1 hc1 (abs_nonneg _) (by norm_num)) hdΨ
              (abs_nonneg _) (by norm_num)
        _ = C := by ring
    have hD : |6 * (fun θ' => Ψ z θ') θ * Work.Elliptic.sinCos2 θ| ≤ 6 * C := by
      rw [abs_mul]
      have h6 : |(6 : ℝ) * (fun θ' => Ψ z θ') θ| ≤ 6 * C := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
        exact mul_le_mul_of_nonneg_left hΨ (by norm_num)
      have hsc1 : |Work.Elliptic.sinCos2 θ| ≤ 1 :=
        Work.FTS.EllipticEst.abs_sinCos2_le_one hθIθ
      calc |(6 : ℝ) * (fun θ' => Ψ z θ') θ| * |Work.Elliptic.sinCos2 θ| ≤ (6 * C) * 1 :=
            mul_le_mul h6 hsc1 (abs_nonneg _) (by linarith)
        _ = 6 * C := by ring
    -- triangle inequality and assembly
    have htri : |-(deriv (deriv (fun θ' => Ψ z θ')) θ) * Work.Elliptic.sinCos2 θ
          + Real.sin θ * (fun θ' => Ψ z θ') θ
          + (Real.sin θ) ^ 2 * Real.cos θ * deriv (fun θ' => Ψ z θ') θ
          - 6 * (fun θ' => Ψ z θ') θ * Work.Elliptic.sinCos2 θ|
        ≤ |-(deriv (deriv (fun θ' => Ψ z θ')) θ) * Work.Elliptic.sinCos2 θ|
          + |Real.sin θ * (fun θ' => Ψ z θ') θ|
          + |(Real.sin θ) ^ 2 * Real.cos θ * deriv (fun θ' => Ψ z θ') θ|
          + |6 * (fun θ' => Ψ z θ') θ * Work.Elliptic.sinCos2 θ| := by
      have h1 := abs_add_le
        (-(deriv (deriv (fun θ' => Ψ z θ')) θ) * Work.Elliptic.sinCos2 θ
          + Real.sin θ * (fun θ' => Ψ z θ') θ
          + (Real.sin θ) ^ 2 * Real.cos θ * deriv (fun θ' => Ψ z θ') θ)
        (-(6 * (fun θ' => Ψ z θ') θ * Work.Elliptic.sinCos2 θ))
      rw [abs_neg] at h1
      have h2 := abs_add_le
        (-(deriv (deriv (fun θ' => Ψ z θ')) θ) * Work.Elliptic.sinCos2 θ
          + Real.sin θ * (fun θ' => Ψ z θ') θ)
        ((Real.sin θ) ^ 2 * Real.cos θ * deriv (fun θ' => Ψ z θ') θ)
      have h3 := abs_add_le
        (-(deriv (deriv (fun θ' => Ψ z θ')) θ) * Work.Elliptic.sinCos2 θ)
        (Real.sin θ * (fun θ' => Ψ z θ') θ)
      have hg : |-(deriv (deriv (fun θ' => Ψ z θ')) θ) * Work.Elliptic.sinCos2 θ
            + Real.sin θ * (fun θ' => Ψ z θ') θ
            + (Real.sin θ) ^ 2 * Real.cos θ * deriv (fun θ' => Ψ z θ') θ
            - 6 * (fun θ' => Ψ z θ') θ * Work.Elliptic.sinCos2 θ|
          = |(-(deriv (deriv (fun θ' => Ψ z θ')) θ) * Work.Elliptic.sinCos2 θ
            + Real.sin θ * (fun θ' => Ψ z θ') θ
            + (Real.sin θ) ^ 2 * Real.cos θ * deriv (fun θ' => Ψ z θ') θ)
            + -(6 * (fun θ' => Ψ z θ') θ * Work.Elliptic.sinCos2 θ)| := by
        rw [sub_eq_add_neg]
      rw [hg]
      linarith
    linarith
  -- the transfer from the open interval to `Iθ` (the two endpoints are null)
  have hIntIoo : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      Work.FTS.EllipticEst.Lzero1 (fun θ' => Ψ z θ') θ * Work.Elliptic.sinCos2 θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    MeasureTheory.Integrable.mono' hGintIoo haesm (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      exact hbound θ hθ)
  exact MeasureTheory.IntegrableOn.congr_set_ae hIntIoo (by
    show Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2)
    rw [Work.Spaces.Iθ]
    exact (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2)).symm)

end Work.FTS.EllipticEst.Endpt
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Endpt.integrableOn_fstar_pzIter2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst.Endpt

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-- The elementary absorption `|x| ≤ x² + 1`: for `|x| ≤ 1` the right-hand side is at least `1`,
and for `|x| ≥ 1` one has `|x| ≤ |x|² = x²`. -/
theorem abs_le_sq_add_one' (x : ℝ) : |x| ≤ x ^ 2 + 1 := by
  rcases le_or_gt |x| 1 with h | h
  · nlinarith [sq_nonneg x]
  · have h2 : |x| ≤ |x| * |x| := by
      calc |x| = 1 * |x| := (one_mul _).symm
        _ ≤ |x| * |x| := mul_le_mul_of_nonneg_right (le_of_lt h) (abs_nonneg x)
    have h3 : |x| * |x| = x ^ 2 := by
      rw [← sq_abs]
      ring
    linarith [h2, h3]

/-- **Pointwise domination on the open angular interval.**  For `z > 0` and `θ ∈ (0,π/2)`,

  `(∂_z²Ψ(z,θ))² ≤ HkIntegrand α 0 (z² ∂_z²Ψ) (z,θ)`.

Indeed `(∂_z²Ψ)² sin(2θ)^{-η} ≤ HkIntegrand` (`pzIter2_sq_mul_sEta_le_HkIntegrand`) and
multiplication by `sin(2θ)^{η} ≤ 1` (with `sin(2θ) > 0`) removes the weight. -/
theorem pzIter2_sq_le_HkIntegrand {α : ℝ} {Ψ : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (Work.Spaces.pzIter 2 Ψ z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hspos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  have hsle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hpowle : Real.sin (2 * θ) ^ Work.Spaces.eta ≤ 1 :=
    Real.rpow_le_one hspos.le hsle (by norm_num [Work.Spaces.eta])
  have hmul := mul_le_mul_of_nonneg_right
    (pzIter2_sq_mul_sEta_le_HkIntegrand (α := α) (Ψ := Ψ) hz hθI)
    (Real.rpow_nonneg hspos.le Work.Spaces.eta)
  have hid : (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta)
      * Real.sin (2 * θ) ^ Work.Spaces.eta = (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 := by
    rw [mul_assoc, ← Real.rpow_add hspos, neg_add_cancel, Real.rpow_zero, mul_one]
  rw [hid] at hmul
  exact le_trans hmul
    (mul_le_of_le_one_right (Work.Spaces.HkIntegrand_nonneg α 0 _ z θ) hpowle)

/-- **The slicewise `L²`-bound for the angular moment of `∂_z²Ψ`.**  For `z > 0`, if the
level-`0` integrand of `z² ∂_z²Ψ` is `θ`-integrable and the slice of `∂_z²Ψ` is a.e. strongly
measurable, then

  `F_*(∂_z²Ψ)(z)² ≤ (π/2) ∫_θ HkIntegrand α 0 (z² ∂_z²Ψ) z θ`.

This is Cauchy–Schwarz in `θ` (`Work.Elliptic.Fstar_sq_le`) followed by the monotone comparison
`(∂_z²Ψ)² ≤ HkIntegrand` on the full-measure set `(0,π/2) ⊆ Iθ`. -/
theorem Fstar_pzIter2_sq_le {α : ℝ} {Ψ : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hH : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) Work.Spaces.Iθ)
    (hae : AEStronglyMeasurable (fun θ => Work.Spaces.pzIter 2 Ψ z θ)
      (volume.restrict Work.Spaces.Iθ)) :
    (Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) z) ^ 2
      ≤ (π / 2) * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ := by
  have hle_ae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.pzIter 2 Ψ z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ := by
    have hEq : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo 0 (π / 2) :=
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm
    rw [MeasureTheory.Measure.restrict_congr_set hEq]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact pzIter2_sq_le_HkIntegrand hz hθ
  have hsq : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pzIter 2 Ψ z θ) ^ 2)
      Work.Spaces.Iθ := by
    refine Integrable.mono' hH (hae.pow 2) ?_
    filter_upwards [hle_ae] with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hθ
  have hcs := Work.Elliptic.Fstar_sq_le (Work.Spaces.pzIter 2 Ψ) z hsq
  have hmono : ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ z θ) ^ 2
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ :=
    integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _) hH hle_ae
  calc (Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) z) ^ 2
      ≤ (π / 2) * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 := hcs
    _ ≤ (π / 2) * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ :=
        mul_le_mul_of_nonneg_left hmono (by linarith [Real.pi_pos])

theorem integrableOn_fstar_pzIter2 {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hmZ : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :
    ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ))
        (Set.Icc a b) := by
  intro a b ha hab
  have hΨ : SmoothOpen Ψ := smoothOpen_of_forall hsm
  have hsub : Set.Icc a b ⊆ Work.Spaces.Iz := fun x hx => le_trans (le_of_lt ha) hx.1
  -- Strong measurability of the moment, from continuity of `∂_z²Ψ` on the open quadrant.
  have hFstar_aesm : AEStronglyMeasurable
      (fun z => Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) z)
      (volume.restrict (Set.Icc a b)) := by
    have h0 : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ)
        (volume.restrict (Set.Ioi 0)) :=
      aestronglyMeasurable_integral_Itheta_Q0 (Work.Spaces.pzIter 2 Ψ)
        (hΨ.pzIter 2).continuousOn Work.Elliptic.sinCos2
        (by unfold Work.Elliptic.sinCos2; fun_prop)
    exact AEStronglyMeasurable.mono_set (t := Set.Ioi 0)
      (fun x hx => by simp only [Set.mem_Ioi]; linarith [ha, hx.1]) h0
  -- The dominating function `(π/2)·∫_θ HkIntegrand + 1` is integrable on `[a,b]`.
  have hJint : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ)
      (Set.Icc a b) := hmZ.2.mono_set hsub
  have hconst_int : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc a b) :=
    integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  refine hJint.const_mul (π / 2) |>.add hconst_int |>.mono' hFstar_aesm ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with z hz
  have hzpos : 0 < z := lt_of_lt_of_le ha hz.1
  have hzI : z ∈ Work.Spaces.Iz := hsub hz
  have hpt := Fstar_pzIter2_sq_le (α := α) (Ψ := Ψ) hzpos (hmZ.1 z hzI)
    (hΨ.aesm_slice_pzIter 2 hzpos)
  have hJnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ :=
    integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ
  rw [Real.norm_eq_abs]
  simp only [Pi.add_apply] at *
  exact le_trans (abs_le_sq_add_one' _) (by linarith)

end Work.FTS.EllipticEst.Endpt
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Endpt

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {Ψ : ℝ → ℝ → ℝ}

/-! ## Slicewise facts for a function smooth on the open strip

The hypotheses of `sliceBdd_of_hmB` are: `Ψ` is smooth on the *open* strip
`(0,∞) × (0,π/2)`, and the second angular derivative `∂_θθΨ` lies in the level-`0` weighted
space `ℋ⁰`, i.e. `(∂_θθΨ · w/ sin(2θ)^{η/2})²` is honestly integrable.  Since the level-`0`
integrand is the single square `(∂_θθΨ)² w² sin(2θ)^{-η}`, for every `z > 0` the slice
`θ ↦ ∂_θθΨ(z,θ)` is integrable against the angular weight `σ = sin(2θ)^{-η}` on `Iθ`; the
fundamental theorem of calculus on the open interval `(0,π/2)` then bounds `∂_θΨ` and, once
more, `Ψ` itself on that interval.

The same argument is carried out for the honest class of
`Submission/Work/FTS/EllipticEst/Honest/HonSliceBdd.lean`; here it is restated for the two
hypotheses actually used, without the Dirichlet data, the orthogonality conditions or the
smoothness of `z²∂_zzΨ`. -/

/-- The `θ`-slices of a function smooth on the open strip `(0,∞) × (0,π/2)` are smooth on
`(0,π/2)`. -/
theorem contDiffOn_slice_of_strip
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    {z : ℝ} (hz : 0 < z) (n : ℕ) : ContDiffOn ℝ n (fun θ => Ψ z θ) (Set.Ioo 0 (π / 2)) := by
  have hmap : Set.MapsTo (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (π / 2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := fun θ hθ => ⟨hz, hθ⟩
  exact (hsm n).comp (by fun_prop) hmap

/-- The slice `θ ↦ ∂_θθΨ(z,·)` of the second angular derivative is continuous on the open
interval `(0,π/2)`. -/
theorem continuousOn_pthIter2_of_strip
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun θ => Work.Spaces.pthIter 2 Ψ z θ) (Set.Ioo 0 (π / 2)) := by
  have hslice : ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Ioo 0 (π / 2)) :=
    contDiffOn_slice_of_strip hsm hz 2
  have hfun : (fun θ => Work.Spaces.pthIter 2 Ψ z θ)
      = fun θ => deriv (deriv (fun θ' => Ψ z θ')) θ := rfl
  rw [hfun]
  have h1 : ContDiffOn ℝ 1 (deriv (fun θ' => Ψ z θ')) (Set.Ioo 0 (π / 2)) :=
    hslice.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have h2 : ContDiffOn ℝ 0 (deriv (deriv (fun θ' => Ψ z θ'))) (Set.Ioo 0 (π / 2)) :=
    h1.deriv_of_isOpen isOpen_Ioo (by norm_num)
  exact h2.continuousOn

/-- On `Iθ` the level-`0` `HkIntegrand` is the single weighted square
`g² w² σ` with `σ = sEta = sin(2θ)^{-η}` (the mixed-derivative sum of `HkIntegrand` is empty
at level `0`). -/
theorem HkIntegrand_zero_eq_sEta (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  have hkey : Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    simp [Work.Spaces.HkIntegrand]
  rw [hkey]
  exact Work.FTS.EllipticEst.mul_w_sin_rpow_sq (g z θ) (Work.Spaces.w z) hθ

/-- `HkMem α 0 (∂_θθΨ)` gives the slicewise `σ`-weighted integrability of `∂_θθΨ`: for
every `z > 0` the function `θ ↦ (∂_θθΨ(z,θ))² σ θ` is integrable on `Iθ`. -/
theorem integrableOn_pthIter2_sEta_of_HkMem {α : ℝ}
    (hmB : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ)) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have h1 := hmB.1 z hzI
  have h2 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
    h1.congr_fun (fun θ hθ => HkIntegrand_zero_eq_sEta α (Work.Spaces.pthIter 2 Ψ) z hθ)
      measurableSet_Icc
  have hw' : Work.Spaces.w z ≠ 0 := by
    rw [Work.Spaces.w]
    exact div_ne_zero (pow_ne_zero _ (by linarith)) (pow_ne_zero _ (ne_of_gt hz))
  have h3 := h2.mul_const ((Work.Spaces.w z) ^ 2)⁻¹
  refine h3.congr (Filter.Eventually.of_forall (fun θ => ?_))
  show ((Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.sEta θ) * ((Work.Spaces.w z) ^ 2)⁻¹
      = (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
  field_simp

/-- `|∂_θθΨ(z,·)|` is integrable on `Iθ`. -/
theorem integrableOn_abs_pthIter2_of_HkMem {α : ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hmB : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ)) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => |Work.Spaces.pthIter 2 Ψ z θ|) Work.Spaces.Iθ :=
  SgamBound.integrableOn_abs_of_sq_mul_sEta (continuousOn_pthIter2_of_strip hsm hz)
    (integrableOn_pthIter2_sEta_of_HkMem hmB hz)

/-- The absolute value of an interval integral over a subinterval of `(0,π/2)` is bounded by
the set integral of `|f|` over `Iθ`. -/
theorem abs_intervalIntegral_le_setIntegral {f : ℝ → ℝ} {a b : ℝ}
    (ha : a ∈ Set.Ioo (0 : ℝ) (π / 2)) (hb : b ∈ Set.Ioo (0 : ℝ) (π / 2))
    (hI : IntervalIntegrable (fun x => |f x|) volume 0 (π / 2)) :
    |∫ x in a..b, f x| ≤ ∫ x in Work.Spaces.Iθ, |f x| := by
  have hIeq : (∫ x in (0 : ℝ)..(π / 2), |f x|) = ∫ x in Work.Spaces.Iθ, |f x| := by
    rw [intervalIntegral.integral_of_le (by positivity), Work.Spaces.Iθ,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rcases le_total a b with hh | hh
  · exact le_trans (intervalIntegral.abs_integral_le_integral_abs hh) (by
      rw [← hIeq]
      exact intervalIntegral.integral_mono_interval ha.1.le hh hb.2.le
        (Eventually.of_forall (fun x => abs_nonneg _)) hI)
  · rw [intervalIntegral.integral_symm b a, abs_neg]
    exact le_trans (intervalIntegral.abs_integral_le_integral_abs hh) (by
      rw [← hIeq]
      exact intervalIntegral.integral_mono_interval hb.1.le hh ha.2.le
        (Eventually.of_forall (fun x => abs_nonneg _)) hI)

/-- **Boundedness of `∂_θΨ` on a slice.**  For `z > 0`, the first angular derivative of the
slice is bounded by its value at `π/4` plus the total `σ`-weighted `L¹`-mass of `∂_θθΨ`
(the fundamental theorem of calculus on `(0,π/2)`, whose endpoints are not in the open
interval). -/
theorem pth_le_of_strip_HkMem {α : ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hmB : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ)) {z : ℝ} (hz : 0 < z) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.pth Ψ z θ| ≤ |Work.Spaces.pth Ψ z (π / 4)|
        + ∫ t in Work.Spaces.Iθ, |Work.Spaces.pthIter 2 Ψ z t| := by
  have hslice : ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Ioo 0 (π / 2)) :=
    contDiffOn_slice_of_strip hsm hz 2
  have hint := integrableOn_abs_pthIter2_of_HkMem hsm hmB hz
  have hIi : IntervalIntegrable (fun t : ℝ => |Work.Spaces.pthIter 2 Ψ z t|)
      volume 0 (π / 2) := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ π / 2)]
    exact hint.mono_set Set.Ioc_subset_Icc_self
  have h1 : ContDiffOn ℝ 1 (fun t => Work.Spaces.pth Ψ z t) (Set.Ioo 0 (π / 2)) := by
    have hd : ContDiffOn ℝ 1 (deriv (fun θ' => Ψ z θ')) (Set.Ioo 0 (π / 2)) :=
      hslice.deriv_of_isOpen isOpen_Ioo (by norm_num)
    have hfun : (fun t => Work.Spaces.pth Ψ z t) = deriv (fun θ' => Ψ z θ') := rfl
    rwa [hfun]
  intro θ hθ
  have hpi4 : π / 4 ∈ Set.Ioo (0 : ℝ) (π / 2) := by
    refine ⟨by positivity, ?_⟩
    nlinarith [Real.pi_pos]
  have hseg : Set.uIcc (π / 4) θ ⊆ Set.Ioo (0 : ℝ) (π / 2) := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨lt_of_lt_of_le hpi4.1 h1, lt_of_le_of_lt h2 hθ.2⟩
    · exact ⟨lt_of_lt_of_le hθ.1 h1, lt_of_le_of_lt h2 hpi4.2⟩
  have hFTC : (∫ t in (π / 4)..θ, Work.Spaces.pthIter 2 Ψ z t)
      = Work.Spaces.pth Ψ z θ - Work.Spaces.pth Ψ z (π / 4) := by
    have := intervalIntegral.integral_deriv_of_contDiffOn_uIcc (h1.mono hseg)
    simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth] using this
  have hval : Work.Spaces.pth Ψ z θ
      = Work.Spaces.pth Ψ z (π / 4)
        + ∫ t in (π / 4)..θ, Work.Spaces.pthIter 2 Ψ z t := by linarith [hFTC]
  calc |Work.Spaces.pth Ψ z θ|
      = |Work.Spaces.pth Ψ z (π / 4)
          + ∫ t in (π / 4)..θ, Work.Spaces.pthIter 2 Ψ z t| := by rw [hval]
    _ ≤ |Work.Spaces.pth Ψ z (π / 4)|
          + |∫ t in (π / 4)..θ, Work.Spaces.pthIter 2 Ψ z t| := abs_add_le _ _
    _ ≤ |Work.Spaces.pth Ψ z (π / 4)|
          + ∫ t in Work.Spaces.Iθ, |Work.Spaces.pthIter 2 Ψ z t| := by
        have := abs_intervalIntegral_le_setIntegral hpi4 hθ hIi
        linarith

/-- **Boundedness of `Ψ` on a slice.**  For `z > 0`, the slice is bounded by its value at
`π/4` plus `(π/2)` times the bound of `∂_θΨ` obtained above. -/
theorem psi_le_of_strip_HkMem {α : ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hmB : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ)) {z : ℝ} (hz : 0 < z) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Ψ z θ| ≤ |Ψ z (π / 4)|
        + (π / 2) * (|Work.Spaces.pth Ψ z (π / 4)|
          + ∫ t in Work.Spaces.Iθ, |Work.Spaces.pthIter 2 Ψ z t|) := by
  have hslice : ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Ioo 0 (π / 2)) :=
    contDiffOn_slice_of_strip hsm hz 2
  have hpth := pth_le_of_strip_HkMem hsm hmB hz
  set B : ℝ := |Work.Spaces.pth Ψ z (π / 4)|
    + ∫ t in Work.Spaces.Iθ, |Work.Spaces.pthIter 2 Ψ z t| with hBdef
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    have := integral_nonneg (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun t => |Work.Spaces.pthIter 2 Ψ z t|) (fun t => abs_nonneg _)
    linarith [abs_nonneg (Work.Spaces.pth Ψ z (π / 4))]
  intro θ hθ
  have hpi4 : π / 4 ∈ Set.Ioo (0 : ℝ) (π / 2) := by
    refine ⟨by positivity, ?_⟩
    nlinarith [Real.pi_pos]
  have hseg : Set.uIcc (π / 4) θ ⊆ Set.Ioo (0 : ℝ) (π / 2) := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨lt_of_lt_of_le hpi4.1 h1, lt_of_le_of_lt h2 hθ.2⟩
    · exact ⟨lt_of_lt_of_le hθ.1 h1, lt_of_le_of_lt h2 hpi4.2⟩
  have hFTC : (∫ t in (π / 4)..θ, Work.Spaces.pth Ψ z t) = Ψ z θ - Ψ z (π / 4) := by
    have hc1 : ContDiffOn ℝ 1 (fun t => Ψ z t) (Set.Ioo (0 : ℝ) (π / 2)) :=
      hslice.of_le (by norm_num)
    have := intervalIntegral.integral_deriv_of_contDiffOn_uIcc (hc1.mono hseg)
    simpa only [Work.Spaces.pth] using this
  have hval : Ψ z θ = Ψ z (π / 4) + ∫ t in (π / 4)..θ, Work.Spaces.pth Ψ z t := by
    linarith [hFTC]
  have hbound : (∀ x ∈ Set.uIoc (π / 4) θ, ‖Work.Spaces.pth Ψ z x‖ ≤ B) := by
    intro x hx
    rw [Real.norm_eq_abs]
    refine le_trans (hpth x ?_) le_rfl
    rw [Set.mem_uIoc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨lt_of_lt_of_le hpi4.1 (le_of_lt h1), lt_of_le_of_lt h2 hθ.2⟩
    · exact ⟨lt_of_lt_of_le hθ.1 (le_of_lt h1), lt_of_le_of_lt h2 hpi4.2⟩
  have habs : |θ - π / 4| ≤ π / 2 := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos]
  calc |Ψ z θ| = |Ψ z (π / 4) + ∫ t in (π / 4)..θ, Work.Spaces.pth Ψ z t| := by rw [hval]
    _ ≤ |Ψ z (π / 4)| + |∫ t in (π / 4)..θ, Work.Spaces.pth Ψ z t| := abs_add_le _ _
    _ ≤ |Ψ z (π / 4)| + B * |θ - π / 4| := by
        have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
        rw [Real.norm_eq_abs] at h
        linarith
    _ ≤ |Ψ z (π / 4)| + B * (π / 2) := by
        have := mul_le_mul_of_nonneg_left habs hB0
        linarith
    _ = |Ψ z (π / 4)| + (π / 2) * B := by ring

/-! ## The target -/

theorem sliceBdd_of_hmB {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hmB : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ)) {z : ℝ} (hz : 0 < z) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Ψ z θ| ≤ C ∧ |deriv (fun θ' => Ψ z θ') θ| ≤ C := by
  have hpth := pth_le_of_strip_HkMem hsm hmB hz
  have hpsi := psi_le_of_strip_HkMem hsm hmB hz
  have hI0 : 0 ≤ ∫ t in Work.Spaces.Iθ, |Work.Spaces.pthIter 2 Ψ z t| :=
    integral_nonneg (fun t => abs_nonneg _)
  have hp40 : 0 ≤ |Work.Spaces.pth Ψ z (π / 4)| := abs_nonneg _
  have hB : 0 ≤ |Work.Spaces.pth Ψ z (π / 4)|
      + ∫ t in Work.Spaces.Iθ, |Work.Spaces.pthIter 2 Ψ z t| := add_nonneg hp40 hI0
  have h2B : 0 ≤ (π / 2) * (|Work.Spaces.pth Ψ z (π / 4)|
      + ∫ t in Work.Spaces.Iθ, |Work.Spaces.pthIter 2 Ψ z t|) :=
    mul_nonneg (by positivity) hB
  refine ⟨|Ψ z (π / 4)| + (π / 2) * (|Work.Spaces.pth Ψ z (π / 4)|
      + ∫ t in Work.Spaces.Iθ, |Work.Spaces.pthIter 2 Ψ z t|)
      + (|Work.Spaces.pth Ψ z (π / 4)| + ∫ t in Work.Spaces.Iθ, |Work.Spaces.pthIter 2 Ψ z t|)
      + 1, ?_, ?_⟩
  · linarith [abs_nonneg (Ψ z (π / 4))]
  · intro θ hθ
    have hψ := hpsi θ hθ
    have hθ' : |deriv (fun θ' => Ψ z θ') θ| = |Work.Spaces.pth Ψ z θ| := rfl
    constructor
    · linarith
    · rw [hθ']
      have hp := hpth θ hθ
      linarith [hp, abs_nonneg (Ψ z (π / 4))]

end Work.FTS.EllipticEst.Endpt
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Fstar_Hk_le_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable {F : ℝ → ℝ → ℝ}

/-! ## The moment relation for `B_j = F_*(D_z^j F)`

`Bmom F j z = ∫_θ D_z^j F(z,θ) sinθcos²θ dθ` is the `j`-th radial moment of `F`.  The single
analytic input of the estimate is that the moments form a *tower*: the `j`-th moment is a
primitive of `B_{j+1}(s)/s`.  This is `moment_relation` applied to `u = D_z^j F`, whose
`z`-derivative is `D_z^{j+1}F/s`. -/

/-- The `θ`-integral of `∂_z(D_z^j F)` against `sinθcos²θ` is `B_{j+1}(s)/s`. -/
theorem Bmom_deriv_integral (j : ℕ) {s : ℝ} (hs : 0 < s) :
    (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.pz (Work.Spaces.DzIter j F) s θ * Work.Elliptic.sinCos2 θ)
      = Bmom F (j + 1) s / s := by
  have hid : ∀ θ : ℝ, Work.Spaces.pz (Work.Spaces.DzIter j F) s θ
      = Work.Spaces.DzIter (j + 1) F s θ / s := by
    intro θ
    have h1 : Work.Spaces.DzIter (j + 1) F s θ
        = s * Work.Spaces.pz (Work.Spaces.DzIter j F) s θ := by
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz]
    rw [h1, mul_div_cancel_left₀ _ hs.ne']
  rw [Bmom_eq_Fstar_DzIter, Work.Elliptic.Fstar]
  rw [show (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.pz (Work.Spaces.DzIter j F) s θ * Work.Elliptic.sinCos2 θ)
      = ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.DzIter (j + 1) F s θ / s) * Work.Elliptic.sinCos2 θ from
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by rw [hid θ])]
  rw [show (fun θ : ℝ => (Work.Spaces.DzIter (j + 1) F s θ / s) * Work.Elliptic.sinCos2 θ)
      = fun θ : ℝ => (1 / s) * (Work.Spaces.DzIter (j + 1) F s θ
          * Work.Elliptic.sinCos2 θ) from by
    funext θ; ring]
  rw [MeasureTheory.integral_const_mul]
  ring

/-- **The moment tower.**  For `0 < a < b`,
`B_j(b) = B_j(a) + ∫_a^b B_{j+1}(s)/s ds`, whenever `j + 1 ≤ k`. -/
theorem BFstar_relation (α : ℝ) (k : ℕ) (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    (j : ℕ) (hj : j + 1 ≤ k) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Bmom F j b = Bmom F j a + ∫ s in a..b, Bmom F (j + 1) s / s := by
  have hrel := moment_relation (Work.Spaces.DzIter j F) (hF.DzIter j)
    (fun a b ha hab => boxIntegrable_DzIter α k hF hmem j hj a b ha hab)
    (fun z hz => integrableOn_DzIter_mul_sinCos2 (F := F) α k hF hmem j (by omega) hz)
    ha hab
  rw [Bmom_eq_Fstar_DzIter, Bmom_eq_Fstar_DzIter, hrel]
  congr 1
  rw [show (∫ s in Set.Icc a b, (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.pz (Work.Spaces.DzIter j F) s θ * Work.Elliptic.sinCos2 θ))
      = ∫ s in Set.Icc a b, Bmom F (j + 1) s / s from
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      (fun s hs => Bmom_deriv_integral (F := F) j (lt_of_lt_of_le ha hs.1))]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le]

/-- **The moment tower, anchored at `c`.**  For every `y > 0`,
`B_j(y) = B_j(c) + ∫_c^y B_{j+1}(s)/s ds`. -/
theorem Bmom_eq_const_add_integral (α : ℝ) (k : ℕ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j + 1 ≤ k) {c : ℝ} (hc : 0 < c) :
    ∀ y : ℝ, 0 < y → Bmom F j y = Bmom F j c + ∫ s in c..y, Bmom F (j + 1) s / s := by
  intro y hy
  rcases lt_trichotomy y c with hlt | heq | hgt
  · have hrel := BFstar_relation α k hF hmem j hj hy hlt
    rw [hrel, intervalIntegral.integral_symm]
    ring
  · subst heq
    simp
  · exact BFstar_relation α k hF hmem j hj hc hgt

/-! ## Continuity of the moments -/

/-- The `j`-th moment is continuous on `(0,∞)`, for `j + 1 ≤ k`. -/
theorem continuousOn_Bmom (α : ℝ) (k : ℕ) (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    (j : ℕ) (hj : j + 1 ≤ k) :
    ContinuousOn (fun z => Bmom F j z) (Set.Ioi 0) := by
  intro z hz
  have hz0 : 0 < z := hz
  set a : ℝ := z / 2 with ha_def
  have ha0 : 0 < a := by rw [ha_def]; linarith
  have haz : a < z := by rw [ha_def]; linarith
  have hb : a < z + a := by linarith
  have hg : IntegrableOn (fun s => Bmom F (j + 1) s / s) (Set.uIcc a (z + a)) := by
    rw [Set.uIcc_of_le hb.le]
    exact integrableOn_Bmom_div α k hF hmem (j + 1) (by omega) a (z + a) ha0 hb
  have hΦ : ContinuousOn (fun x : ℝ => ∫ s in a..x, Bmom F (j + 1) s / s)
      (Set.uIcc a (z + a)) :=
    intervalIntegral.continuousOn_primitive_interval hg
  have hnhds : Set.uIcc a (z + a) ∈ 𝓝 z := by
    rw [Set.uIcc_of_le hb.le]
    exact Icc_mem_nhds haz (by linarith)
  have hcontΦ : ContinuousWithinAt (fun x : ℝ => ∫ s in a..x, Bmom F (j + 1) s / s)
      (Set.Ioi 0) z :=
    (hΦ.continuousAt hnhds).continuousWithinAt
  have hev : (fun x : ℝ => Bmom F j x) =ᶠ[𝓝[Set.Ioi 0] z]
      (fun x : ℝ => Bmom F j a + ∫ s in a..x, Bmom F (j + 1) s / s) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact Bmom_eq_const_add_integral α k hF hmem j hj ha0 x hx
  have hz_e : Bmom F j z = Bmom F j a + ∫ s in a..z, Bmom F (j + 1) s / s :=
    Bmom_eq_const_add_integral α k hF hmem j hj ha0 z hz0
  exact (continuousWithinAt_const.add hcontΦ).congr_of_eventuallyEq hev hz_e

/-! ## Differentiability of the moments -/

/-- The `j`-th moment is differentiable on `(0,∞)` with derivative `B_{j+1}(z)/z`, for
`j + 2 ≤ k`. -/
theorem hasDerivAt_Bmom (α : ℝ) (k : ℕ) (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    (j : ℕ) (hj : j + 2 ≤ k) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z => Bmom F j z) (Bmom F (j + 1) z / z) z := by
  have hz0 : 0 < z := hz
  set a : ℝ := z / 2 with ha_def
  have ha0 : 0 < a := by rw [ha_def]; linarith
  have haz : a < z := by rw [ha_def]; linarith
  have hcont : ContinuousAt (fun s : ℝ => Bmom F (j + 1) s / s) z :=
    ((continuousOn_Bmom α k hF hmem (j + 1) (by omega)).continuousAt
      (isOpen_Ioi.mem_nhds hz0)).div continuousAt_id (by simpa using hz0.ne')
  have hg_cont : ContinuousOn (fun s : ℝ => Bmom F (j + 1) s / s) (Set.Ioi 0) :=
    (continuousOn_Bmom α k hF hmem (j + 1) (by omega)).div continuousOn_id
      (fun s hs => hs.ne')
  have hInt : IntervalIntegrable (fun s : ℝ => Bmom F (j + 1) s / s) volume a z := by
    rw [intervalIntegrable_iff]
    refine (integrableOn_Bmom_div α k hF hmem (j + 1) (by omega) a z ha0 haz).mono_set ?_
    intro x hx
    rw [Set.uIoc_of_le haz.le] at hx
    exact ⟨le_of_lt hx.1, hx.2⟩
  have hder := intervalIntegral.integral_hasDerivAt_right hInt
    ((hg_cont.stronglyMeasurableAtFilter isOpen_Ioi) z hz0) hcont
  have hev : (fun x : ℝ => Bmom F j x) =ᶠ[𝓝 z]
      (fun x : ℝ => Bmom F j a + ∫ s in a..x, Bmom F (j + 1) s / s) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz0] with x hx
    exact Bmom_eq_const_add_integral α k hF hmem j (by omega) ha0 x hx
  exact hev.hasDerivAt_iff.mpr (hder.const_add (Bmom F j a))

/-- **A.e. differentiability of the top moment.**  For `k ≥ 1`, for almost every `z > 0` the
moment `B_{k-1}` is differentiable at `z` with derivative `B_k(z)/z`. -/
theorem ae_hasDerivAt_Bmom (α : ℝ) (k : ℕ) (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    (hk : 1 ≤ k) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      HasDerivAt (fun z => Bmom F (k - 1) z) (Bmom F k z / z) z := by
  set P : ℝ → Prop := fun x => HasDerivAt (fun x => Bmom F (k - 1) x) (Bmom F k x / x) x
    with hP
  have key : ∀ n : ℕ, ∀ᵐ x ∂(volume.restrict (Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2))),
      P x := by
    intro n
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hlt : (1 : ℝ) / ((n : ℝ) + 1) < (n : ℝ) + 2 := by
      have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h2 : (1 : ℝ) ≤ ((n : ℝ) + 1) * ((n : ℝ) + 2) := by
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith
      rw [div_lt_iff₀ h1]
      nlinarith [h2]
    have hInt : IntervalIntegrable (fun s : ℝ => Bmom F k s / s) volume
        (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2) := by
      rw [intervalIntegrable_iff]
      refine (integrableOn_Bmom_div α k hF hmem k le_rfl _ _ hpos hlt).mono_set ?_
      intro x hx
      rw [Set.uIoc_of_le hlt.le] at hx
      exact ⟨le_of_lt hx.1, hx.2⟩
    have hldt := IntervalIntegrable.ae_hasDerivAt_integral hInt
    rw [show Set.uIcc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2)
        = Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2) from Set.uIcc_of_le hlt.le] at hldt
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hldt] with x hx hxmem
    refine ((hx hxmem (1 / ((n : ℝ) + 1))
      ⟨le_rfl, hlt.le⟩).const_add (Bmom F (k - 1) (1 / ((n : ℝ) + 1)))).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioi.mem_nhds (lt_of_lt_of_le hpos hxmem.1)] with y hy
    have h := Bmom_eq_const_add_integral α k hF hmem (k - 1) (by omega) hpos y hy
    simpa only [Nat.sub_add_cancel hk, Nat.sub_add_cancel (show 1 ≤ k by omega)] using h
  have keynull : ∀ n : ℕ, volume {x | x ∈ Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2)
      ∧ ¬ P x} = 0 := by
    intro n
    have h := key n
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc, MeasureTheory.ae_iff] at h
    simpa only [not_imp] using h
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi, MeasureTheory.ae_iff]
  refine measure_mono_null ?_ (measure_iUnion_null keynull)
  intro x hx
  rw [Set.mem_setOf_eq] at hx
  obtain ⟨hx0, hxn⟩ := not_imp.mp hx
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ,
      1 / ((n : ℝ) + 1) ≤ x ∧ x ≤ (n : ℝ) + 2 := by
    obtain ⟨n, hn⟩ := exists_nat_ge (max x (1 / x))
    refine ⟨n, ?_, ?_⟩
    · have hx1 : 1 / x ≤ (n : ℝ) := le_trans (le_max_right _ _) hn
      have : 1 ≤ x * (n : ℝ) := by
        rw [div_le_iff₀ hx0] at hx1
        linarith
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    · have hxn' : x ≤ (n : ℝ) := le_trans (le_max_left _ _) hn
      linarith
  exact Set.mem_iUnion.mpr ⟨n, ⟨hn1, hn2⟩, hxn⟩

/-! ## The identity `(D_z^j F_*)(z) = B_j(z)` -/

/-- **The `D_z`-iterates of the angular moment are the moments.**  For `j + 1 ≤ k` and every
`z > 0`, `radIter (B_0) j z = B_j z`. -/
theorem radIter_Bmom_eq (α : ℝ) (k : ℕ) (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) :
    ∀ j : ℕ, j + 1 ≤ k → ∀ z : ℝ, 0 < z →
      radIter (fun z => Bmom F 0 z) j z = Bmom F j z := by
  intro j
  induction j with
  | zero => intro _ z _; rfl
  | succ n ih =>
      intro hj z hz
      rw [radIter_succ]
      have hev : (radIter (fun z => Bmom F 0 z) n) =ᶠ[𝓝 z] (fun z => Bmom F n z) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih (by omega) z' hz'
      rw [hev.deriv_eq, (hasDerivAt_Bmom α k hF hmem n (by omega) hz).deriv]
      field_simp

/-- **The top `D_z`-iterate**, almost everywhere: for `k ≥ 1` and almost every `z > 0`,
`radIter (B_0) k z = B_k z`. -/
theorem ae_radIter_Bmom_eq_top (α : ℝ) (k : ℕ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (hk : 1 ≤ k) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      radIter (fun z => Bmom F 0 z) k z = Bmom F k z := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have h1 := ae_hasDerivAt_Bmom α (m + 1) hF hmem (by omega)
  simp only [Nat.add_sub_cancel] at h1
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi] at h1
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [h1] with z hzimp hzmem
  have hz0 : 0 < z := hzmem
  rw [radIter_succ]
  have hev : (radIter (fun z => Bmom F 0 z) m) =ᶠ[𝓝 z] (fun z => Bmom F m z) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz0] with z' hz'
    exact radIter_Bmom_eq α (m + 1) hF hmem m (by omega) z' hz'
  rw [hev.deriv_eq, (hzimp hzmem).deriv]
  field_simp

/-! ## The slice estimate for `F_*(F)·sin 2θ` -/

/-- **Pointwise domination of the `H^k`-integrand of `F_*(F)·sin 2θ`**, almost everywhere in
`z`.  The `D_z`-summands are the squares of the moments `PsiInt F i z` times `sin 2θ`, and the
mixed summands are the moments times the angular profiles `D_θ^i (sin 2θ)`. -/
theorem HkIntegrand_fstarSin_le_open (α : ℝ) (k : ℕ) (hF : SmoothOpen F)
    (hα : 0 < α) (hα1 : α ≤ 1) (hmem : Work.Spaces.HkMem α k F) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) z θ
        ≤ (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta)
          + (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
              * FstarHkOpen.angKsum k) := by
  have hid_lt : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), ∀ i < k,
      radIter (fun z => Bmom F 0 z) i z = Bmom F i z := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz i hi
    exact radIter_Bmom_eq α k hF hmem i (by omega) z hz
  have hid_top : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      radIter (fun z => Bmom F 0 z) k z = Bmom F k z := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk
    · subst hk0
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z _
      rfl
    · exact ae_radIter_Bmom_eq_top α k hF hmem hk
  filter_upwards [hid_lt, hid_top, MeasureTheory.ae_restrict_mem measurableSet_Ioi]
    with z hlt htop hz
  intro θ hθ
  have hg : (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ))
      = fun z θ => Bmom F 0 z * Real.sin (2 * θ) := by
    funext z θ
    rw [Bmom_zero]
  have hDz : ∀ i ≤ k, Work.Spaces.DzIter i
      (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) z θ
        = PsiInt F i z * Real.sin (2 * θ) := by
    intro i hi
    rw [hg, DzIter_fstarSin_eq]
    congr 1
    rcases lt_or_eq_of_le hi with h | h
    · exact hlt i h
    · subst h; exact htop
  have hmix : ∀ i j : ℕ, 1 ≤ i → i + j ≤ k →
      Work.Spaces.mixed j i (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) z θ
        = PsiInt F j z * sinProf i θ := by
    intro i j hi hij
    rw [hg, mixed_fstarSin_eq]
    congr 1
    exact hlt j (by omega)
  have hs0 : 0 ≤ Real.sin (2 * θ) := FstarHkOpen.sin_two_nonneg hθ
  have hγ1 : 1 ≤ Work.Spaces.gam α := le_of_lt (Work.Spaces.one_lt_gam hα)
  have hγ2 : Work.Spaces.gam α ≤ 2 := by rw [Work.Spaces.gam]; linarith
  have hpos2η : 0 ≤ (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) := Real.rpow_nonneg hs0 _
  have hπ2 : (0 : ℝ) ≤ π / 2 := by positivity
  have hUj : ∀ i : ℕ, 0 ≤ FstarHkOpen.Uj F z i := fun i => FstarHkOpen.Uj_nonneg F z i
  have hle_K : ∀ i : ℕ, i ≤ k → FstarHkOpen.angK i ≤ FstarHkOpen.angKsum k := by
    intro i hi
    rw [FstarHkOpen.angKsum]
    exact Finset.single_le_sum (fun a _ => (FstarHkOpen.angK_pos a).le)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  have hCS : ∀ i ≤ k, (PsiInt F i z) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ (π / 2) * FstarHkOpen.Uj F z i := fun i hi =>
    PsiInt_sq_mul_w_le_open F hF i hz
      (integrableOn_zSummand α k hF hmem i hi (Set.mem_Ici.mpr hz.le))
  rw [Work.Spaces.HkIntegrand]
  refine add_le_add ?_ ?_
  · calc ∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i
            (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = ∑ i ∈ Finset.range (k + 1), (PsiInt F i z * Real.sin (2 * θ)
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [hDz i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
      _ = ∑ i ∈ Finset.range (k + 1), (PsiInt F i z) ^ 2 * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) := by
          refine Finset.sum_congr rfl fun i _ => FstarHkOpen.zTerm_eq_on (PsiInt F i z) z θ hθ
      _ ≤ ∑ i ∈ Finset.range (k + 1), ((π / 2) * FstarHkOpen.Uj F z i)
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) := by
          refine Finset.sum_le_sum fun i hi => ?_
          exact mul_le_mul_of_nonneg_right
            (hCS i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))) hpos2η
      _ = (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
  · calc ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i
              (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0)
        = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then (PsiInt F j z * sinProf i θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          by_cases hc : 1 ≤ i ∧ i + j ≤ k
          · rw [if_pos hc, if_pos hc, hmix i j hc.1 hc.2]
          · rw [if_neg hc, if_neg hc]
      _ = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then (PsiInt F j z) ^ 2 * (Work.Spaces.w z) ^ 2
              * ((sinProf i θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
              else 0) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          by_cases hc : 1 ≤ i ∧ i + j ≤ k
          · rw [if_pos hc, if_pos hc]
            exact FstarHkOpen.mixedTerm_eq_on α (PsiInt F j z) z (sinProf i) θ hθ
          · rw [if_neg hc, if_neg hc]
      _ ≤ ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            ((π / 2) * FstarHkOpen.Uj F z j * FstarHkOpen.angKsum k) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          by_cases hc : 1 ≤ i ∧ i + j ≤ k
          · rw [if_pos hc]
            have hi' : i ≤ k := by omega
            have hj' : j ≤ k := by omega
            have h1 : (PsiInt F j z) ^ 2 * (Work.Spaces.w z) ^ 2
                * ((sinProf i θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
                ≤ ((π / 2) * FstarHkOpen.Uj F z j) * FstarHkOpen.angK i :=
              mul_le_mul (hCS j hj')
                (FstarHkOpen.angK_bound i (Work.Spaces.gam α) hγ1 hγ2 hθ)
                (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _))
                (mul_nonneg hπ2 (hUj j))
            have h2 : ((π / 2) * FstarHkOpen.Uj F z j) * FstarHkOpen.angK i
                ≤ ((π / 2) * FstarHkOpen.Uj F z j) * FstarHkOpen.angKsum k :=
              mul_le_mul_of_nonneg_left (hle_K i hi') (mul_nonneg hπ2 (hUj j))
            exact le_trans h1 h2
          · rw [if_neg hc]
            exact mul_nonneg (mul_nonneg hπ2 (hUj j)) (FstarHkOpen.angKsum_nonneg k)
      _ = (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
            * FstarHkOpen.angKsum k) := by
          have hrow : ∀ i : ℕ, (∑ j ∈ Finset.range (k + 1),
              ((π / 2) * FstarHkOpen.Uj F z j * FstarHkOpen.angKsum k))
              = (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
                * FstarHkOpen.angKsum k := by
            intro i
            rw [← Finset.sum_mul, Finset.mul_sum]
          refine (Finset.sum_congr rfl (fun i _ => hrow i)).trans ?_
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring

set_option maxHeartbeats 3000000 in
/-- **The slice estimate.**  For almost every `z ∈ Iz`, the `θ`-integral of the `H^k`-integrand
of `F_*(F)·sin 2θ` is bounded by `hkConst k` times the `θ`-integral of the `H^k`-integrand
of `F`. -/
theorem slice_Hk_le_open (α : ℝ) (k : ℕ) (hF : SmoothOpen F)
    (hα : 0 < α) (hα1 : α ≤ 1) (hmem : Work.Spaces.HkMem α k F) :
    ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
          (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) z θ)
        ≤ FstarHkOpen.hkConst k
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) := by
  have hmeas : (volume.restrict Work.Spaces.Iz) = volume.restrict (Set.Ioi 0) :=
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
  rw [hmeas]
  have hae_le : ∀ {f g : ℝ → ℝ}, (∀ θ ∈ Work.Spaces.Iθ, f θ ≤ g θ) →
      f ≤ᵐ[volume.restrict Work.Spaces.Iθ] g := by
    intro f g h
    show ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), f θ ≤ g θ
    rw [ae_restrict_iff' (show MeasurableSet Work.Spaces.Iθ from by
      rw [Work.Spaces.Iθ]; exact measurableSet_Icc)]
    exact Eventually.of_forall h
  filter_upwards [HkIntegrand_fstarSin_le_open α k hF hα hα1 hmem,
    MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz hzmem
  have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hzmem.le
  have hsumU : (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ := by
    have hint : ∀ j ∈ Finset.range (k + 1), IntegrableOn (fun θ : ℝ =>
        (Work.Spaces.DzIter j F z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        Work.Spaces.Iθ :=
      fun j hj => integrableOn_zSummand α k hF hmem j
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hzI
    have hsum : (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
        = ∫ θ in Work.Spaces.Iθ, ∑ j ∈ Finset.range (k + 1), (Work.Spaces.DzIter j F z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      simp only [FstarHkOpen.Uj]
      rw [← MeasureTheory.integral_finsetSum]
      exact hint
    rw [hsum]
    refine MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ => Finset.sum_nonneg fun j _ => sq_nonneg _)
      (hmem.1 z hzI) (Eventually.of_forall fun θ => ?_)
    rw [Work.Spaces.HkIntegrand]
    exact le_add_of_nonneg_right (Work.Spaces.hkMixedSum_nonneg α k F z θ)
  have hcont1 : Continuous (fun θ : ℝ => (π / 2) * (∑ j ∈ Finset.range (k + 1),
      FstarHkOpen.Uj F z j) * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta)) := by
    refine Continuous.mul continuous_const ?_
    refine Continuous.rpow (by fun_prop) continuous_const (fun θ => Or.inr ?_)
    rw [Work.Spaces.eta]; norm_num
  have hBc : (0 : ℝ) ≤ (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1),
      FstarHkOpen.Uj F z j) * FstarHkOpen.angKsum k) :=
    mul_nonneg (by positivity) (mul_nonneg
      (mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => FstarHkOpen.Uj_nonneg F z j))
      (FstarHkOpen.angKsum_nonneg k))
  have hMint : IntegrableOn (fun θ : ℝ => (π / 2) * (∑ j ∈ Finset.range (k + 1),
      FstarHkOpen.Uj F z j) * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta)
      + (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
        * FstarHkOpen.angKsum k)) Work.Spaces.Iθ :=
    (hcont1.add continuous_const).continuousOn.integrableOn_compact isCompact_Icc
  have hvol : volume.real Work.Spaces.Iθ = π / 2 := by
    rw [MeasureTheory.measureReal_def, Work.Spaces.Iθ, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  have hZa : ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) ≤ π / 2 := by
    have hle : ∀ θ ∈ Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) ≤ (1 : ℝ) :=
      fun θ hθ => Real.rpow_le_one (FstarHkOpen.sin_two_nonneg hθ)
        (FstarHkOpen.sin_two_le_one θ) (by rw [Work.Spaces.eta]; norm_num)
    calc ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta)
        ≤ ∫ θ in Work.Spaces.Iθ, (1 : ℝ) := by
          refine MeasureTheory.integral_mono_of_nonneg
            (hae_le fun θ hθ =>
              Real.rpow_nonneg (FstarHkOpen.sin_two_nonneg hθ) _)
            (integrableOn_const (s := Work.Spaces.Iθ) (C := (1 : ℝ))
              (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
            (hae_le hle)
      _ = π / 2 := FstarHkOpen.integral_Iθ_one
  have hZann : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) := by
    refine MeasureTheory.integral_nonneg_of_ae ?_
    exact hae_le fun θ hθ => Real.rpow_nonneg (FstarHkOpen.sin_two_nonneg hθ) _
  have hIntM : ∫ θ in Work.Spaces.Iθ, ((π / 2) * (∑ j ∈ Finset.range (k + 1),
        FstarHkOpen.Uj F z j) * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta)
      + (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
        * FstarHkOpen.angKsum k))
      = (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta))
        + (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
          * FstarHkOpen.angKsum k) * (π / 2) := by
    have hInt1 : IntegrableOn (fun θ : ℝ => (π / 2) * (∑ j ∈ Finset.range (k + 1),
        FstarHkOpen.Uj F z j) * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta))
        Work.Spaces.Iθ := by
      rw [Work.Spaces.Iθ]
      exact hcont1.continuousOn.integrableOn_compact isCompact_Icc
    have hInt2 : IntegrableOn (fun _ : ℝ => (k + 1) * ((π / 2)
        * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
        * FstarHkOpen.angKsum k)) Work.Spaces.Iθ := by
      rw [Work.Spaces.Iθ]
      exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    rw [MeasureTheory.integral_add hInt1 hInt2]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.setIntegral_const, smul_eq_mul, hvol]
    ring
  have hπ0 : (0 : ℝ) ≤ π / 2 := by positivity
  have hk0 : (0 : ℝ) ≤ (k + 1) := by positivity
  have hσ : 0 ≤ ∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j :=
    Finset.sum_nonneg fun j _ => FstarHkOpen.Uj_nonneg F z j
  have hK : 0 ≤ FstarHkOpen.angKsum k := FstarHkOpen.angKsum_nonneg k
  have hfin : (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta))
        + (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
          * FstarHkOpen.angKsum k) * (π / 2)
      ≤ FstarHkOpen.hkConst k * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) := by
    have h1 : (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta))
        ≤ (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) * (π / 2) :=
      mul_le_mul_of_nonneg_left hZa (mul_nonneg hπ0 hσ)
    have h2 : (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) * (π / 2)
          + (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
            * FstarHkOpen.angKsum k) * (π / 2)
        ≤ FstarHkOpen.hkConst k * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) := by
      have hAB : (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
            + (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
              * FstarHkOpen.angKsum k)
          ≤ (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) * (1 + (k + 1))
            * (1 + FstarHkOpen.angKsum k) := by
        have he : (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
            + (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
              * FstarHkOpen.angKsum k)
          = (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
            * (1 + (k + 1) * FstarHkOpen.angKsum k) := by ring
        rw [he]
        have hfac : 1 + (k + 1) * FstarHkOpen.angKsum k
            ≤ (1 + (k + 1)) * (1 + FstarHkOpen.angKsum k) := by
          nlinarith [hk0, hK, mul_nonneg hk0 hK]
        have hpos : (0 : ℝ) ≤ (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) :=
          mul_nonneg hπ0 hσ
        calc (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
              * (1 + (k + 1) * FstarHkOpen.angKsum k)
            = ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j))
                * (1 + (k + 1) * FstarHkOpen.angKsum k) := by ring
          _ ≤ ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j))
                * ((1 + (k + 1)) * (1 + FstarHkOpen.angKsum k)) :=
              mul_le_mul_of_nonneg_left hfac hpos
          _ = (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) * (1 + (k + 1))
                * (1 + FstarHkOpen.angKsum k) := by ring
      have h3 : (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
            * (1 + (k + 1)) * (1 + FstarHkOpen.angKsum k) * (π / 2)
          ≤ FstarHkOpen.hkConst k * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) := by
        have heq : (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
              * (1 + (k + 1)) * (1 + FstarHkOpen.angKsum k) * (π / 2)
            = ((π / 2) ^ 2 * (1 + (k + 1)) * (1 + FstarHkOpen.angKsum k))
              * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) := by ring
        rw [heq, FstarHkOpen.hkConst]
        have hc0 : (0 : ℝ) ≤ (π / 2) ^ 2 * (1 + (k + 1)) * (1 + FstarHkOpen.angKsum k) :=
          mul_nonneg (mul_nonneg (sq_nonneg _) (by linarith : (0:ℝ) ≤ 1 + (k + 1)))
            (by linarith : (0:ℝ) ≤ 1 + FstarHkOpen.angKsum k)
        nlinarith [hc0, hσ]
      calc (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) * (π / 2)
            + (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
              * FstarHkOpen.angKsum k) * (π / 2)
          = ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
              + (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
                * FstarHkOpen.angKsum k)) * (π / 2) := by ring
        _ ≤ ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) * (1 + (k + 1))
              * (1 + FstarHkOpen.angKsum k)) * (π / 2) := mul_le_mul_of_nonneg_right hAB hπ0
        _ ≤ FstarHkOpen.hkConst k * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) := h3
        _ ≤ FstarHkOpen.hkConst k * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) :=
            mul_le_mul_of_nonneg_left hsumU (FstarHkOpen.hkConst_pos k).le
    linarith [h1, h2]
  calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
          (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) z θ)
      ≤ ∫ θ in Work.Spaces.Iθ, ((π / 2) * (∑ j ∈ Finset.range (k + 1),
          FstarHkOpen.Uj F z j) * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta)
        + (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
          * FstarHkOpen.angKsum k)) := by
        refine MeasureTheory.integral_mono_of_nonneg
          (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k _ z θ)
          hMint (hae_le fun θ hθ => hz θ hθ)
    _ = (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta))
        + (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
          * FstarHkOpen.angKsum k) * (π / 2) := hIntM
    _ ≤ FstarHkOpen.hkConst k * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) :=
        hfin

/-- **Lemma `HardyInequality4` for the angular moment** (Elgindi, §'Elliptic Regularity
Estimates'): for `0 < α ≤ 1` and `F` of class `C^∞` on the open quadrant with `F ∈ ℋ^k`, the
function `F_*(F)(z)·sin 2θ` is bounded in `ℋ^k` by a *universal* multiple (independent of `α`)
of `F`:

`|F_*(F)·sin 2θ|_{H^k} ≤ C_k |F|_{H^k}`. -/
theorem Fstar_Hk_le_open (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) →
      Work.Spaces.HkMem α k F →
      Work.Spaces.HkNorm α k (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ))
        ≤ C * Work.Spaces.HkNorm α k F := by
  classical
  refine ⟨FstarHkOpen.hkConst k + 1,
    by linarith [FstarHkOpen.hkConst_pos k], ?_⟩
  intro α F hα hα1 hsm hmem
  have hF : SmoothOpen F := smoothOpen_of_forall hsm
  have hslice := slice_Hk_le_open α k hF hα hα1 hmem
  have hsq : Work.Spaces.HkSq α k (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ))
      ≤ (FstarHkOpen.hkConst k + 1) ^ 2 * Work.Spaces.HkSq α k F := by
    rw [Work.Spaces.HkSq, Work.Spaces.HkSq, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun z => integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α k _ z θ)
      (hmem.2.const_mul ((FstarHkOpen.hkConst k + 1) ^ 2)) ?_
    filter_upwards [hslice] with z hz
    have h2 : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ :=
      integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k F z θ
    have h3 : FstarHkOpen.hkConst k ≤ (FstarHkOpen.hkConst k + 1) ^ 2 := by
      nlinarith [FstarHkOpen.hkConst_pos k]
    exact le_trans hz (mul_le_mul_of_nonneg_right h3 h2)
  rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
  refine le_trans (Real.sqrt_le_sqrt hsq) (le_of_eq ?_)
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith [FstarHkOpen.hkConst_pos k])]

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.GbarSin.Fstar_local_integrableOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.GbarSin

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Elementary estimates -/

/-- AM–GM in the form used below: `√X ≤ (X + 1)/2` for `X ≥ 0`. -/
theorem sqrt_le_add_one_div_two {X : ℝ} (hX : 0 ≤ X) : Real.sqrt X ≤ (X + 1) / 2 := by
  rw [Real.sqrt_le_iff]
  exact ⟨by positivity, by nlinarith [sq_nonneg (1 - X)]⟩

/-- The `j`-th summand of the `H^k`-integrand of the source, integrated over the angle, is
dominated by the full angular slice of the `H^k`-integrand. -/
theorem slice_le_HkIntegrand (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j ≤ k) {r : ℝ} (hr : r ∈ Work.Spaces.Iz) :
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j F r θ
        * (Work.Spaces.w r / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ :=
  integral_mono_of_nonneg
    (Eventually.of_forall fun θ =>
      sq_nonneg (Work.Spaces.DzIter j F r θ
        * (Work.Spaces.w r / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
    (hmem.1 r hr)
    (Eventually.of_forall fun θ => Work.Spaces.sq_le_HkIntegrand_z α k F r θ j hj)

/-! ## The pointwise Cauchy–Schwarz bound for the angular moment -/

/-- **The `L¹` bound for the angular moment.**  For `r > 0`,
`|F_*(D_z^j F)(r)|/r ≤ ((π/2)·∫_θ HkIntegrand α k F r θ + 1)/2`, the right-hand side being an
integrable function of `r` on every bounded interval of `(0,∞)`. -/
theorem Fstar_div_le_majorant (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) (j : ℕ)
    (hj : j ≤ k) {r : ℝ} (hr : 0 < r) :
    |Work.Elliptic.Fstar (Work.Spaces.DzIter j F) r| / r
      ≤ ((Real.pi / 2) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ) + 1) / 2 := by
  have hrI : r ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz]; exact le_of_lt hr
  have hGnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ :=
    integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k F r θ
  set X : ℝ := (Real.pi / 2) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ)
    with hX
  have hXnn : 0 ≤ X := by rw [hX]; exact mul_nonneg (by positivity) hGnn
  -- Cauchy–Schwarz for the angular moment, with the slice dominated by the full integrand
  have hsq : (Work.Elliptic.Fstar (Work.Spaces.DzIter j F) r) ^ 2 * (Work.Spaces.w r) ^ 2
      ≤ X := by
    rw [hX]
    exact le_trans (FstarDzIter_sq_mul_w_le_open α k F hF hmem j hj hr)
      (mul_le_mul_of_nonneg_left (slice_le_HkIntegrand α k F hmem j hj hrI) (by positivity))
  have hmul : (Work.Elliptic.Fstar (Work.Spaces.DzIter j F) r * Work.Spaces.w r) ^ 2 ≤ X := by
    rw [mul_pow]; exact hsq
  -- `r · w(r) = (1+r)²/r ≥ 1`, so that `1/r ≤ w(r)`
  have hweight : 1 ≤ Work.Spaces.w r * r := by
    rw [Work.Spaces.w]
    field_simp
    nlinarith [hr, sq_nonneg r, pow_pos hr 3]
  have hw_pos : 0 < Work.Spaces.w r := by rw [Work.Spaces.w]; positivity
  have h1r : r⁻¹ ≤ Work.Spaces.w r := by
    have h : 1 / r ≤ Work.Spaces.w r := (div_le_iff₀ hr).mpr hweight
    simpa only [one_div] using h
  calc |Work.Elliptic.Fstar (Work.Spaces.DzIter j F) r| / r
      = |Work.Elliptic.Fstar (Work.Spaces.DzIter j F) r| * r⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ |Work.Elliptic.Fstar (Work.Spaces.DzIter j F) r| * Work.Spaces.w r :=
        mul_le_mul_of_nonneg_left h1r (abs_nonneg _)
    _ = |Work.Elliptic.Fstar (Work.Spaces.DzIter j F) r * Work.Spaces.w r| := by
        rw [abs_mul, abs_of_nonneg hw_pos.le]
    _ = Real.sqrt ((Work.Elliptic.Fstar (Work.Spaces.DzIter j F) r * Work.Spaces.w r) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt X := Real.sqrt_le_sqrt hmul
    _ ≤ (X + 1) / 2 := sqrt_le_add_one_div_two hXnn
    _ = ((Real.pi / 2) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ) + 1) / 2 := by
        rw [hX]

/-! ## Measurability of the angular moment -/

/-- The angular moment `r ↦ F_*(D_z^j F)(r)` is a.e. strongly measurable on `(0,∞)`: it is the
integral over `θ` of a function continuous on the open quadrant. -/
theorem Fstar_aesm (F : ℝ → ℝ → ℝ) (hF : Work.FTS.EllipticEst.SmoothOpen F) (j : ℕ) :
    AEStronglyMeasurable (fun r : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter j F) r)
      (volume.restrict (Set.Ioi 0)) := by
  have hcont : ContinuousOn Work.Elliptic.sinCos2 Work.Spaces.Iθ := by
    show ContinuousOn (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) Work.Spaces.Iθ
    exact ((Real.continuous_sin.mul (Real.continuous_cos.pow 2)).continuousOn).mono
      (Set.subset_univ _)
  have h := aestronglyMeasurable_integral_Itheta_Q0 (Work.Spaces.DzIter j F)
    ((hF.DzIter j).continuousOn) Work.Elliptic.sinCos2 hcont
  change AEStronglyMeasurable (fun r : ℝ => ∫ θ in Work.Spaces.Iθ,
    Work.Spaces.DzIter j F r θ * Work.Elliptic.sinCos2 θ) (volume.restrict (Set.Ioi 0))
  exact h

/-- `r ↦ F_*(D_z^j F)(r)/r` is a.e. strongly measurable on any `(0,z)`. -/
theorem Fstar_div_aesm (F : ℝ → ℝ → ℝ) (hF : Work.FTS.EllipticEst.SmoothOpen F) (j : ℕ)
    {z : ℝ} :
    AEStronglyMeasurable (fun r : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter j F) r / r)
      (volume.restrict (Set.Ioo 0 z)) := by
  have hmom : AEStronglyMeasurable
      (fun r : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter j F) r)
      (volume.restrict (Set.Ioo 0 z)) :=
    (Fstar_aesm F hF j).mono_measure (Measure.restrict_mono (fun r hr => hr.1) le_rfl)
  have hinv : AEStronglyMeasurable (fun r : ℝ => r⁻¹) (volume.restrict (Set.Ioo 0 z)) :=
    (continuousOn_id.inv₀ (fun _ hr => ne_of_gt hr.1)).aestronglyMeasurable measurableSet_Ioo
  exact hmom.mul hinv


/-! ## Integrability of the majorant -/

/-- **The majorant is integrable** on every measurable subset of `[0,∞)` of finite measure:
this is just `HkMem` together with the finiteness of `∫_θ HkIntegrand α k F r θ`. -/
theorem majorant_integrableOn (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hmem : Work.Spaces.HkMem α k F) {s : Set ℝ} (hs : s ⊆ Work.Spaces.Iz)
    (hvol : volume s ≠ ⊤) :
    IntegrableOn (fun r : ℝ => ((Real.pi / 2) * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k F r θ) + 1) / 2) s := by
  have hG : IntegrableOn (fun r : ℝ => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k F r θ) s := hmem.2.mono_set hs
  have h1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) s :=
    integrableOn_const (s := s) (C := (1 : ℝ)) hvol
  exact ((hG.const_mul (Real.pi / 2)).add h1).div_const 2


/-! ## The theorem -/


end Work.FTS.EllipticEst.GbarSin
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.I4GlobalAssembly =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option maxHeartbeats 1600000

/-! ## The two auxiliary steps of the assembly -/

theorem I4IntegrableOnOfConstMul {f : ℝ → ℝ} {s : Set ℝ} {c : ℝ}
    (h : MeasureTheory.IntegrableOn (fun θ => c * f θ) s) (hc : c ≠ 0)
    (hs : MeasurableSet s) :
    MeasureTheory.IntegrableOn f s := by
  have h2 := h.mul_const c⁻¹
  refine MeasureTheory.IntegrableOn.congr_fun h2 (fun θ hθ => ?_) hs
  show (c * f θ) * c⁻¹ = f θ
  calc (c * f θ) * c⁻¹ = f θ * (c * c⁻¹) := by ring
    _ = f θ * 1 := by rw [mul_inv_cancel₀ hc]
    _ = f θ := by ring



end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Mine.FstarDzOnePsi =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Mine

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 8000000

/-! ## Elementary angular facts -/

/-- `sin (2θ) ≥ 0` on the angular interval. -/
theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ] at hθ
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `sin (2θ) > 0` on the *open* angular interval. -/
theorem sin_two_pos_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The angular weight `sEta` is nonnegative on `Iθ`. -/
theorem sEta_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.FTS.EllipticEst.sEta θ :=
  Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _

/-- The angular weight `sin θ cos²θ` of the solvability condition is nonnegative on `Iθ`. -/
theorem sinCos2_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Elliptic.sinCos2 θ := by
  rw [Work.Elliptic.sinCos2]
  have h1 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  positivity

/-- `w z > 0` for `z > 0`. -/
theorem w_pos {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z := by
  have h : Work.Spaces.w z = ((1 + z) / z) ^ 2 := by rw [Work.Spaces.w, ← div_pow]
  rw [h]
  have : 0 < (1 + z) / z := div_pos (by linarith) hz
  positivity

/-- `w` is decreasing on `(0,∞)`, in the form used below. -/
theorem w_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : Work.Spaces.w b ≤ Work.Spaces.w a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h1 : 1 / b ≤ 1 / a := one_div_le_one_div_of_le ha hab
  have h2 : 0 ≤ 1 / b := by positivity
  have hbw : Work.Spaces.w b = (1 + 1 / b) ^ 2 := by
    rw [Work.Spaces.w, ← div_pow, add_div, div_self (ne_of_gt hb)]
    ring
  have haw : Work.Spaces.w a = (1 + 1 / a) ^ 2 := by
    rw [Work.Spaces.w, ← div_pow, add_div, div_self (ne_of_gt ha)]
    ring
  rw [hbw, haw]
  exact pow_le_pow_left₀ (by linarith) (by linarith) 2

/-! ## The pointwise slice domination -/

/-- **Pointwise slice domination.**  For `z₀ < s < 2z₀` and `θ ∈ Iθ`, the weighted slice of
`∂_z²Ψ` is bounded by the `ℋ^k`-integrand of `z ↦ z²∂_z²Ψ` at the same point. -/
theorem pzIter2_sq_sEta_le_HkIntegrand_pt {α : ℝ} {k : ℕ} {Ψ : ℝ → ℝ → ℝ}
    {z₀ : ℝ} (hz₀ : 0 < z₀) {s : ℝ} (hs : s ∈ Set.Ioo z₀ (2 * z₀)) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      ≤ (1 / (z₀ ^ 4 * (Work.Spaces.w (2 * z₀)) ^ 2))
        * Work.Spaces.HkIntegrand α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ := by
  have hspos : 0 < s := lt_trans hz₀ hs.1
  have hsle : s ≤ 2 * z₀ := le_of_lt hs.2
  have hx : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  have hkey : ((fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ
        * (Work.Spaces.w s / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
      = s ^ 4 * (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * (Work.Spaces.w s) ^ 2
          * Work.FTS.EllipticEst.sEta θ := by
    have hxx : (Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2))) ^ 2
        = Work.FTS.EllipticEst.sEta θ := by
      rw [Work.FTS.EllipticEst.sEta, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hx]
      congr 1
      ring
    have hmid : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)
        = (Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2)))⁻¹ := by
      have h := Real.rpow_neg hx (-(Work.Spaces.eta / 2))
      rwa [neg_neg] at h
    rw [div_eq_mul_inv, hmid, inv_inv]
    simp only [mul_pow]
    rw [hxx]
    ring
  have hle1 : ((fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ
      * (Work.Spaces.w s / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ Work.Spaces.HkIntegrand α k
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ :=
    Work.Spaces.sq_le_HkIntegrand_z α k
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ 0 (by omega)
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α k
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ :=
    Work.Spaces.HkIntegrand_nonneg _ _ _ _ _
  have hcoef : 0 < 1 / (s ^ 4 * (Work.Spaces.w s) ^ 2) :=
    one_div_pos.mpr (mul_pos (by positivity) (pow_pos (w_pos hspos) 2))
  have hconst : 1 / (s ^ 4 * (Work.Spaces.w s) ^ 2) ≤ 1 / (z₀ ^ 4 * (Work.Spaces.w (2 * z₀)) ^ 2) := by
    have hws2 : (Work.Spaces.w (2 * z₀)) ^ 2 ≤ (Work.Spaces.w s) ^ 2 :=
      pow_le_pow_left₀ (w_pos (by linarith : (0:ℝ) < 2 * z₀)).le (w_antitone hspos hsle) 2
    have hz4 : z₀ ^ 4 ≤ s ^ 4 := pow_le_pow_left₀ (le_of_lt hz₀) (le_of_lt hs.1) 4
    have hden : z₀ ^ 4 * (Work.Spaces.w (2 * z₀)) ^ 2 ≤ s ^ 4 * (Work.Spaces.w s) ^ 2 :=
      mul_le_mul hz4 hws2 (by positivity) (by positivity)
    have hpos : 0 < z₀ ^ 4 * (Work.Spaces.w (2 * z₀)) ^ 2 :=
      mul_pos (by positivity) (pow_pos (w_pos (by linarith : (0:ℝ) < 2 * z₀)) 2)
    exact one_div_le_one_div_of_le hpos hden
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hwsne : Work.Spaces.w s ≠ 0 := ne_of_gt (w_pos hspos)
  calc (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      = (1 / (s ^ 4 * (Work.Spaces.w s) ^ 2))
          * ((fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ
              * (Work.Spaces.w s / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        rw [hkey]
        field_simp
    _ ≤ (1 / (s ^ 4 * (Work.Spaces.w s) ^ 2))
          * Work.Spaces.HkIntegrand α k
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ :=
        mul_le_mul_of_nonneg_left hle1 hcoef.le
    _ ≤ (1 / (z₀ ^ 4 * (Work.Spaces.w (2 * z₀)) ^ 2))
          * Work.Spaces.HkIntegrand α k
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ :=
        mul_le_mul_of_nonneg_right hconst hHnn

/-! ## The slice domination by the `ℋ^k`-integrand -/

/-- **Slice domination.**  For `z₀ < s < 2z₀`, the weighted `L²`-slice of `∂_z²Ψ` against the
angular weight `sEta` is bounded by the `ℋ^k`-integrand of `z ↦ z²∂_z²Ψ`, with the explicit
constant `1/(z₀⁴·w(2z₀)²)`. -/
theorem pzIter2_sq_sEta_le_HkIntegrand {α : ℝ} {k : ℕ} {Ψ : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hmemA : Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    {z₀ : ℝ} (hz₀ : 0 < z₀) {s : ℝ} (hs : s ∈ Set.Ioo z₀ (2 * z₀)) :
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ
      ∧ ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
          ≤ (1 / (z₀ ^ 4 * (Work.Spaces.w (2 * z₀)) ^ 2))
            * ∫ θ in Work.Spaces.Iθ,
                Work.Spaces.HkIntegrand α k
                  (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ := by
  have hspos : 0 < s := lt_trans hz₀ hs.1
  have hsle : s ≤ 2 * z₀ := le_of_lt hs.2
  have h2pos : 0 < 2 * z₀ := by linarith
  have hsIz : s ∈ Work.Spaces.Iz := le_of_lt hspos
  set M : ℝ := 1 / (z₀ ^ 4 * (Work.Spaces.w (2 * z₀)) ^ 2) with hMdef
  -- the `ℋ^k`-integrand is integrable on the slice
  have hHk : MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.HkIntegrand α k
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ) Work.Spaces.Iθ := hmemA.1 s hsIz
  -- the constant comparison
  have hconst : 1 / (s ^ 4 * (Work.Spaces.w s) ^ 2) ≤ M := by
    have hws2 : (Work.Spaces.w (2 * z₀)) ^ 2 ≤ (Work.Spaces.w s) ^ 2 :=
      pow_le_pow_left₀ (w_pos h2pos).le (w_antitone hspos hsle) 2
    have hz4 : z₀ ^ 4 ≤ s ^ 4 := pow_le_pow_left₀ (le_of_lt hz₀) (le_of_lt hs.1) 4
    have hden : z₀ ^ 4 * (Work.Spaces.w (2 * z₀)) ^ 2 ≤ s ^ 4 * (Work.Spaces.w s) ^ 2 :=
      mul_le_mul hz4 hws2 (by positivity) (by positivity)
    have hpos : 0 < z₀ ^ 4 * (Work.Spaces.w (2 * z₀)) ^ 2 :=
      mul_pos (by positivity) (pow_pos (w_pos h2pos) 2)
    exact one_div_le_one_div_of_le hpos hden
  -- the pointwise bound
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        ≤ M * Work.Spaces.HkIntegrand α k
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ := by
    intro θ hθ
    have hx : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
    have hkey : ((fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ
          * (Work.Spaces.w s / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
        = s ^ 4 * (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * (Work.Spaces.w s) ^ 2
            * Work.FTS.EllipticEst.sEta θ := by
      have hxx : (Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2))) ^ 2
          = Work.FTS.EllipticEst.sEta θ := by
        rw [Work.FTS.EllipticEst.sEta, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hx]
        congr 1
        ring
      have hmid : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)
          = (Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2)))⁻¹ := by
        have h := Real.rpow_neg hx (-(Work.Spaces.eta / 2))
        rwa [neg_neg] at h
      rw [div_eq_mul_inv, hmid, inv_inv]
      simp only [mul_pow]
      rw [hxx]
      ring
    have hle1 : ((fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ
        * (Work.Spaces.w s / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Work.Spaces.HkIntegrand α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ :=
      Work.Spaces.sq_le_HkIntegrand_z α k
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ 0 (by omega)
    have hHnn : 0 ≤ Work.Spaces.HkIntegrand α k
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ :=
      Work.Spaces.HkIntegrand_nonneg _ _ _ _ _
    have hcoef : 0 < 1 / (s ^ 4 * (Work.Spaces.w s) ^ 2) :=
      one_div_pos.mpr (mul_pos (by positivity) (pow_pos (w_pos hspos) 2))
    have hsne : s ≠ 0 := ne_of_gt hspos
    have hwsne : Work.Spaces.w s ≠ 0 := ne_of_gt (w_pos hspos)
    calc (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        = (1 / (s ^ 4 * (Work.Spaces.w s) ^ 2))
            * ((fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ
                * (Work.Spaces.w s / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
          rw [hkey]
          field_simp
      _ ≤ (1 / (s ^ 4 * (Work.Spaces.w s) ^ 2))
            * Work.Spaces.HkIntegrand α k
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ :=
          mul_le_mul_of_nonneg_left hle1 hcoef.le
      _ ≤ M * Work.Spaces.HkIntegrand α k
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ :=
          mul_le_mul_of_nonneg_right hconst hHnn
  -- measurability of the integrand
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have hsEta : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
      have hsin : Continuous fun p : ℝ × ℝ => Real.sin (2 * p.2) :=
        Real.continuous_sin.comp (continuous_const.mul continuous_snd)
      refine ContinuousOn.rpow_const hsin.continuousOn ?_
      intro p hp
      exact Or.inl (ne_of_gt (sin_two_pos_Ioo ⟨hp.2.1, hp.2.2⟩))
    exact Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => (Work.Spaces.pzIter 2 Ψ p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2)
      (((Work.FTS.EllipticEst.SmoothOpen.pzIter hsm 2).continuousOn).pow 2 |>.mul hsEta) hspos
  have hInt : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono' (hHk.const_mul M) hmeas ?_
    rw [ae_restrict_iff' (show MeasurableSet Work.Spaces.Iθ from by
      rw [Work.Spaces.Iθ]; exact measurableSet_Icc)]
    filter_upwards with θ hθ
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))]
    exact hpt θ hθ
  refine ⟨hInt, ?_⟩
  have hmono : ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      ≤ M * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ := by
    have hle_ae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
          ≤ M * Work.Spaces.HkIntegrand α k
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ := by
      rw [MeasureTheory.ae_restrict_iff' (show MeasurableSet Work.Spaces.Iθ from by
        rw [Work.Spaces.Iθ]; exact measurableSet_Icc)]
      exact Eventually.of_forall (fun θ hθ => hpt θ hθ)
    have h := MeasureTheory.integral_mono_ae hInt (hHk.const_mul M) hle_ae
    rw [← MeasureTheory.integral_const_mul]
    exact h
  exact hmono

/-! ## Integrals over shrinking intervals -/

/-- **Absolute continuity of the Lebesgue integral, sequence form.**  If `g` is integrable on
`Ioc c (c+A)` with `A > 0`, the integrals over the shrinking sets `Ioc c (c + A/(n+1))` tend to
`0`. -/
theorem tendsto_integral_Ioc_shrink {g : ℝ → ℝ} {c A : ℝ} (hA : 0 < A)
    (hg : MeasureTheory.IntegrableOn g (Set.Ioc c (c + A))) :
    Filter.Tendsto (fun n : ℕ => ∫ x in Set.Ioc c (c + A / (n + 1 : ℝ)), g x)
      Filter.atTop (nhds 0) := by
  have hmeas : ∀ n : ℕ, MeasurableSet (Set.Ioc c (c + A / (n + 1 : ℝ))) :=
    fun _ => measurableSet_Ioc
  have hanti : Antitone (fun n : ℕ => Set.Ioc c (c + A / (n + 1 : ℝ))) := by
    intro m n hmn
    refine Set.Ioc_subset_Ioc_right ?_
    have h1 : (0 : ℝ) < (m + 1 : ℝ) := by positivity
    have h3 : (m + 1 : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast Nat.succ_le_succ hmn
    simpa using div_le_div_of_nonneg_left hA.le h1 h3
  have hfin : ∃ i : ℕ, MeasureTheory.IntegrableOn g (Set.Ioc c (c + A / (i + 1 : ℝ))) := by
    refine ⟨0, ?_⟩
    have h0 : c + A / ((0 : ℕ) + 1 : ℝ) = c + A := by norm_num
    rw [h0]; exact hg
  have hmain := MeasureTheory.tendsto_setIntegral_of_antitone hmeas hanti hfin
  have hempty : (⋂ n : ℕ, Set.Ioc c (c + A / (n + 1 : ℝ))) = ∅ := by
    have hmempty : ∀ x, x ∉ (⋂ n : ℕ, Set.Ioc c (c + A / (n + 1 : ℝ))) := by
      intro x hx
      rw [Set.mem_iInter] at hx
      have hxc : c < x := (hx 0).1
      have hpos : 0 < x - c := by linarith
      obtain ⟨n, hn⟩ := exists_nat_gt (A / (x - c))
      have hnpos : (0 : ℝ) < (n : ℝ) := lt_trans (div_pos hA hpos) hn
      have hA_lt : A < (n : ℝ) * (x - c) := (div_lt_iff₀ hpos).mp hn
      have hlt : A / (n : ℝ) < x - c := by
        rw [div_lt_iff₀ hnpos]; linarith [hA_lt]
      have hle : A / ((n : ℝ) + 1) ≤ A / (n : ℝ) :=
        div_le_div_of_nonneg_left hA.le hnpos (by linarith)
      have : A / ((n : ℕ) + 1 : ℝ) < x - c := by
        push_cast
        linarith [hle, hlt]
      exact absurd (hx n).2 (not_le.mpr (by linarith))
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    exact hmempty x
  rw [hempty, MeasureTheory.setIntegral_empty] at hmain
  exact hmain

/-! ## The main estimate -/

/-- The angular interval is, up to a null set, the open interval. -/
theorem ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  have hfin : MeasureTheory.volume ({0, Real.pi / 2} : Set ℝ) = 0 := by
    have h1 : ({0, Real.pi / 2} : Set ℝ) = {0} ∪ {Real.pi / 2} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    rw [h1, MeasureTheory.measure_union_null_iff]
    exact ⟨MeasureTheory.measure_singleton 0, MeasureTheory.measure_singleton _⟩
  rw [MeasureTheory.ae_restrict_iff' (show MeasurableSet Work.Spaces.Iθ from by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc)]
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_ hfin
  intro θ hθ
  simp only [Set.mem_setOf_eq] at hθ
  push_neg at hθ
  obtain ⟨hI, hnot⟩ := hθ
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hI
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  by_cases h0 : θ = 0
  · exact Or.inl h0
  · refine Or.inr (le_antisymm hI.2 ?_)
    by_contra hlt
    push_neg at hlt
    exact hnot ⟨lt_of_le_of_ne hI.1 (Ne.symm h0), hlt⟩

/-- **The angular moment of `∂_zΨ` vanishes.**  For a datum of the weak class, the radial
derivative of the angular moment `F_*(Ψ)` is `F_*(∂_zΨ)`; since `F_*(Ψ) ≡ 0`, that moment
vanishes.  This is the `Ψ`-half of the moment chain. -/
theorem pz_moment_of_integrable {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z₀ : ℝ} (hz₀ : 0 < z₀)
    (hint : MeasureTheory.Integrable
      (fun θ : ℝ => Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ = 0 := by
  have hsm : Work.FTS.EllipticEst.SmoothOpen Ψ := Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hZsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl
      (Work.FTS.EllipticEst.SmoothOpen.pzIter hsm 2)
  set L : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ with hLdef
  -- (1) the slices of `Ψ` are integrable against the angular weight
  have hΨslice : ∀ z : ℝ, 0 < z → MeasureTheory.Integrable
      (fun θ : ℝ => Ψ z θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    have habs : MeasureTheory.Integrable (fun θ : ℝ => |Ψ z θ| * Work.Elliptic.sinCos2 θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (Work.FTS.EllipticEst.remov.Psi_slice_sinCos2_integrable hk h z hz).integrable
    have hnorm : MeasureTheory.Integrable (fun θ : ℝ => ‖Ψ z θ * Work.Elliptic.sinCos2 θ‖)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      refine habs.congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from by
        rw [Work.Spaces.Iθ]; exact measurableSet_Icc)] with θ hθ
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sinCos2_nonneg hθ)]
    have hmeas : MeasureTheory.AEStronglyMeasurable
        (fun θ : ℝ => Ψ z θ * Work.Elliptic.sinCos2 θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      have hc1 : ContinuousOn (fun p : ℝ × ℝ => Ψ p.1 p.2) Work.FTS.EllipticEst.Q0 :=
        hsm.continuousOn
      have hc2 : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2)
          Work.FTS.EllipticEst.Q0 := by
        show ContinuousOn (fun p : ℝ × ℝ => Real.sin p.2 * Real.cos p.2 ^ 2)
          Work.FTS.EllipticEst.Q0
        fun_prop
      refine (Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => Ψ p.1 p.2 * Work.Elliptic.sinCos2 p.2) (hc1.mul hc2) hz).congr ?_
      filter_upwards with θ
      rfl
    exact (MeasureTheory.integrable_norm_iff hmeas).mp hnorm
  -- (2) the constants and the slice functional
  set C₂ : ℝ := ∫ θ in Work.Spaces.Iθ,
    (Work.Elliptic.sinCos2 θ) ^ 2 / Work.FTS.EllipticEst.sEta θ with hC₂def
  set M : ℝ := 1 / (z₀ ^ 4 * (Work.Spaces.w (2 * z₀)) ^ 2) with hMdef
  set Hki : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ with hHkidef
  have hzero : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (0 : ℝ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    refine (integrableOn_const (s := Work.Spaces.Iθ) (C := (0 : ℝ)) (by
      rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).congr ?_
    filter_upwards with θ
    simp
  obtain ⟨hC₂int, hC₂nn, -⟩ :=
    sinCos2_cs_sEta (u := fun _ : ℝ => (0 : ℝ)) hzero MeasureTheory.aestronglyMeasurable_const
  have hMnni : 0 ≤ M := by
    rw [hMdef]
    exact (one_div_pos.mpr (mul_pos (by positivity)
      (pow_pos (w_pos (by linarith : (0:ℝ) < 2 * z₀)) 2))).le
  -- (3) the estimate for every `hh ∈ (0, z₀)`
  have key : ∀ hh : ℝ, 0 < hh → hh < z₀ →
      |L| ≤ Real.sqrt (C₂ * M) * (hh + ∫ z in Set.Ioc z₀ (z₀ + hh), Hki z) := by
    intro hh hhpos hhlt
    have hhle : hh ≤ z₀ := le_of_lt hhlt
    have hzle : z₀ ≤ z₀ + hh := by linarith
    set μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Ioc z₀ (z₀ + hh)) with hμdef
    set ν : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict Work.Spaces.Iθ with hνdef
    have hIθ_meas : MeasurableSet Work.Spaces.Iθ := by
      rw [Work.Spaces.Iθ]; exact measurableSet_Icc
    have hsEta : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2)
        Work.FTS.EllipticEst.Q0 := by
      have hsin : Continuous fun p : ℝ × ℝ => Real.sin (2 * p.2) :=
        Real.continuous_sin.comp (continuous_const.mul continuous_snd)
      refine ContinuousOn.rpow_const hsin.continuousOn ?_
      intro p hp
      exact Or.inl (ne_of_gt (sin_two_pos_Ioo ⟨hp.2.1, hp.2.2⟩))
    have hbox_le : μ.prod ν ≤ (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      refine MeasureTheory.Measure.prod_mono ?_ le_rfl
      rw [hμdef]
      exact MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume
        (fun x hx => le_of_lt (lt_of_lt_of_le hz₀ (le_of_lt hx.1)))
    have hbox_meas : MeasurableSet (Set.Ioc z₀ (z₀ + hh) ×ˢ Work.Spaces.Iθ) :=
      measurableSet_Ioc.prod hIθ_meas
    -- joint integrability of the `ℋ^k`-integrand on the slab
    have hHkbox : MeasureTheory.Integrable
        (Function.uncurry (fun z θ => Work.Spaces.HkIntegrand α k
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ)) (μ.prod ν) :=
      (integrable_hkIntegrand_prod
        (Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand hZsm α k) h.memA).mono_measure hbox_le
    -- the quadratic slice function
    have hφaesm : MeasureTheory.AEStronglyMeasurable
        (Function.uncurry (fun z θ => (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
        (μ.prod ν) := by
      refine (Work.Spaces.aesm_of_continuousOn_Qd
        (fun p : ℝ × ℝ => (Work.Spaces.pzIter 2 Ψ p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2)
        (((Work.FTS.EllipticEst.SmoothOpen.pzIter hsm 2).continuousOn).pow 2 |>.mul hsEta)).mono_measure hbox_le
    have hφbox : MeasureTheory.Integrable
        (Function.uncurry (fun z θ => (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
        (μ.prod ν) := by
      refine MeasureTheory.Integrable.mono' (hHkbox.const_mul M) hφaesm ?_
      rw [hμdef, hνdef, MeasureTheory.Measure.prod_restrict,
        MeasureTheory.ae_restrict_iff' hbox_meas]
      filter_upwards with p hp
      obtain ⟨a, b⟩ := p
      simp only [Function.uncurry_apply_pair]
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sEta_nonneg hp.2))]
      exact pzIter2_sq_sEta_le_HkIntegrand_pt hz₀ ⟨hp.1.1, by linarith [hp.1.2, hhle]⟩ hp.2
    -- the `θ`-only weight
    have hone : MeasureTheory.Integrable
        (Function.uncurry (fun _ : ℝ => fun θ : ℝ =>
          (Work.Elliptic.sinCos2 θ) ^ 2 / Work.FTS.EllipticEst.sEta θ)) (μ.prod ν) := by
      have h1 : MeasureTheory.Integrable (fun _ : ℝ => (1 : ℝ)) μ := integrable_const (1 : ℝ)
      refine (MeasureTheory.Integrable.mul_prod h1 hC₂int).congr ?_
      filter_upwards with p
      show (1 : ℝ) * ((Work.Elliptic.sinCos2 p.2) ^ 2 / Work.FTS.EllipticEst.sEta p.2)
        = (Work.Elliptic.sinCos2 p.2) ^ 2 / Work.FTS.EllipticEst.sEta p.2
      ring
    -- joint integrability of `|∂_z²Ψ|` against the angular weight
    have hιbox : MeasureTheory.Integrable
        (Function.uncurry (fun z θ => |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ))
        (μ.prod ν) := by
      have hv2 : ∀ θ ∈ Work.Spaces.Iθ,
          (Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2))) ^ 2 = Work.FTS.EllipticEst.sEta θ := by
        intro θ hθ
        have hx : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
        rw [Work.FTS.EllipticEst.sEta, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hx]
        congr 1
        ring
      have hιaesm : MeasureTheory.AEStronglyMeasurable
          (Function.uncurry (fun z θ => |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ))
          (μ.prod ν) := by
        have hc1 : ContinuousOn (fun p : ℝ × ℝ => |Work.Spaces.pzIter 2 Ψ p.1 p.2|)
            Work.FTS.EllipticEst.Q0 :=
          ((Work.FTS.EllipticEst.SmoothOpen.pzIter hsm 2).continuousOn).abs
        have hc2 : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2)
            Work.FTS.EllipticEst.Q0 := by
          show ContinuousOn (fun p : ℝ × ℝ => Real.sin p.2 * Real.cos p.2 ^ 2)
            Work.FTS.EllipticEst.Q0
          fun_prop
        refine (Work.Spaces.aesm_of_continuousOn_Qd
          (fun p : ℝ × ℝ => |Work.Spaces.pzIter 2 Ψ p.1 p.2| * Work.Elliptic.sinCos2 p.2)
          (hc1.mul hc2)).mono_measure hbox_le
      refine MeasureTheory.Integrable.mono'
        ((hφbox.const_mul (1/2)).add (hone.const_mul (1/2))) hιaesm ?_
      rw [hμdef, hνdef, MeasureTheory.Measure.prod_restrict,
        MeasureTheory.ae_restrict_iff' hbox_meas]
      filter_upwards with p hp
      obtain ⟨a, b⟩ := p
      have hw0 : 0 ≤ Work.Elliptic.sinCos2 b := sinCos2_nonneg hp.2
      have hnorm : ‖Function.uncurry (fun z θ => |Work.Spaces.pzIter 2 Ψ z θ|
            * Work.Elliptic.sinCos2 θ) (a, b)‖
          = |Work.Spaces.pzIter 2 Ψ a b| * Work.Elliptic.sinCos2 b := by
        rw [Function.uncurry_apply_pair, Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) hw0)]
      rw [hnorm]
      change |Work.Spaces.pzIter 2 Ψ a b| * Work.Elliptic.sinCos2 b
        ≤ (1/2) * ((Work.Spaces.pzIter 2 Ψ a b) ^ 2 * Work.FTS.EllipticEst.sEta b)
          + (1/2) * ((Work.Elliptic.sinCos2 b) ^ 2 / Work.FTS.EllipticEst.sEta b)
      by_cases hv : Real.sin (2 * b) = 0
      · have hwz : Work.Elliptic.sinCos2 b = 0 := by
          obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hv
          have h2 : 2 * b = (k : ℝ) * Real.pi := hk.symm
          have hk0 : (0 : ℤ) ≤ k := by
            by_contra hc
            push_neg at hc
            have hk1 : k ≤ -1 := by omega
            have hk2 : (k : ℝ) ≤ -1 := by exact_mod_cast hk1
            have h3 : (k : ℝ) * Real.pi ≤ -Real.pi := by nlinarith [Real.pi_pos]
            rw [← h2] at h3
            linarith [hp.2.1, Real.pi_pos]
          have hk1' : k ≤ 1 := by
            by_contra hc
            push_neg at hc
            have hk2 : (2 : ℤ) ≤ k := by omega
            have hk3 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
            have h3 : 2 * Real.pi ≤ (k : ℝ) * Real.pi := by nlinarith [Real.pi_pos]
            rw [← h2] at h3
            linarith [hp.2.2, Real.pi_pos]
          interval_cases k
          · have hp0 : b = 0 := by
              have h2' : 2 * b = 0 := by simpa using h2
              linarith
            rw [Work.Elliptic.sinCos2, hp0]; simp
          · have hpp : b = Real.pi / 2 := by
              have h2' : 2 * b = Real.pi := by simpa using h2
              linarith
            rw [Work.Elliptic.sinCos2, hpp, Real.cos_pi_div_two]; simp
        rw [hwz, mul_zero]
        have hz0 : (0 : ℝ) ^ 2 / Work.FTS.EllipticEst.sEta b = 0 := by simp
        rw [hz0, mul_zero, add_zero]
        exact mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) (sEta_nonneg hp.2))
      · have hvpos : 0 < Real.sin (2 * b) := lt_of_le_of_ne (sin_two_nonneg_Iθ hp.2) (Ne.symm hv)
        set v : ℝ := Real.sin (2 * b) ^ (-(Work.Spaces.eta / 2)) with hvdef
        have hvne : v ≠ 0 := by
          rw [hvdef]
          exact ne_of_gt (Real.rpow_pos_of_pos hvpos _)
        have hv2p : v ^ 2 = Work.FTS.EllipticEst.sEta b := hv2 b hp.2
        have hamgm := two_mul_le_add_sq (|Work.Spaces.pzIter 2 Ψ a b| * v)
          (Work.Elliptic.sinCos2 b * v⁻¹)
        have hleft : 2 * (|Work.Spaces.pzIter 2 Ψ a b| * v) * (Work.Elliptic.sinCos2 b * v⁻¹)
            = 2 * (|Work.Spaces.pzIter 2 Ψ a b| * Work.Elliptic.sinCos2 b) := by
          have hvne' : v ≠ 0 := hvne
          field_simp
        have hright : (|Work.Spaces.pzIter 2 Ψ a b| * v) ^ 2 + (Work.Elliptic.sinCos2 b * v⁻¹) ^ 2
            = (Work.Spaces.pzIter 2 Ψ a b) ^ 2 * Work.FTS.EllipticEst.sEta b
              + (Work.Elliptic.sinCos2 b) ^ 2 / Work.FTS.EllipticEst.sEta b := by
          rw [mul_pow, mul_pow, sq_abs, hv2p, inv_pow, ← hv2p]
          ring
        rw [hleft, hright] at hamgm
        linarith [hamgm]
    -- the moment identity
    have hmom : ∫ θ in Work.Spaces.Iθ,
        (Ψ (z₀ + hh) θ - Ψ z₀ θ) * Work.Elliptic.sinCos2 θ = 0 := by
      rw [show (fun θ : ℝ => (Ψ (z₀ + hh) θ - Ψ z₀ θ) * Work.Elliptic.sinCos2 θ)
          = fun θ : ℝ => Ψ (z₀ + hh) θ * Work.Elliptic.sinCos2 θ
              - Ψ z₀ θ * Work.Elliptic.sinCos2 θ from by funext θ; ring]
      rw [MeasureTheory.integral_sub (hΨslice (z₀ + hh) (by linarith)) (hΨslice z₀ hz₀)]
      rw [show (∫ θ in Work.Spaces.Iθ, Ψ (z₀ + hh) θ * Work.Elliptic.sinCos2 θ) = 0 from
            h.orthPsi (z₀ + hh) (by linarith),
          show (∫ θ in Work.Spaces.Iθ, Ψ z₀ θ * Work.Elliptic.sinCos2 θ) = 0 from h.orthPsi z₀ hz₀]
      ring
    -- the difference quotient and the `z`-integral of the second derivative
    set Afun : ℝ → ℝ := fun θ => (1/hh) * ((Ψ (z₀ + hh) θ - Ψ z₀ θ) * Work.Elliptic.sinCos2 θ)
      with hAdef
    set Gfun : ℝ → ℝ := fun θ => ∫ z in z₀..(z₀ + hh),
        (Work.Spaces.pz Ψ z θ - Work.Spaces.pz Ψ z₀ θ) with hGdef
    have hAint : MeasureTheory.Integrable Afun (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      refine ((MeasureTheory.Integrable.sub (hΨslice (z₀ + hh) (by linarith))
        (hΨslice z₀ hz₀)).const_mul (1/hh)).congr ?_
      filter_upwards with θ
      simp only [hAdef, Pi.sub_apply]
      ring
    have hAzero : ∫ θ in Work.Spaces.Iθ, Afun θ = 0 := by
      rw [hAdef]
      rw [MeasureTheory.integral_const_mul, hmom, mul_zero]
    have hAG : ∀ θ ∈ Set.Ioo 0 (π/2),
        Afun θ = (1/hh) * (Gfun θ * Work.Elliptic.sinCos2 θ)
          + Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ := by
      intro θ hθi
      have hInt1 : IntervalIntegrable (fun z => Work.Spaces.pz Ψ z θ) volume z₀ (z₀ + hh) := by
        have hc : ContinuousOn (fun z : ℝ => Work.Spaces.pz Ψ z θ) (Set.uIcc z₀ (z₀ + hh)) := by
          refine ((hsm.pz.curry_z hθi).continuousOn).mono ?_
          intro z hz
          rw [Set.uIcc_of_le hzle] at hz
          exact lt_of_lt_of_le hz₀ hz.1
        exact hc.intervalIntegrable
      have hderiv : ∀ z ∈ Set.uIcc z₀ (z₀ + hh),
          HasDerivAt (fun z' : ℝ => Ψ z' θ) (Work.Spaces.pz Ψ z θ) z := by
        intro z hz
        rw [Set.uIcc_of_le hzle] at hz
        exact hsm.hasDerivAt_slice hθi (lt_of_lt_of_le hz₀ hz.1)
      have hftc0 := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hInt1
      have hdiff : IntervalIntegrable (fun z => Work.Spaces.pz Ψ z θ - Work.Spaces.pz Ψ z₀ θ)
          volume z₀ (z₀ + hh) := hInt1.sub intervalIntegrable_const
      have hftc : Ψ (z₀ + hh) θ - Ψ z₀ θ = hh * Work.Spaces.pz Ψ z₀ θ + Gfun θ := by
        rw [hGdef, ← hftc0]
        rw [show (fun z : ℝ => Work.Spaces.pz Ψ z θ)
            = fun z : ℝ => Work.Spaces.pz Ψ z₀ θ
              + (Work.Spaces.pz Ψ z θ - Work.Spaces.pz Ψ z₀ θ) from by funext z; ring]
        rw [intervalIntegral.integral_add intervalIntegrable_const hdiff,
          intervalIntegral.integral_const]
        ring
      change (1/hh) * ((Ψ (z₀ + hh) θ - Ψ z₀ θ) * Work.Elliptic.sinCos2 θ)
        = (1/hh) * (Gfun θ * Work.Elliptic.sinCos2 θ)
          + Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ
      rw [hftc]
      field_simp
      ring
    have hGint : MeasureTheory.Integrable (fun θ : ℝ => (1/hh) * (Gfun θ * Work.Elliptic.sinCos2 θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      have hf : MeasureTheory.Integrable
          (fun θ : ℝ => Afun θ - Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := MeasureTheory.Integrable.sub hAint hint
      refine hf.congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem hIθ_meas, ae_mem_Ioo_Iθ] with θ hθ hθi
      show Afun θ - Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ
        = (1/hh) * (Gfun θ * Work.Elliptic.sinCos2 θ)
      rw [hAG θ hθi]
      ring
    have hval : L = -∫ θ in Work.Spaces.Iθ, (1/hh) * (Gfun θ * Work.Elliptic.sinCos2 θ) := by
      have h1 := MeasureTheory.integral_sub hAint hint
      have h2 : ∫ θ in Work.Spaces.Iθ, (1/hh) * (Gfun θ * Work.Elliptic.sinCos2 θ)
          = (∫ θ in Work.Spaces.Iθ, Afun θ)
            - ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ := by
        rw [← h1]
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [MeasureTheory.ae_restrict_mem hIθ_meas, ae_mem_Ioo_Iθ] with θ hθ hθi
        rw [hAG θ hθi]
        ring
      have h3 : L = -((∫ θ in Work.Spaces.Iθ, Afun θ)
            - ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ) := by
        rw [hLdef, hAzero]
        ring
      rw [h3, h2]
    -- the pointwise bound on the difference quotient
    have hGbound : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        |Gfun θ| ≤ hh * ∫ z in Set.Ioc z₀ (z₀ + hh), |Work.Spaces.pzIter 2 Ψ z θ| := by
      filter_upwards [ae_mem_Ioo_Iθ] with θ hθi
      have hcont2 : ContinuousOn (fun z : ℝ => Work.Spaces.pzIter 2 Ψ z θ)
          (Set.Icc z₀ (z₀ + hh)) := by
        refine ((hsm.pzIter 2).curry_z hθi).continuousOn.mono ?_
        intro z hz
        exact lt_of_lt_of_le hz₀ hz.1
      have hslice_int : MeasureTheory.IntegrableOn (fun z : ℝ => |Work.Spaces.pzIter 2 Ψ z θ|)
          (Set.Ioc z₀ (z₀ + hh)) := by
        have h0 : MeasureTheory.IntegrableOn (fun z : ℝ => Work.Spaces.pzIter 2 Ψ z θ)
            (Set.Icc z₀ (z₀ + hh)) := hcont2.integrableOn_Icc
        exact MeasureTheory.IntegrableOn.mono_set h0.abs
          (fun x hx => ⟨le_of_lt hx.1, hx.2⟩)
      have hzb : ∀ z ∈ Set.Ioc z₀ (z₀ + hh),
          |Work.Spaces.pz Ψ z θ - Work.Spaces.pz Ψ z₀ θ|
            ≤ ∫ z' in Set.Ioc z₀ (z₀ + hh), |Work.Spaces.pzIter 2 Ψ z' θ| := by
        intro z hz
        have hzle' : z₀ ≤ z := le_of_lt hz.1
        have hcontz : ContinuousOn (fun z' : ℝ => Work.Spaces.pzIter 2 Ψ z' θ) (Set.Icc z₀ z) := by
          refine ((hsm.pzIter 2).curry_z hθi).continuousOn.mono ?_
          intro z' hz'
          exact lt_of_lt_of_le hz₀ hz'.1
        have hcontu : ContinuousOn (fun z' : ℝ => Work.Spaces.pzIter 2 Ψ z' θ) (Set.uIcc z₀ z) := by
          rw [Set.uIcc_of_le hzle']; exact hcontz
        have hderiv : ∀ z' ∈ Set.uIcc z₀ z,
            HasDerivAt (fun z'' : ℝ => Work.Spaces.pzIter 1 Ψ z'' θ)
              (Work.Spaces.pzIter 2 Ψ z' θ) z' := by
          intro z' hz'
          rw [Set.uIcc_of_le hzle'] at hz'
          exact hsm.hasDerivAt_slice_pzIter 1 hθi (lt_of_lt_of_le hz₀ hz'.1)
        have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcontu.intervalIntegrable
        have hftc' : ∫ y in z₀..z, Work.Spaces.pzIter 2 Ψ y θ
            = Work.Spaces.pz Ψ z θ - Work.Spaces.pz Ψ z₀ θ := by
          simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using hftc
        have e1 : Work.Spaces.pz Ψ z θ - Work.Spaces.pz Ψ z₀ θ
            = ∫ z' in Set.Ioc z₀ z, Work.Spaces.pzIter 2 Ψ z' θ := by
          rw [← hftc', intervalIntegral.integral_of_le hzle']
        rw [e1]
        have hIntg : MeasureTheory.IntegrableOn (fun z' : ℝ => Work.Spaces.pzIter 2 Ψ z' θ)
            (Set.Ioc z₀ z) :=
          MeasureTheory.IntegrableOn.mono_set hcontz.integrableOn_Icc
            (fun x hx => ⟨le_of_lt hx.1, hx.2⟩)
        have hstep1 : |∫ z' in Set.Ioc z₀ z, Work.Spaces.pzIter 2 Ψ z' θ|
            ≤ ∫ z' in Set.Ioc z₀ z, |Work.Spaces.pzIter 2 Ψ z' θ| := by
          have := MeasureTheory.norm_integral_le_integral_norm
            (μ := MeasureTheory.volume.restrict (Set.Ioc z₀ z))
            (f := fun z' : ℝ => Work.Spaces.pzIter 2 Ψ z' θ)
          simpa only [Real.norm_eq_abs] using this
        have hsub : MeasureTheory.volume.restrict (Set.Ioc z₀ z)
            ≤ MeasureTheory.volume.restrict (Set.Ioc z₀ (z₀ + hh)) :=
          MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume
            (fun x hx => ⟨hx.1, le_trans hx.2 hz.2⟩)
        have hstep2 : ∫ z' in Set.Ioc z₀ z, |Work.Spaces.pzIter 2 Ψ z' θ|
            ≤ ∫ z' in Set.Ioc z₀ (z₀ + hh), |Work.Spaces.pzIter 2 Ψ z' θ| := by
          have := MeasureTheory.integral_mono_measure hsub
            (Eventually.of_forall (fun x => abs_nonneg _)) hslice_int
          simpa only [Real.norm_eq_abs] using this
        exact hstep1.trans hstep2
      have hGfac : Gfun θ = ∫ z in Set.Ioc z₀ (z₀ + hh),
          (Work.Spaces.pz Ψ z θ - Work.Spaces.pz Ψ z₀ θ) := by
        rw [hGdef]
        exact intervalIntegral.integral_of_le hzle
      rw [hGfac]
      have hc : ContinuousOn (fun z : ℝ => Work.Spaces.pz Ψ z θ) (Set.Icc z₀ (z₀ + hh)) := by
        refine ((hsm.pz.curry_z hθi).continuousOn).mono ?_
        intro z hz
        exact lt_of_lt_of_le hz₀ hz.1
      have hf_int : MeasureTheory.IntegrableOn (fun z : ℝ =>
          Work.Spaces.pz Ψ z θ - Work.Spaces.pz Ψ z₀ θ) (Set.Ioc z₀ (z₀ + hh)) := by
        have hIcc : MeasureTheory.IntegrableOn (fun z : ℝ =>
            Work.Spaces.pz Ψ z θ - Work.Spaces.pz Ψ z₀ θ) (Set.Icc z₀ (z₀ + hh)) :=
          MeasureTheory.IntegrableOn.sub hc.integrableOn_Icc
            (MeasureTheory.integrableOn_const (s := Set.Icc z₀ (z₀ + hh)) (C := Work.Spaces.pz Ψ z₀ θ)
              (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
        exact MeasureTheory.IntegrableOn.mono_set hIcc (fun x hx => ⟨le_of_lt hx.1, hx.2⟩)
      have hstep1 : |∫ z in Set.Ioc z₀ (z₀ + hh),
            (Work.Spaces.pz Ψ z θ - Work.Spaces.pz Ψ z₀ θ)|
          ≤ ∫ z in Set.Ioc z₀ (z₀ + hh),
            |Work.Spaces.pz Ψ z θ - Work.Spaces.pz Ψ z₀ θ| := by
        have := MeasureTheory.norm_integral_le_integral_norm
          (μ := MeasureTheory.volume.restrict (Set.Ioc z₀ (z₀ + hh)))
          (f := fun z : ℝ => Work.Spaces.pz Ψ z θ - Work.Spaces.pz Ψ z₀ θ)
        simpa only [Real.norm_eq_abs] using this
      refine hstep1.trans ?_
      have hInt2 : MeasureTheory.IntegrableOn (fun _ : ℝ =>
          ∫ z' in Set.Ioc z₀ (z₀ + hh), |Work.Spaces.pzIter 2 Ψ z' θ|)
          (Set.Ioc z₀ (z₀ + hh)) :=
        integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      have hle_ae : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioc z₀ (z₀ + hh))),
          |Work.Spaces.pz Ψ z θ - Work.Spaces.pz Ψ z₀ θ|
            ≤ ∫ z' in Set.Ioc z₀ (z₀ + hh), |Work.Spaces.pzIter 2 Ψ z' θ| := by
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
        exact Eventually.of_forall (fun z hz => hzb z hz)
      refine (MeasureTheory.integral_mono_ae hf_int.abs hInt2 hle_ae).trans ?_
      · have hstep : ∫ z in Set.Ioc z₀ (z₀ + hh), (∫ z' in Set.Ioc z₀ (z₀ + hh),
            |Work.Spaces.pzIter 2 Ψ z' θ|) = hh * ∫ z' in Set.Ioc z₀ (z₀ + hh),
            |Work.Spaces.pzIter 2 Ψ z' θ| := by
          rw [← intervalIntegral.integral_of_le hzle, intervalIntegral.integral_const]
          ring
        rw [hstep]
    -- Cauchy–Schwarz on the slab
    have hB : ∀ z ∈ Set.Ioc z₀ (z₀ + hh),
        (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ)
          ≤ Real.sqrt (C₂ * M) * Real.sqrt (Hki z) := by
      intro z hz
      have hzpos : 0 < z := lt_trans hz₀ hz.1
      have hzIoo : z ∈ Set.Ioo z₀ (2 * z₀) := ⟨hz.1, by linarith [hz.2, hhle]⟩
      obtain ⟨hAint, hAle⟩ := pzIter2_sq_sEta_le_HkIntegrand hsm h.memA hz₀ hzIoo
      obtain ⟨-, hC₂nn', -, hCSineq⟩ := sinCos2_cs_sEta hAint (hsm.aesm_slice_pzIter 2 hzpos)
      have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ :=
        MeasureTheory.setIntegral_nonneg hIθ_meas
          (fun θ hθ => mul_nonneg (abs_nonneg _) (sinCos2_nonneg hθ))
      have hHknn : 0 ≤ Hki z := by
        rw [hHkidef]
        exact MeasureTheory.setIntegral_nonneg hIθ_meas
          (fun θ _ => Work.Spaces.HkIntegrand_nonneg _ _ _ _ _)
      have hsq : (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ) ^ 2
          ≤ (C₂ * M) * Hki z := by
        refine le_trans hCSineq ?_
        have h1 : ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ ≤ M * Hki z := by
          rw [hMdef, hHkidef]
          exact hAle
        calc C₂ * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
            ≤ C₂ * (M * Hki z) := mul_le_mul_of_nonneg_left h1 hC₂nn
          _ = (C₂ * M) * Hki z := by ring
      calc (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ)
          = Real.sqrt ((∫ θ in Work.Spaces.Iθ, |Work.Spaces.pzIter 2 Ψ z θ|
              * Work.Elliptic.sinCos2 θ) ^ 2) := (Real.sqrt_sq hnn).symm
        _ ≤ Real.sqrt ((C₂ * M) * Hki z) := Real.sqrt_le_sqrt hsq
        _ = Real.sqrt (C₂ * M) * Real.sqrt (Hki z) := Real.sqrt_mul (mul_nonneg hC₂nn hMnni) _
    -- swapping the two integrals
    have hKle : ∀ θ : ℝ, (∫ z in Set.Ioc z₀ (z₀ + hh), |Work.Spaces.pzIter 2 Ψ z θ|)
        * Work.Elliptic.sinCos2 θ
        = ∫ z, (|Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ) ∂μ := by
      intro θ
      rw [MeasureTheory.integral_mul_const]
    have hswap : ∫ θ in Work.Spaces.Iθ, (∫ z in Set.Ioc z₀ (z₀ + hh),
          |Work.Spaces.pzIter 2 Ψ z θ|) * Work.Elliptic.sinCos2 θ
        = ∫ z in Set.Ioc z₀ (z₀ + hh),
            (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ) := by
      have h1 : ∫ θ, (∫ z, (|Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ) ∂μ) ∂ν
          = ∫ z, (∫ θ, (|Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ) ∂ν) ∂μ :=
        (MeasureTheory.integral_integral_swap hιbox).symm
      have h2 : ∫ θ, (∫ z, (|Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ) ∂μ) ∂ν
          = ∫ θ in Work.Spaces.Iθ, (∫ z in Set.Ioc z₀ (z₀ + hh),
              |Work.Spaces.pzIter 2 Ψ z θ|) * Work.Elliptic.sinCos2 θ := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards with θ
        rw [← hKle θ]
      rw [← h2, h1]
    have hole : ∫ z in Set.Ioc z₀ (z₀ + hh),
          (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ)
        ≤ Real.sqrt (C₂ * M) * (hh + ∫ z in Set.Ioc z₀ (z₀ + hh), Hki z) := by
      have hHki_nn : ∀ z : ℝ, 0 ≤ Hki z := by
        intro z
        rw [hHkidef]
        exact MeasureTheory.setIntegral_nonneg hIθ_meas
          (fun θ _ => Work.Spaces.HkIntegrand_nonneg _ _ _ _ _)
      have hHkIloc : MeasureTheory.IntegrableOn Hki (Set.Ioc z₀ (z₀ + hh)) :=
        h.memA.2.mono_set (fun x hx => le_of_lt (lt_of_lt_of_le hz₀ (le_of_lt hx.1)))
      have hone : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc z₀ (z₀ + hh)) :=
        integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      have hsqrt : MeasureTheory.IntegrableOn (fun z : ℝ => Real.sqrt (Hki z))
          (Set.Ioc z₀ (z₀ + hh)) := by
        refine MeasureTheory.Integrable.mono' (hone.add hHkIloc)
          (Real.continuous_sqrt.comp_aestronglyMeasurable
            (MeasureTheory.Integrable.aestronglyMeasurable hHkIloc)) ?_
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
        filter_upwards with z hz
        rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_le_iff]
        refine ⟨?_, ?_⟩
        · show (0 : ℝ) ≤ 1 + Hki z
          linarith [hHki_nn z]
        · show Hki z ≤ ((1 : ℝ) + Hki z) ^ 2
          nlinarith [hHki_nn z, sq_nonneg (Hki z)]
      have hBint : MeasureTheory.IntegrableOn (fun z : ℝ =>
          ∫ θ in Work.Spaces.Iθ, |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ)
          (Set.Ioc z₀ (z₀ + hh)) := hιbox.integral_prod_left
      have h2int : MeasureTheory.IntegrableOn (fun z : ℝ => Real.sqrt (C₂ * M) * Real.sqrt (Hki z))
          (Set.Ioc z₀ (z₀ + hh)) := hsqrt.const_mul _
      have hmono : ∫ z in Set.Ioc z₀ (z₀ + hh),
            (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ)
          ≤ ∫ z in Set.Ioc z₀ (z₀ + hh), Real.sqrt (C₂ * M) * Real.sqrt (Hki z) := by
        have hle_ae : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioc z₀ (z₀ + hh))),
            (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ)
              ≤ Real.sqrt (C₂ * M) * Real.sqrt (Hki z) := by
          rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
          exact Eventually.of_forall (fun z hz => hB z hz)
        exact MeasureTheory.integral_mono_ae hBint h2int hle_ae
      have h3 : ∫ z in Set.Ioc z₀ (z₀ + hh), Real.sqrt (Hki z)
          ≤ hh + ∫ z in Set.Ioc z₀ (z₀ + hh), Hki z := by
        have h4 : MeasureTheory.IntegrableOn (fun z : ℝ => (1 : ℝ) + Hki z)
            (Set.Ioc z₀ (z₀ + hh)) := hone.add hHkIloc
        have h6 : ∫ z in Set.Ioc z₀ (z₀ + hh), Real.sqrt (Hki z)
            ≤ ∫ z in Set.Ioc z₀ (z₀ + hh), ((1 : ℝ) + Hki z) := by
          have hle_ae : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioc z₀ (z₀ + hh))),
              Real.sqrt (Hki z) ≤ (1 : ℝ) + Hki z := by
            rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
            filter_upwards with z hz
            rw [Real.sqrt_le_iff]
            refine ⟨?_, ?_⟩
            · show (0 : ℝ) ≤ 1 + Hki z
              linarith [hHki_nn z]
            · show Hki z ≤ ((1 : ℝ) + Hki z) ^ 2
              nlinarith [hHki_nn z, sq_nonneg (Hki z)]
          exact MeasureTheory.integral_mono_ae hsqrt h4 hle_ae
        have h7 : ∫ z in Set.Ioc z₀ (z₀ + hh), ((1 : ℝ) + Hki z)
            = hh + ∫ z in Set.Ioc z₀ (z₀ + hh), Hki z := by
          rw [MeasureTheory.integral_add hone hHkIloc]
          congr 1
          rw [← intervalIntegral.integral_of_le hzle, intervalIntegral.integral_const]
          ring
        rw [h7] at h6
        exact h6
      calc ∫ z in Set.Ioc z₀ (z₀ + hh),
            (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ)
          ≤ ∫ z in Set.Ioc z₀ (z₀ + hh), Real.sqrt (C₂ * M) * Real.sqrt (Hki z) := hmono
        _ = Real.sqrt (C₂ * M) * ∫ z in Set.Ioc z₀ (z₀ + hh), Real.sqrt (Hki z) :=
            MeasureTheory.integral_const_mul _ _
        _ ≤ Real.sqrt (C₂ * M) * (hh + ∫ z in Set.Ioc z₀ (z₀ + hh), Hki z) :=
            mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)
    -- the final estimate
    have h1 : |L| = |∫ θ in Work.Spaces.Iθ, (1/hh) * (Gfun θ * Work.Elliptic.sinCos2 θ)| := by
      rw [hval, abs_neg]
    have h2 : |∫ θ in Work.Spaces.Iθ, (1/hh) * (Gfun θ * Work.Elliptic.sinCos2 θ)|
        ≤ ∫ θ in Work.Spaces.Iθ, |(1/hh) * (Gfun θ * Work.Elliptic.sinCos2 θ)| := by
      have := MeasureTheory.norm_integral_le_integral_norm
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (f := fun θ : ℝ => (1/hh) * (Gfun θ * Work.Elliptic.sinCos2 θ))
      simpa only [Real.norm_eq_abs] using this
    have h3 : ∫ θ in Work.Spaces.Iθ, |(1/hh) * (Gfun θ * Work.Elliptic.sinCos2 θ)|
        ≤ ∫ θ in Work.Spaces.Iθ, (∫ z in Set.Ioc z₀ (z₀ + hh),
            |Work.Spaces.pzIter 2 Ψ z θ|) * Work.Elliptic.sinCos2 θ := by
      have h4 : MeasureTheory.IntegrableOn
          (fun θ : ℝ => |(1/hh) * (Gfun θ * Work.Elliptic.sinCos2 θ)|) Work.Spaces.Iθ := hGint.abs
      have h5 : MeasureTheory.IntegrableOn (fun θ : ℝ => (∫ z in Set.Ioc z₀ (z₀ + hh),
            |Work.Spaces.pzIter 2 Ψ z θ|) * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
        refine (hιbox.integral_prod_right).congr ?_
        filter_upwards with θ
        exact (hKle θ).symm
      have hle_ae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          |(1/hh) * (Gfun θ * Work.Elliptic.sinCos2 θ)|
            ≤ (∫ z in Set.Ioc z₀ (z₀ + hh), |Work.Spaces.pzIter 2 Ψ z θ|)
              * Work.Elliptic.sinCos2 θ := by
        filter_upwards [hGbound, MeasureTheory.ae_restrict_mem hIθ_meas] with θ hgb hθ
        rw [abs_mul, abs_mul, abs_of_pos (one_div_pos.mpr hhpos), abs_of_nonneg (sinCos2_nonneg hθ)]
        calc (1 / hh) * (|Gfun θ| * Work.Elliptic.sinCos2 θ)
          ≤ (1 / hh) * ((hh * ∫ z in Set.Ioc z₀ (z₀ + hh), |Work.Spaces.pzIter 2 Ψ z θ|)
            * Work.Elliptic.sinCos2 θ) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hgb (sinCos2_nonneg hθ))
              (by positivity)
        _ = (∫ z in Set.Ioc z₀ (z₀ + hh), |Work.Spaces.pzIter 2 Ψ z θ|)
            * Work.Elliptic.sinCos2 θ := by
            field_simp
      exact MeasureTheory.integral_mono_ae h4 h5 hle_ae
    exact h1 ▸ h2.trans (h3.trans (hswap ▸ hole))
  -- (4) the limit
  have hbound' : ∀ n : ℕ,
      |L| ≤ Real.sqrt (C₂ * M) * (z₀ / (n + 2 : ℝ)
        + ∫ z in Set.Ioc z₀ (z₀ + z₀ / (n + 2 : ℝ)), Hki z) := by
    intro n
    refine key (z₀ / (n + 2 : ℝ)) (by positivity) ?_
    rw [div_lt_iff₀ (by positivity : (0:ℝ) < ((n : ℝ) + 2))]
    nlinarith [hz₀]
  have hki_int : MeasureTheory.IntegrableOn Hki (Set.Ioc z₀ (z₀ + z₀)) :=
    h.memA.2.mono_set (fun x hx => le_of_lt (lt_of_lt_of_le hz₀ (le_of_lt hx.1)))
  have hlimHki : Filter.Tendsto (fun n : ℕ =>
      ∫ z in Set.Ioc z₀ (z₀ + z₀ / (n + 2 : ℝ)), Hki z) Filter.atTop (nhds 0) := by
    refine (tendsto_integral_Ioc_shrink hz₀ hki_int).comp
      (tendsto_add_atTop_nat 1) |>.congr' ?_
    filter_upwards with n
    show (∫ x in Set.Ioc z₀ (z₀ + z₀ / (((n + 1 : ℕ) : ℝ) + 1)), Hki x)
      = ∫ x in Set.Ioc z₀ (z₀ + z₀ / ((n : ℝ) + 2)), Hki x
    congr 2
    push_cast
    ring
  have hlimh : Filter.Tendsto (fun n : ℕ => z₀ / (n + 2 : ℝ)) Filter.atTop (nhds 0) := by
    refine (tendsto_const_div_atTop_nhds_zero_nat (z₀)).comp
      (tendsto_add_atTop_nat 2) |>.congr' ?_
    filter_upwards with n
    show z₀ / (((n + 2 : ℕ)) : ℝ) = z₀ / ((n : ℝ) + 2)
    congr 1
    push_cast
    ring
  have hlim : Filter.Tendsto (fun n : ℕ => Real.sqrt (C₂ * M) * (z₀ / (n + 2 : ℝ)
      + ∫ z in Set.Ioc z₀ (z₀ + z₀ / (n + 2 : ℝ)), Hki z)) Filter.atTop (nhds 0) := by
    have hh : Filter.Tendsto (fun n : ℕ => z₀ / (n + 2 : ℝ)
        + ∫ z in Set.Ioc z₀ (z₀ + z₀ / (n + 2 : ℝ)), Hki z) Filter.atTop (nhds 0) := by
      simpa using hlimh.add hlimHki
    simpa using hh.const_mul (Real.sqrt (C₂ * M))
  have hLle : |L| ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Filter.Eventually.of_forall hbound')
  have hL0 : L = 0 := abs_eq_zero.mp (le_antisymm hLle (abs_nonneg L))
  exact hL0

theorem pz_moment_eq_zero {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ z : ℝ, 0 < z → ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ = 0 := by
  intro z hz
  by_cases hint : MeasureTheory.Integrable
      (fun θ : ℝ => Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)
  · exact pz_moment_of_integrable hk h hz hint
  · exact MeasureTheory.integral_undef hint

theorem FstarDzOnePsi : ∀ (α : ℝ) {k : ℕ}, 1 ≤ k → ∀ (F Ψ : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
    ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z = 0 := by
  intro α k hk F Ψ h z hz
  rw [Work.Elliptic.Fstar]
  rw [show (fun θ : ℝ => Work.Spaces.DzIter 1 Ψ z θ * Work.Elliptic.sinCos2 θ)
      = fun θ : ℝ => z * (Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) from by
    funext θ
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz, Work.Spaces.pz]
    ring]
  rw [MeasureTheory.integral_const_mul, pz_moment_eq_zero hk h z hz, mul_zero]

end Work.FTS.EllipticEst.Mine
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.wsDzSplits =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open Filter Set

namespace Work.FTS.EllipticEst.remov


end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.wsMomentDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false

/-- **The reference `θ`-energy of a datum `Ψ`.**  The sum of the four `sEta`-weighted
`θ`-energies that the weak class controls: those of `∂_θθΨ`, of `D_z∂_θθΨ`, of `z²∂_zzΨ`
and of `D_z(z²∂_zzΨ)`.  Every `θ`-energy `thetaE (D_z^j Ψ)` with `1 ≤ j ≤ 3` is bounded on a
compact radial interval by a constant times `1 + Eref Ψ`, and `Eref Ψ` is locally integrable
— this is `remov.sliceEnergyBounds`. -/
def Eref (Ψ : ℝ → ℝ → ℝ) (s : ℝ) : ℝ :=
  thetaE (Work.Spaces.pthIter 2 Ψ) s
    + thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s
    + thetaE (fun u θ => u ^ 2 * Work.Spaces.pzIter 2 Ψ u θ) s
    + thetaE (Work.Spaces.DzIter 1 (fun u θ => u ^ 2 * Work.Spaces.pzIter 2 Ψ u θ)) s

theorem Eref_nonneg (Ψ : ℝ → ℝ → ℝ) (s : ℝ) : 0 ≤ Eref Ψ s := by
  unfold Eref
  have h1 := thetaE_nonneg (Work.Spaces.pthIter 2 Ψ) s
  have h2 := thetaE_nonneg (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s
  have h3 := thetaE_nonneg (fun u θ => u ^ 2 * Work.Spaces.pzIter 2 Ψ u θ) s
  have h4 := thetaE_nonneg (Work.Spaces.DzIter 1 (fun u θ => u ^ 2 * Work.Spaces.pzIter 2 Ψ u θ)) s
  linarith

end Work.FTS.EllipticEst.remov
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.wsPzPthIterThetaE =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option maxHeartbeats 1600000



end Work.FTS.EllipticEst.remov
end
end
-- ===== merged: Submission.Work.FTS.H2.QangBox =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The radial weight and the derivatives -/

/-- The radial weight is at least `1` (it is `(1 + 1/z)²`). -/
theorem one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-! ## Almost-everywhere statements on the quadrant and on a box -/

/-- A property which holds on the *open* quadrant holds almost everywhere on `Iz × Iθ` (the
complement is contained in the coordinate hyperplanes and the two angular endpoints). -/
theorem ae_prod_quad {p : ℝ × ℝ → Prop}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → p (z, θ)) :
    ∀ᵐ q ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), p q := by
  have h1 : (MeasureTheory.volume.restrict Work.Spaces.Iz : Measure ℝ)
      = MeasureTheory.volume.restrict (Set.Ioi 0) := by
    rw [Work.Spaces.Iz]
    exact (MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioi_ae_eq_Ici).symm
  have h2 : (MeasureTheory.volume.restrict Work.Spaces.Iθ : Measure ℝ)
      = MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2)) := by
    rw [Work.Spaces.Iθ]
    exact (MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm
  rw [h1, h2, MeasureTheory.Measure.prod_restrict]
  refine MeasureTheory.ae_restrict_of_forall_mem (isOpen_Ioi.prod isOpen_Ioo).measurableSet ?_
  rintro ⟨z, θ⟩ hq
  simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hq
  exact h z θ hq.1 hq.2.1 hq.2.2

/-- The same for the box `uIoc a b ×ˢ uIoc 0 (π/2)`, `a ≤ b`. -/
theorem ae_prod_box {a b : ℝ} (hab : a ≤ b) {p : ℝ × ℝ → Prop}
    (h : ∀ z θ : ℝ, z ∈ Set.uIoc a b → 0 < θ → θ < π / 2 → p (z, θ)) :
    ∀ᵐ q ∂((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
      (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2)))), p q := by
  have h2 : (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2)) : Measure ℝ)
      = MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2)) := by
    rw [Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ π / 2)]
    exact (MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc).symm
  rw [h2, MeasureTheory.Measure.prod_restrict]
  refine MeasureTheory.ae_restrict_of_forall_mem
    ((measurableSet_uIoc).prod isOpen_Ioo.measurableSet) ?_
  rintro ⟨z, θ⟩ hq
  simp only [Set.mem_prod, Set.mem_Ioo] at hq
  exact h z θ hq.1 hq.2.1 hq.2.2

/-! ## Joint integrability of the `ℋ⁴`-integrand -/

/-- The uncurried `ℋ⁴`-integrand of a `SmoothQuad` function is a.e. strongly measurable for the
product of the restrictions of Lebesgue measure. -/
theorem aesm_joint_HkIntegrand {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 g p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _
    (Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α 4 g hsm)

/-- **`HkIntegrand α 4 g` is jointly integrable on the quadrant** for
`SmoothQuad g + HkMem α 4 g`, by Tonelli: both iterated integrals are the two halves of
`HkMem α 4 g`. -/
theorem HkIntegrand_joint_integrable {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 g p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hnn : ∀ z θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    fun z θ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  have haesm := aesm_joint_HkIntegrand (α := α) hsm
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => Work.Spaces.HkIntegrand α 4 g z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    exact hmem.1 z hz
  have houter : MeasureTheory.Integrable
      (fun z => ∫ θ, Work.Spaces.HkIntegrand α 4 g z θ
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hmem.2
  exact (Work.Spaces.integrable_prod_of_iterated hnn haesm hslice houter).1

/-! ## Joint integrability of the square of a `D_z`-iterate -/

/-- **`(D_zⁱ g)²` is jointly integrable on the quadrant** for `i ≤ 4`: it is dominated by
`HkIntegrand α 4 g` because `w ≥ 1` on `z > 0`. -/
theorem DzIter_sq_joint_integrable {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g)
    {i : ℕ} (hi : i ≤ 4) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => (Work.Spaces.DzIter i g p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  refine MeasureTheory.Integrable.mono' (HkIntegrand_joint_integrable hsm hmem) ?_ ?_
  · have hcont : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.DzIter i g p.1 p.2) ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      ((SmoothQuad.toSmoothOpen hsm).DzIter i).continuousOn.pow 2
    exact Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  · refine ae_prod_quad (fun z θ hz hθ1 hθ2 => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h1 := sq_DzIter_le_HkIntegrand_div_w_sq α 4 g i hi hz ⟨hθ1, hθ2⟩
    have h2 : Work.Spaces.HkIntegrand α 4 g z θ / (Work.Spaces.w z) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
      rw [div_le_iff₀ (pow_pos (w_pos hz) 2)]
      have hw2 : (1 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := by
        have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (one_le_w hz) 2
        simpa using h
      nlinarith [Work.Spaces.HkIntegrand_nonneg α 4 g z θ, hw2]
    linarith

/-! ## The joint integrand of the angular moment on a box -/

/-- The joint integrand `(x,θ) ↦ Kθ(θ)·D_z^{j+1} g x θ / x` is continuous on the open
quadrant. -/
theorem continuousOn_Ktheta_DzIter_div {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) (j : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2
      * Work.Spaces.DzIter j g p.1 p.2 / p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
  (continuousOn_Ktheta_DzIter hsm j).div continuousOn_fst (fun p hp => ne_of_gt hp.1)

/-- **Joint integrability on a box, and of its `θ`-integral.**  For `0 < a ≤ b` and `j ≤ 3`,

* the joint integrand `(x,θ) ↦ Kθ(θ)·D_z^{j+1} g x θ / x` is integrable on the box
  `uIoc a b ×ˢ uIoc 0 (π/2)` (this is the Fubini hypothesis);
* its `θ`-integral `x ↦ Qang g (j+1) x / x` is integrable on `uIoc a b`. -/
theorem QangBoxIntegrable {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g)
    {j : ℕ} (hj : j ≤ 3) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    MeasureTheory.IntegrableOn
        (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 * Work.Spaces.DzIter (j + 1) g p.1 p.2 / p.1)
        (Set.uIoc a b ×ˢ Set.uIoc 0 (π / 2)) ∧
      MeasureTheory.IntegrableOn (fun x : ℝ => Work.Elliptic.Qang g (j + 1) x / x)
        (Set.uIoc a b) := by
  have hsub1 : Set.uIoc a b ⊆ Work.Spaces.Iz := by
    rw [Work.Spaces.Iz, Set.uIoc_of_le hab]
    exact fun x hx => le_of_lt (lt_trans ha hx.1)
  have hsub2 : Set.uIoc 0 (π / 2) ⊆ Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ, Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ π / 2)]
    exact fun x hx => ⟨le_of_lt hx.1, hx.2⟩
  have hle : (MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2)))
      ≤ (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.Measure.restrict_mono (Set.prod_mono hsub1 hsub2) le_rfl
  have hD2 : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.DzIter (j + 1) g p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2)))) :=
    (DzIter_sq_joint_integrable hsm hmem (by omega)).mono_measure hle
  have hconst : MeasureTheory.Integrable (fun _ : ℝ × ℝ => (1 : ℝ))
      ((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2)))) := by
    have hne : ((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2)))) Set.univ ≠ ⊤ := by
      rw [← Set.univ_prod_univ, MeasureTheory.Measure.prod_prod,
        MeasureTheory.Measure.restrict_apply_univ, MeasureTheory.Measure.restrict_apply_univ,
        Set.uIoc_of_le hab, Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ π / 2),
        Real.volume_Ioc, Real.volume_Ioc]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    simpa only [MeasureTheory.IntegrableOn, MeasureTheory.Measure.restrict_univ] using
      (MeasureTheory.integrableOn_const (μ := (MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2)))) (s := Set.univ) (C := (1 : ℝ)) hne)
  -- the a.e. domination of the joint integrand
  have haesmF : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2
        * Work.Spaces.DzIter (j + 1) g p.1 p.2 / p.1)
      ((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2)))) :=
    (Work.Spaces.aesm_of_continuousOn_Qd _
      (continuousOn_Ktheta_DzIter_div hsm (j + 1))).mono_measure hle
  have hdom : ∀ᵐ p ∂((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
      (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2)))),
      ‖Work.Elliptic.Ktheta p.2 * Work.Spaces.DzIter (j + 1) g p.1 p.2 / p.1‖
        ≤ (3 / a) * ((Work.Spaces.DzIter (j + 1) g p.1 p.2) ^ 2 + 1) := by
    refine ae_prod_box hab (fun z θ hz hθ1 hθ2 => ?_)
    have hzpos : 0 < z := by
      rw [Set.uIoc_of_le hab] at hz
      exact lt_trans ha hz.1
    have haz : a ≤ z := by
      rw [Set.uIoc_of_le hab] at hz
      exact hz.1.le
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hzpos, abs_mul]
    have hD1 : |Work.Spaces.DzIter (j + 1) g z θ|
        ≤ (Work.Spaces.DzIter (j + 1) g z θ) ^ 2 + 1 := by
      nlinarith [sq_nonneg (|Work.Spaces.DzIter (j + 1) g z θ| - 1),
        sq_abs (Work.Spaces.DzIter (j + 1) g z θ),
        abs_nonneg (Work.Spaces.DzIter (j + 1) g z θ)]
    have hDnn : 0 ≤ |Work.Spaces.DzIter (j + 1) g z θ| := abs_nonneg _
    have h1 : |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter (j + 1) g z θ| / z
        ≤ 3 * |Work.Spaces.DzIter (j + 1) g z θ| / z :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (abs_Ktheta_le_three θ) hDnn) hzpos.le
    have h2 : 3 * |Work.Spaces.DzIter (j + 1) g z θ| / z
        ≤ 3 * ((Work.Spaces.DzIter (j + 1) g z θ) ^ 2 + 1) / z :=
      div_le_div_of_nonneg_right (by linarith) hzpos.le
    have h3 : 3 * ((Work.Spaces.DzIter (j + 1) g z θ) ^ 2 + 1) / z
        ≤ 3 * ((Work.Spaces.DzIter (j + 1) g z θ) ^ 2 + 1) / a :=
      div_le_div_of_nonneg_left (by positivity) ha haz
    have h4 : 3 * ((Work.Spaces.DzIter (j + 1) g z θ) ^ 2 + 1) / a
        = (3 / a) * ((Work.Spaces.DzIter (j + 1) g z θ) ^ 2 + 1) := by ring
    linarith [h1, h2, h3, h4.le, h4.ge]
  have hFbox : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2
        * Work.Spaces.DzIter (j + 1) g p.1 p.2 / p.1)
      ((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2)))) :=
    MeasureTheory.Integrable.mono' ((hD2.add hconst).const_mul (3 / a)) haesmF hdom
  refine ⟨?_, ?_⟩
  · have hvol : (MeasureTheory.volume : Measure (ℝ × ℝ)).restrict
        (Set.uIoc a b ×ˢ Set.uIoc 0 (π / 2))
        = (MeasureTheory.volume.restrict (Set.uIoc a b)).prod
          (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2))) := by
      rw [MeasureTheory.Measure.prod_restrict]
      rfl
    show MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2
        * Work.Spaces.DzIter (j + 1) g p.1 p.2 / p.1)
      ((MeasureTheory.volume : Measure (ℝ × ℝ)).restrict
        (Set.uIoc a b ×ˢ Set.uIoc 0 (π / 2)))
    rw [hvol]
    exact hFbox
  · have h1 : MeasureTheory.Integrable
        (fun x : ℝ => ∫ θ, (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2
            * Work.Spaces.DzIter (j + 1) g p.1 p.2 / p.1) (x, θ)
          ∂(MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2))))
        (MeasureTheory.volume.restrict (Set.uIoc a b)) :=
      MeasureTheory.Integrable.integral_prod_left hFbox
    have hset : Set.uIoc 0 (π / 2) =ᵐ[MeasureTheory.volume] Work.Spaces.Iθ := by
      rw [Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ π / 2), Work.Spaces.Iθ]
      exact MeasureTheory.Ioc_ae_eq_Icc
    refine h1.congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc (fun x hx => ?_)
    have hxpos : 0 < x := by
      rw [Set.uIoc_of_le hab] at hx
      exact lt_trans ha hx.1
    change (∫ θ in Set.uIoc 0 (π / 2),
        Work.Elliptic.Ktheta θ * Work.Spaces.DzIter (j + 1) g x θ / x)
      = Work.Elliptic.Qang g (j + 1) x / x
    rw [MeasureTheory.setIntegral_congr_set hset, MeasureTheory.integral_div]
    rfl

end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5 =====
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

set_option linter.unusedVariables false

/-! ## The weighted derivatives of `1 - χ`, up to order `5`

The proof of `Work.FTS.LocData.OneSubChi_deriv_bound` (orders `≤ 4`) uses nothing about `4`:
for `k ≥ 1` the function `x ↦ x ^ k · ∂^k (1 - χ)(x)` is continuous (χ is `C^∞`) and vanishes
off `|x| ≤ 2`, hence is bounded on the compact set `[-2,2]`; the case `k = 0` is the trivial
bound `|1 - χ x| ≤ 1`.  We re-run that argument with the order bound `5`. -/

/-- **The weighted derivatives of `1 - χ` are bounded up to order `5`.**  There is a constant
`M` dominating `|x ^ k · ∂^k (1 - χ)(x)|` for all `k ≤ 5` and all `x : ℝ`. -/
theorem OneSubChi_deriv_bound5 :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k ≤ 5, ∀ x : ℝ,
      |x ^ k * iteratedDeriv k (fun x => (1 : ℝ) - Work.Stability.chi x) x| ≤ M := by
  have hsm : ContDiff ℝ Work.Stability.smoothOrder
      (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) :=
    contDiff_const.sub Work.Stability.chi_contDiff
  have key : ∀ k : ℕ, ∃ Mk : ℝ, 0 ≤ Mk ∧
      ∀ x : ℝ, |x ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) x| ≤ Mk := by
    intro k
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · -- `k = 0`: the bound `|1 - χ x| ≤ 1`
      subst h0
      refine ⟨1, zero_le_one, fun x => ?_⟩
      have hxg : iteratedDeriv 0 (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) x
          = 1 - Work.Stability.chi x :=
        congrFun (iteratedDeriv_zero (f := fun x : ℝ => (1 : ℝ) - Work.Stability.chi x)) x
      rw [hxg]
      simp only [pow_zero, one_mul]
      rw [abs_le]
      constructor
      · linarith [Work.Stability.chi_le_one x]
      · linarith [Work.Stability.chi_nonneg x]
    · -- `k ≥ 1`: continuity on the compact set `[-2,2]` plus vanishing off `(-2,2)`
      have hcont : Continuous (fun x : ℝ =>
          x ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) x) :=
        (continuous_id.pow k).mul (hsm.continuous_iteratedDeriv k (by simp))
      obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
        (f := fun x : ℝ =>
          x ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) x)
        hcont.continuousOn
      refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
      by_cases hx : |x| ≤ 2
      · have hxmem : x ∈ Set.Icc (-2 : ℝ) 2 := by
          rw [Set.mem_Icc, ← abs_le]; exact hx
        have hbound := hC x hxmem
        rw [Real.norm_eq_abs] at hbound
        exact le_trans hbound (le_max_left _ _)
      · -- `|x| > 2`: `χ ≡ 0` on a neighbourhood of `x`, so all its derivatives vanish there
        have hx2 : 2 < |x| := not_le.mp hx
        have hvan : iteratedDeriv k Work.Stability.chi x = 0 := by
          have hev : Work.Stability.chi =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
            have hmem : ∀ᶠ y in 𝓝 x, 2 < |y| :=
              (isOpen_lt continuous_const continuous_abs).mem_nhds (by simpa using hx2)
            filter_upwards [hmem] with y hy
            exact Work.Stability.chi_eq_zero (le_of_lt hy)
          rw [hev.iteratedDeriv_eq k, Work.Spaces.iteratedDeriv_zero_fun k x]
        have hgk : iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) x
            = - iteratedDeriv k Work.Stability.chi x := by
          rw [iteratedDeriv_const_sub hpos (1 : ℝ)]
          simp
        rw [hgk, hvan]
        simp
  obtain ⟨M0, _, hM0⟩ := key 0
  obtain ⟨M1, _, hM1⟩ := key 1
  obtain ⟨M2, _, hM2⟩ := key 2
  obtain ⟨M3, _, hM3⟩ := key 3
  obtain ⟨M4, _, hM4⟩ := key 4
  obtain ⟨M5, _, hM5⟩ := key 5
  refine ⟨M0 + M1 + M2 + M3 + M4 + M5, by linarith, fun k hk x => ?_⟩
  interval_cases k
  · exact le_trans (hM0 x) (by linarith)
  · exact le_trans (hM1 x) (by linarith)
  · exact le_trans (hM2 x) (by linarith)
  · exact le_trans (hM3 x) (by linarith)
  · exact le_trans (hM4 x) (by linarith)
  · exact le_trans (hM5 x) (by linarith)



end Work.FTS.LocDataExt
end
end
