import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_bd_ptwise
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.EllipticEst.remov.wsSliceRight
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS_EllLimOK.EGap.integrableOn_PhiD
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.FTS.EllipticEst.Alpha4.slice_key =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Alpha4

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem sin_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem sin_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- On `Iθ`, division by `s ^ p` (`s ≥ 0`, `p > 0`) is multiplication by `s ^ (-p)`. -/
theorem div_eq_mul_rpow_neg {a s p : ℝ} (hs : 0 ≤ s) (hp : 0 < p) :
    a / s ^ p = a * s ^ (-p) := by
  rcases eq_or_lt_of_le hs with h | h
  · rw [← h, Real.zero_rpow (ne_of_gt hp), Real.zero_rpow (neg_ne_zero.mpr (ne_of_gt hp)),
      div_zero, mul_zero]
  · rw [div_eq_mul_inv, Real.rpow_neg h.le]

/-- `x ^ 2 * x ^ (-(2+p)) = x ^ (-p)` for `x > 0`. -/
theorem sq_mul_rpow_neg_two_add {x p : ℝ} (hx : 0 < x) :
    x ^ 2 * x ^ (-(2 + p)) = x ^ (-p) := by
  have hx2 : x ^ 2 = x ^ (2 : ℝ) := (Real.rpow_natCast x 2).symm
  rw [hx2, ← Real.rpow_add hx]
  ring_nf

/-- On the open interval `(0,π/2)`, `cot(2θ)² σ = cos²(2θ) sin(2θ)^{-(2+η)}`. -/
theorem cot_sq_mul_thEta {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Real.cot (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ
      = (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) := by
  have hs : 0 < Real.sin (2 * θ) := sin_pos_of_mem_Ioo hθ
  have hkey : (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))
      = ((Real.sin (2 * θ)) ^ 2)⁻¹ * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
    rw [show -(2 + Work.Spaces.eta) = (-2 : ℝ) + (-Work.Spaces.eta) by ring,
      Real.rpow_add hs, Real.rpow_neg hs.le]
    rw [show (Real.sin (2 * θ)) ^ (2 : ℝ) = (Real.sin (2 * θ)) ^ 2 from
      Real.rpow_natCast _ 2]
  rw [hkey, Real.cot_eq_cos_div_sin, div_pow, Work.FTS.EllipticEst.thEta, div_eq_mul_inv,
    Real.rpow_neg hs.le]
  ring

theorem slice_key : ∃ c₁ : ℝ, 0 < c₁ ∧
    ∀ (f : ℝ → ℝ),
      ContDiffOn ℝ 2 f (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) →
      f 0 = 0 → f (Real.pi / 2) = 0 →
      (1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)
          * (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ - (∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ)
          + c₁ * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
  obtain ⟨C_H, hC_H_pos, hC_H⟩ := Work.FTS.EllipticEst.hardy_shift_two_same_weight
    Work.Spaces.eta Work.Spaces.eta_pos.le Work.Spaces.eta_lt_one
  have hη : (0 : ℝ) < Work.Spaces.eta := Work.Spaces.eta_pos
  have hη1 : Work.Spaces.eta < 1 := Work.Spaces.eta_lt_one
  have h1η : (0 : ℝ) < 1 + Work.Spaces.eta := by linarith
  refine ⟨Work.Spaces.eta * (1 + Work.Spaces.eta) * C_H, by positivity, ?_⟩
  intro f hf hf0 hf1
  -- the four angular integrals
  set I : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ with hIdef
  set J : ℝ := ∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ
      * Work.FTS.EllipticEst.thEta θ with hJdef
  set K : ℝ := ∫ θ in Work.Spaces.Iθ, f θ * deriv f θ * Real.cot (2 * θ)
      * Work.FTS.EllipticEst.thEta θ with hKdef
  set V : ℝ := ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ with hVdef
  set Y : ℝ := ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) with hYdef
  set W : ℝ := ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * (Real.cot (2 * θ)) ^ 2
      * Work.FTS.EllipticEst.thEta θ with hWdef
  -- the angular integration by parts
  have hAng : I = -J + 2 * Work.Spaces.eta * K := by
    rw [hIdef, hJdef, hKdef]
    exact Work.FTS.EllipticEst.ThetaU.ang_ibp_eta hf hf0 hf1
  -- integrability of the three pieces of the IBP
  obtain ⟨hIint, hJint, hKint⟩ :=
    Work.FTS.EllipticEst.ThetaU.integrableOn_ang_pieces hf hf0 hf1
  -- the slice bounds
  obtain ⟨C, M₃, hC0, hM₃0, hfb, hdb, hddb⟩ :=
    Work.FTS.EllipticEst.ThetaU.slice_bounds hf hf0 hf1
  -- continuity of the pieces on the open interval
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) :=
    fun θ hθ => ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hIooIθ : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ := Set.Ioo_subset_Icc_self
  have hcont_f : ContinuousOn f (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hf.continuousOn.mono hsub
  have hcont_sin : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ))) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hsinn : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.sin (2 * θ) ≠ 0 :=
    fun θ hθ => ne_of_gt (sin_pos_of_mem_Ioo hθ)
  have hcont_th : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hcont_sin.rpow_const (fun θ hθ => Or.inl (hsinn θ hθ))
  -- the pointwise majorant for the singular weight, reused below
  have hmaj : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))
        ≤ C ^ 2 * (Real.pi / 4) ^ (2 + Work.Spaces.eta)
            * (θ ^ (-Work.Spaces.eta) + (Real.pi / 2 - θ) ^ (-Work.Spaces.eta)) := by
    intro θ hθ
    have hs : (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))
        ≤ (Real.pi / 4) ^ (2 + Work.Spaces.eta)
            * (θ ^ (-(2 + Work.Spaces.eta))
              + (Real.pi / 2 - θ) ^ (-(2 + Work.Spaces.eta))) :=
      Work.Spaces.sin_rpow_le_majorant_pi (2 + Work.Spaces.eta) θ (by positivity) (hIooIθ hθ)
    have hmin0 : 0 ≤ min θ (Real.pi / 2 - θ) := le_min hθ.1.le (by linarith [hθ.2])
    have hfa : |f θ| ≤ C * min θ (Real.pi / 2 - θ) := hfb θ (hIooIθ hθ)
    have hf2 : (f θ) ^ 2 ≤ C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2 := by
      rw [← sq_abs]
      simpa only [mul_pow] using pow_le_pow_left₀ (abs_nonneg (f θ)) hfa 2
    have hspos : 0 < (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) :=
      Real.rpow_pos_of_pos (sin_pos_of_mem_Ioo hθ) _
    have hmin_le1 : min θ (Real.pi / 2 - θ) ≤ θ := min_le_left _ _
    have hmin_le2 : min θ (Real.pi / 2 - θ) ≤ Real.pi / 2 - θ := min_le_right _ _
    have hsq1 : (min θ (Real.pi / 2 - θ)) ^ 2 * θ ^ (-(2 + Work.Spaces.eta))
        ≤ θ ^ (-Work.Spaces.eta) := by
      have h2 : (min θ (Real.pi / 2 - θ)) ^ 2 ≤ θ ^ 2 :=
        pow_le_pow_left₀ hmin0 hmin_le1 2
      calc (min θ (Real.pi / 2 - θ)) ^ 2 * θ ^ (-(2 + Work.Spaces.eta))
          ≤ θ ^ 2 * θ ^ (-(2 + Work.Spaces.eta)) :=
            mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hθ.1.le _)
        _ = θ ^ (-(Work.Spaces.eta)) := sq_mul_rpow_neg_two_add hθ.1
    have hsq2 : (min θ (Real.pi / 2 - θ)) ^ 2
          * (Real.pi / 2 - θ) ^ (-(2 + Work.Spaces.eta))
        ≤ (Real.pi / 2 - θ) ^ (-Work.Spaces.eta) := by
      have h2 : (min θ (Real.pi / 2 - θ)) ^ 2 ≤ (Real.pi / 2 - θ) ^ 2 :=
        pow_le_pow_left₀ hmin0 hmin_le2 2
      have hpos : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
      calc (min θ (Real.pi / 2 - θ)) ^ 2 * (Real.pi / 2 - θ) ^ (-(2 + Work.Spaces.eta))
          ≤ (Real.pi / 2 - θ) ^ 2 * (Real.pi / 2 - θ) ^ (-(2 + Work.Spaces.eta)) :=
            mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hpos.le _)
        _ = (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta)) := sq_mul_rpow_neg_two_add hpos
    calc (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))
        ≤ C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2
            * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) :=
          mul_le_mul_of_nonneg_right hf2 hspos.le
      _ ≤ C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2
            * ((Real.pi / 4) ^ (2 + Work.Spaces.eta)
              * (θ ^ (-(2 + Work.Spaces.eta))
                + (Real.pi / 2 - θ) ^ (-(2 + Work.Spaces.eta)))) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = C ^ 2 * (Real.pi / 4) ^ (2 + Work.Spaces.eta)
            * ((min θ (Real.pi / 2 - θ)) ^ 2 * θ ^ (-(2 + Work.Spaces.eta))
              + (min θ (Real.pi / 2 - θ)) ^ 2
                * (Real.pi / 2 - θ) ^ (-(2 + Work.Spaces.eta))) := by ring
      _ ≤ C ^ 2 * (Real.pi / 4) ^ (2 + Work.Spaces.eta)
            * (θ ^ (-Work.Spaces.eta) + (Real.pi / 2 - θ) ^ (-Work.Spaces.eta)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact add_le_add hsq1 hsq2
  -- nonnegativity of the weighted `cot²` integrand on `Iθ`
  have hpt_nn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ (f θ) ^ 2 * (Real.cot (2 * θ)) ^ 2
      * Work.FTS.EllipticEst.thEta θ := by
    intro θ hθ
    have h1 : 0 ≤ Work.FTS.EllipticEst.thEta θ := by
      rcases eq_or_lt_of_le (sin_nonneg_of_mem_Iθ hθ) with h | h
      · rw [Work.FTS.EllipticEst.thEta, ← h, Real.zero_rpow (neg_ne_zero.mpr hη.ne')]
      · exact (Real.rpow_pos_of_pos h _).le
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) h1
  -- the pointwise comparison `f² cot²(2θ) σ ≤ f² sin(2θ)^{-(2+η)}` on `Iθ`
  have hpt : ∀ θ ∈ Work.Spaces.Iθ, (f θ) ^ 2 * (Real.cot (2 * θ)) ^ 2
      * Work.FTS.EllipticEst.thEta θ
      ≤ (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) := by
    intro θ hθ
    rcases eq_or_ne (Real.sin (2 * θ)) 0 with hsin | hsin
    · have hσ : Work.FTS.EllipticEst.thEta θ = 0 := by
        rw [Work.FTS.EllipticEst.thEta, hsin, Real.zero_rpow (neg_ne_zero.mpr hη.ne')]
      have h2 : (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) = 0 := by
        rw [hsin, Real.zero_rpow (neg_ne_zero.mpr (by positivity : (2 + Work.Spaces.eta) ≠ 0))]
      rw [hσ, h2]
      simp
    · have hs : 0 < Real.sin (2 * θ) :=
        lt_of_le_of_ne (sin_nonneg_of_mem_Iθ hθ) (Ne.symm hsin)
      have hθ0 : θ ≠ 0 := by
        intro h; exact hsin (by rw [h]; norm_num)
      have hθ1 : θ ≠ Real.pi / 2 := by
        intro h
        apply hsin
        rw [h, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      have hθ' : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨lt_of_le_of_ne hθ.1 (Ne.symm hθ0), lt_of_le_of_ne hθ.2 hθ1⟩
      have hcos : (Real.cos (2 * θ)) ^ 2 ≤ 1 := by
        have h := Real.sin_sq_add_cos_sq (2 * θ)
        nlinarith [sq_nonneg (Real.sin (2 * θ))]
      calc (f θ) ^ 2 * (Real.cot (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ
          = (f θ) ^ 2 * ((Real.cos (2 * θ)) ^ 2
              * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))) := by
            rw [show (f θ) ^ 2 * (Real.cot (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ
                = (f θ) ^ 2 * ((Real.cot (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ) by ring,
              cot_sq_mul_thEta hθ']
        _ ≤ (f θ) ^ 2 * (1 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hcos (Real.rpow_nonneg hs.le _)) (sq_nonneg _)
        _ = (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) := by ring
  -- the same bound with the majorant
  have hpt_maj : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (f θ) ^ 2 * (Real.cot (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ
        ≤ C ^ 2 * (Real.pi / 4) ^ (2 + Work.Spaces.eta)
            * (θ ^ (-Work.Spaces.eta) + (Real.pi / 2 - θ) ^ (-Work.Spaces.eta)) := by
    intro θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := Set.Ioo_subset_Icc_self hθ
    exact le_trans (hpt θ hθI) (hmaj θ hθ)
  -- integrability of the three `θ`-integrals
  have hYint : IntegrableOn (fun θ => (f θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))) Work.Spaces.Iθ := by
    refine Work.Elliptic.integrableOn_of_rpow_majorant hη.le hη1
      (by positivity : (0 : ℝ) ≤ C ^ 2 * (Real.pi / 4) ^ (2 + Work.Spaces.eta)) ?_ ?_
    · exact (hcont_f.pow 2).mul hcont_th
    · intro θ hθ
      have hnn : 0 ≤ (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) :=
        mul_nonneg (sq_nonneg _) (Real.rpow_pos_of_pos (sin_pos_of_mem_Ioo hθ) _).le
      calc ‖(f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))‖
          = (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) := by
            rw [Real.norm_eq_abs, abs_of_nonneg hnn]
        _ ≤ C ^ 2 * (Real.pi / 4) ^ (2 + Work.Spaces.eta)
              * (θ ^ (-Work.Spaces.eta) + (Real.pi / 2 - θ) ^ (-Work.Spaces.eta)) := hmaj θ hθ
  have hVint : IntegrableOn (fun θ => (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ := by
    have hcont_thη : ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      hcont_sin.rpow_const (fun θ hθ => Or.inl (hsinn θ hθ))
    refine Work.Elliptic.integrableOn_of_rpow_majorant hη.le hη1
      (by positivity : (0 : ℝ) ≤ C ^ 2 * (Real.pi / 2) ^ 2 * (Real.pi / 4) ^ Work.Spaces.eta)
      ?_ ?_
    · exact (hcont_f.pow 2).mul hcont_thη
    · intro θ hθ
      have hs : Work.FTS.EllipticEst.thEta θ
          ≤ (Real.pi / 4) ^ Work.Spaces.eta
              * (θ ^ (-Work.Spaces.eta) + (Real.pi / 2 - θ) ^ (-Work.Spaces.eta)) :=
        Work.Spaces.sin_rpow_le_majorant_pi Work.Spaces.eta θ hη (hIooIθ hθ)
      have hfa : |f θ| ≤ C * min θ (Real.pi / 2 - θ) := hfb θ (hIooIθ hθ)
      have hminl : min θ (Real.pi / 2 - θ) ≤ Real.pi / 2 :=
        le_trans (min_le_left _ _) hθ.2.le
      have hfb' : |f θ| ≤ C * (Real.pi / 2) := by
        calc |f θ| ≤ C * min θ (Real.pi / 2 - θ) := hfa
          _ ≤ C * (Real.pi / 2) := mul_le_mul_of_nonneg_left hminl hC0
      have hf2 : (f θ) ^ 2 ≤ (C * (Real.pi / 2)) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hfb' 2
      have hth_nn : 0 ≤ Work.FTS.EllipticEst.thEta θ :=
        (Real.rpow_pos_of_pos (sin_pos_of_mem_Ioo hθ) _).le
      have hnn : 0 ≤ (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ :=
        mul_nonneg (sq_nonneg _) hth_nn
      calc ‖(f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ‖
          = (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
            rw [Real.norm_eq_abs, abs_of_nonneg hnn]
        _ ≤ (C * (Real.pi / 2)) ^ 2 * Work.FTS.EllipticEst.thEta θ :=
            mul_le_mul_of_nonneg_right hf2 hth_nn
        _ ≤ (C * (Real.pi / 2)) ^ 2 * ((Real.pi / 4) ^ Work.Spaces.eta
              * (θ ^ (-Work.Spaces.eta) + (Real.pi / 2 - θ) ^ (-Work.Spaces.eta))) :=
            mul_le_mul_of_nonneg_left hs (by positivity)
        _ = C ^ 2 * (Real.pi / 2) ^ 2 * (Real.pi / 4) ^ Work.Spaces.eta
              * (θ ^ (-Work.Spaces.eta) + (Real.pi / 2 - θ) ^ (-Work.Spaces.eta)) := by ring
  -- integrability of `f² cot²(2θ) σ`, obtained from `hYint` by comparison
  have hWint : IntegrableOn (fun θ => (f θ) ^ 2 * (Real.cot (2 * θ)) ^ 2
      * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
    have hcont_cot : ContinuousOn (fun θ : ℝ => Real.cot (2 * θ))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      rw [show (fun θ : ℝ => Real.cot (2 * θ))
          = fun θ : ℝ => Real.cos (2 * θ) / Real.sin (2 * θ) from by
        funext θ; rw [Real.cot_eq_cos_div_sin]]
      exact ContinuousOn.div
        ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn)
        hcont_sin (fun θ hθ => hsinn θ hθ)
    have hcont_g : ContinuousOn (fun θ : ℝ => (f θ) ^ 2 * (Real.cot (2 * θ)) ^ 2
        * Work.FTS.EllipticEst.thEta θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      refine ContinuousOn.mul (ContinuousOn.mul (hcont_f.pow 2) (hcont_cot.pow 2)) ?_
      exact hcont_sin.rpow_const (fun θ hθ => Or.inl (hsinn θ hθ))
    have haesm : AEStronglyMeasurable (fun θ : ℝ => (f θ) ^ 2 * (Real.cot (2 * θ)) ^ 2
        * Work.FTS.EllipticEst.thEta θ) (volume.restrict Work.Spaces.Iθ) := by
      rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl]
      rw [← MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ))
        (b := Real.pi / 2))]
      exact hcont_g.aestronglyMeasurable measurableSet_Ioo
    refine hYint.mono' haesm ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    have hnn := hpt_nn θ hθ
    calc ‖(f θ) ^ 2 * (Real.cot (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ‖
        = (f θ) ^ 2 * (Real.cot (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
          rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      _ ≤ (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) := hpt θ hθ
  -- `W ≤ Y`
  have hWY : W ≤ Y := by
    rw [hWdef, hYdef]
    refine MeasureTheory.integral_mono_of_nonneg (μ := volume.restrict Work.Spaces.Iθ)
      (by filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
          exact hpt_nn θ hθ) ?_ ?_
    · exact hYint
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact hpt θ hθ
  -- the pointwise AM–GM bound
  have hAM : ∀ θ ∈ Work.Spaces.Iθ,
      |f θ * deriv f θ * Real.cot (2 * θ) * Work.FTS.EllipticEst.thEta θ|
        ≤ (1 / (2 * (1 + Work.Spaces.eta))) * ((deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          + ((1 + Work.Spaces.eta) / 2)
            * ((f θ) ^ 2 * (Real.cot (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
    intro θ hθ
    rcases eq_or_ne (Real.sin (2 * θ)) 0 with hsin | hsin
    · have hσ : Work.FTS.EllipticEst.thEta θ = 0 := by
        rw [Work.FTS.EllipticEst.thEta, hsin, Real.zero_rpow (neg_ne_zero.mpr hη.ne')]
      rw [hσ]
      simp
    · have hs : 0 < Real.sin (2 * θ) :=
        lt_of_le_of_ne (sin_nonneg_of_mem_Iθ hθ) (Ne.symm hsin)
      have hsq : Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2))
          * Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2))
          = Work.FTS.EllipticEst.thEta θ := by
        rw [← Real.rpow_add hs]
        have : -(Work.Spaces.eta / 2) + -(Work.Spaces.eta / 2) = -Work.Spaces.eta := by ring
        rw [this, Work.FTS.EllipticEst.thEta]
      set A : ℝ := deriv f θ * Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2)) with hA
      set B : ℝ := f θ * Real.cot (2 * θ) * Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2)) with hB
      have hAB : f θ * deriv f θ * Real.cot (2 * θ) * Work.FTS.EllipticEst.thEta θ = A * B := by
        rw [hA, hB, ← hsq]
        ring
      have hA2 : A ^ 2 = (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
        rw [hA, show (deriv f θ * Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2))) ^ 2
            = (deriv f θ) ^ 2 * (Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2))
              * Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2))) by ring, hsq]
      have hB2 : B ^ 2 = (f θ) ^ 2 * (Real.cot (2 * θ)) ^ 2
          * Work.FTS.EllipticEst.thEta θ := by
        rw [hB, show (f θ * Real.cot (2 * θ) * Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2))) ^ 2
            = (f θ) ^ 2 * (Real.cot (2 * θ)) ^ 2
              * (Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2))
                * Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2))) by ring, hsq]
      have hg : |f θ * deriv f θ * Real.cot (2 * θ) * Work.FTS.EllipticEst.thEta θ|
          = |A| * |B| := by
        rw [hAB, abs_mul]
      rw [hg]
      have hsq0 := sq_nonneg (|A| - (1 + Work.Spaces.eta) * |B|)
      have hpos : (0 : ℝ) < 2 * (1 + Work.Spaces.eta) := by positivity
      have h2 : 2 * (1 + Work.Spaces.eta) * (|A| * |B|) ≤ A ^ 2
          + (1 + Work.Spaces.eta) ^ 2 * B ^ 2 := by
        have hsqA : |A| ^ 2 = A ^ 2 := sq_abs A
        have hsqB : |B| ^ 2 = B ^ 2 := sq_abs B
        nlinarith [hsq0, hsqA, hsqB]
      have h3 := div_le_div_of_nonneg_right h2 hpos.le
      rw [mul_div_cancel_left₀ _ (ne_of_gt hpos)] at h3
      rw [hA2, hB2] at h3
      have h4 : ((deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
            + (1 + Work.Spaces.eta) ^ 2
              * ((f θ) ^ 2 * (Real.cot (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ))
            / (2 * (1 + Work.Spaces.eta))
          = (1 / (2 * (1 + Work.Spaces.eta)))
              * ((deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
            + ((1 + Work.Spaces.eta) / 2)
              * ((f θ) ^ 2 * (Real.cot (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
        field_simp
        try ring
      rw [h4] at h3
      exact h3
  -- the bound on `K`
  have hKbound : 2 * Work.Spaces.eta * K
      ≤ (Work.Spaces.eta / (1 + Work.Spaces.eta)) * I
        + (Work.Spaces.eta * (1 + Work.Spaces.eta)) * W := by
    have hKabs : K ≤ ∫ θ in Work.Spaces.Iθ,
        |f θ * deriv f θ * Real.cot (2 * θ) * Work.FTS.EllipticEst.thEta θ| := by
      rw [hKdef]
      calc (∫ θ in Work.Spaces.Iθ, f θ * deriv f θ * Real.cot (2 * θ)
              * Work.FTS.EllipticEst.thEta θ)
          ≤ |∫ θ in Work.Spaces.Iθ, f θ * deriv f θ * Real.cot (2 * θ)
              * Work.FTS.EllipticEst.thEta θ| := le_abs_self _
        _ ≤ _ := MeasureTheory.abs_integral_le_integral_abs
    have hsum_eq : (∫ θ in Work.Spaces.Iθ,
          ((1 / (2 * (1 + Work.Spaces.eta)))
              * ((deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
            + ((1 + Work.Spaces.eta) / 2)
              * ((f θ) ^ 2 * (Real.cot (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ)))
        = (1 / (2 * (1 + Work.Spaces.eta))) * I + ((1 + Work.Spaces.eta) / 2) * W := by
      rw [MeasureTheory.integral_add (hIint.const_mul _) (hWint.const_mul _),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, ← hIdef, ← hWdef]
    have hmono : (∫ θ in Work.Spaces.Iθ,
          |f θ * deriv f θ * Real.cot (2 * θ) * Work.FTS.EllipticEst.thEta θ|) ≤
        (1 / (2 * (1 + Work.Spaces.eta))) * I + ((1 + Work.Spaces.eta) / 2) * W := by
      rw [← hsum_eq]
      refine MeasureTheory.integral_mono_of_nonneg (μ := volume.restrict Work.Spaces.Iθ)
        (Filter.Eventually.of_forall fun θ => abs_nonneg _)
        ((hIint.const_mul _).add (hWint.const_mul _)) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact hAM θ hθ
    have hfin : K ≤ (1 / (2 * (1 + Work.Spaces.eta))) * I
        + ((1 + Work.Spaces.eta) / 2) * W := le_trans hKabs hmono
    have h2 : 2 * Work.Spaces.eta * K ≤ 2 * Work.Spaces.eta
        * ((1 / (2 * (1 + Work.Spaces.eta))) * I + ((1 + Work.Spaces.eta) / 2) * W) :=
      mul_le_mul_of_nonneg_left hfin (by positivity)
    have hrw : 2 * Work.Spaces.eta * ((1 / (2 * (1 + Work.Spaces.eta))) * I
          + ((1 + Work.Spaces.eta) / 2) * W)
        = (Work.Spaces.eta / (1 + Work.Spaces.eta)) * I
          + (Work.Spaces.eta * (1 + Work.Spaces.eta)) * W := by
      field_simp
      try ring
    rwa [hrw] at h2
  -- the sharp Hardy inequality applied to `f`
  have hconvI : (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 / Real.sin (2 * θ) ^ Work.Spaces.eta)
      = I := by
    rw [hIdef]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    exact div_eq_mul_rpow_neg (sin_nonneg_of_mem_Iθ hθ) hη
  have hconvV : (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 / Real.sin (2 * θ) ^ Work.Spaces.eta) = V := by
    rw [hVdef]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    exact div_eq_mul_rpow_neg (sin_nonneg_of_mem_Iθ hθ) hη
  have hconvY : (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 / Real.sin (2 * θ) ^ (2 + Work.Spaces.eta))
      = Y := by
    rw [hYdef]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    exact div_eq_mul_rpow_neg (sin_nonneg_of_mem_Iθ hθ) (by positivity)
  have hsubIcc : Set.Icc (0 : ℝ) (Real.pi / 2) ⊆ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) :=
    fun θ hθ => ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hHardy : Y ≤ (1 / (1 + Work.Spaces.eta) ^ 2) * I + C_H * V := by
    have h := hC_H f ((hf.mono hsubIcc).of_le (by norm_num)) hf0 hf1
    rw [hconvY, hconvI, hconvV] at h
    simpa [add_comm] using h
  -- assembling
  have h3 : (Work.Spaces.eta * (1 + Work.Spaces.eta)) * W
      ≤ (Work.Spaces.eta * (1 + Work.Spaces.eta))
        * ((1 / (1 + Work.Spaces.eta) ^ 2) * I + C_H * V) :=
    mul_le_mul_of_nonneg_left (le_trans hWY hHardy) (by positivity)
  have h4 : (Work.Spaces.eta * (1 + Work.Spaces.eta))
        * ((1 / (1 + Work.Spaces.eta) ^ 2) * I + C_H * V)
      = (Work.Spaces.eta / (1 + Work.Spaces.eta)) * I
        + (Work.Spaces.eta * (1 + Work.Spaces.eta) * C_H) * V := by
    field_simp
    try ring
  have h5 : 2 * Work.Spaces.eta * K ≤ (Work.Spaces.eta / (1 + Work.Spaces.eta)) * I
      + (Work.Spaces.eta / (1 + Work.Spaces.eta)) * I
      + (Work.Spaces.eta * (1 + Work.Spaces.eta) * C_H) * V := by
    rw [h4] at h3
    have h := hKbound
    linarith
  have h6 : I ≤ -J + (Work.Spaces.eta / (1 + Work.Spaces.eta)) * I
      + (Work.Spaces.eta / (1 + Work.Spaces.eta)) * I
      + (Work.Spaces.eta * (1 + Work.Spaces.eta) * C_H) * V := by
    have h := h5
    linarith [hAng, h]
  have h8 : I - (2 * (Work.Spaces.eta / (1 + Work.Spaces.eta))) * I
      = ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * I := by
    field_simp
    try ring
  have h7 : I - (2 * (Work.Spaces.eta / (1 + Work.Spaces.eta))) * I
      ≤ -J + (Work.Spaces.eta * (1 + Work.Spaces.eta) * C_H) * V := by
    linarith [h6]
  rw [h8] at h7
  exact h7

end Work.FTS.EllipticEst.Alpha4
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.angSliceBoundsWeak =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngAWeak

open MeasureTheory Set Filter

theorem angSliceBoundsWeak : ∀ f : ℝ → ℝ,
      ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
      ContinuousOn f (Set.Icc 0 (Real.pi / 2)) →
      f 0 = 0 → f (Real.pi / 2) = 0 →
      MeasureTheory.IntegrableOn
        (fun θ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
      ∃ C : ℝ, 0 < C ∧
        (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ C * θ) ∧
        (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ C * (Real.pi / 2 - θ)) ∧
        (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv f θ| ≤ C) := by
  intro f hsm hcont h0 hpi hint
  -- `C²` on the open interval plus the weighted square-integrability of `f''` bounds
  -- `f` and `f'` by a constant on `(0, π/2)`.
  obtain ⟨C₀, hC₀nn, hC₀⟩ :=
    Work.FTS.EllipticEst.Honest.slice_bdd_of_sq_mul_sEta hsm hint
  have hdiff : DifferentiableOn ℝ f (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hsm.differentiableOn (by norm_num)
  refine ⟨C₀ + 1, by linarith, ?_, ?_, ?_⟩
  · -- linear vanishing at `0`, by the mean value theorem on `[0, θ]`
    intro θ hθ
    obtain ⟨c, hc, hder⟩ := exists_deriv_eq_slope f hθ.1
      (hcont.mono (fun x hx => ⟨hx.1, le_trans hx.2 hθ.2.le⟩))
      (hdiff.mono (fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 hθ.2.le⟩))
    have hcI : c ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hc.1, lt_trans hc.2 hθ.2⟩
    have hthis : f θ = deriv f c * θ := by
      rw [hder, h0, sub_zero, sub_zero, div_mul_cancel₀]
      exact hθ.1.ne'
    rw [hthis, abs_mul, abs_of_pos hθ.1]
    refine mul_le_mul_of_nonneg_right ?_ hθ.1.le
    have hc' := (hC₀ c hcI).2
    linarith
  · -- linear vanishing at `π/2`, by the mean value theorem on `[θ, π/2]`
    intro θ hθ
    obtain ⟨c, hc, hder⟩ := exists_deriv_eq_slope f hθ.2
      (hcont.mono (fun x hx => ⟨le_trans hθ.1.le hx.1, hx.2⟩))
      (hdiff.mono (fun x hx => ⟨lt_trans hθ.1 hx.1, hx.2⟩))
    have hcI : c ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨lt_trans hθ.1 hc.1, hc.2⟩
    have hpos : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
    have hder2 : deriv f c = -(f θ / (Real.pi / 2 - θ)) := by
      rw [hder, hpi, zero_sub, neg_div]
    have hthis : f θ = -(deriv f c) * (Real.pi / 2 - θ) := by
      rw [hder2, neg_neg, div_mul_cancel₀]
      exact hpos.ne'
    rw [hthis, abs_mul, abs_neg, abs_of_pos hpos]
    refine mul_le_mul_of_nonneg_right ?_ hpos.le
    have hc' := (hC₀ c hcI).2
    linarith
  · -- the derivative bound
    intro θ hθ
    have hc' := (hC₀ θ hθ).2
    linarith

end Work.FTS.EllipticEst.AngAWeak
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.cosSqHardyWeakFts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngAWeak

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **The sharp same-weight Hardy inequality with the `cos²(2θ)` factor, in the weak
(open-interval) class** (the constant `1/(1+η)²` is the sharp one for the unconstrained class).
There is no extra integrability hypothesis: `D θ = (deriv f θ)² sin(2θ)^{-η}` is automatically
integrable on `Iθ = [0, π/2]` from `|deriv f θ| ≤ M` and `η < 1`.

Proof (the flux argument, all integrals honest).  The primitive
`Φ θ = f θ² cos(2θ) sin(2θ)^{-(1+η)}` has derivative `2G - 2B - 2(1+η)L` where
`G = f f' cos(2θ) sin(2θ)^{-(1+η)}`, `B = f² sin(2θ)^{-η}`, `L = f² cos²(2θ) sin(2θ)^{-(2+η)}`, and
`|Φ| ≤ M² sin(2θ)^{1-η} → 0` at both endpoints since `η < 1`; hence `∫_{Iθ}(2G-2B-2(1+η)L) = 0`
(`Work.FTS.EllipticEst.AngSecond.slice_ftc_zero`, which needs only `HasDerivAt` on `(0,π/2)`, the
interval-integrability of the derivative, and the two one-sided limits `0`).
The three integrands are dominated by `C sin(2θ)^{-η}` (for `G` and `L` use `|f| ≤ M sin 2θ` and
`|cos| ≤ 1`; for `B` use `sin ≤ 1`), hence integrable on `Iθ` by
`Work.FTS.H2.intervalIntegrable_of_sin_bound` with `p = -η > -1` — the open-interval continuity of
the integrands is lifted from `Ioo` to `Icc` with
`MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc`.  Finally the pointwise AM–GM
`|G| ≤ (ε/2)·L + (1/(2ε))·D` with `ε = 1 + η` gives `(1+η)∫L = ∫G - ∫B ≤ ∫|G| ≤ ((1+η)/2)∫L +
(1/(2(1+η)))∫D`, i.e. `∫L ≤ (1+η)^{-2} ∫D`. -/
theorem cosSqHardyWeakFts (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) :
    ∀ f : ℝ → ℝ,
      ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
      (∃ M : ℝ, 0 ≤ M ∧
        (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ M * Real.sin (2 * θ)) ∧
        (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv f θ| ≤ M)) →
      (∫ θ in Work.Spaces.Iθ,
          (f θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)))
        ≤ 1 / (1 + η) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) := by
  intro f hf hbnd
  obtain ⟨M, hM0, hMf, hMd⟩ := hbnd
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  -- (1) the pointwise derivative of the flux
  have hderiv := Work.FTS.EllipticEst.AngAWeakFts.fluxDeriv η hf
  -- (2) the four integrands are interval integrable
  obtain ⟨hIL, hIB, hIG, hID⟩ :=
    Work.FTS.EllipticEst.AngAWeakFts.fluxIntegrable η hη0 hη1 hf hM0 hMf hMd
  -- (3) the flux vanishes at both endpoints
  obtain ⟨hT0, hTπ⟩ := Work.FTS.EllipticEst.AngAWeakFts.fluxTendsto η hη0 hη1 hM0 hMf
  have hIcomb : IntervalIntegrable
      (fun θ : ℝ => 2 * hardyFtsG η f θ - 2 * hardyFtsB η f θ
        - 2 * (1 + η) * hardyFtsL η f θ) volume 0 (Real.pi / 2) :=
    ((hIG.const_mul 2).sub (hIB.const_mul 2)).sub (hIL.const_mul (2 * (1 + η)))
  -- (4) the fundamental theorem of calculus: the flux drops out
  have hftc : (∫ θ in Work.Spaces.Iθ, (2 * hardyFtsG η f θ - 2 * hardyFtsB η f θ
      - 2 * (1 + η) * hardyFtsL η f θ)) = 0 :=
    Work.FTS.EllipticEst.AngSecond.slice_ftc_zero (hardyFtsFlux η f)
      (fun θ : ℝ => 2 * hardyFtsG η f θ - 2 * hardyFtsB η f θ
        - 2 * (1 + η) * hardyFtsL η f θ) hderiv hIcomb hT0 hTπ
  -- (5) integrability over `Iθ` (transport along `Ioc =ᵐ Icc`)
  have hGI : IntegrableOn (hardyFtsG η f) Work.Spaces.Iθ volume :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hpi).mp hIG).congr_set_ae
      (MeasureTheory.Ioc_ae_eq_Icc (μ := volume)).symm
  have hBI : IntegrableOn (hardyFtsB η f) Work.Spaces.Iθ volume :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hpi).mp hIB).congr_set_ae
      (MeasureTheory.Ioc_ae_eq_Icc (μ := volume)).symm
  have hLI : IntegrableOn (hardyFtsL η f) Work.Spaces.Iθ volume :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hpi).mp hIL).congr_set_ae
      (MeasureTheory.Ioc_ae_eq_Icc (μ := volume)).symm
  have hDI : IntegrableOn (hardyFtsD η f) Work.Spaces.Iθ volume :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hpi).mp hID).congr_set_ae
      (MeasureTheory.Ioc_ae_eq_Icc (μ := volume)).symm
  -- (6) linearity of the integral:  `(1+η)∫L = ∫G - ∫B`
  have hlin : (∫ θ in Work.Spaces.Iθ, (2 * hardyFtsG η f θ - 2 * hardyFtsB η f θ
        - 2 * (1 + η) * hardyFtsL η f θ))
      = 2 * (∫ θ in Work.Spaces.Iθ, hardyFtsG η f θ)
        - 2 * (∫ θ in Work.Spaces.Iθ, hardyFtsB η f θ)
        - 2 * (1 + η) * (∫ θ in Work.Spaces.Iθ, hardyFtsL η f θ) := by
    have hBA : MeasureTheory.Integrable
        (fun θ : ℝ => 2 * hardyFtsB η f θ + 2 * (1 + η) * hardyFtsL η f θ)
        (volume.restrict Work.Spaces.Iθ) :=
      (hBI.const_mul 2).add (hLI.const_mul (2 * (1 + η)))
    have hA : (∫ θ in Work.Spaces.Iθ, (2 * hardyFtsG η f θ - 2 * hardyFtsB η f θ
          - 2 * (1 + η) * hardyFtsL η f θ))
        = ∫ θ in Work.Spaces.Iθ, (2 * hardyFtsG η f θ
            - (2 * hardyFtsB η f θ + 2 * (1 + η) * hardyFtsL η f θ)) :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
    have hB : (∫ θ in Work.Spaces.Iθ, (2 * hardyFtsG η f θ
            - (2 * hardyFtsB η f θ + 2 * (1 + η) * hardyFtsL η f θ)))
        = (∫ θ in Work.Spaces.Iθ, 2 * hardyFtsG η f θ)
          - (∫ θ in Work.Spaces.Iθ,
              (2 * hardyFtsB η f θ + 2 * (1 + η) * hardyFtsL η f θ)) :=
      MeasureTheory.integral_sub (f := fun θ : ℝ => 2 * hardyFtsG η f θ)
        (g := fun θ : ℝ => 2 * hardyFtsB η f θ + 2 * (1 + η) * hardyFtsL η f θ)
        (hGI.const_mul 2) hBA
    have hC : (∫ θ in Work.Spaces.Iθ,
          (2 * hardyFtsB η f θ + 2 * (1 + η) * hardyFtsL η f θ))
        = (∫ θ in Work.Spaces.Iθ, 2 * hardyFtsB η f θ)
          + (∫ θ in Work.Spaces.Iθ, 2 * (1 + η) * hardyFtsL η f θ) :=
      MeasureTheory.integral_add (f := fun θ : ℝ => 2 * hardyFtsB η f θ)
        (g := fun θ : ℝ => 2 * (1 + η) * hardyFtsL η f θ)
        (hBI.const_mul 2) (hLI.const_mul (2 * (1 + η)))
    have hD : (∫ θ in Work.Spaces.Iθ, 2 * hardyFtsG η f θ)
        = 2 * (∫ θ in Work.Spaces.Iθ, hardyFtsG η f θ) :=
      MeasureTheory.integral_const_mul 2 (fun θ : ℝ => hardyFtsG η f θ)
    have hE : (∫ θ in Work.Spaces.Iθ, 2 * hardyFtsB η f θ)
        = 2 * (∫ θ in Work.Spaces.Iθ, hardyFtsB η f θ) :=
      MeasureTheory.integral_const_mul 2 (fun θ : ℝ => hardyFtsB η f θ)
    have hF : (∫ θ in Work.Spaces.Iθ, 2 * (1 + η) * hardyFtsL η f θ)
        = 2 * (1 + η) * (∫ θ in Work.Spaces.Iθ, hardyFtsL η f θ) :=
      MeasureTheory.integral_const_mul (2 * (1 + η)) (fun θ : ℝ => hardyFtsL η f θ)
    rw [hA, hB, hC, hD, hE, hF]
    ring
  -- (7) the middle term is nonnegative
  have hBnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, hardyFtsB η f θ :=
    MeasureTheory.integral_nonneg_of_ae
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => show 0 ≤ (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η) from
          mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hardyFts_sin_nonneg hθ) _)))
  -- (8) the pointwise weighted AM–GM, integrated
  have hGle : (∫ θ in Work.Spaces.Iθ, hardyFtsG η f θ)
      ≤ ((1 + η) / 2) * (∫ θ in Work.Spaces.Iθ, hardyFtsL η f θ)
        + (1 / (2 * (1 + η))) * (∫ θ in Work.Spaces.Iθ, hardyFtsD η f θ) := by
    have hpt : ∀ θ ∈ Work.Spaces.Iθ,
        hardyFtsG η f θ ≤ ((1 + η) / 2) * hardyFtsL η f θ
          + (1 / (2 * (1 + η))) * hardyFtsD η f θ :=
      fun θ hθ => le_trans (le_abs_self _)
        (Work.FTS.EllipticEst.AngAWeakFts.amgmG η hη0 f θ hθ)
    have hR : MeasureTheory.Integrable
        (fun θ : ℝ => ((1 + η) / 2) * hardyFtsL η f θ
          + (1 / (2 * (1 + η))) * hardyFtsD η f θ) (volume.restrict Work.Spaces.Iθ) :=
      (hLI.const_mul ((1 + η) / 2)).add (hDI.const_mul (1 / (2 * (1 + η))))
    have hmono := MeasureTheory.integral_mono_ae hGI hR
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hpt)
    have h1 : (∫ θ in Work.Spaces.Iθ, (((1 + η) / 2) * hardyFtsL η f θ
          + (1 / (2 * (1 + η))) * hardyFtsD η f θ))
        = (∫ θ in Work.Spaces.Iθ, ((1 + η) / 2) * hardyFtsL η f θ)
          + (∫ θ in Work.Spaces.Iθ, (1 / (2 * (1 + η))) * hardyFtsD η f θ) :=
      MeasureTheory.integral_add (f := fun θ : ℝ => ((1 + η) / 2) * hardyFtsL η f θ)
        (g := fun θ : ℝ => (1 / (2 * (1 + η))) * hardyFtsD η f θ)
        (hLI.const_mul ((1 + η) / 2)) (hDI.const_mul (1 / (2 * (1 + η))))
    have h2 : (∫ θ in Work.Spaces.Iθ, ((1 + η) / 2) * hardyFtsL η f θ)
        = ((1 + η) / 2) * (∫ θ in Work.Spaces.Iθ, hardyFtsL η f θ) :=
      MeasureTheory.integral_const_mul ((1 + η) / 2) (fun θ : ℝ => hardyFtsL η f θ)
    have h3 : (∫ θ in Work.Spaces.Iθ, (1 / (2 * (1 + η))) * hardyFtsD η f θ)
        = (1 / (2 * (1 + η))) * (∫ θ in Work.Spaces.Iθ, hardyFtsD η f θ) :=
      MeasureTheory.integral_const_mul (1 / (2 * (1 + η))) (fun θ : ℝ => hardyFtsD η f θ)
    rw [h1, h2, h3] at hmono
    exact hmono
  -- (9) the arithmetic:  `(1+η)∫L ≤ ((1+η)/2)∫L + (1/(2(1+η)))∫D`
  have hkey : (1 + η) * (∫ θ in Work.Spaces.Iθ, hardyFtsL η f θ)
      ≤ ((1 + η) / 2) * (∫ θ in Work.Spaces.Iθ, hardyFtsL η f θ)
        + (1 / (2 * (1 + η))) * (∫ θ in Work.Spaces.Iθ, hardyFtsD η f θ) := by
    have h1 : (1 + η) * (∫ θ in Work.Spaces.Iθ, hardyFtsL η f θ)
        = (∫ θ in Work.Spaces.Iθ, hardyFtsG η f θ)
          - (∫ θ in Work.Spaces.Iθ, hardyFtsB η f θ) := by
      linarith [hftc, hlin]
    linarith [h1, hBnn, hGle]
  have hne : ((1 + η) ^ 2) ≠ 0 := by positivity
  have hstep : (1 + η) / 2 * (∫ θ in Work.Spaces.Iθ, hardyFtsL η f θ)
      ≤ 1 / (2 * (1 + η)) * (∫ θ in Work.Spaces.Iθ, hardyFtsD η f θ) := by
    linarith [hkey]
  have h2 : (2 * (1 + η)) * ((1 + η) / 2 * (∫ θ in Work.Spaces.Iθ, hardyFtsL η f θ))
      ≤ (2 * (1 + η)) * (1 / (2 * (1 + η)) * (∫ θ in Work.Spaces.Iθ, hardyFtsD η f θ)) :=
    mul_le_mul_of_nonneg_left hstep (by positivity)
  have e1 : (2 * (1 + η)) * ((1 + η) / 2 * (∫ θ in Work.Spaces.Iθ, hardyFtsL η f θ))
      = (1 + η) ^ 2 * (∫ θ in Work.Spaces.Iθ, hardyFtsL η f θ) := by ring
  have e2 : (2 * (1 + η)) * (1 / (2 * (1 + η)) * (∫ θ in Work.Spaces.Iθ, hardyFtsD η f θ))
      = (∫ θ in Work.Spaces.Iθ, hardyFtsD η f θ) := by
    rw [one_div, ← mul_assoc, mul_inv_cancel₀ (by positivity : (2 * (1 + η)) ≠ 0), one_mul]
  rw [e1, e2] at h2
  have e3 : (1 / (1 + η) ^ 2) * ((1 + η) ^ 2 * (∫ θ in Work.Spaces.Iθ, hardyFtsL η f θ))
      = (∫ θ in Work.Spaces.Iθ, hardyFtsL η f θ) := by
    rw [← mul_assoc, one_div, inv_mul_cancel₀ hne, one_mul]
  have h3 := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 1 / (1 + η) ^ 2 by positivity)
  rwa [e3] at h3

end

end Work.FTS.EllipticEst.AngAWeak
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.sliceIbpSigmaWeakFts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The angular weight and its first two derivatives on `(0, π/2)` -/

/-- The angular weight `σ θ = sin(2θ)^{-η}`. -/
abbrev sigE (η θ : ℝ) : ℝ := Real.sin (2 * θ) ^ (-η)

/-- The derivative of `σ` on the open interval: `σ' = -2η cos(2θ) sin(2θ)^{-(1+η)}`. -/
abbrev sigD (η θ : ℝ) : ℝ := -2 * η * Real.cos (2 * θ) * Real.sin (2 * θ) ^ (-(1 + η))

/-- The second derivative of `σ` on the open interval. -/
abbrev sigDD (η θ : ℝ) : ℝ :=
  4 * η * Real.sin (2 * θ) ^ (-η)
    + 4 * η * (1 + η) * Real.cos (2 * θ) ^ 2 * Real.sin (2 * θ) ^ (-(2 + η))

@[simp] theorem sigE_apply (η θ : ℝ) : sigE η θ = Real.sin (2 * θ) ^ (-η) := rfl

@[simp] theorem sigD_apply (η θ : ℝ) :
    sigD η θ = -2 * η * Real.cos (2 * θ) * Real.sin (2 * θ) ^ (-(1 + η)) := rfl

@[simp] theorem sigDD_apply (η θ : ℝ) :
    sigDD η θ = 4 * η * Real.sin (2 * θ) ^ (-η)
      + 4 * η * (1 + η) * Real.cos (2 * θ) ^ 2 * Real.sin (2 * θ) ^ (-(2 + η)) := rfl

/-! ## Derivatives of `σ` and `σ'` -/

/-- `σ` is differentiable on `(0, π/2)` with derivative `σ'`. -/
theorem sigE_hasDerivAt_weak (η : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt (fun t : ℝ => sigE η t) (sigD η θ) θ := by
  have hspos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hlin : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ := hlin.sin
  have hpow := hsin.rpow_const (p := -η) (Or.inl (ne_of_gt hspos))
  have hval : (Real.cos (2 * θ) * 2) * (-η) * Real.sin (2 * θ) ^ (-η - 1) = sigD η θ := by
    rw [sigD_apply]
    have h_exp : -η - 1 = -(1 + η) := by ring
    rw [h_exp]
    ring
  exact hpow.congr_deriv hval

/-- `σ'` is differentiable on `(0, π/2)` with derivative `σ''`. -/
theorem sigD_hasDerivAt_weak (η : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt (fun t : ℝ => sigD η t) (sigDD η θ) θ := by
  have hspos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hlin : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ := hlin.sin
  have hcos : HasDerivAt (fun t : ℝ => Real.cos (2 * t)) (-Real.sin (2 * θ) * 2) θ := hlin.cos
  have hpow : HasDerivAt (fun t : ℝ => Real.sin (2 * t) ^ (-(1 + η)))
      ((Real.cos (2 * θ) * 2) * (-(1 + η)) * Real.sin (2 * θ) ^ (-(1 + η) - 1)) θ :=
    hsin.rpow_const (Or.inl (ne_of_gt hspos))
  have hprod := (hcos.mul hpow).const_mul (-2 * η)
  have hfun : (fun t : ℝ => sigD η t)
      = fun y => -2 * η * (((fun t : ℝ => Real.cos (2 * t))
          * fun t : ℝ => Real.sin (2 * t) ^ (-(1 + η))) y) := by
    funext y
    simp only [Pi.mul_apply, sigD_apply]
    ring
  rw [hfun]
  refine hprod.congr_deriv ?_
  simp only [sigDD_apply]
  have h2 : Real.sin (2 * θ) ^ (-(1 + η) - 1) = Real.sin (2 * θ) ^ (-(2 + η)) := by
    congr 1
    ring
  have h1 : Real.sin (2 * θ) ^ (-(1 + η))
      = Real.sin (2 * θ) ^ (-η) / Real.sin (2 * θ) := by
    rw [eq_div_iff hspos.ne', ← Real.rpow_add_one hspos.ne']
    congr 1
    ring
  rw [h1, h2]
  field_simp
  ring

/-- The absolute value of `σ'` on `(0, π/2)`. -/
theorem abs_sigD_le (η : ℝ) (hη0 : 0 ≤ η) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |sigD η θ| ≤ 2 * η * Real.sin (2 * θ) ^ (-(1 + η)) := by
  have hspos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hcos : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
  have ht : (0 : ℝ) ≤ Real.sin (2 * θ) ^ (-(1 + η)) := Real.rpow_nonneg hspos.le _
  rw [sigD_apply, abs_mul, abs_mul, abs_mul,
    show |(-2 : ℝ)| = 2 by norm_num, abs_of_nonneg hη0, abs_of_nonneg ht]
  calc 2 * η * |Real.cos (2 * θ)| * Real.sin (2 * θ) ^ (-(1 + η))
      ≤ 2 * η * 1 * Real.sin (2 * θ) ^ (-(1 + η)) := by
        refine mul_le_mul_of_nonneg_right ?_ ht
        exact mul_le_mul_of_nonneg_left hcos (by positivity)
    _ = 2 * η * Real.sin (2 * θ) ^ (-(1 + η)) := by ring

/-! ## An elementary one-sided squeeze -/

theorem tendsto_zero_of_eventually_le {f g : ℝ → ℝ} {l : Filter ℝ}
    (hf : ∀ᶠ t in l, 0 ≤ f t) (hfg : ∀ᶠ t in l, f t ≤ g t) (hg : Tendsto g l (nhds 0)) :
    Tendsto f l (nhds 0) := by
  rw [tendsto_order]
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards [hf] with t ht
    linarith
  · have h := (tendsto_order.mp hg).2 b hb
    filter_upwards [h, hfg] with t ht hle
    linarith

/-! ## Integrability of the six pieces of the two integrations by parts -/

/-- All the integrands appearing in the two integrations by parts are integrable on `Iθ`, under
the weak hypotheses `|f| ≤ M sin(2θ)`, `|f'| ≤ M` on the *open* interval and the integrability
of `(f'')² σ`. -/
theorem weak_integrands_integrable (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) (f : ℝ → ℝ)
    (M : ℝ) (hM : 0 ≤ M)
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hfb : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |f θ| ≤ M * Real.sin (2 * θ))
    (hdb : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv f θ| ≤ M)
    (hint : IntegrableOn
      (fun θ => (deriv (deriv f) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) Work.Spaces.Iθ) :
    IntegrableOn (fun θ => deriv f θ ^ 2 * sigE η θ) Work.Spaces.Iθ
      ∧ IntegrableOn (fun θ => f θ * deriv (deriv f) θ * sigE η θ) Work.Spaces.Iθ
      ∧ IntegrableOn (fun θ => f θ * deriv f θ * sigD η θ) Work.Spaces.Iθ
      ∧ IntegrableOn (fun θ => f θ ^ 2 * sigE η θ) Work.Spaces.Iθ
      ∧ IntegrableOn (fun θ => f θ ^ 2 * Real.cos (2 * θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(2 + η))) Work.Spaces.Iθ
      ∧ IntegrableOn (fun θ => f θ ^ 2 * sigDD η θ) Work.Spaces.Iθ := by
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by positivity
  have hres : volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2)).symm
  have hsin_pos : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hsig_int : Integrable (fun θ : ℝ => sigE η θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    rw [← hres]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hpi2.le).mp
      (Work.FTS.H2.intervalIntegrable_sin_rpow (-η) (by linarith))
  have hint' : Integrable (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * sigE η θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    rw [← hres]
    exact hint
  have hf_aesm : AEStronglyMeasurable f (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hf.continuousOn.aestronglyMeasurable measurableSet_Ioo
  have hfd_aesm : AEStronglyMeasurable (deriv f)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (measurable_deriv f).aestronglyMeasurable
  have hfdd_aesm : AEStronglyMeasurable (deriv (deriv f))
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (measurable_deriv (deriv f)).aestronglyMeasurable
  have hsig_cont : ContinuousOn (fun θ : ℝ => sigE η θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
      (fun θ hθ => Or.inl (ne_of_gt (hsin_pos θ hθ)))
  have hsig_aesm : AEStronglyMeasurable (fun θ : ℝ => sigE η θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hsig_cont.aestronglyMeasurable measurableSet_Ioo
  have hcos2_aesm : AEStronglyMeasurable (fun θ : ℝ => Real.cos (2 * θ) ^ 2)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (((Real.continuous_cos.comp (continuous_const.mul continuous_id)).pow 2).continuousOn
      ).aestronglyMeasurable measurableSet_Ioo
  have hsinD_cont : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ) ^ (-(1 + η)))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
      (fun θ hθ => Or.inl (ne_of_gt (hsin_pos θ hθ)))
  have hsin2_aesm : AEStronglyMeasurable (fun θ : ℝ => Real.sin (2 * θ) ^ (-(2 + η)))
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
      (fun θ hθ => Or.inl (ne_of_gt (hsin_pos θ hθ)))).aestronglyMeasurable measurableSet_Ioo
  have hsigD_aesm : AEStronglyMeasurable (fun θ : ℝ => sigD η θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    change AEStronglyMeasurable
      (fun θ : ℝ => -2 * η * Real.cos (2 * θ) * Real.sin (2 * θ) ^ (-(1 + η))) _
    have hcos_cont : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
    have hmain : AEStronglyMeasurable
        (fun θ : ℝ => -2 * η * (Real.cos (2 * θ) * Real.sin (2 * θ) ^ (-(1 + η))))
        (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
      ((hcos_cont.mul hsinD_cont).const_mul (-2 * η)).aestronglyMeasurable measurableSet_Ioo
    simpa only [mul_assoc] using hmain
  have h1 : IntegrableOn (fun θ : ℝ => deriv f θ ^ 2 * sigE η θ) Work.Spaces.Iθ := by
    rw [MeasureTheory.IntegrableOn, hres]
    refine MeasureTheory.Integrable.mono' (hsig_int.const_mul (M ^ 2)) ?_ ?_
    · exact (hfd_aesm.pow 2).mul hsig_aesm
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      have hσ : (0 : ℝ) ≤ sigE η θ := Real.rpow_nonneg (hsin_pos θ hθ).le _
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (deriv f θ)), abs_of_nonneg hσ]
      have hfd : |deriv f θ| ≤ M := hdb θ hθ
      have h2 : deriv f θ ^ 2 ≤ M ^ 2 := by
        calc deriv f θ ^ 2 = |deriv f θ| ^ 2 := (sq_abs _).symm
          _ ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hfd 2
      exact mul_le_mul_of_nonneg_right h2 hσ
  have h2i : IntegrableOn (fun θ : ℝ => f θ * deriv (deriv f) θ * sigE η θ) Work.Spaces.Iθ := by
    rw [MeasureTheory.IntegrableOn, hres]
    have hmaj : Integrable
        (fun θ : ℝ => (1 / 2) * (M ^ 2 * sigE η θ + (deriv (deriv f) θ) ^ 2 * sigE η θ))
        (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
      ((hsig_int.const_mul (M ^ 2)).add hint').const_mul (1 / 2)
    refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
    · exact (hf_aesm.mul hfdd_aesm).mul hsig_aesm
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      have hσ : (0 : ℝ) ≤ sigE η θ := Real.rpow_nonneg (hsin_pos θ hθ).le _
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hσ]
      have hspos := hsin_pos θ hθ
      have ha : |f θ| ≤ M * Real.sin (2 * θ) := hfb θ hθ
      have haM : |f θ| ≤ M := by
        have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
        nlinarith [ha, hsin1, hM, hspos]
      have hamgm : 2 * (|f θ| * |deriv (deriv f) θ|) ≤ M ^ 2 + deriv (deriv f) θ ^ 2 := by
        have hA : 2 * (|f θ| * |deriv (deriv f) θ|)
            ≤ |f θ| ^ 2 + |deriv (deriv f) θ| ^ 2 := by
          nlinarith [sq_nonneg (|f θ| - |deriv (deriv f) θ|)]
        have hB : |f θ| ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) haM 2
        have hC : |deriv (deriv f) θ| ^ 2 = deriv (deriv f) θ ^ 2 := sq_abs _
        linarith [hA, hB, hC]
      have hle : |f θ| * |deriv (deriv f) θ| ≤ (M ^ 2 + deriv (deriv f) θ ^ 2) / 2 := by
        linarith
      calc |f θ| * |deriv (deriv f) θ| * sigE η θ
          = (|f θ| * |deriv (deriv f) θ|) * sigE η θ := by ring
        _ ≤ ((M ^ 2 + deriv (deriv f) θ ^ 2) / 2) * sigE η θ :=
            mul_le_mul_of_nonneg_right hle hσ
        _ = (1 / 2) * (M ^ 2 * sigE η θ + (deriv (deriv f) θ) ^ 2 * sigE η θ) := by ring
  have h3i : IntegrableOn (fun θ : ℝ => f θ * deriv f θ * sigD η θ) Work.Spaces.Iθ := by
    rw [MeasureTheory.IntegrableOn, hres]
    refine MeasureTheory.Integrable.mono' (hsig_int.const_mul (2 * η * M ^ 2)) ?_ ?_
    · exact (hf_aesm.mul hfd_aesm).mul hsigD_aesm
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      have hspos := hsin_pos θ hθ
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have ha : |f θ| ≤ M * Real.sin (2 * θ) := hfb θ hθ
      have hb : |deriv f θ| ≤ M := hdb θ hθ
      have hsd : |sigD η θ| ≤ 2 * η * Real.sin (2 * θ) ^ (-(1 + η)) := abs_sigD_le η hη0 hθ
      have ht : (0 : ℝ) ≤ Real.sin (2 * θ) ^ (-(1 + η)) := Real.rpow_nonneg hspos.le _
      have hA : |f θ| * |deriv f θ| ≤ (M * Real.sin (2 * θ)) * M :=
        mul_le_mul ha hb (abs_nonneg _) (mul_nonneg hM hspos.le)
      have h2 : |f θ| * |deriv f θ| * |sigD η θ|
          ≤ ((M * Real.sin (2 * θ)) * M) * (2 * η * Real.sin (2 * θ) ^ (-(1 + η))) :=
        mul_le_mul hA hsd (abs_nonneg _) (mul_nonneg (mul_nonneg hM hspos.le) hM)
      refine le_trans h2 ?_
      have h3 : Real.sin (2 * θ) * Real.sin (2 * θ) ^ (-(1 + η))
          = Real.sin (2 * θ) ^ (-η) := by
        rw [mul_comm, ← Real.rpow_add_one hspos.ne' (-(1 + η))]
        congr 1
        ring
      exact le_of_eq (by
        rw [sigE_apply]
        calc ((M * Real.sin (2 * θ)) * M) * (2 * η * Real.sin (2 * θ) ^ (-(1 + η)))
            = 2 * η * M ^ 2 * (Real.sin (2 * θ) * Real.sin (2 * θ) ^ (-(1 + η))) := by ring
          _ = 2 * η * M ^ 2 * Real.sin (2 * θ) ^ (-η) := by rw [h3])
  have h4 : IntegrableOn (fun θ : ℝ => f θ ^ 2 * sigE η θ) Work.Spaces.Iθ := by
    rw [MeasureTheory.IntegrableOn, hres]
    refine MeasureTheory.Integrable.mono' (hsig_int.const_mul (M ^ 2)) ?_ ?_
    · exact (hf_aesm.pow 2).mul hsig_aesm
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      have hspos := hsin_pos θ hθ
      have hσ : (0 : ℝ) ≤ sigE η θ := Real.rpow_nonneg hspos.le _
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (f θ)), abs_of_nonneg hσ]
      have ha : |f θ| ≤ M * Real.sin (2 * θ) := hfb θ hθ
      have haM : |f θ| ≤ M := by
        have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
        nlinarith [ha, hsin1, hM, hspos]
      have hf2 : f θ ^ 2 ≤ M ^ 2 := by
        calc f θ ^ 2 = |f θ| ^ 2 := (sq_abs _).symm
          _ ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) haM 2
      exact mul_le_mul_of_nonneg_right hf2 hσ
  have h5 : IntegrableOn (fun θ : ℝ => f θ ^ 2 * Real.cos (2 * θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(2 + η))) Work.Spaces.Iθ := by
    rw [MeasureTheory.IntegrableOn, hres]
    refine MeasureTheory.Integrable.mono' (hsig_int.const_mul (M ^ 2)) ?_ ?_
    · exact ((hf_aesm.pow 2).mul hcos2_aesm).mul hsin2_aesm
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      have hspos := hsin_pos θ hθ
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (f θ)),
        abs_of_nonneg (sq_nonneg (Real.cos (2 * θ))),
        abs_of_nonneg (Real.rpow_nonneg hspos.le _)]
      have hc : Real.cos (2 * θ) ^ 2 ≤ 1 := by
        have h := Real.abs_cos_le_one (2 * θ)
        nlinarith [abs_nonneg (Real.cos (2 * θ)), sq_abs (Real.cos (2 * θ)), h]
      have hf2 : f θ ^ 2 ≤ (M * Real.sin (2 * θ)) ^ 2 := by
        have ha : |f θ| ≤ M * Real.sin (2 * θ) := hfb θ hθ
        calc f θ ^ 2 = |f θ| ^ 2 := (sq_abs _).symm
          _ ≤ (M * Real.sin (2 * θ)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) ha 2
      have h3 : Real.sin (2 * θ) ^ 2 * Real.sin (2 * θ) ^ (-(2 + η))
          = Real.sin (2 * θ) ^ (-η) := by
        have h4' : Real.sin (2 * θ) ^ 2 = Real.sin (2 * θ) ^ (2 : ℝ) :=
          (Real.rpow_natCast (Real.sin (2 * θ)) 2).symm
        rw [h4', ← Real.rpow_add hspos]
        congr 1
        ring
      calc f θ ^ 2 * Real.cos (2 * θ) ^ 2 * Real.sin (2 * θ) ^ (-(2 + η))
          ≤ (M * Real.sin (2 * θ)) ^ 2 * 1 * Real.sin (2 * θ) ^ (-(2 + η)) := by
            refine mul_le_mul (mul_le_mul hf2 hc (sq_nonneg _) (sq_nonneg _)) (le_refl _)
              (Real.rpow_nonneg hspos.le _) (mul_nonneg (sq_nonneg _) zero_le_one)
        _ = M ^ 2 * (Real.sin (2 * θ) ^ 2 * Real.sin (2 * θ) ^ (-(2 + η))) := by ring
        _ = M ^ 2 * sigE η θ := by rw [h3, sigE_apply]
  have h6 : IntegrableOn (fun θ : ℝ => f θ ^ 2 * sigDD η θ) Work.Spaces.Iθ := by
    have hsum : Integrable (fun θ : ℝ => 4 * η * (f θ ^ 2 * sigE η θ)
        + 4 * η * (1 + η) * (f θ ^ 2 * Real.cos (2 * θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(2 + η)))) (volume.restrict Work.Spaces.Iθ) :=
      (MeasureTheory.Integrable.const_mul h4 (4 * η)).add
        (MeasureTheory.Integrable.const_mul h5 (4 * η * (1 + η)))
    refine hsum.congr (Filter.Eventually.of_forall (fun θ => ?_))
    simp only [sigDD_apply, sigE_apply]
    ring
  exact ⟨h1, h2i, h3i, h4, h5, h6⟩

/-! ## Vanishing of the two fluxes at both endpoints -/

/-- The two fluxes `f f' σ` and `f² σ'` vanish at `θ → 0⁺` and `θ → (π/2)⁻`, from the
bounds `|f θ| ≤ M sin(2θ)` and `|f' θ| ≤ M` on the open interval. -/
theorem weak_boundary_tendsto (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) (f : ℝ → ℝ) (M : ℝ)
    (hM : 0 ≤ M)
    (hfb : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |f θ| ≤ M * Real.sin (2 * θ))
    (hdb : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv f θ| ≤ M) :
    Tendsto (fun θ => f θ * deriv f θ * sigE η θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)
      ∧ Tendsto (fun θ => f θ * deriv f θ * sigE η θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)
      ∧ Tendsto (fun θ => f θ ^ 2 * sigD η θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)
      ∧ Tendsto (fun θ => f θ ^ 2 * sigD η θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by positivity
  have h4 : (0 : ℝ) < Real.pi / 4 := by positivity
  have hη1' : (0 : ℝ) < 1 - η := by linarith
  have hmem0 : Set.Ioo (0 : ℝ) (Real.pi / 4) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    rw [← nhdsWithin_Ioo_eq_nhdsGT h4]
    exact self_mem_nhdsWithin
  have hmemπ : Set.Ioo (Real.pi / 4) (Real.pi / 2)
      ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) := by
    rw [← nhdsWithin_Ioo_eq_nhdsLT (by linarith : Real.pi / 4 < Real.pi / 2)]
    exact self_mem_nhdsWithin
  -- pointwise estimates on the open interval
  have key1 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |f θ * deriv f θ * sigE η θ| ≤ M ^ 2 * Real.sin (2 * θ) ^ (1 - η) := by
    intro θ hθ
    have hspos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hspos.le (-η))]
    have ha : |f θ| ≤ M * Real.sin (2 * θ) := hfb θ hθ
    have hb : |deriv f θ| ≤ M := hdb θ hθ
    have h3 : Real.sin (2 * θ) * Real.sin (2 * θ) ^ (-η) = Real.sin (2 * θ) ^ (1 - η) := by
      rw [mul_comm, ← Real.rpow_add_one hspos.ne' (-η)]
      congr 1
      ring
    have hA : (|f θ| * |deriv f θ|) * Real.sin (2 * θ) ^ (-η)
        ≤ ((M * Real.sin (2 * θ)) * M) * Real.sin (2 * θ) ^ (-η) :=
      mul_le_mul_of_nonneg_right (mul_le_mul ha hb (abs_nonneg _) (mul_nonneg hM hspos.le))
        (Real.rpow_nonneg hspos.le _)
    refine le_trans hA ?_
    exact le_of_eq (by
      calc ((M * Real.sin (2 * θ)) * M) * Real.sin (2 * θ) ^ (-η)
          = M ^ 2 * (Real.sin (2 * θ) * Real.sin (2 * θ) ^ (-η)) := by ring
        _ = M ^ 2 * Real.sin (2 * θ) ^ (1 - η) := by rw [h3])
  have key2 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |f θ ^ 2 * sigD η θ| ≤ 2 * η * M ^ 2 * Real.sin (2 * θ) ^ (1 - η) := by
    intro θ hθ
    have hspos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    rw [abs_mul, abs_of_nonneg (sq_nonneg (f θ))]
    have hf2 : f θ ^ 2 ≤ (M * Real.sin (2 * θ)) ^ 2 := by
      have ha : |f θ| ≤ M * Real.sin (2 * θ) := hfb θ hθ
      calc f θ ^ 2 = |f θ| ^ 2 := (sq_abs _).symm
        _ ≤ (M * Real.sin (2 * θ)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) ha 2
    have hsd : |sigD η θ| ≤ 2 * η * Real.sin (2 * θ) ^ (-(1 + η)) := abs_sigD_le η hη0 hθ
    have hA : f θ ^ 2 * |sigD η θ|
        ≤ (M * Real.sin (2 * θ)) ^ 2 * (2 * η * Real.sin (2 * θ) ^ (-(1 + η))) :=
      mul_le_mul hf2 hsd (abs_nonneg _) (sq_nonneg _)
    refine le_trans hA ?_
    have hp : Real.sin (2 * θ) ^ (1 - η)
        = Real.sin (2 * θ) ^ (-(1 + η)) * Real.sin (2 * θ) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hspos]
      congr 1
      ring
    exact le_of_eq (by
      calc (M * Real.sin (2 * θ)) ^ 2 * (2 * η * Real.sin (2 * θ) ^ (-(1 + η)))
          = 2 * η * M ^ 2
              * (Real.sin (2 * θ) ^ (-(1 + η)) * Real.sin (2 * θ) ^ 2) := by ring
        _ = 2 * η * M ^ 2 * Real.sin (2 * θ) ^ (1 - η) := by rw [← hp])
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_zero_of_eventually_le (g := fun θ : ℝ => M ^ 2 * Real.sin (2 * θ) ^ (1 - η))
      (Filter.Eventually.of_forall (fun t => norm_nonneg _)) ?_ ?_
    · filter_upwards [hmem0] with θ hθ
      have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
      simpa only [Real.norm_eq_abs] using key1 θ hθI
    · have h := (Work.FTS.H2.tendsto_sin_rpow_zero_right (1 - η) hη1').const_mul (M ^ 2)
      simpa using h
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_zero_of_eventually_le (g := fun θ : ℝ => M ^ 2 * Real.sin (2 * θ) ^ (1 - η))
      (Filter.Eventually.of_forall (fun t => norm_nonneg _)) ?_ ?_
    · filter_upwards [hmemπ] with θ hθ
      have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
      simpa only [Real.norm_eq_abs] using key1 θ hθI
    · have h := (Work.FTS.H2.tendsto_sin_rpow_zero_left (1 - η) hη1').const_mul (M ^ 2)
      simpa using h
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_zero_of_eventually_le
      (g := fun θ : ℝ => 2 * η * M ^ 2 * Real.sin (2 * θ) ^ (1 - η))
      (Filter.Eventually.of_forall (fun t => norm_nonneg _)) ?_ ?_
    · filter_upwards [hmem0] with θ hθ
      have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
      simpa only [Real.norm_eq_abs] using key2 θ hθI
    · have h := (Work.FTS.H2.tendsto_sin_rpow_zero_right (1 - η) hη1').const_mul (2 * η * M ^ 2)
      simpa using h
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_zero_of_eventually_le
      (g := fun θ : ℝ => 2 * η * M ^ 2 * Real.sin (2 * θ) ^ (1 - η))
      (Filter.Eventually.of_forall (fun t => norm_nonneg _)) ?_ ?_
    · filter_upwards [hmemπ] with θ hθ
      have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
      simpa only [Real.norm_eq_abs] using key2 θ hθI
    · have h := (Work.FTS.H2.tendsto_sin_rpow_zero_left (1 - η) hη1').const_mul (2 * η * M ^ 2)
      simpa using h

/-- **The two integrations by parts for a weak `C²` angular slice, combined into one identity.**

For `0 ≤ η < 1`, `f` of class `C²` on the open interval `(0, π/2)`, `M ≥ 0` with
`|f θ| ≤ M sin(2θ)` and `|deriv f θ| ≤ M` on `(0, π/2)`, and `(f'')² sin(2θ)^{-η}` integrable on
`Iθ = [0, π/2]`:

  `∫_{Iθ} (f')² σ = -∫_{Iθ} f f'' σ + 2η ∫_{Iθ} f² σ + 2η(1+η) ∫_{Iθ} f² cos²(2θ) sin(2θ)^{-(2+η)}`,
  `σ = sin(2θ)^{-η}`.

Route (this is the weak-class version of the *proved* `Work.FTS.EllipticEst.remov.slice_ibp_sigma_fts`,
which does exactly this for `f` of class `C²` on the *closed* interval with `f 0 = f (π/2) = 0`;
that file's `sigD_hasDerivAt_fts` is the model for the derivative of `σ`).  Two fluxes:
`Φ₁ = f f' σ` (so `Φ₁' = (f')²σ + f f''σ + f f' σ'`) and `Φ₂ = f² σ'` (so `Φ₂' = 2 f f' σ' + f² σ''`);
`Work.FTS.EllipticEst.AngSecond.slice_ftc_zero` applied to each gives `∫Φ₁' = 0`, `∫Φ₂' = 0`;
substituting the second into the first and expanding
`σ'' = 4η σ + 4η(1+η) cos²(2θ) sin(2θ)^{-(2+η)}` gives the identity.  All boundary terms vanish
because `|Φ₁| ≤ M² sin(2θ)^{1-η}` and `|Φ₂| ≤ 2η M² sin(2θ)^{1-η}`, and the integrands of the two
derivatives are integrable: `(f')²σ ≤ M²σ`, `f f' σ' ≤ 2ηM²σ`, `f²σ ≤ M² sin(2θ)^{2-η}`, and
`∫|f f''|σ < ∞` by Cauchy–Schwarz against the hypothesis, with
`Work.FTS.H2.intervalIntegrable_of_sin_bound` with `p = -η > -1` together with
`MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc` to pass from the
open-interval continuity to `Iθ`. -/
theorem sliceIbpSigmaWeakFts (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) (f : ℝ → ℝ) (M : ℝ)
    (hM : 0 ≤ M)
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hfb : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |f θ| ≤ M * Real.sin (2 * θ))
    (hdb : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv f θ| ≤ M)
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv f) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      = -(∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * (Real.sin (2 * θ)) ^ (-η))
        + 2 * η * (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η))
        + 2 * η * (1 + η) * (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * Real.cos (2 * θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(2 + η))) := by
  suffices key : (∫ θ in Work.Spaces.Iθ, deriv f θ ^ 2 * sigE η θ)
      = -(∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * sigE η θ)
        + 2 * η * (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * sigE η θ)
        + 2 * η * (1 + η) * (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * Real.cos (2 * θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(2 + η))) by
    simpa only [sigE_apply] using key
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by positivity
  obtain ⟨hI1, hI2, hI3, hI4, hI5, hI6⟩ :=
    weak_integrands_integrable η hη0 hη1 f M hM hf hfb hdb hint
  obtain ⟨hb1, hb2, hb3, hb4⟩ := weak_boundary_tendsto η hη0 hη1 f M hM hfb hdb
  -- `f` is `C²` at interior points, so its first and second derivatives exist there.
  have hcd : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ContDiffAt ℝ 2 f θ := by
    intro θ hθ
    exact (hf θ hθ).contDiffAt (Ioo_mem_nhds hθ.1 hθ.2)
  have hdf : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt f (deriv f θ) θ := fun θ hθ =>
    ((hcd θ hθ).differentiableAt (by norm_num)).hasDerivAt
  have hddf : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (deriv f) (deriv (deriv f) θ) θ := fun θ hθ =>
    (((hcd θ hθ).derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  -- The first integration by parts.
  have hA_deriv : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun t : ℝ => f t * deriv f t * sigE η t)
        (deriv f θ ^ 2 * sigE η θ + f θ * deriv (deriv f) θ * sigE η θ
          + f θ * deriv f θ * sigD η θ) θ := by
    intro θ hθ
    have h := ((hdf θ hθ).mul (hddf θ hθ)).mul (sigE_hasDerivAt_weak η hθ)
    refine h.congr_deriv ?_
    simp only [Pi.mul_apply]
    ring
  have hA_int : IntervalIntegrable (fun θ : ℝ => deriv f θ ^ 2 * sigE η θ
      + f θ * deriv (deriv f) θ * sigE η θ + f θ * deriv f θ * sigD η θ)
      MeasureTheory.volume 0 (Real.pi / 2) := by
    have h : IntegrableOn (fun θ : ℝ => deriv f θ ^ 2 * sigE η θ
        + f θ * deriv (deriv f) θ * sigE η θ + f θ * deriv f θ * sigD η θ)
        Work.Spaces.Iθ := (hI1.add hI2).add hI3
    rw [Work.Spaces.Iθ] at h
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hpi2.le).mpr h
  have hA_zero : (∫ θ in Work.Spaces.Iθ, deriv f θ ^ 2 * sigE η θ
      + f θ * deriv (deriv f) θ * sigE η θ + f θ * deriv f θ * sigD η θ) = 0 :=
    Work.FTS.EllipticEst.AngSecond.slice_ftc_zero
      (fun t : ℝ => f t * deriv f t * sigE η t)
      (fun θ : ℝ => deriv f θ ^ 2 * sigE η θ + f θ * deriv (deriv f) θ * sigE η θ
        + f θ * deriv f θ * sigD η θ) hA_deriv hA_int hb1 hb2
  have hA_split : (∫ θ in Work.Spaces.Iθ, deriv f θ ^ 2 * sigE η θ
        + f θ * deriv (deriv f) θ * sigE η θ + f θ * deriv f θ * sigD η θ)
      = (∫ θ in Work.Spaces.Iθ, deriv f θ ^ 2 * sigE η θ)
        + (∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * sigE η θ)
        + (∫ θ in Work.Spaces.Iθ, f θ * deriv f θ * sigD η θ) := by
    have h12 : IntegrableOn (fun θ : ℝ => deriv f θ ^ 2 * sigE η θ
        + f θ * deriv (deriv f) θ * sigE η θ) Work.Spaces.Iθ := hI1.add hI2
    rw [MeasureTheory.integral_add h12 hI3, MeasureTheory.integral_add hI1 hI2]
  -- The second integration by parts.
  have hB_deriv : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun t : ℝ => f t ^ 2 * sigD η t)
        (2 * (f θ * deriv f θ * sigD η θ) + f θ ^ 2 * sigDD η θ) θ := by
    intro θ hθ
    have h := ((hdf θ hθ).mul (hdf θ hθ)).mul (sigD_hasDerivAt_weak η hθ)
    have hfun : (f * f) * (fun t : ℝ => sigD η t)
        = fun t : ℝ => f t ^ 2 * sigD η t := by
      funext t
      simp only [Pi.mul_apply]
      ring
    rw [hfun] at h
    refine h.congr_deriv ?_
    simp only [Pi.mul_apply]
    ring
  have hB_int : IntervalIntegrable (fun θ : ℝ => 2 * (f θ * deriv f θ * sigD η θ)
      + f θ ^ 2 * sigDD η θ) MeasureTheory.volume 0 (Real.pi / 2) := by
    have h : IntegrableOn (fun θ : ℝ => 2 * (f θ * deriv f θ * sigD η θ)
        + f θ ^ 2 * sigDD η θ) Work.Spaces.Iθ :=
      (MeasureTheory.Integrable.const_mul hI3 2).add hI6
    rw [Work.Spaces.Iθ] at h
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hpi2.le).mpr h
  have hB_zero : (∫ θ in Work.Spaces.Iθ, 2 * (f θ * deriv f θ * sigD η θ)
      + f θ ^ 2 * sigDD η θ) = 0 :=
    Work.FTS.EllipticEst.AngSecond.slice_ftc_zero (fun t : ℝ => f t ^ 2 * sigD η t)
      (fun θ : ℝ => 2 * (f θ * deriv f θ * sigD η θ) + f θ ^ 2 * sigDD η θ)
      hB_deriv hB_int hb3 hb4
  -- Expand `σ''`.
  have hI6_eq : (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * sigDD η θ)
      = 4 * η * (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * sigE η θ)
        + 4 * η * (1 + η) * (∫ θ in Work.Spaces.Iθ,
            f θ ^ 2 * Real.cos (2 * θ) ^ 2 * Real.sin (2 * θ) ^ (-(2 + η))) := by
    have hfun : (fun θ => f θ ^ 2 * sigDD η θ)
        = (fun θ => 4 * η * (f θ ^ 2 * sigE η θ)
            + 4 * η * (1 + η) * (f θ ^ 2 * Real.cos (2 * θ) ^ 2
                * Real.sin (2 * θ) ^ (-(2 + η)))) := by
      funext θ
      simp only [sigDD_apply, sigE_apply]
      ring
    rw [hfun, MeasureTheory.integral_add (MeasureTheory.Integrable.const_mul hI4 (4 * η))
        (MeasureTheory.Integrable.const_mul hI5 (4 * η * (1 + η))),
      MeasureTheory.integral_const_mul (4 * η) (fun θ => f θ ^ 2 * sigE η θ),
      MeasureTheory.integral_const_mul (4 * η * (1 + η))
        (fun θ => f θ ^ 2 * Real.cos (2 * θ) ^ 2 * Real.sin (2 * θ) ^ (-(2 + η)))]
  have hB_split : (∫ θ in Work.Spaces.Iθ, 2 * (f θ * deriv f θ * sigD η θ)
        + f θ ^ 2 * sigDD η θ)
      = 2 * (∫ θ in Work.Spaces.Iθ, f θ * deriv f θ * sigD η θ)
        + (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * sigDD η θ) := by
    rw [MeasureTheory.integral_add (MeasureTheory.Integrable.const_mul hI3 2) hI6,
      MeasureTheory.integral_const_mul 2 (fun θ => f θ * deriv f θ * sigD η θ)]
  -- Assemble.
  set a := ∫ θ in Work.Spaces.Iθ, deriv f θ ^ 2 * sigE η θ with ha
  set b := ∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * sigE η θ with hb
  set c := ∫ θ in Work.Spaces.Iθ, f θ * deriv f θ * sigD η θ with hc
  set d := ∫ θ in Work.Spaces.Iθ, f θ ^ 2 * sigE η θ with hd
  set e := ∫ θ in Work.Spaces.Iθ, f θ ^ 2 * Real.cos (2 * θ) ^ 2
    * (Real.sin (2 * θ)) ^ (-(2 + η)) with he
  have h1' : a + b + c = 0 := by
    rw [← hA_split]; exact hA_zero
  have h2' : 2 * c + (4 * η * d + 4 * η * (1 + η) * e) = 0 := by
    rw [← hI6_eq, ← hB_split]; exact hB_zero
  have hmain : a = -b + 2 * η * d + 2 * η * (1 + η) * e := by linarith
  exact hmain

end Work.FTS.EllipticEst.AngAWeak
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Gbar_hardy_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-! ## Cauchy–Schwarz for Lebesgue integrals -/

/-- Cauchy–Schwarz for the Lebesgue integral, in the form needed below. -/
theorem gbar_cs_integral {s : Set ℝ} {a b : ℝ → ℝ}
    (ha : AEStronglyMeasurable a (volume.restrict s))
    (hb : AEStronglyMeasurable b (volume.restrict s))
    (ha2 : IntegrableOn (fun x => a x ^ 2) s) (hb2 : IntegrableOn (fun x => b x ^ 2) s) :
    (∫ x in s, a x * b x) ^ 2 ≤ (∫ x in s, a x ^ 2) * (∫ x in s, b x ^ 2) :=
  Work.Spaces.cs_integral ((memLp_two_iff_integrable_sq ha).mpr ha2)
    ((memLp_two_iff_integrable_sq hb).mpr hb2)

/-! ## The pointwise weighted Cauchy–Schwarz bound -/

/-- **Pointwise (weighted Cauchy–Schwarz) step of the Hardy inequality.**  For `β > 1`, `z > 0`
and `f` with `f²` integrable on `(0,∞)`,
`(HarOp β f z)² ≤ (1/β) z^{-β} ∫_{(0,z]} s^{β-1} (f s)²`, in `ℝ≥0∞`. -/
theorem gbar_HarOp_pointwise_sq (β : ℝ) (hβ : 1 < β) (f : ℝ → ℝ)
    (hf : IntegrableOn (fun z : ℝ => f z ^ 2) (Set.Ioi 0)) {z : ℝ} (hz : 0 < z) :
    ENNReal.ofReal ((HarOp β f z) ^ 2)
      ≤ ENNReal.ofReal (1 / β) * ENNReal.ofReal (z ^ (-β)) *
        ∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) := by
  have hβ0 : 0 < β := one_pos.trans hβ
  have hb1 : 0 ≤ β - 1 := by linarith
  have hb1' : 0 < β - 1 := by linarith
  have hb2 : 0 ≤ (β - 1) / 2 := by linarith
  have hb2' : 0 < (β - 1) / 2 := by linarith
  have hz0 : 0 ≤ z := hz.le
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) z)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  set I : ℝ := ∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s with hI
  set J2 : ℝ := ∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s ^ 2 with hJ2
  have hf2 : Integrable (fun s : ℝ => f s ^ 2) (volume.restrict (Set.Ioc (0 : ℝ) z)) :=
    hf.mono_set Set.Ioc_subset_Ioi_self
  have hM : Integrable (fun s : ℝ => z ^ (β - 1) + z ^ (β - 1) * f s ^ 2)
      (volume.restrict (Set.Ioc (0 : ℝ) z)) :=
    (integrable_const _).add (hf2.const_mul _)
  have hφ : AEStronglyMeasurable (absF f) (volume.restrict (Set.Ioc (0 : ℝ) z)) := by
    change AEStronglyMeasurable (fun x : ℝ => Real.sqrt (f x ^ 2)) _
    exact Real.continuous_sqrt.comp_aestronglyMeasurable hf2.aestronglyMeasurable
  have hcont : AEStronglyMeasurable (fun s : ℝ => s ^ ((β - 1) / 2))
      (volume.restrict (Set.Ioc (0 : ℝ) z)) :=
    (Real.continuous_rpow_const hb2).aestronglyMeasurable
  have ha : Integrable (fun s : ℝ => (s ^ ((β - 1) / 2)) ^ 2)
      (volume.restrict (Set.Ioc (0 : ℝ) z)) := by
    refine Integrable.mono' hM ((Real.continuous_rpow_const hb2).pow 2).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hx0 : 0 < x := hx.1
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (x ^ ((β - 1) / 2))), sq_rpow hx0,
      show ((β - 1) / 2 + (β - 1) / 2) = β - 1 from by ring]
    calc x ^ (β - 1) ≤ z ^ (β - 1) := Real.rpow_le_rpow hx0.le hx.2 hb1
      _ ≤ z ^ (β - 1) + z ^ (β - 1) * f x ^ 2 :=
          le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg hz0 _) (sq_nonneg _))
  have hb : Integrable (fun s : ℝ => (s ^ ((β - 1) / 2) * absF f s) ^ 2)
      (volume.restrict (Set.Ioc (0 : ℝ) z)) := by
    refine Integrable.mono' hM ((hcont.mul hφ).pow 2) ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hx0 : 0 < x := hx.1
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (x ^ ((β - 1) / 2) * absF f x)),
      mul_pow, sq_rpow hx0, absF_sq,
      show ((β - 1) / 2 + (β - 1) / 2) = β - 1 from by ring]
    calc x ^ (β - 1) * f x ^ 2 ≤ z ^ (β - 1) * f x ^ 2 :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hx0.le hx.2 hb1) (sq_nonneg _)
      _ ≤ z ^ (β - 1) + z ^ (β - 1) * f x ^ 2 :=
          le_add_of_nonneg_left (Real.rpow_nonneg hz0 _)
  -- ## Cauchy–Schwarz
  have hcs := gbar_cs_integral (s := Set.Ioc (0 : ℝ) z)
    (a := fun s : ℝ => s ^ ((β - 1) / 2)) (b := fun s : ℝ => s ^ ((β - 1) / 2) * absF f s)
    hcont (hcont.mul hφ) ha hb
  have hA : (∫ s in Set.Ioc (0 : ℝ) z, s ^ ((β - 1) / 2) * (s ^ ((β - 1) / 2) * absF f s))
      = ∫ s in (0 : ℝ)..z, s ^ (β - 1) * absF f s := by
    have h1 : (∫ s in Set.Ioc (0 : ℝ) z,
          s ^ ((β - 1) / 2) * (s ^ ((β - 1) / 2) * absF f s))
        = ∫ s in Set.Ioc (0 : ℝ) z, s ^ (β - 1) * absF f s :=
      setIntegral_congr_fun measurableSet_Ioc (fun x hx => by
        have h2 : x ^ ((β - 1) / 2) * x ^ ((β - 1) / 2) = x ^ (β - 1) := by
          rw [← Real.rpow_add hx.1]; congr 1; ring
        rw [show x ^ ((β - 1) / 2) * (x ^ ((β - 1) / 2) * absF f x)
            = (x ^ ((β - 1) / 2) * x ^ ((β - 1) / 2)) * absF f x from by ring, h2])
    rw [h1, ← intervalIntegral.integral_of_le hz0]
  have hB : (∫ s in Set.Ioc (0 : ℝ) z, (s ^ ((β - 1) / 2)) ^ 2) = z ^ β / β := by
    have h1 : (∫ s in Set.Ioc (0 : ℝ) z, (s ^ ((β - 1) / 2)) ^ 2)
        = ∫ s in Set.Ioc (0 : ℝ) z, s ^ (β - 1) := by
      refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
      rcases eq_or_lt_of_le hx.1.le with h | h
      · rw [← h, Real.zero_rpow (ne_of_gt hb2'), Real.zero_rpow (ne_of_gt hb1')]
        norm_num
      · rw [sq_rpow h, show ((β - 1) / 2 + (β - 1) / 2) = β - 1 from by ring]
    rw [h1, ← intervalIntegral.integral_of_le hz0]
    exact intervalIntegral_rpow_sub_one hβ0
  have hC : (∫ s in Set.Ioc (0 : ℝ) z, (s ^ ((β - 1) / 2) * absF f s) ^ 2) = J2 := by
    have h1 : (∫ s in Set.Ioc (0 : ℝ) z, (s ^ ((β - 1) / 2) * absF f s) ^ 2)
        = ∫ s in Set.Ioc (0 : ℝ) z, s ^ (β - 1) * f s ^ 2 := by
      refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
      rw [mul_pow, sq_rpow hx.1, absF_sq,
        show ((β - 1) / 2 + (β - 1) / 2) = β - 1 from by ring]
    rw [h1, ← intervalIntegral.integral_of_le hz0]
  have hCS : (∫ s in (0 : ℝ)..z, s ^ (β - 1) * absF f s) ^ 2 ≤ (z ^ β / β) * J2 := by
    have h := hcs
    rw [hA, hB, hC] at h
    exact h
  -- ## The integral itself
  have hJle : |I| ≤ ∫ s in (0 : ℝ)..z, s ^ (β - 1) * absF f s := by
    have h1 := intervalIntegral.norm_integral_le_integral_norm
      (μ := volume) (f := fun s : ℝ => s ^ (β - 1) * f s) hz0
    rw [← hI, Real.norm_eq_abs, intervalIntegral.integral_of_le hz0] at h1
    refine h1.trans (le_of_eq ?_)
    rw [intervalIntegral.integral_of_le hz0]
    refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx.1.le (β - 1)),
      absF_eq_abs]
  have hI2 : I ^ 2 ≤ (z ^ β / β) * J2 := by
    have h2 : |I| ^ 2 ≤ (∫ s in (0 : ℝ)..z, s ^ (β - 1) * absF f s) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg I) hJle 2
    rw [sq_abs] at h2
    linarith [hCS, h2]
  -- ## The a.e. bridge to the Lebesgue integral
  have hgI : IntegrableOn (fun s : ℝ => s ^ (β - 1) * f s ^ 2) (Set.Ioc 0 z) :=
    hb.congr ((ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall fun x hx => by
        show (x ^ ((β - 1) / 2) * absF f x) ^ 2 = x ^ (β - 1) * f x ^ 2
        rw [mul_pow, sq_rpow hx.1, absF_sq,
          show ((β - 1) / 2 + (β - 1) / 2) = β - 1 from by ring]))
  have hbridge : ENNReal.ofReal J2
      = ∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) := by
    rw [hJ2, intervalIntegral.integral_of_le hz0]
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hgI
      ((ae_restrict_iff' measurableSet_Ioc).mpr
        (Filter.Eventually.of_forall fun x hx =>
          mul_nonneg (Real.rpow_nonneg hx.1.le _) (sq_nonneg (f x))))
  -- ## Final assembly
  have huz : z ^ (-β) * z ^ β = 1 := by
    rw [← Real.rpow_add hz, show -β + β = 0 from by ring, Real.rpow_zero]
  have hmain : (HarOp β f z) ^ 2 = (z ^ (-β)) ^ 2 * I ^ 2 := by
    rw [HarOp, ← hI]
    ring
  have hkey : (z ^ (-β)) ^ 2 * ((z ^ β / β) * J2) = (1 / β) * (z ^ (-β) * J2) := by
    have h1 : (z ^ (-β)) ^ 2 * z ^ β = z ^ (-β) := by
      have h2 : (z ^ (-β)) ^ 2 * z ^ β = z ^ (-β) * (z ^ (-β) * z ^ β) := by ring
      rw [h2, huz, mul_one]
    have h3 : (z ^ (-β)) ^ 2 * ((z ^ β / β) * J2)
        = ((z ^ (-β)) ^ 2 * z ^ β) * (J2 / β) := by ring
    rw [h3, h1]
    ring
  calc ENNReal.ofReal ((HarOp β f z) ^ 2)
      = ENNReal.ofReal ((z ^ (-β)) ^ 2 * I ^ 2) := by rw [hmain]
    _ ≤ ENNReal.ofReal ((z ^ (-β)) ^ 2 * ((z ^ β / β) * J2)) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_left hI2 (sq_nonneg _)
    _ = ENNReal.ofReal (1 / β) * ENNReal.ofReal (z ^ (-β)) * ENNReal.ofReal J2 := by
        rw [hkey, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (Real.rpow_nonneg hz0 (-β))]
        ring
    _ = ENNReal.ofReal (1 / β) * ENNReal.ofReal (z ^ (-β)) *
          ∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) := by
        rw [hbridge]

/-! ## The `lintegral` form of the weighted Hardy inequality -/

/-- The weighted Hardy inequality in `ℝ≥0∞` form, with the sharp constant `1/(β(β-1))`. -/
theorem gbar_HarOp_weighted_lintegral (β : ℝ) (hβ : 5 ≤ β) (f : ℝ → ℝ)
    (hf : IntegrableOn (fun z : ℝ => (f z) ^ 2) (Set.Ioi 0)) :
    ∫⁻ z in Set.Ioi 0, ENNReal.ofReal
        ((Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)
      ≤ ENNReal.ofReal (100 / β ^ 2) *
          ∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (f z) ^ 2) := by
  have hβ1 : (1 : ℝ) < β := by linarith
  have hpt : ∀ z ∈ Set.Ioi (0 : ℝ),
      ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)
        ≤ ENNReal.ofReal (1 / β) *
          (ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) *
            ∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2)) := by
    intro z hz
    have hz0 : 0 < z := hz
    have hy := gbar_HarOp_pointwise_sq β hβ1 f hf hz0
    calc ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)
        = ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * ENNReal.ofReal ((HarOp β f z) ^ 2) :=
          ENNReal.ofReal_mul (sq_nonneg (Work.Spaces.w z))
      _ ≤ ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
            (ENNReal.ofReal (1 / β) * ENNReal.ofReal (z ^ (-β)) *
              ∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2)) :=
          mul_le_mul_of_nonneg_left hy bot_le
      _ = ENNReal.ofReal (1 / β) *
            (ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) *
              ∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2)) := by
          rw [mul_assoc (ENNReal.ofReal (1 / β)) (ENNReal.ofReal (z ^ (-β)))
                (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2))]
          rw [mul_left_comm (ENNReal.ofReal ((Work.Spaces.w z) ^ 2))
                (ENNReal.ofReal (1 / β))
                (ENNReal.ofReal (z ^ (-β)) *
                  ∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2))]
          rw [← mul_assoc (ENNReal.ofReal ((Work.Spaces.w z) ^ 2))
                (ENNReal.ofReal (z ^ (-β)))
                (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2))]
          rw [← ENNReal.ofReal_mul (sq_nonneg (Work.Spaces.w z))]
  have hA : ∫⁻ z in Set.Ioi 0, ENNReal.ofReal
        ((Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)
      ≤ ENNReal.ofReal (1 / β) *
        ∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) *
          (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2)) := by
    have h := setLIntegral_mono' (μ := volume) measurableSet_Ioi hpt
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h
    exact h
  rw [HarOp_lintegral_swap β hβ1 f hf] at hA
  have hC : ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) *
        (∫⁻ z in Set.Ici s, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)))
      ≤ ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) *
        ENNReal.ofReal ((Work.Spaces.w s) ^ 2 * s ^ (1 - β) / (β - 1)) :=
    setLIntegral_mono' (μ := volume) measurableSet_Ioi
      (fun s hs => mul_le_mul_of_nonneg_left (w_tail_lintegral_bound β hβ1 hs) bot_le)
  have hD : ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) *
        ENNReal.ofReal ((Work.Spaces.w s) ^ 2 * s ^ (1 - β) / (β - 1))
      = ENNReal.ofReal (1 / (β - 1)) *
        ∫⁻ s in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w s) ^ 2 * f s ^ 2) := by
    have hpt2 : ∀ s ∈ Set.Ioi (0 : ℝ),
        ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) *
          ENNReal.ofReal ((Work.Spaces.w s) ^ 2 * s ^ (1 - β) / (β - 1))
        = ENNReal.ofReal (1 / (β - 1)) *
          ENNReal.ofReal ((Work.Spaces.w s) ^ 2 * f s ^ 2) := by
      intro s hs
      have hs0 : 0 < s := hs
      rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hs0.le _) (sq_nonneg _))]
      rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / (β - 1))]
      congr 1
      have h1 : s ^ (β - 1) * s ^ (1 - β) = 1 := by
        rw [← Real.rpow_add hs0, show β - 1 + (1 - β) = 0 by ring, Real.rpow_zero]
      calc s ^ (β - 1) * f s ^ 2 * ((Work.Spaces.w s) ^ 2 * s ^ (1 - β) / (β - 1))
          = (s ^ (β - 1) * s ^ (1 - β)) * ((Work.Spaces.w s) ^ 2 * f s ^ 2) / (β - 1) := by
            ring
        _ = (Work.Spaces.w s) ^ 2 * f s ^ 2 / (β - 1) := by rw [h1, one_mul]
        _ = 1 / (β - 1) * ((Work.Spaces.w s) ^ 2 * f s ^ 2) := by ring
    rw [setLIntegral_congr_fun measurableSet_Ioi hpt2,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hconst : (1 : ℝ) / β * (1 / (β - 1)) ≤ 100 / β ^ 2 := by
    rw [div_mul_div_comm, one_mul]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hβ]
  calc ∫⁻ z in Set.Ioi 0, ENNReal.ofReal
        ((Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)
      ≤ ENNReal.ofReal (1 / β) *
        ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) *
          (∫⁻ z in Set.Ici s, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β))) := hA
    _ ≤ ENNReal.ofReal (1 / β) *
        ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) *
          ENNReal.ofReal ((Work.Spaces.w s) ^ 2 * s ^ (1 - β) / (β - 1)) :=
        mul_le_mul_of_nonneg_left hC bot_le
    _ = ENNReal.ofReal (1 / β) *
        (ENNReal.ofReal (1 / (β - 1)) *
          ∫⁻ s in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w s) ^ 2 * f s ^ 2)) := by
        rw [hD]
    _ = (ENNReal.ofReal (1 / β) * ENNReal.ofReal (1 / (β - 1))) *
        ∫⁻ s in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w s) ^ 2 * f s ^ 2) := by
        rw [mul_assoc]
    _ ≤ ENNReal.ofReal (100 / β ^ 2) *
        ∫⁻ s in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w s) ^ 2 * f s ^ 2) := by
        refine mul_le_mul_of_nonneg_right ?_ bot_le
        rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / β)]
        exact ENNReal.ofReal_le_ofReal hconst

/-! ## The real-integral form -/

/-- **The weighted Hardy inequality**, real-integral form, with the a.e. strong measurability of
`HarOp β f` supplied as a hypothesis. -/
theorem gbar_HarOp_weighted_integral_le (β : ℝ) (hβ : 5 ≤ β) (f : ℝ → ℝ)
    (hf : IntegrableOn (fun z : ℝ => (f z) ^ 2) (Set.Ioi 0))
    (hfw : IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (f z) ^ 2) (Set.Ioi 0))
    (hmeas : AEStronglyMeasurable (HarOp β f) (volume.restrict (Set.Ioi 0))) :
    IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2) (Set.Ioi 0) ∧
      (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2)
        ≤ (100 / β ^ 2) * ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (f z) ^ 2 := by
  have hC : (0 : ℝ) ≤ 100 / β ^ 2 := by positivity
  let G : ℝ → ℝ := fun z => (Work.Spaces.w z) ^ 2 * (HarOp β f z) ^ 2
  let H : ℝ → ℝ := fun z => (Work.Spaces.w z) ^ 2 * (f z) ^ 2
  have hGnn : ∀ z, 0 ≤ G z := fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hHnn : ∀ z, 0 ≤ H z := fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hlin : ∫⁻ z in Set.Ioi 0, ENNReal.ofReal (G z)
      ≤ ENNReal.ofReal (100 / β ^ 2) * ∫⁻ z in Set.Ioi 0, ENNReal.ofReal (H z) :=
    gbar_HarOp_weighted_lintegral β hβ f hf
  have hHfin : ∫⁻ z in Set.Ioi 0, ENNReal.ofReal (H z) < ⊤ := by
    have hEq : ENNReal.ofReal (∫ z, H z ∂volume.restrict (Set.Ioi 0))
        = ∫⁻ z, ENNReal.ofReal (H z) ∂volume.restrict (Set.Ioi 0) :=
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfw
        (Filter.Eventually.of_forall hHnn)
    rw [← hEq]
    exact ENNReal.ofReal_lt_top
  have hGfin : ∫⁻ z in Set.Ioi 0, ENNReal.ofReal (G z) < ⊤ :=
    lt_of_le_of_lt hlin (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hHfin)
  have hHasFin : MeasureTheory.HasFiniteIntegral G (volume.restrict (Set.Ioi 0)) :=
    (MeasureTheory.hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hGnn)).mpr hGfin
  have hw2 : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      (volume.restrict (Set.Ioi 0)) := by
    have hw0 : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi 0) := by
      unfold Work.Spaces.w
      exact ((continuous_const.add continuous_id).pow 2).continuousOn.div
        (continuous_id.pow 2).continuousOn (fun z hz => by
          simp only [Set.mem_Ioi] at hz
          positivity)
    exact (hw0.pow 2).aestronglyMeasurable measurableSet_Ioi
  have hAESM : AEStronglyMeasurable G (volume.restrict (Set.Ioi 0)) :=
    hw2.mul (hmeas.pow 2)
  refine ⟨⟨hAESM, hHasFin⟩, ?_⟩
  exact Work.FTS.EllipticEst.Blocks.integral_le_of_lintegral_le hC hGnn hHnn hfw hlin

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.weakFirstIter =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false

/-- For `0 ≤ s ≤ 1`, `0 < γ` and `γ ≤ 2` one has `s ^ 2 * s ^ (-γ) ≤ 1`: it is the standard
comparison `s ^ (2 - γ) ≤ s ^ 0 = 1` (the case `s = 0` is trivial). -/
private lemma sq_mul_rpow_neg_le_one {s γ : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hγ0 : 0 < γ) (hγ2 : γ ≤ 2) : s ^ 2 * s ^ (-γ) ≤ 1 := by
  rcases eq_or_lt_of_le hs0 with h | h
  · rw [← h, Real.zero_rpow (show (-γ) ≠ 0 by linarith)]
    norm_num
  · rw [show s ^ 2 = s ^ (2 : ℝ) from (Real.rpow_two s).symm,
      ← Real.rpow_add h (2 : ℝ) (-γ), show (2 : ℝ) + -γ = 2 - γ by ring]
    calc s ^ (2 - γ) ≤ s ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_ge h hs1 (by linarith)
      _ = 1 := Real.rpow_zero s

/-- **The first angular derivative is bounded by the second one, weakly.**

There is a universal constant `C` (quantified before `α` and `u`) such that for every
`α ∈ (0, 1/4]` and every `u : ℝ → ℝ` which is `C^∞` on `(0, π/2)`, continuous on
`[0, π/2]`, vanishes at both endpoints, and whose second derivative is `L²` for the
weight `sin(2θ)^{-η}` (`η = 99/100`), one has

`∫_{Iθ} (D_θu)² sin(2θ)^{-γ} ≤ C ∫_{Iθ} (u'')² sin(2θ)^{-η}`,  `γ = 1 + α/10`.

This is the *weak* (only two derivatives, no `Lzero1 u` term) form of the first-order
estimate of §H2.  Proof: pointwise `(D_θu)² sin(2θ)^{-γ} = (u')² sin(2θ)^{2-γ} ≤ (u')²`
because `2 - γ ≥ 0` and `sin(2θ) ≤ 1` on `Iθ`; and `(u')²` is bounded on `(0, π/2)` by
`A·B` with `A = ∫_{Iθ}(u'')² sin(2θ)^{-η}` and `B = ∫_{Iθ} sin(2θ)^η ≤ π/2`
(`weakSliceDerivBound`: Rolle for a zero of `u'`, Newton–Leibniz, then Cauchy–Schwarz).
Integrating gives `≤ (π/2)·A·B ≤ (π/2)²·A ≤ 4A` since `(π/2)² ≤ 4 < π²/4`... in fact
`(π/2)² ≤ 4` because `π < 4`. -/
theorem weakFirstIter : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u : ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    (∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) →
    ContinuousOn u Work.Spaces.Iθ → u 0 = 0 → u (Real.pi / 2) = 0 →
    MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ →
    (∫ θ in Work.Spaces.Iθ,
        (Work.Elliptic.Dth1Iter 1 u θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ)
      ≤ C * (∫ θ in Work.Spaces.Iθ,
          (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  refine ⟨4, by norm_num, ?_⟩
  intro α u hα hα4 hu hcont h0 h1 hint
  -- ## The exponents
  have hγpos : 0 < Work.Spaces.gam α := Work.Spaces.gam_pos hα
  have hγ2 : Work.Spaces.gam α ≤ 2 := by
    rw [Work.Spaces.gam]; linarith
  -- ## The two integrals
  set A : ℝ := ∫ θ in Work.Spaces.Iθ,
    (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ with hA
  set B : ℝ := ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta) with hB
  have hvol : (volume : Measure ℝ).real Work.Spaces.Iθ = Real.pi / 2 := by
    rw [MeasureTheory.measureReal_def,
      show (volume : Measure ℝ) Work.Spaces.Iθ = ENNReal.ofReal (Real.pi / 2) from by
        rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl, Real.volume_Icc,
          sub_zero],
      ENNReal.toReal_ofReal (by positivity)]
  -- ## `A ≥ 0`
  have hAnn : 0 ≤ A := by
    rw [hA]
    refine MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => ?_)
    exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.TT.sEta_nonneg hθ)
  -- ## `B ≤ π/2`
  have hBle : B ≤ Real.pi / 2 := by
    rw [hB]
    have hint1 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
      integrableOn_const (by
        rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl, Real.volume_Icc,
          sub_zero]
        exact ENNReal.ofReal_ne_top)
    have hle : (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta))
        ≤ (∫ _ in Work.Spaces.Iθ, (1 : ℝ)) := by
      refine integral_mono_of_nonneg ?_ hint1 ?_
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        exact Real.rpow_nonneg (Work.FTS.EllipticEst.TT.sin_two_nonneg hθ) _
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        have hs0 : 0 ≤ Real.sin (2 * θ) := Work.FTS.EllipticEst.TT.sin_two_nonneg hθ
        have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
        have heta : 0 ≤ Work.Spaces.eta := by rw [Work.Spaces.eta]; norm_num
        calc (Real.sin (2 * θ)) ^ (Work.Spaces.eta) ≤ (1 : ℝ) ^ (Work.Spaces.eta) :=
              Real.rpow_le_rpow hs0 hs1 heta
          _ = 1 := Real.one_rpow _
    calc (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta))
        ≤ (∫ _ in Work.Spaces.Iθ, (1 : ℝ)) := hle
      _ = Real.pi / 2 := by rw [MeasureTheory.setIntegral_const, hvol, smul_eq_mul]; norm_num
  -- ## The pointwise bound `(u')² ≤ A·B` on the open interval
  have hbound : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (deriv u θ) ^ 2 ≤ A * B := by
    intro θ hθ
    have h := (weakSliceDerivBound u hu hcont h0 h1 hint).1 θ hθ
    simpa [hA, hB] using h
  -- ## The pointwise bound for the target integrand on the open interval
  have hpt_open : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.Elliptic.Dth1Iter 1 u θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ
        ≤ A * (Real.pi / 2) := by
    intro θ hθ
    have hIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hsq : (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) ≤ 1 :=
      sq_mul_rpow_neg_le_one (Work.FTS.EllipticEst.TT.sin_two_nonneg hIθ)
        (Real.sin_le_one _) hγpos hγ2
    have hderiv : (Work.Elliptic.Dth1Iter 1 u θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ
        ≤ (deriv u θ) ^ 2 := by
      simp only [Work.Elliptic.Dth1Iter_succ, Work.Elliptic.Dth1Iter_zero,
        Work.Elliptic.Dth1, Work.FTS.EllipticEst.sGam]
      rw [mul_pow]
      have hre : (Real.sin (2 * θ)) ^ 2 * (deriv u θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          = (deriv u θ) ^ 2
            * ((Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
        ring
      rw [hre]
      calc (deriv u θ) ^ 2
            * ((Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          ≤ (deriv u θ) ^ 2 * 1 := mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
        _ = (deriv u θ) ^ 2 := by ring
    have h2 : (deriv u θ) ^ 2 ≤ A * B := hbound θ hθ
    have h3 : A * B ≤ A * (Real.pi / 2) := mul_le_mul_of_nonneg_left hBle hAnn
    linarith
  -- ## The same bound almost everywhere on `Iθ`
  have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (Work.Elliptic.Dth1Iter 1 u θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ
        ≤ A * (Real.pi / 2) := by
    have h := Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
      (p := fun θ => (Work.Elliptic.Dth1Iter 1 u θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ
        ≤ A * (Real.pi / 2)) hpt_open
    simpa [Work.Spaces.Iθ] using h
  have hnn : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      0 ≤ (Work.Elliptic.Dth1Iter 1 u θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.TT.sGam_nonneg α hθ)
  -- ## Integrating the comparison
  have hIntc : MeasureTheory.IntegrableOn (fun _ : ℝ => A * (Real.pi / 2))
      Work.Spaces.Iθ :=
    integrableOn_const (by
      rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl, Real.volume_Icc,
        sub_zero]
      exact ENNReal.ofReal_ne_top)
  have hmain := integral_mono_of_nonneg hnn hIntc hae
  have hconstval : (∫ _ in Work.Spaces.Iθ, (A * (Real.pi / 2)))
      = (Real.pi / 2) * (A * (Real.pi / 2)) := by
    rw [MeasureTheory.setIntegral_const, hvol, smul_eq_mul]
  rw [hconstval] at hmain
  -- ## Numerical comparison
  have hπ2 : (Real.pi / 2) ^ 2 ≤ 4 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
  have hfin : (Real.pi / 2) * (A * (Real.pi / 2)) ≤ 4 * A := by
    have heq : (Real.pi / 2) * (A * (Real.pi / 2)) = (Real.pi / 2) ^ 2 * A := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right hπ2 hAnn
  linarith [hmain, hfin]

end Work.FTS.EllipticEst.H2W
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.SliceSetup =====
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

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## The fundamental theorem of calculus and integration by parts on `(a,b)` -/

/-- **FTC-2 on an open interval.**  If `G` is differentiable on `(a,b)` with derivative `G'`,
`G'` is integrable there, and `G` has limits `m` at `a⁺` and `l` at `b⁻`, then
`∫_a^b G' = l - m`. -/
theorem integral_Ioo_eq_sub_of_tendsto {a b m l : ℝ} (hab : a < b) {G G' : ℝ → ℝ}
    (hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt G (G' x) x)
    (hint : IntegrableOn G' (Set.Ioo a b))
    (hbot : Tendsto G (𝓝[>] a) (𝓝 m)) (htop : Tendsto G (𝓝[<] b) (𝓝 l)) :
    ∫ x in Set.Ioo a b, G' x = l - m := by
  have hle : a ≤ b := le_of_lt hab
  have hI : IntervalIntegrable G' volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hle).mpr hint
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hab hderiv hI hbot htop
  rw [intervalIntegral.integral_of_le hle, MeasureTheory.integral_Ioc_eq_integral_Ioo] at h
  exact h

/-- **Integration by parts against a weight vanishing at both endpoints.**  If
`(ρ f²) → 0` at `a⁺` and at `b⁻`, then `∫ ρ f f' = -(1/2) ∫ ρ' f²` on `(a,b)`. -/
theorem integral_Ioo_mul_deriv_eq_neg_half {a b : ℝ} (hab : a < b) {ρ ρ' f f' : ℝ → ℝ}
    (hρ : ∀ x ∈ Set.Ioo a b, HasDerivAt ρ (ρ' x) x)
    (hf : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hint1 : IntegrableOn (fun x => ρ' x * f x ^ 2) (Set.Ioo a b))
    (hint2 : IntegrableOn (fun x => ρ x * f x * f' x) (Set.Ioo a b))
    (hbot : Tendsto (fun x => ρ x * f x ^ 2) (𝓝[>] a) (𝓝 0))
    (htop : Tendsto (fun x => ρ x * f x ^ 2) (𝓝[<] b) (𝓝 0)) :
    ∫ x in Set.Ioo a b, ρ x * f x * f' x = -(1 / 2) * ∫ x in Set.Ioo a b, ρ' x * f x ^ 2 := by
  have hderivG : ∀ x ∈ Set.Ioo a b,
      HasDerivAt (fun y => (1 / 2) * (ρ y * f y ^ 2))
        (ρ x * f x * f' x + (1 / 2) * (ρ' x * f x ^ 2)) x := by
    intro x hx
    have h := ((hρ x hx).mul ((hf x hx).pow 2)).const_mul (1 / 2)
    have h2 : (2 : ℕ) - 1 = 1 := rfl
    rw [h2, pow_one] at h
    convert h using 1
    simp only [Pi.pow_apply]
    ring
  have hInt : IntegrableOn
      (fun x => ρ x * f x * f' x + (1 / 2) * (ρ' x * f x ^ 2)) (Set.Ioo a b) :=
    hint2.add (hint1.const_mul (1 / 2))
  have hlim1 : Tendsto (fun y => (1 / 2) * (ρ y * f y ^ 2)) (𝓝[>] a) (𝓝 0) := by
    simpa using hbot.const_mul (1 / 2 : ℝ)
  have hlim2 : Tendsto (fun y => (1 / 2) * (ρ y * f y ^ 2)) (𝓝[<] b) (𝓝 0) := by
    simpa using htop.const_mul (1 / 2 : ℝ)
  have hFTC := integral_Ioo_eq_sub_of_tendsto hab hderivG hInt hlim1 hlim2
  simp only [sub_zero] at hFTC
  have hsplit : ∫ x in Set.Ioo a b, (ρ x * f x * f' x + (1 / 2) * (ρ' x * f x ^ 2))
      = (∫ x in Set.Ioo a b, ρ x * f x * f' x)
        + (1 / 2) * ∫ x in Set.Ioo a b, ρ' x * f x ^ 2 := by
    rw [integral_add hint2 (hint1.const_mul (1 / 2)), integral_const_mul]
  rw [hsplit] at hFTC
  linarith [hFTC]

/-! ## A limit at the right endpoint, from the integrability of the derivative -/

/-- **A differentiable function with integrable derivative has a limit at the right endpoint.**

If `f` is differentiable on the open interval `(a,b)` with derivative `f'`, and `f'` is
integrable on `(a,b)`, then `f` has a finite limit as `x → b⁻`.  (Companion, at the right
endpoint, of `Work.FTS.EllipticEst.exists_tendsto_nhdsGT_zero_of_integrableOn_deriv`.) -/
theorem exists_tendsto_nhdsLT_of_integrableOn_deriv {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hint : IntegrableOn f' (Set.Ioo a b)) :
    ∃ L : ℝ, Tendsto f (𝓝[<] b) (𝓝 L) := by
  set c : ℝ := (a + b) / 2 with hcdef
  have hac : a < c := by rw [hcdef]; linarith
  have hcb : c < b := by rw [hcdef]; linarith
  have hIoo_cb : IntegrableOn f' (Set.Ioo c b) :=
    hint.mono_set fun x hx => ⟨lt_trans hac hx.1, hx.2⟩
  have hIcc : IntegrableOn f' (Set.Icc c b) :=
    hIoo_cb.congr_set_ae (MeasureTheory.Ioo_ae_eq_Icc (a := c) (b := b)).symm
  have hcont : ContinuousOn (fun x => ∫ t in c..x, f' t) (Set.Icc c b) := by
    have h := intervalIntegral.continuousOn_primitive_interval (a := c) (b := b) (by
      rw [Set.uIcc_of_le hcb.le]; exact hIcc)
    rwa [Set.uIcc_of_le hcb.le] at h
  refine ⟨f c + ∫ t in c..b, f' t, ?_⟩
  have hcontAt : ContinuousWithinAt (fun x => ∫ t in c..x, f' t) (Set.Icc c b) b :=
    hcont.continuousWithinAt (Set.right_mem_Icc.mpr hcb.le)
  have hlimprim : Tendsto (fun x => ∫ t in c..x, f' t) (𝓝[<] b) (𝓝 (∫ t in c..b, f' t)) := by
    have hle : 𝓝[<] b ≤ 𝓝[Set.Icc c b] b := by
      rw [← nhdsWithin_Ioo_eq_nhdsLT hcb]
      exact nhdsWithin_mono b (fun x hx => ⟨hx.1.le, hx.2.le⟩)
    exact hcontAt.mono_left hle
  have hlim : Tendsto (fun x => f c + ∫ t in c..x, f' t) (𝓝[<] b) (𝓝 (f c + ∫ t in c..b, f' t)) :=
    hlimprim.const_add (f c)
  refine hlim.congr' ?_
  have hmem : Set.Ioo c b ∈ 𝓝[<] b := by
    rw [← nhdsWithin_Ioo_eq_nhdsLT hcb]
    exact self_mem_nhdsWithin
  filter_upwards [hmem] with x hx
  have hFTC : ∫ t in c..x, f' t = f x - f c :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y hy => hderiv y (by
        have hy' : y ∈ Set.Icc c x := by rwa [Set.uIcc_of_le hx.1.le] at hy
        exact ⟨lt_of_lt_of_le hac hy'.1, lt_of_le_of_lt hy'.2 hx.2⟩))
      ((show IntegrableOn f' (Set.uIcc c x) volume from by
          rw [Set.uIcc_of_le hx.1.le]
          exact hIcc.mono_set (Set.Icc_subset_Icc le_rfl hx.2.le)).intervalIntegrable)
  linarith [hFTC]

/-! ## A `liminf` consequence of the divergence of `∫ dt/t` at `0` -/

/-- **If `F ≥ c > 0` on `(0,δ)` then `F t / t` is not integrable there** (because `∫_0^δ dt/t`
diverges).  Contrapositively: an integrable `F t / t` must have arbitrarily small values of
`F` arbitrarily close to `0`. -/
theorem not_integrableOn_div_of_ge_const {F : ℝ → ℝ} {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hF : ∀ t ∈ Set.Ioo (0 : ℝ) δ, c ≤ F t) :
    ¬ IntegrableOn (fun t => F t / t) (Set.Ioo (0 : ℝ) δ) := by
  intro hint
  have hmeas : AEStronglyMeasurable (fun t : ℝ => c / t)
      ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) δ)) :=
    (measurable_const.div measurable_id).aestronglyMeasurable
  have hdom : IntegrableOn (fun t : ℝ => c / t) (Set.Ioo (0 : ℝ) δ) := by
    refine hint.mono' hmeas ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    have ht0 : 0 < t := ht.1
    have h1 : c ≤ F t := hF t ht
    rw [Real.norm_of_nonneg (div_nonneg hc.le ht0.le)]
    exact div_le_div_of_nonneg_right h1 ht0.le
  have hpow : IntegrableOn (fun t : ℝ => t ^ (-1 : ℝ)) (Set.Ioo (0 : ℝ) δ) := by
    have h := hdom.const_mul (c⁻¹)
    have h1 : (fun t : ℝ => c⁻¹ * (c / t))
        =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) δ)] (fun t : ℝ => t ^ (-1 : ℝ)) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      have ht0 : 0 < t := ht.1
      simp only [div_eq_mul_inv, Real.rpow_neg_one]
      field_simp
    exact h.congr h1
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff hδ] at hpow
  norm_num at hpow

end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.slice_coercive =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## The integrals are non-negative -/







/-! ## The theorem -/


end Work.FTS.EllipticEst.TT
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.ThetaEnergy1Inf =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

/-! # The truncated `θ`-energy identity at `C^∞` smoothness

`Work.FTS.EllipticEst.Aux.thetaEnergy1_dev` demands `ContDiff ℝ ⊤ W`, i.e. *analyticity*
of the cutoff; with `HasCompactSupport W` that forces `W = 0`, so the identity is only
available for the trivial cutoff.  Here the same identity is proved with the correct
smoothness hypothesis `ContDiff ℝ ∞ W` (`∞ = (⊤ : ℕ∞) : ℕ∞ω`), which is what the
cutoff families of the `E1`/`E2`/`ZpzEst` estimates satisfy. -/

namespace Work.FTS.EllipticEst.InfDev

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

/-! ## Small helpers -/








end

end Work.FTS.EllipticEst.InfDev
end
-- ===== merged: Submission.Work.FTS.EllipticEst.WeakMoment.SliceSqBoundsOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.WeakMoment

/-! ## Weighted `L²` bounds from a pointwise bound

The estimate below is the `θ`-slice form of the weighted Poincaré inequality used by the
weak-moment interface: a function that is continuous on the open interval `(0, π/2)` and bounded
by a constant `M` there has weighted square `∫ f² sin(2θ)^{-η}` integrable, and the weighted
square integral is at most `M² ∫ sin(2θ)^{-η}`. -/

theorem sq_mul_sEta_integrableOn_and_integral_le {f : ℝ → ℝ} {M : ℝ}
    (hf : ContinuousOn f (Set.Ioo (0 : ℝ) (Real.pi / 2))) (hM : 0 ≤ M)
    (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |f θ| ≤ M) :
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ M ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ) := by
  have hIoo : MeasurableSet (Set.Ioo (0 : ℝ) (Real.pi / 2)) := measurableSet_Ioo
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
    fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hae : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    MeasureTheory.Ioo_ae_eq_Icc.symm
  have hms : volume.restrict Work.Spaces.Iθ
      = volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    MeasureTheory.Measure.restrict_congr_set hae
  -- the weight is integrable on `Iθ`
  have hsEta_int : MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := (Work.FTS.EllipticEst.integrableOn_thEta).1
  -- the weight is positive and continuous on the open interval
  have hsEta_pos : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      0 < Work.FTS.EllipticEst.sEta θ := by
    intro θ hθ
    have hsin : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    exact Real.rpow_pos_of_pos hsin _
  have hsEta_cont : ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.sEta θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      Real.continuous_sin.comp_continuousOn ((continuous_const.mul continuous_id).continuousOn)
    refine hsin.rpow_const (fun θ hθ => Or.inl ?_)
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos]))
  -- the dominating function on the open interval
  have hmaj : MeasureTheory.IntegrableOn (fun θ : ℝ => M ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (hsEta_int.mono_set hsub).const_mul (M ^ 2)
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    ((hf.aestronglyMeasurable hIoo).pow 2).mul (hsEta_cont.aestronglyMeasurable hIoo)
  have hle : (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))]
      (fun θ : ℝ => M ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    filter_upwards [ae_restrict_mem hIoo] with θ hθ
    have hs0 : 0 ≤ Work.FTS.EllipticEst.sEta θ := le_of_lt (hsEta_pos θ hθ)
    have hf2 : (f θ) ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs (f θ)]
      exact pow_le_pow_left₀ (abs_nonneg _) (h θ hθ) 2
    exact mul_le_mul_of_nonneg_right hf2 hs0
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))]
      (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    filter_upwards [ae_restrict_mem hIoo] with θ hθ
    exact mul_nonneg (sq_nonneg _) (le_of_lt (hsEta_pos θ hθ))
  have hnorm : ∀ᵐ θ ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))),
      ‖(f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ‖ ≤ M ^ 2 * Work.FTS.EllipticEst.sEta θ := by
    filter_upwards [hle, hnn] with θ h1 h2
    rwa [Real.norm_of_nonneg h2]
  have hint_Ioo := hmaj.mono' hmeas hnorm
  constructor
  · change MeasureTheory.Integrable
        (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        (volume.restrict Work.Spaces.Iθ)
    rw [hms]
    exact hint_Ioo
  · have hmono := MeasureTheory.integral_mono_of_nonneg hnn hmaj hle
    have e1 : (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
      MeasureTheory.setIntegral_congr_set hae
    have e2 : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ)
        = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.sEta θ :=
      MeasureTheory.setIntegral_congr_set hae
    have e3 : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          M ^ 2 * Work.FTS.EllipticEst.sEta θ)
        = M ^ 2 * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            Work.FTS.EllipticEst.sEta θ) :=
      MeasureTheory.integral_const_mul _ _
    rw [e1, e2, ← e3]
    exact hmono

/-! ## The arithmetic of the final constant -/

private lemma slice_arith_two {A G : ℝ} (hG : 0 ≤ G)
    (hAG : A ^ 2 ≤ G * (Real.pi / 2)) :
    (Real.pi / 2 * A) ^ 2 * 10000 ≤ 100000 * G := by
  have hpi : (Real.pi / 2) ^ 3 * 10000 ≤ 100000 := by
    have h1 : Real.pi / 2 ≤ 2 := by linarith [Real.pi_le_four]
    have h2 : (Real.pi / 2) ^ 3 ≤ (2 : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
    norm_num at h2
    linarith
  have h2 : (Real.pi / 2) ^ 2 * A ^ 2 * 10000
      ≤ (Real.pi / 2) ^ 2 * (G * (Real.pi / 2)) * 10000 := by
    have hk : 0 ≤ (Real.pi / 2) ^ 2 * 10000 := by positivity
    have hstep := mul_le_mul_of_nonneg_right hAG hk
    nlinarith [hstep]
  calc (Real.pi / 2 * A) ^ 2 * 10000 = (Real.pi / 2) ^ 2 * A ^ 2 * 10000 := by ring
    _ ≤ (Real.pi / 2) ^ 2 * (G * (Real.pi / 2)) * 10000 := h2
    _ = ((Real.pi / 2) ^ 3 * 10000) * G := by ring
    _ ≤ 100000 * G := mul_le_mul_of_nonneg_right hpi hG

private lemma slice_arith_one {A G : ℝ} (hG : 0 ≤ G)
    (hAG : A ^ 2 ≤ G * (Real.pi / 2)) :
    A ^ 2 * 10000 ≤ 100000 * G := by
  have hpi : (Real.pi / 2) * 10000 ≤ 100000 := by
    have h1 : Real.pi / 2 ≤ 2 := by linarith [Real.pi_le_four]
    linarith
  calc A ^ 2 * 10000 ≤ (G * (Real.pi / 2)) * 10000 :=
        mul_le_mul_of_nonneg_right hAG (by norm_num)
    _ = ((Real.pi / 2) * 10000) * G := by ring
    _ ≤ 100000 * G := mul_le_mul_of_nonneg_right hpi hG

/-! ## The slice bounds, with the four open-interval ingredients

The four inputs (unweighted integrability of `u''`, the weighted Cauchy–Schwarz bound, the
Rolle/Newton–Leibniz bound on `u'`, and the mean-value bound on `u`) are delegated lemmas in
`Submission/Work/FTS/EllipticEst/WeakMoment/Open/`. -/

theorem SliceSqBoundsOpen : ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ → ℝ,
    (∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo (0 : ℝ) (Real.pi / 2))) →
    ContinuousOn u Work.Spaces.Iθ → u 0 = 0 → u (Real.pi / 2) = 0 →
    MeasureTheory.IntegrableOn (fun θ => (deriv (fun t => deriv u t) θ) ^ 2
      * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ C * (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) ∧
    MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ C * (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) := by
  refine ⟨100000, by norm_num, ?_⟩
  intro u hsm hcont h0 hpi h5
  -- the hypothesis rewritten in the vocabulary of `TT.D2`
  have h5D : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.FTS.EllipticEst.TT.D2 u θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := h5
  -- integrability of `(u'')²` and of `|u''|`
  obtain ⟨_, hD2abs⟩ := Work.FTS.EllipticEst.WeakMoment.Open.IntegrableD2OfWeighted h5D
  -- Cauchy–Schwarz: `(∫|u''|)² ≤ (∫(u'')² sin(2θ)^{-η}) · π/2`
  have hcs := Work.FTS.EllipticEst.WeakMoment.Open.D2CsBound hsm h5D
  -- the pointwise bound `|u'| ≤ ∫|u''|`
  have hderiv := Work.FTS.EllipticEst.WeakMoment.Open.DerivLeIntegralAbsD2 hsm hcont h0 hpi hD2abs
  have hA0 : 0 ≤ ∫ x in Work.Spaces.Iθ, |Work.FTS.EllipticEst.TT.D2 u x| :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun _ _ => abs_nonneg _)
  -- the pointwise bound `|u| ≤ (π/2)∫|u''|`
  have hu := Work.FTS.EllipticEst.WeakMoment.Open.ULeIntegralDerivBound hsm hcont h0 hA0 hderiv
  -- the weight
  have hsEta_le : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ) ≤ 10000 :=
    (Work.FTS.EllipticEst.integrableOn_thEta).2
  have hG0 : 0 ≤ ∫ θ in Work.Spaces.Iθ,
      (Work.FTS.EllipticEst.TT.D2 u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun x hx => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.TT.sEta_nonneg hx))
  -- continuity, to feed the pointwise bounds into the weighted estimates
  have hcont_u : ContinuousOn u (Set.Ioo (0 : ℝ) (Real.pi / 2)) := (hsm 1).continuousOn
  have hcont_du : ContinuousOn (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h : ContDiffOn ℝ 1 (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (hsm 2).deriv_of_isOpen isOpen_Ioo (by norm_num)
    exact h.continuousOn
  obtain ⟨hu_int, hu_le⟩ := sq_mul_sEta_integrableOn_and_integral_le hcont_u (by positivity) hu
  obtain ⟨hdu_int, hdu_le⟩ := sq_mul_sEta_integrableOn_and_integral_le hcont_du hA0 hderiv
  refine ⟨hu_int, ?_, hdu_int, ?_⟩
  · refine le_trans hu_le ?_
    calc ((Real.pi / 2) * ∫ x in Work.Spaces.Iθ, |Work.FTS.EllipticEst.TT.D2 u x|) ^ 2
          * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ)
        ≤ ((Real.pi / 2) * ∫ x in Work.Spaces.Iθ, |Work.FTS.EllipticEst.TT.D2 u x|) ^ 2
            * 10000 := mul_le_mul_of_nonneg_left hsEta_le (sq_nonneg _)
      _ ≤ 100000 * (∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.TT.D2 u θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) := slice_arith_two hG0 hcs
      _ = 100000 * (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) := by
          simp only [Work.FTS.EllipticEst.TT.D2]
  · refine le_trans hdu_le ?_
    calc (∫ x in Work.Spaces.Iθ, |Work.FTS.EllipticEst.TT.D2 u x|) ^ 2
          * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ)
        ≤ (∫ x in Work.Spaces.Iθ, |Work.FTS.EllipticEst.TT.D2 u x|) ^ 2 * 10000 :=
          mul_le_mul_of_nonneg_left hsEta_le (sq_nonneg _)
      _ ≤ 100000 * (∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.TT.D2 u θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) := slice_arith_one hG0 hcs
      _ = 100000 * (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) := by
          simp only [Work.FTS.EllipticEst.TT.D2]

end Work.FTS.EllipticEst.WeakMoment
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.slice_v2_interval =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

open scoped Real Topology Interval
open MeasureTheory Set Filter

noncomputable section

set_option maxHeartbeats 8000000

/-! ## The two slope estimates for `σ` on `[π/4, π/2)` (from `slice_V2_le`) -/

/-- On `(0, π/2)`, `deriv (cos · σ) = σ · ((2-γ) cos 2θ / sin θ - sin θ)`. -/
private lemma deriv_cos_sgm (γ : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ)) θ
      = Real.rpow (Real.sin (2 * θ)) (2 - γ)
          * ((2 - γ) * Real.cos (2 * θ) / Real.sin θ - Real.sin θ) := by
  have hsin2 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_mem_Ioo ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have h1 : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (2 * Real.cos (2 * θ)) θ := by
    have h := (Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul (2 : ℝ))
    rwa [show Real.cos (2 * θ) * (2 * 1) = 2 * Real.cos (2 * θ) from by ring] at h
  have h2 : HasDerivAt (fun t : ℝ => Real.rpow (Real.sin (2 * t)) (2 - γ))
      ((2 * Real.cos (2 * θ)) * (2 - γ) * Real.rpow (Real.sin (2 * θ)) (2 - γ - 1)) θ :=
    h1.rpow_const (Or.inl hsin2.ne')
  have h3 : HasDerivAt (fun t : ℝ => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ))
      ((-Real.sin θ) * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        + Real.cos θ * ((2 * Real.cos (2 * θ)) * (2 - γ)
            * Real.rpow (Real.sin (2 * θ)) (2 - γ - 1))) θ :=
    (Real.hasDerivAt_cos θ).mul h2
  rw [h3.deriv]
  have hsplit : Real.rpow (Real.sin (2 * θ)) (2 - γ - 1) * Real.sin (2 * θ)
      = Real.rpow (Real.sin (2 * θ)) (2 - γ) := by
    have h := Real.rpow_add hsin2 (2 - γ - 1) 1
    rw [Real.rpow_one (Real.sin (2 * θ))] at h
    rw [show (2 - γ - 1) + 1 = 2 - γ from by ring] at h
    exact h.symm
  have hkey : (2 * Real.cos θ) * Real.rpow (Real.sin (2 * θ)) (2 - γ - 1)
      = Real.rpow (Real.sin (2 * θ)) (2 - γ) / Real.sin θ := by
    have hsinθ : 0 < Real.sin θ := Real.sin_pos_of_mem_Ioo ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    rw [eq_div_iff hsinθ.ne']
    rw [show (2 * Real.cos θ) * Real.rpow (Real.sin (2 * θ)) (2 - γ - 1) * Real.sin θ
        = (Real.sin (2 * θ)) * Real.rpow (Real.sin (2 * θ)) (2 - γ - 1) from by
          rw [Real.sin_two_mul]; ring,
      mul_comm (Real.sin (2 * θ)) (Real.rpow _ _), hsplit]
  rw [show (-Real.sin θ) * Real.rpow (Real.sin (2 * θ)) (2 - γ)
      + Real.cos θ * ((2 * Real.cos (2 * θ)) * (2 - γ)
          * Real.rpow (Real.sin (2 * θ)) (2 - γ - 1))
      = Real.rpow (Real.sin (2 * θ)) (2 - γ)
          * ((2 - γ) * Real.cos (2 * θ) / Real.sin θ - Real.sin θ) from by
    rw [show Real.cos θ * ((2 * Real.cos (2 * θ)) * (2 - γ)
          * Real.rpow (Real.sin (2 * θ)) (2 - γ - 1))
        = ((2 - γ) * Real.cos (2 * θ))
            * ((2 * Real.cos θ) * Real.rpow (Real.sin (2 * θ)) (2 - γ - 1)) from by ring,
      hkey]
    ring]

/-- The two slope estimates for `σ` on `[π/4, π/2)`: the coercivity coefficient
`4 sin θ σ + ½ (cos · σ)'` dominates `(3/2)σ`, and `|(cos · σ)'| ≤ 4σ`. -/
private lemma weight_facts (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) {θ : ℝ}
    (hθ : θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2)) :
    (3 / 2) * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        ≤ 4 * Real.sin θ * Real.rpow (Real.sin (2 * θ)) (2 - γ)
          + (1 / 2) * deriv (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ)) θ
      ∧ |deriv (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ)) θ|
          ≤ 4 * Real.rpow (Real.sin (2 * θ)) (2 - γ) := by
  have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hsinθ : 0 < Real.sin θ := Real.sin_pos_of_mem_Ioo ⟨hθ'.1, by linarith [hθ'.2, Real.pi_pos]⟩
  have hsin2 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  have hσpos : 0 < Real.rpow (Real.sin (2 * θ)) (2 - γ) := Real.rpow_pos_of_pos hsin2 _
  have hc2 : Real.cos (2 * θ) ≤ 0 :=
    Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith [hθ.1, Real.pi_pos])
      (by linarith [hθ.2, Real.pi_pos])
  have hc2le : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
  have hg2γ : (2 - γ) ≤ 1 := by linarith
  have hg2γ0 : (0 : ℝ) < 2 - γ := by linarith
  have hsinθge : Real.sqrt 2 / 2 ≤ Real.sin θ := by
    have h1 : Real.sin (Real.pi / 4) ≤ Real.sin θ :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
        (by linarith [hθ.2]) hθ.1
    rwa [Real.sin_pi_div_four] at h1
  have hq : |(2 - γ) * Real.cos (2 * θ) / Real.sin θ| ≤ Real.sqrt 2 := by
    simp only [abs_div, abs_mul, abs_of_pos hg2γ0, abs_of_pos hsinθ]
    have h4 : (2 - γ) * |Real.cos (2 * θ)| ≤ 1 := by nlinarith [hc2le, hg2γ]
    have h5 : 1 / (Real.sqrt 2 / 2) = Real.sqrt 2 := by
      rw [div_div_eq_mul_div, one_mul, div_eq_iff (by positivity : Real.sqrt 2 ≠ 0)]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    calc (2 - γ) * |Real.cos (2 * θ)| / Real.sin θ
        ≤ 1 / Real.sin θ := div_le_div_of_nonneg_right h4 hsinθ.le
      _ ≤ 1 / (Real.sqrt 2 / 2) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) hsinθge
      _ = Real.sqrt 2 := h5
  have hder := deriv_cos_sgm γ hθ'
  have hA : 4 * Real.sin θ * Real.rpow (Real.sin (2 * θ)) (2 - γ)
      + (1 / 2) * deriv (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ)) θ
      = Real.rpow (Real.sin (2 * θ)) (2 - γ)
          * ((7 / 2) * Real.sin θ + ((2 - γ) * Real.cos (2 * θ) / Real.sin θ) / 2) := by
    rw [hder]; ring
  constructor
  · rw [hA]
    have hlow : (3 : ℝ) / 2 ≤ (7 / 2) * Real.sin θ
        + ((2 - γ) * Real.cos (2 * θ) / Real.sin θ) / 2 := by
      have h1 : (2 - γ) * Real.cos (2 * θ) / Real.sin θ ≥ -Real.sqrt 2 := by
        have := abs_le.mp hq; linarith [this.1]
      have h2 : (7 / 2) * Real.sin θ ≥ 7 / 2 * (Real.sqrt 2 / 2) :=
        mul_le_mul_of_nonneg_left hsinθge (by norm_num)
      have hs2 : (6 : ℝ) / 5 ≤ Real.sqrt 2 :=
        (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
      have h3 : (7 : ℝ) / 2 * (Real.sqrt 2 / 2) = 7 * Real.sqrt 2 / 4 := by ring
      nlinarith [h1, h2, h3, hs2]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hlow hσpos.le
  · rw [hder, abs_mul, abs_of_pos hσpos]
    have hb : |(2 - γ) * Real.cos (2 * θ) / Real.sin θ - Real.sin θ| ≤ 4 := by
      have h1 := abs_le.mp hq
      have hs1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
      have h2 : |(2 - γ) * Real.cos (2 * θ) / Real.sin θ - Real.sin θ|
          ≤ |(2 - γ) * Real.cos (2 * θ) / Real.sin θ| + |Real.sin θ| := abs_sub _ _
      rw [abs_of_pos hsinθ] at h2
      linarith [h1.1, h1.2, h2]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hb hσpos.le

/-! ## The assembly step, given the pointwise boundary bound -/

/-- On `Iθ`, `sin(2θ)^{-η} ≥ 0`. -/
private lemma sEta_nonneg' {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  exact Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
    ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _

/-- Almost-everywhere nonnegativity on `Iθ` from pointwise nonnegativity. -/
private lemma ae_nonneg_forall_Iθ {f : ℝ → ℝ} (h : ∀ x ∈ Work.Spaces.Iθ, 0 ≤ f x) :
    0 ≤ᵐ[(volume : Measure ℝ).restrict Work.Spaces.Iθ] f := by
  rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl]
  exact (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall h)

/-- `∫_{(π/4,b]} f ≤ ∫_{Iθ} f` for nonnegative `f`. -/
private lemma setIntegral_Ioc_le_Iθ {f : ℝ → ℝ} {b : ℝ} (hb2 : b ≤ Real.pi / 2)
    (hint : IntegrableOn f Work.Spaces.Iθ) (hnn : ∀ x ∈ Work.Spaces.Iθ, 0 ≤ f x) :
    (∫ x in Set.Ioc (Real.pi / 4) b, f x) ≤ ∫ x in Work.Spaces.Iθ, f x :=
  MeasureTheory.setIntegral_mono_set hint (ae_nonneg_forall_Iθ hnn)
    (Filter.Eventually.of_forall fun x hx =>
      ⟨le_trans (by linarith [Real.pi_pos]) hx.1.le, le_trans hx.2 hb2⟩)



end

end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EllipticEst.zHardyCutDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-- **The *smooth* order `∞` of `ContDiff`** — written as an explicit term because the literal
`⊤ : ℕ∞ω` is the *analytic* order `ω` in this Mathlib (`ℕ∞ω = WithTop ℕ∞`, `∞ = ((⊤ : ℕ∞) : ℕ∞ω)`;
see `Mathlib/Analysis/Calculus/ContDiff/Defs.lean`).  Writing `⊤` where smoothness is meant gives
the analytic class, which is a trap already recorded in `Submission/Work/Stability/Cutoff.lean`. -/
abbrev smoothOrder : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)


/-- The logarithmic cutoff `ψ_k(z) = φ(log z / log k)`. -/
def psiFun (φ : ℝ → ℝ) (k : ℕ) (z : ℝ) : ℝ := φ (Real.log z / Real.log (k : ℝ))

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.H2.STFacts =====
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
set_option maxHeartbeats 1000000

/-! ## The angular function `sin (2·)` and its `D_θ`-iterates -/

/-- The angular function `θ ↦ sin(2θ)`, viewed as a function of `(z,θ)`.  It is the
multiplier relating `D_θ` and `∂_θ`. -/
def Sfun : ℝ → ℝ → ℝ := fun _ θ => Real.sin (2 * θ)

/-- The constant multiplying `sin(2θ)` in the bound for `D_θ^r (sin 2·)`. -/
def Asin : ℕ → ℝ
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 48
  | _ + 4 => 384

theorem Asin_pos (r : ℕ) : 0 < Asin r := by
  rcases r with _ | _ | _ | _ | _ <;> norm_num [Asin]

theorem hasDerivAt_sin_two (θ : ℝ) :
    HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
  have h2 : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h := (Real.hasDerivAt_sin (2 * θ)).comp θ h2
  simpa [Function.comp_def, mul_comm] using h

theorem hasDerivAt_cos_two (θ : ℝ) :
    HasDerivAt (fun θ' : ℝ => Real.cos (2 * θ')) (-(Real.sin (2 * θ)) * 2) θ := by
  have h2 : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h := (Real.hasDerivAt_cos (2 * θ)).comp θ h2
  simpa [Function.comp_def] using h

theorem hasDerivAt_two_cos_two (θ : ℝ) :
    HasDerivAt (fun θ' : ℝ => 2 * Real.cos (2 * θ')) (2 * (-(Real.sin (2 * θ)) * 2)) θ := by
  have h := (hasDerivAt_cos_two θ).const_mul (2 : ℝ)
  convert h using 1 <;> ring

theorem deriv_sin_two (θ : ℝ) :
    deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ = 2 * Real.cos (2 * θ) :=
  (hasDerivAt_sin_two θ).deriv

theorem DthIter_one_Sfun : Work.Spaces.DthIter 1 Sfun
    = fun _ θ => Real.sin (2 * θ) * (2 * Real.cos (2 * θ)) := by
  funext z θ
  show Real.sin (2 * θ) * Work.Spaces.pth Sfun z θ
      = Real.sin (2 * θ) * (2 * Real.cos (2 * θ))
  rw [show Work.Spaces.pth Sfun z θ = deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ from rfl,
    deriv_sin_two]

theorem DthIter_two_Sfun : Work.Spaces.DthIter 2 Sfun
    = fun _ θ => Real.sin (2 * θ)
        * (4 * Real.cos (2 * θ) ^ 2 - 4 * Real.sin (2 * θ) ^ 2) := by
  funext z θ
  rw [show Work.Spaces.DthIter 2 Sfun
      = Work.Spaces.Dth (Work.Spaces.DthIter 1 Sfun) from rfl, DthIter_one_Sfun]
  show Real.sin (2 * θ)
      * deriv (fun θ' : ℝ => Real.sin (2 * θ') * (2 * Real.cos (2 * θ'))) θ = _
  have hfun : (fun θ' : ℝ => Real.sin (2 * θ') * (2 * Real.cos (2 * θ')))
      = (fun θ' : ℝ => Real.sin (2 * θ')) * (fun θ' : ℝ => 2 * Real.cos (2 * θ')) := rfl
  rw [hfun, ((hasDerivAt_sin_two θ).mul (hasDerivAt_two_cos_two θ)).deriv]
  ring

theorem DthIter_three_Sfun : Work.Spaces.DthIter 3 Sfun
    = fun _ θ => Real.sin (2 * θ)
        * (8 * Real.cos (2 * θ) ^ 3 - 40 * Real.cos (2 * θ) * Real.sin (2 * θ) ^ 2) := by
  funext z θ
  rw [show Work.Spaces.DthIter 3 Sfun
      = Work.Spaces.Dth (Work.Spaces.DthIter 2 Sfun) from rfl, DthIter_two_Sfun]
  show Real.sin (2 * θ) * deriv (fun θ' : ℝ => Real.sin (2 * θ')
      * (4 * Real.cos (2 * θ') ^ 2 - 4 * Real.sin (2 * θ') ^ 2)) θ = _
  have hq : HasDerivAt (fun θ' : ℝ => 4 * Real.cos (2 * θ') ^ 2 - 4 * Real.sin (2 * θ') ^ 2)
      (-(32 * Real.cos (2 * θ) * Real.sin (2 * θ))) θ := by
    have h := (((hasDerivAt_cos_two θ).pow 2).const_mul 4).sub
      (((hasDerivAt_sin_two θ).pow 2).const_mul 4)
    convert h using 1 <;> ring
  have hfun : (fun θ' : ℝ => Real.sin (2 * θ')
        * (4 * Real.cos (2 * θ') ^ 2 - 4 * Real.sin (2 * θ') ^ 2))
      = (fun θ' : ℝ => Real.sin (2 * θ'))
        * (fun θ' : ℝ => 4 * Real.cos (2 * θ') ^ 2 - 4 * Real.sin (2 * θ') ^ 2) := rfl
  rw [hfun, ((hasDerivAt_sin_two θ).mul hq).deriv]
  ring

theorem DthIter_four_Sfun : Work.Spaces.DthIter 4 Sfun
    = fun _ θ => Real.sin (2 * θ)
        * (16 * Real.cos (2 * θ) ^ 4 - 288 * Real.cos (2 * θ) ^ 2 * Real.sin (2 * θ) ^ 2
          + 80 * Real.sin (2 * θ) ^ 4) := by
  funext z θ
  rw [show Work.Spaces.DthIter 4 Sfun
      = Work.Spaces.Dth (Work.Spaces.DthIter 3 Sfun) from rfl, DthIter_three_Sfun]
  have hQ : (fun θ' : ℝ => Real.sin (2 * θ')
        * (8 * Real.cos (2 * θ') ^ 3 - 40 * Real.cos (2 * θ') * Real.sin (2 * θ') ^ 2))
      = (fun θ' : ℝ => Real.sin (2 * θ')
        * (8 * Real.cos (2 * θ') ^ 3
          - 40 * (Real.cos (2 * θ') * Real.sin (2 * θ') ^ 2))) := by
    funext θ'; ring
  rw [hQ]
  show Real.sin (2 * θ) * deriv (fun θ' : ℝ => Real.sin (2 * θ')
      * (8 * Real.cos (2 * θ') ^ 3
        - 40 * (Real.cos (2 * θ') * Real.sin (2 * θ') ^ 2))) θ = _
  have h1 : HasDerivAt (fun θ' : ℝ => 8 * Real.cos (2 * θ') ^ 3)
      (-48 * Real.cos (2 * θ) ^ 2 * Real.sin (2 * θ)) θ := by
    convert ((hasDerivAt_cos_two θ).pow 3).const_mul (8 : ℝ) using 1
    ring
  have h2 : HasDerivAt (fun θ' : ℝ => 40 * (Real.cos (2 * θ') * Real.sin (2 * θ') ^ 2))
      (-80 * Real.sin (2 * θ) ^ 3 + 160 * Real.cos (2 * θ) ^ 2 * Real.sin (2 * θ)) θ := by
    convert ((hasDerivAt_cos_two θ).mul ((hasDerivAt_sin_two θ).pow 2)).const_mul (40 : ℝ)
      using 1
    simp only [Pi.pow_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hq : HasDerivAt (fun θ' : ℝ => 8 * Real.cos (2 * θ') ^ 3
      - 40 * (Real.cos (2 * θ') * Real.sin (2 * θ') ^ 2))
      (80 * Real.sin (2 * θ) ^ 3 - 208 * Real.cos (2 * θ) ^ 2 * Real.sin (2 * θ)) θ := by
    convert h1.sub h2 using 1
    ring
  have hfun : (fun θ' : ℝ => Real.sin (2 * θ')
        * (8 * Real.cos (2 * θ') ^ 3
          - 40 * (Real.cos (2 * θ') * Real.sin (2 * θ') ^ 2)))
      = (fun θ' : ℝ => Real.sin (2 * θ'))
        * (fun θ' : ℝ => 8 * Real.cos (2 * θ') ^ 3
            - 40 * (Real.cos (2 * θ') * Real.sin (2 * θ') ^ 2)) := rfl
  rw [hfun, ((hasDerivAt_sin_two θ).mul hq).deriv]
  ring

theorem abs_DthIter_Sfun_le (r : ℕ) (hr : r ≤ 4) (z : ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.DthIter r Sfun z θ| ≤ Asin r * Real.sin (2 * θ) := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  have hcos : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one (2 * θ)
  have hsin1 : |Real.sin (2 * θ)| ≤ 1 := Real.abs_sin_le_one (2 * θ)
  have hsc : Real.cos (2 * θ) ^ 2 + Real.sin (2 * θ) ^ 2 = 1 := by
    linarith [Real.sin_sq_add_cos_sq (2 * θ)]
  interval_cases r
  · have h0 : Work.Spaces.DthIter 0 Sfun z θ = Real.sin (2 * θ) := rfl
    rw [h0, abs_of_nonneg hs]
    have hA : Asin 0 = 1 := by norm_num [Asin]
    rw [hA]; linarith
  · rw [DthIter_one_Sfun, abs_mul, abs_of_nonneg hs]
    have h2 : |2 * Real.cos (2 * θ)| ≤ 2 := by
      rw [abs_mul, show |(2:ℝ)| = 2 by norm_num]; linarith
    have hA : Asin 1 = 2 := by norm_num [Asin]
    rw [hA]; nlinarith [hs, h2]
  · rw [DthIter_two_Sfun, abs_mul, abs_of_nonneg hs]
    have h2 : |4 * Real.cos (2 * θ) ^ 2 - 4 * Real.sin (2 * θ) ^ 2| ≤ 4 := by
      have h1 : 4 * Real.cos (2 * θ) ^ 2 - 4 * Real.sin (2 * θ) ^ 2
          = 4 * (Real.cos (2 * θ) ^ 2 - Real.sin (2 * θ) ^ 2) := by ring
      rw [h1, abs_mul, show |(4:ℝ)| = 4 by norm_num]
      have h3 : |Real.cos (2 * θ) ^ 2 - Real.sin (2 * θ) ^ 2| ≤ 1 := by
        refine abs_le.mpr ⟨?_, ?_⟩ <;> nlinarith [sq_nonneg (Real.sin (2 * θ)), hsc]
      linarith
    have hA : Asin 2 = 4 := by norm_num [Asin]
    rw [hA]; nlinarith [hs, h2]
  · rw [DthIter_three_Sfun, abs_mul, abs_of_nonneg hs]
    have h2 : |8 * Real.cos (2 * θ) ^ 3 - 40 * Real.cos (2 * θ) * Real.sin (2 * θ) ^ 2|
        ≤ 48 := by
      have h1 : 8 * Real.cos (2 * θ) ^ 3 - 40 * Real.cos (2 * θ) * Real.sin (2 * θ) ^ 2
          = 8 * (Real.cos (2 * θ) ^ 3 - 5 * (Real.cos (2 * θ) * Real.sin (2 * θ) ^ 2)) := by
        ring
      rw [h1, abs_mul, show |(8:ℝ)| = 8 by norm_num]
      have h4 : |Real.cos (2 * θ) ^ 3| ≤ 1 := by
        rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hcos
      have h5 : |Real.cos (2 * θ) * Real.sin (2 * θ) ^ 2| ≤ 1 := by
        rw [abs_mul, abs_pow]
        have hs1 : |Real.sin (2 * θ)| ^ 2 ≤ 1 :=
          pow_le_one₀ (abs_nonneg _) hsin1
        calc |Real.cos (2 * θ)| * |Real.sin (2 * θ)| ^ 2 ≤ 1 * 1 :=
              mul_le_mul hcos hs1 (by positivity) (by norm_num)
          _ = 1 := by norm_num
      have h6 : |Real.cos (2 * θ) ^ 3 - 5 * (Real.cos (2 * θ) * Real.sin (2 * θ) ^ 2)| ≤ 6 := by
        calc |Real.cos (2 * θ) ^ 3 - 5 * (Real.cos (2 * θ) * Real.sin (2 * θ) ^ 2)|
            ≤ |Real.cos (2 * θ) ^ 3|
              + |5 * (Real.cos (2 * θ) * Real.sin (2 * θ) ^ 2)| := abs_sub_le_abs_add _ _
          _ ≤ 1 + 5 := by
              refine add_le_add h4 ?_
              rw [abs_mul, show |(5:ℝ)| = 5 by norm_num]; linarith
          _ = 6 := by norm_num
      linarith
    have hA : Asin 3 = 48 := by norm_num [Asin]
    rw [hA]; nlinarith [hs, h2]
  · rw [DthIter_four_Sfun, abs_mul, abs_of_nonneg hs, Asin]
    have h4c : |Real.cos (2 * θ) ^ 4| ≤ 1 := by
      rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hcos
    have hs4 : |Real.sin (2 * θ) ^ 4| ≤ 1 := by
      rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hsin1
    have hcs : |Real.cos (2 * θ) ^ 2 * Real.sin (2 * θ) ^ 2| ≤ 1 := by
      rw [abs_mul, abs_pow, abs_pow]
      exact mul_le_one₀ (pow_le_one₀ (abs_nonneg _) hcos)
        (pow_nonneg (abs_nonneg _) 2) (pow_le_one₀ (abs_nonneg _) hsin1)
    have h2 : |16 * Real.cos (2 * θ) ^ 4 - 288 * Real.cos (2 * θ) ^ 2 * Real.sin (2 * θ) ^ 2
        + 80 * Real.sin (2 * θ) ^ 4| ≤ 384 := by
      have e1 : |(16:ℝ) * Real.cos (2 * θ) ^ 4| ≤ 16 := by
        rw [abs_mul, show |(16:ℝ)| = 16 by norm_num]; nlinarith [h4c]
      have e2 : |(288:ℝ) * Real.cos (2 * θ) ^ 2 * Real.sin (2 * θ) ^ 2| ≤ 288 := by
        rw [show (288:ℝ) * Real.cos (2 * θ) ^ 2 * Real.sin (2 * θ) ^ 2
            = 288 * (Real.cos (2 * θ) ^ 2 * Real.sin (2 * θ) ^ 2) from by ring, abs_mul,
          show |(288:ℝ)| = 288 by norm_num]
        nlinarith [hcs]
      have e3 : |(80:ℝ) * Real.sin (2 * θ) ^ 4| ≤ 80 := by
        rw [abs_mul, show |(80:ℝ)| = 80 by norm_num]; nlinarith [hs4]
      have e4 := abs_sub_le_abs_add ((16:ℝ) * Real.cos (2 * θ) ^ 4)
        ((288:ℝ) * Real.cos (2 * θ) ^ 2 * Real.sin (2 * θ) ^ 2)
      have e5 := abs_add_le ((16:ℝ) * Real.cos (2 * θ) ^ 4
          - (288:ℝ) * Real.cos (2 * θ) ^ 2 * Real.sin (2 * θ) ^ 2)
        ((80:ℝ) * Real.sin (2 * θ) ^ 4)
      linarith
    nlinarith [hs, h2]


/-! ## The local Leibniz bound for `D_θ^i` on the open interval -/


/-! ## A `z`-independent factor passes through `∂_z^j` -/

theorem pzIter_const_mul (c : ℝ → ℝ) (K : ℝ → ℝ → ℝ) (j : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter j (fun z θ => c θ * K z θ) z θ = c θ * Work.Spaces.pzIter j K z θ := by
  induction j generalizing z θ with
  | zero => rfl
  | succ j ih =>
    rw [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_succ]
    have heq : Work.Spaces.pzIter j (fun z θ => c θ * K z θ)
        = fun z θ => c θ * Work.Spaces.pzIter j K z θ :=
      funext fun z => funext fun θ => ih z θ
    rw [heq, pz_const_mul]


/-- Multiplication by `sin(2θ)` converts `D_z^c (∂_θ g)` into `D_z^c D_θ g`. -/
theorem sin_mul_dzIter_pth (g : ℝ → ℝ → ℝ) (c : ℕ) (z θ : ℝ) :
    Real.sin (2 * θ) * Work.Spaces.DzIter c (Work.Spaces.pth g) z θ
      = Work.Spaces.mixed c 1 g z θ := by
  have h1 : Work.Spaces.mixed c 1 g = Work.Spaces.DzIter c (Work.Spaces.Dth g) := by
    simp only [Work.Spaces.mixed, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero]
  rw [h1]
  exact (DzIter_const_mul_apply (fun θ => Real.sin (2 * θ)) (Work.Spaces.pth g) c z θ).symm

/-! ## Congruence and smoothness of the `D_θ`-iterates -/

theorem DthIter_congr_of_isOpen {u v : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry u) (Function.uncurry v) V) (c : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter c u))
      (Function.uncurry (Work.Spaces.DthIter c v)) V := by
  induction c with
  | zero => exact h
  | succ c ih =>
    intro y hy
    show Real.sin (2 * y.2) * Work.Spaces.pth (Work.Spaces.DthIter c u) y.1 y.2
      = Real.sin (2 * y.2) * Work.Spaces.pth (Work.Spaces.DthIter c v) y.1 y.2
    rw [Work.Spaces.pth_congr_of_isOpen hV ih hy]

theorem contDiffOn_uncurry_Dth {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ ⊤ (Function.uncurry G) V) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.Dth G)) V := by
  have hfd : ContDiffOn ℝ ⊤ (fderiv ℝ (Function.uncurry G)) V :=
    ContDiffOn.fderiv_of_isOpen h hV (by simp)
  have hev : ContDiffOn ℝ ⊤ (fun y : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) y) (0,1)) V :=
    hfd.clm_apply contDiffOn_const
  have hsin : ContDiffOn ℝ ⊤ (fun y : ℝ × ℝ => Real.sin (2 * y.2)) V :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  have hfun : ContDiffOn ℝ ⊤ (fun y : ℝ × ℝ =>
      Real.sin (2 * y.2) * (fderiv ℝ (Function.uncurry G) y) (0,1)) V := hsin.mul hev
  refine hfun.congr (fun y hy => ?_)
  have hdiff : DifferentiableAt ℝ (Function.uncurry G) y :=
    (ContDiffOn.contDiffAt h (hV.mem_nhds hy)).differentiableAt (by norm_num)
  have hderiv : deriv (fun θ' => Function.uncurry G (y.1, θ')) y.2
      = (fderiv ℝ (Function.uncurry G) y) (0,1) := Work.Spaces.deriv_slice_snd _ _ _ hdiff
  show Real.sin (2 * y.2) * deriv (fun θ' => Function.uncurry G (y.1, θ')) y.2
      = Real.sin (2 * y.2) * (fderiv ℝ (Function.uncurry G) y) (0,1)
  rw [hderiv]

theorem contDiffOn_uncurry_DthIter {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ ⊤ (Function.uncurry G) V) (c : ℕ) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.DthIter c G)) V := by
  induction c with
  | zero => simpa using h
  | succ c ih => simpa [Work.Spaces.DthIter_succ] using contDiffOn_uncurry_Dth hV ih




/-! ## `D_z`-bounds from the pointwise bounds on `z^k ∂_z^k` -/


/-! ## The pointwise bounds on the `f`-side -/




/-! ## The commutation of `D_z^b` with `D_θ^a` on an open set -/



/-! ## The angular commutator bound -/


/-! ## A `θ`-slice version of the slicing lemma -/

theorem contDiffOn_thslice_of_uncurry {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ ⊤ (Function.uncurry G) V) {z : ℝ} {W : Set ℝ} (hW : IsOpen W)
    (hz : ∀ θ' ∈ W, (z, θ') ∈ V) :
    ContDiffOn ℝ ⊤ (fun θ' => G z θ') W := by
  have hp : ContDiffOn ℝ ⊤ (fun θ' : ℝ => (z, θ')) W := by fun_prop
  have h2 := h.comp hp hz
  simpa [Function.comp_def, Function.uncurry] using h2

theorem Asin_le (r : ℕ) (hr : r ≤ 3) : Asin r ≤ 48 := by
  interval_cases r <;> norm_num [Asin]


/-! ## The mixed `f`-derivative bound -/



end Work.FTS.H2
end
end
