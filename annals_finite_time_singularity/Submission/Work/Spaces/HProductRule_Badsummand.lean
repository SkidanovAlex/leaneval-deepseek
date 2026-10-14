import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.ZCuts.zHardy_compact
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_complete
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS_EllLimOK.BoxDataH.BoxUniform
import Submission.Work.FTS_EllLimOK.EGap.integrableOn_PhiD
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.Spaces.BadTermSqBound
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.aesm_mixed_Wt_sq_prod
import Submission.Work.Spaces.bt_f_bound
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.sup_mixed_le_H4
-- ===== merged: Submission.Work.Elliptic.DivSinTermwise =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set

namespace Work.Elliptic

set_option linter.unusedVariables false

/-! ## a.e. facts on `Iθ` -/



/-! ## pointwise algebra -/




/-! ## the two slice-level estimates -/



end Work.Elliptic

namespace Work.Elliptic

/-! ## identification of the slices -/






end Work.Elliptic

namespace Work.Elliptic









end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.L12H =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false
set_option linter.unusedVariables false



end Work.Elliptic
end
end
-- ===== merged: Submission.Work.EllipticEst.ModalSolution.eFam_parseval =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.EllipticEst.ModalSolution

local notation "Iθ" => Work.Spaces.Iθ
local notation "angMeasure" => Work.FTS.EllipticEst.LevelOneAsm.angMeasure

theorem eFam_parseval (F : ℝ → ℝ → ℝ) (z : ℝ)
    (hmeas : MeasureTheory.AEStronglyMeasurable (fun θ => F z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hz : MeasureTheory.IntegrableOn (fun θ => F z θ ^ 2 * Real.cos θ) Work.Spaces.Iθ) :
    Filter.Tendsto (fun N : ℕ => ∑ m ∈ Finset.range (N + 1),
        (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 *
          (∫ θ in Work.Spaces.Iθ,
            Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ))
      Filter.atTop (nhds (∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ)) := by
  let f : ℝ → ℝ := fun θ => F z θ
  have hfm : MemLp f 2 angMeasure :=
    Work.FTS.EllipticEst.LevelOneAsm.memLp_of_hyps hmeas.aemeasurable hz
  have hb := HilbertBasis.hasSum_inner_mul_inner
    (HilbertBasis.mkOfOrthogonalEqBot (v := eFamE) eFamE_orthonormal_aux
      eFamE_span_orthogonal_eq_bot_aux)
    (MemLp.toLp f hfm) (MemLp.toLp f hfm)
  simp only [HilbertBasis.coe_mkOfOrthogonalEqBot] at hb
  -- the elementary arithmetic collapsing the two normalising square roots
  have harith : ∀ D A : ℝ, 0 < D →
      (Real.sqrt D)⁻¹ * A * ((Real.sqrt D)⁻¹ * A) = (A / D) ^ 2 * D := by
    intro D A hD
    have hsq : (Real.sqrt D)⁻¹ * (Real.sqrt D)⁻¹ = D⁻¹ := by
      rw [← mul_inv, ← sq, Real.sq_sqrt hD.le]
    rw [show (Real.sqrt D)⁻¹ * A * ((Real.sqrt D)⁻¹ * A)
          = ((Real.sqrt D)⁻¹ * (Real.sqrt D)⁻¹) * (A * A) from by ring, hsq]
    field_simp
  -- the `m`-th summand of the Hilbert-basis expansion is `(cmode m F z)² · eFamD m`
  have hterm : ∀ m : ℕ,
      inner ℝ (MemLp.toLp f hfm) (eFamE m) * inner ℝ (eFamE m) (MemLp.toLp f hfm)
        = (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * eFamD m := by
    intro m
    rw [inner_toLp_eFamE hfm m, inner_eFamE_toLp hfm m, cmode_eq_setIntegral_aux F z m]
    have hBA : (∫ θ in Iθ, eM m θ * f θ * Real.cos θ)
        = ∫ θ in Iθ, f θ * eM m θ * Real.cos θ :=
      setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
    rw [hBA]
    exact harith (eFamD m) (∫ θ in Iθ, f θ * eM m θ * Real.cos θ) (eFamD_pos m)
  have hb' : HasSum (fun m => (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * eFamD m)
      (∫ θ in Iθ, F z θ ^ 2 * Real.cos θ) := by
    have h1 := hb.congr_fun (fun m => (hterm m).symm)
    rw [Work.FTS.EllipticEst.LevelOneAsm.inner_toLp_toLp hfm hfm] at h1
    have hval : (∫ θ in Iθ, f θ * f θ * Real.cos θ)
        = ∫ θ in Iθ, F z θ ^ 2 * Real.cos θ := by
      refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
      show f θ * f θ * Real.cos θ = F z θ ^ 2 * Real.cos θ
      rw [show f θ = F z θ from rfl]
      ring
    rwa [hval] at h1
  -- the partial sums are exactly those of the statement
  have htend := hb'.tendsto_sum_nat
  have hcomp := htend.comp (Filter.tendsto_add_atTop_nat 1)
  refine Tendsto.congr' ?_ hcomp
  refine Filter.Eventually.of_forall (fun N => ?_)
  refine Finset.sum_congr rfl (fun m _ => ?_)
  simp only [eFamD, eM]

end Work.EllipticEst.ModalSolution
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.kernelJensen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Work.FTS.EllSol.PkgK5.K5c

local notation "Iθ" => Work.Spaces.Iθ
local notation "σθ" => Work.FTS.EllipticEst.thEta

/-- The `L²` Schur bound of `thWeightCmp`, in the `a.e.` form over `Iθ` (the two endpoints of
`Iθ`, where the weight `σθ` vanishes, are null). -/
theorem KJ_schur_ae {K₁ ε : ℝ}
    (hK : ∀ u ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (∫ θ in Iθ, σθ θ * KJ ε θ u) ≤ K₁ * σθ u) :
    ∀ᵐ s ∂(volume.restrict Iθ), (∫ θ in Iθ, σθ θ * KJ ε θ s) ≤ K₁ * σθ s := by
  have h1 : ∀ᵐ s ∂(volume.restrict (Set.Ioo 0 (Real.pi / 2))),
      (∫ θ in Iθ, σθ θ * KJ ε θ s) ≤ K₁ * σθ s :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo hK
  have hμ : volume.restrict Iθ = volume.restrict (Set.Ioo 0 (Real.pi / 2)) :=
    restrict_Iθ_eq_restrict_Ioo
  rw [← hμ] at h1
  exact h1

theorem kernelJensen : ∃ K : ℝ, 0 < K ∧ ∀ (g : ℝ → ℝ), MeasureTheory.IntegrableOn (fun s : ℝ => g s ^ 2 * Work.FTS.EllipticEst.thEta s) Work.Spaces.Iθ → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ * (∫ s in Work.Spaces.Iθ, (Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ - s) + Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + s) + Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + s - Real.pi)) * g s) ^ 2) ≤ K * ∫ s in Work.Spaces.Iθ, g s ^ 2 * Work.FTS.EllipticEst.thEta s := by
  obtain ⟨K₁, hK₁pos, hK₁⟩ := Work.FTS.EllSol.K5cAux.thWeightCmp
  refine ⟨3 * K₁, by positivity, ?_⟩
  intro g hg ε hε hε2
  change (∫ θ in Iθ, σθ θ * (∫ s in Iθ, KJ ε θ s * g s) ^ 2)
      ≤ (3 * K₁) * ∫ s in Iθ, g s ^ 2 * σθ s
  have hg2int : IntegrableOn (fun s : ℝ => g s ^ 2) Iθ := integrableOn_sq_of_integrableOn hg
  obtain ⟨hswap_eq, hswap_i1, hswap_i2⟩ := kernelSwap (g := g) hε hg2int
  -- the pointwise bound, integrated
  have hA : IntegrableOn (fun θ : ℝ => 3 * (σθ θ * ∫ s in Iθ, KJ ε θ s * g s ^ 2)) Iθ :=
    hswap_i1.const_mul 3
  have hmono : (∫ θ in Iθ, σθ θ * (∫ s in Iθ, KJ ε θ s * g s) ^ 2)
      ≤ ∫ θ in Iθ, 3 * (σθ θ * ∫ s in Iθ, KJ ε θ s * g s ^ 2) := by
    refine MeasureTheory.integral_mono_of_nonneg (f := fun θ : ℝ =>
        σθ θ * (∫ s in Iθ, KJ ε θ s * g s) ^ 2)
      (g := fun θ : ℝ => 3 * (σθ θ * ∫ s in Iθ, KJ ε θ s * g s ^ 2)) ?_ hA ?_
    · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => mul_nonneg (Work.FTS.EllipticEst.thEta_nonneg hθ) (sq_nonneg _))
    · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
        have hpt := KJ_pointwise (g := g) (ε := ε) (θ := θ) hε hg hθ
        have hσ : 0 ≤ σθ θ := Work.FTS.EllipticEst.thEta_nonneg hθ
        calc σθ θ * (∫ s in Iθ, KJ ε θ s * g s) ^ 2
            ≤ σθ θ * (3 * ∫ s in Iθ, KJ ε θ s * g s ^ 2) :=
              mul_le_mul_of_nonneg_left hpt hσ
          _ = 3 * (σθ θ * ∫ s in Iθ, KJ ε θ s * g s ^ 2) := by ring)
  -- pull out the constant and swap the two integrals
  have hc1 : (∫ θ in Iθ, 3 * (σθ θ * ∫ s in Iθ, KJ ε θ s * g s ^ 2))
      = 3 * ∫ θ in Iθ, σθ θ * ∫ s in Iθ, KJ ε θ s * g s ^ 2 :=
    MeasureTheory.integral_const_mul 3 _
  -- the Schur bound, a.e. in `s`
  have hschur : ∀ᵐ s ∂(volume.restrict Iθ), (∫ θ in Iθ, σθ θ * KJ ε θ s) ≤ K₁ * σθ s :=
    KJ_schur_ae (K₁ := K₁) (ε := ε) (fun u hu => hK₁ ε u hε hε2 hu)
  have hKσ_int : IntegrableOn (fun s : ℝ => g s ^ 2 * (K₁ * σθ s)) Iθ :=
    MeasureTheory.Integrable.congr (hg.const_mul K₁) (Filter.Eventually.of_forall (fun s => by
      show K₁ * (g s ^ 2 * σθ s) = g s ^ 2 * (K₁ * σθ s)
      ring))
  have hmono2 : (∫ s in Iθ, g s ^ 2 * (∫ θ in Iθ, σθ θ * KJ ε θ s))
      ≤ ∫ s in Iθ, g s ^ 2 * (K₁ * σθ s) := by
    refine MeasureTheory.integral_mono_ae hswap_i2 hKσ_int ?_
    filter_upwards [hschur] with s hs
    exact mul_le_mul_of_nonneg_left hs (sq_nonneg (g s))
  have hKσ_eq : (∫ s in Iθ, g s ^ 2 * (K₁ * σθ s)) = K₁ * ∫ s in Iθ, g s ^ 2 * σθ s := by
    have he : (fun s : ℝ => g s ^ 2 * (K₁ * σθ s))
        = fun s : ℝ => K₁ * (g s ^ 2 * σθ s) := by
      funext s; ring
    rw [he, MeasureTheory.integral_const_mul]
  calc (∫ θ in Iθ, σθ θ * (∫ s in Iθ, KJ ε θ s * g s) ^ 2)
      ≤ ∫ θ in Iθ, 3 * (σθ θ * ∫ s in Iθ, KJ ε θ s * g s ^ 2) := hmono
    _ = 3 * ∫ θ in Iθ, σθ θ * ∫ s in Iθ, KJ ε θ s * g s ^ 2 := hc1
    _ = 3 * ∫ s in Iθ, g s ^ 2 * (∫ θ in Iθ, σθ θ * KJ ε θ s) := by rw [hswap_eq]
    _ ≤ 3 * ∫ s in Iθ, g s ^ 2 * (K₁ * σθ s) := by
          exact mul_le_mul_of_nonneg_left hmono2 (by norm_num)
    _ = 3 * (K₁ * ∫ s in Iθ, g s ^ 2 * σθ s) := by rw [hKσ_eq]
    _ = (3 * K₁) * ∫ s in Iθ, g s ^ 2 * σθ s := by ring

end Work.FTS.EllSol.EllPkgAux
end
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.radialAuxHk =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Radial profiles vs. their `sin (2θ)`-multiples: the `H^k`-integrands

Part 4 of the proof of `Work.FTS.EllSol.PkgK5.radialHkNorm_le_sinMul`: the evaluation of the
`H^k`-integrand of a radial profile and of its `sin(2θ)`-multiple, and of the corresponding
`θ`-integrals.
-/

namespace Work.FTS.EllSol.PkgK5

namespace Radial

theorem HkIntegrand_radial (α : ℝ) (k : ℕ) (Λ : ℝ → ℝ)
    (hΛ : ∀ n : ℕ, ContDiffOn ℝ n Λ (Set.Ioi 0)) (z θ : ℝ) (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α k (fun z θ => Λ z) z θ
      = Phi k Λ z * Real.sin (2 * θ) ^ (-Work.Spaces.eta) := by
  have heta : Work.Spaces.eta ≠ 0 := by norm_num [Work.Spaces.eta]
  rw [Work.Spaces.HkIntegrand]
  have hzsum : (∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i (fun z θ => Λ z) z θ
        * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      = Phi k Λ z * Real.sin (2 * θ) ^ (-Work.Spaces.eta) := by
    rw [Phi, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [DzIter_radial Λ i hz θ,
      Work.Spaces.sq_mul_div_rpow (RIter i Λ z) (Work.Spaces.w z) (Real.sin (2 * θ))
        Work.Spaces.eta (sin_two_nonneg hθ) heta]
    ring
  have hmix : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k then
        (Work.Spaces.mixed j i (fun z θ => Λ z) z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) = 0 := by
    refine Finset.sum_eq_zero (fun i hi => Finset.sum_eq_zero (fun j hj => ?_))
    split_ifs with h
    · rw [mixed_radial_zero Λ j i h.1 z θ]; ring
    · rfl
  rw [hzsum, hmix, add_zero]

theorem HkIntegrand_sinMul (α : ℝ) (k : ℕ) (Λ : ℝ → ℝ) (hα : 0 < α)
    (hΛ : ∀ n : ℕ, ContDiffOn ℝ n Λ (Set.Ioi 0)) (z θ : ℝ) (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α k (fun z θ => Λ z * Real.sin (2 * θ)) z θ
      = Phi k Λ z * Real.sin (2 * θ) ^ (2 - Work.Spaces.eta)
        + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then
              (RIter j Λ z * Work.Spaces.w z) ^ 2
                * ((Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ) ^ 2
                    * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)))
             else 0) := by
  have hgam : Work.Spaces.gam α ≠ 0 := by
    rw [Work.Spaces.gam]; intro h; linarith
  have heta : Work.Spaces.eta ≠ 2 := by norm_num [Work.Spaces.eta]
  have heta0 : Work.Spaces.eta ≠ 0 := by norm_num [Work.Spaces.eta]
  have hS : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθ
  have hhalf : (Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) := rpow_neg_half_sq _ hgam hS
  rw [Work.Spaces.HkIntegrand]
  have hzsum : (∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i (fun z θ => Λ z * Real.sin (2 * θ)) z θ
        * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      = Phi k Λ z * Real.sin (2 * θ) ^ (2 - Work.Spaces.eta) := by
    rw [Phi, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [DzIter_mul_theta Λ hΛ (fun θ : ℝ => Real.sin (2 * θ)) i hz θ,
      Work.Spaces.sq_mul_div_rpow (RIter i Λ z * Real.sin (2 * θ)) (Work.Spaces.w z) (Real.sin (2 * θ))
        Work.Spaces.eta hS heta0]
    calc (RIter i Λ z * Real.sin (2 * θ)) ^ 2 * (Work.Spaces.w z) ^ 2
          * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))
        = (RIter i Λ z * Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))) := by ring
      _ = (RIter i Λ z * Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (2 - Work.Spaces.eta) := by
          rw [sq_mul_rpow_neg Work.Spaces.eta heta hS]
  have hmix : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k then
        (Work.Spaces.mixed j i (fun z θ => Λ z * Real.sin (2 * θ)) z θ
          * Work.Spaces.Wt α z θ) ^ 2 else 0))
      = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
            (RIter j Λ z * Work.Spaces.w z) ^ 2
              * ((Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ) ^ 2
                  * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)))
           else 0) := by
    refine Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => ?_))
    by_cases h : 1 ≤ i ∧ i + j ≤ k
    · rw [if_pos h, if_pos h, mixed_sinMul Λ hΛ j i hz θ]
      simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
      calc (RIter j Λ z * Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ
            * (Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2)))) ^ 2
          = ((RIter j Λ z * Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ) ^ 2)
              * ((Work.Spaces.w z) ^ 2
                * (Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2))) ^ 2) := by ring
        _ = (RIter j Λ z * Work.Spaces.w z) ^ 2
              * ((Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ) ^ 2
                  * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))) := by
              rw [hhalf]; ring
    · rw [if_neg h, if_neg h]
  rw [hzsum, hmix]

/-- The `θ`-integral of the `H^k`-integrand of the radial function `Λ`. -/
theorem thetaIntegral_radial (α : ℝ) (k : ℕ) (Λ : ℝ → ℝ)
    (hΛ : ∀ n : ℕ, ContDiffOn ℝ n Λ (Set.Ioi 0)) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (fun z θ => Λ z) z θ)
      = Phi k Λ z * Aeta := by
  rw [show (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (fun z θ => Λ z) z θ)
      = ∫ θ in Work.Spaces.Iθ, Phi k Λ z * Real.sin (2 * θ) ^ (-Work.Spaces.eta) from
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      (fun θ hθ => HkIntegrand_radial α k Λ hΛ z θ hz hθ)]
  rw [MeasureTheory.integral_const_mul]
  rfl

/-- The `θ`-integral of the `H^k`-integrand of `(z,θ) ↦ Λ z · sin(2θ)`. -/
theorem thetaIntegral_sinMul (α : ℝ) (k : ℕ) (Λ : ℝ → ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hΛ : ∀ n : ℕ, ContDiffOn ℝ n Λ (Set.Ioi 0)) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (fun z θ => Λ z * Real.sin (2 * θ)) z θ)
      = Phi k Λ z * Aeta2 + W α k Λ z := by
  obtain ⟨A, hApos, hAbound⟩ := Work.FTS.EllipticEst.Lop_iter_sin_bound k
  have heta1 : -1 < 2 - Work.Spaces.eta := by norm_num [Work.Spaces.eta]
  have heta2 : 2 - Work.Spaces.eta ≤ 2 := by norm_num [Work.Spaces.eta]
  rw [show (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => Λ z * Real.sin (2 * θ)) z θ)
      = ∫ θ in Work.Spaces.Iθ, (Phi k Λ z * Real.sin (2 * θ) ^ (2 - Work.Spaces.eta)
          + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k then
                (RIter j Λ z * Work.Spaces.w z) ^ 2
                  * ((Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ) ^ 2
                      * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)))
               else 0)) from
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      (fun θ hθ => HkIntegrand_sinMul α k Λ hα hΛ z θ hz hθ)]
  have hInt1 : Integrable (fun θ : ℝ => Phi k Λ z * Real.sin (2 * θ) ^ (2 - Work.Spaces.eta))
      (volume.restrict Work.Spaces.Iθ) := (integrable_sin_rpow heta1 heta2).const_mul _
  have hterm : ∀ i j : ℕ, Integrable (fun θ : ℝ =>
      (if 1 ≤ i ∧ i + j ≤ k then
        (RIter j Λ z * Work.Spaces.w z) ^ 2
          * ((Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ) ^ 2
              * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)))
       else 0)) (volume.restrict Work.Spaces.Iθ) := by
    intro i j
    by_cases h : 1 ≤ i ∧ i + j ≤ k
    · have hfun : (fun θ : ℝ => (if 1 ≤ i ∧ i + j ≤ k then
          (RIter j Λ z * Work.Spaces.w z) ^ 2
            * ((Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ) ^ 2
                * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)))
         else 0))
          = (fun θ : ℝ => (RIter j Λ z * Work.Spaces.w z) ^ 2
            * ((Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ) ^ 2
                * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)))) := by
        funext θ; rw [if_pos h]
      rw [hfun]
      exact (integrable_angCoef hα hα1 hApos.le (fun θ hθ => hAbound i (by omega) θ hθ)).const_mul _
    · have hfun : (fun θ : ℝ => (if 1 ≤ i ∧ i + j ≤ k then
          (RIter j Λ z * Work.Spaces.w z) ^ 2
            * ((Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ) ^ 2
                * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)))
         else 0)) = (fun _ : ℝ => (0 : ℝ)) := by
        funext θ; rw [if_neg h]
      rw [hfun]
      exact integrable_zero _ _ _
  have hInt2 : Integrable (fun θ : ℝ =>
      ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then
          (RIter j Λ z * Work.Spaces.w z) ^ 2
            * ((Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ) ^ 2
                * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)))
         else 0)) (volume.restrict Work.Spaces.Iθ) :=
    integrable_finsetSum _ (fun i hi => integrable_finsetSum _ (fun j hj => hterm i j))
  rw [MeasureTheory.integral_add hInt1 hInt2]
  have hsum : (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range (k + 1),
        ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then
          (RIter j Λ z * Work.Spaces.w z) ^ 2
            * ((Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ) ^ 2
                * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)))
         else 0))
      = W α k Λ z := by
    rw [MeasureTheory.integral_finsetSum _
      (fun i hi => integrable_finsetSum _ (fun j hj => hterm i j))]
    rw [show W α k Λ z = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then
          (RIter j Λ z * Work.Spaces.w z) ^ 2 * Bcoef α i else 0) from rfl]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [MeasureTheory.integral_finsetSum _ (fun j hj => hterm i j)]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    by_cases h : 1 ≤ i ∧ i + j ≤ k
    · have hfun : (fun θ : ℝ => (if 1 ≤ i ∧ i + j ≤ k then
          (RIter j Λ z * Work.Spaces.w z) ^ 2
            * ((Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ) ^ 2
                * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)))
         else 0))
          = (fun θ : ℝ => (RIter j Λ z * Work.Spaces.w z) ^ 2
            * ((Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ) ^ 2
                * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)))) := by
        funext θ; rw [if_pos h]
      rw [hfun, MeasureTheory.integral_const_mul, if_pos h]
      rfl
    · have hfun : (fun θ : ℝ => (if 1 ≤ i ∧ i + j ≤ k then
          (RIter j Λ z * Work.Spaces.w z) ^ 2
            * ((Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ) ^ 2
                * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)))
         else 0)) = (fun _ : ℝ => (0 : ℝ)) := by
        funext θ; rw [if_neg h]
      rw [hfun, if_neg h]
      exact MeasureTheory.integral_zero _ _
  rw [MeasureTheory.integral_const_mul, hsum]
  rfl

end Radial

end Work.FTS.EllSol.PkgK5
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.slicePairIneqFluxFree =====
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
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Derivative facts for the angular weight `wS η θ = sin(2θ)^{-η}` -/






/-! ## The integration by parts, the sign of the flux boundary term, and the limit -/


/-! ## The cross term of the sharp Hardy inequality -/


/-! ## The target -/


end Work.FTS.EllipticEst.AngAWeak
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.slice_ibp_light_closed =====
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

/-! ## Helpers: the within-derivatives on `Iθ` and their continuity on the open interval -/





/-- The fact that `θ ↦ sin(2θ)` is continuous on the open angular interval. -/
private lemma continuousOn_sin_two :
    ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  Real.continuous_sin.comp_continuousOn
    ((continuous_const : Continuous fun _ : ℝ => (2 : ℝ)).mul continuous_id).continuousOn

/-! ## The analytic side conditions of `slice_ibp_light`:

integrability of the five integrands and vanishing of the two boundary products. -/




end Work.FTS.EllipticEst.TT
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.zHardy_sq_le =====
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

/-! ## The cutoff and its elementary properties -/

/-- The cutoff `zCut φ k` is `psiFun φ k` on `(0,∞)` and `0` on `(-∞,0]`; the second
convention makes `h = zCut φ k · g` vanish identically on `(-∞,1/k²]`, as required by the
support hypothesis of the compactly supported Hardy inequality. -/
def zCut (φ : ℝ → ℝ) (k : ℕ) (z : ℝ) : ℝ := if 0 < z then psiFun φ k z else 0

/-- A function which vanishes on a neighbourhood of `x` has derivative `0` at `x`. -/
theorem deriv_eq_zero_of_eventuallyEq_zero {f : ℝ → ℝ} {x : ℝ} (h : f =ᶠ[𝓝 x] 0) :
    deriv f x = 0 :=
  ((hasDerivAt_const (x := x) (c := 0)).congr_of_eventuallyEq h).deriv




/-- The derivative of a `C^∞` function on `(0,∞)` is again `C^∞` there.  The order is the
*smooth* order `smoothOrder = ∞` (the literal `⊤` of `ContDiff` is the analytic order). -/
theorem contDiffOn_deriv_of_isOpen {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ smoothOrder f (Set.Ioi 0)) :
    ContDiffOn ℝ smoothOrder (deriv f) (Set.Ioi 0) :=
  hf.deriv_of_isOpen isOpen_Ioi (by simp [smoothOrder])

/-- The square of the weight `w(z) = (1+z)²/z²` is continuous on `(0,∞)`. -/
theorem continuousOn_w_sq : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  have h : ContinuousOn (fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2) (Set.Ioi 0) := by
    refine ContinuousOn.pow (ContinuousOn.div (by fun_prop) (by fun_prop) ?_) 2
    intro z hz
    exact pow_ne_zero 2 (ne_of_gt hz)
  simpa only [Work.Spaces.w] using h


/-! ## The radial weighted Hardy inequality

The boundary terms of `zHardy_pointwise` are killed here by replacing `g` with the
*logarithmically* localised functions `zCut φ k · g` (`H` below): those are compactly supported
inside `(0,∞)`, so that for them the flux `zFlux` has compact support and `∫ (zFlux)'(z) dz = 0`
*exactly*, with no boundary limit and no sequence of "good" points.  The price is the
commutator of the cutoff with `z ∂_z`, controlled by `|z ψ'_k| ≤ K / log k → 0`
(`ZCuts.zCut_props`), and one passes `k → ∞` by dominated convergence (dominated by `w² g²`,
which is integrable by hypothesis).  The constant obtained is `8` (`4` from the pointwise
inequality times `2` from `(a+b)² ≤ 2a² + 2b²`). -/


end Work.FTS.EllipticEst

end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP26.psiB_Lop_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP26

/-- **The angular core for row 26**: the `Lop`-iterates of `θ ↦ sin²θ · Γ(θ)` are bounded by
`D·Γ(θ)·(sin²(2θ) + α)`, uniformly in `0 < α ≤ 1` and `1 ≤ i ≤ 4`.

Recipe (verbatim analogue of `Work.Construction.H4N_GammaTerm_Lop_bound`, whose angular
factor is `ψ = c2m·Γ` instead; the machinery `glop_Gam_deriv`, `glop_comp_cos_sq`, `glop_step`
and the tools `deriv_mono5`, `abs_mono5_le` are all in the tree): on `θ ∈ (0,π/2)` put
`x = cos²θ`.  Then `sin²θ = 1 - x`, `4x(1-x) = sin²(2θ)`, and for smooth `g`
`Lop (Γ·(g ∘ cos²)) = Γ·((-4x(1-x))·g' + (2α/3)(3x-2)·g) ∘ cos²` (uses
`D_θΓ = (α/3)(6cos²θ-4)Γ`).  Hence with the polynomials `B₀ = 1-x`,
`B_{i+1} = -4x(1-x)B_i' + (2α/3)(3x-2)B_i` one has
`Lop^[i] (sin²θ Γ) = Γ(θ)·B_i(cos²θ, α)` for `i ≤ 4`, and the explicit `B_i`
(`i = 1..4`, in the split form `4x(1-x)·V_i + ∑_{k≥1}(α/3)^k P_{i,k}`) are
```
B₁ = 4x(1-x)·(1)                              + (α/3)·(-4 + 10x - 6x²)
B₂ = 4x(1-x)·(-4 + 8x)                        + (α/3)·(-56x + 128x² - 72x³)
                                              + (α/3)²·(16 - 64x + 84x² - 36x³)
B₃ = 4x(1-x)·(16 - 96x + 96x²)                + (α/3)·(288x - 1536x² + 2304x³ - 1056x⁴)
                                              + (α/3)²·(480x - 1776x² + 2160x³ - 864x⁴)
                                              + (α/3)³·(-64 + 352x - 720x² + 648x³ - 216x⁴)
B₄ = 4x(1-x)·(-64 + 896x - 2304x² + 1536x³)   + (α/3)·(-1408x + 15616x² - 45696x³ + 50688x⁴ - 19200x⁵)
                                              + (α/3)²·(-3072x + 24000x² - 58560x³ + 57792x⁴ - 20160x⁵)
                                              + (α/3)³·(-3328x + 17152x² - 32832x³ + 27648x⁴ - 8640x⁵)
                                              + (α/3)⁴·(256 - 1792x + 4992x² - 6912x³ + 4752x⁴ - 1296x⁵)
```
(`B₁` is also `= 4x(1-x) + (2α/3)(3x-2)(1-x)`, the direct computation).  Then
`|B_i(x,α)| ≤ 4x(1-x)·(coefficient sum of V_i) + α·∑_{k≥1}3^{-k}(coefficient sum of P_{i,k})`
(for `0 ≤ x ≤ 1`, `0 < α ≤ 1`, using `(α/3)^k ≤ α/3^k`), and the coefficient sums are
`≤ 4800` and `≤ 76000`, so `D = 10⁵` works. -/
theorem psiB_Lop_bound :
    ∃ D : ℝ, 0 < D ∧ ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ i : ℕ, 1 ≤ i → i ≤ 4 →
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        |(Work.Spaces.Lop^[i] (fun θ : ℝ => Real.sin θ ^ 2 * Work.Spaces.Gam α θ)) θ|
          ≤ D * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α) := by
  refine ⟨10 ^ 6, by norm_num, ?_⟩
  intro α hα hα1 i hi1 hi4 θ hθ
  -- `Γ` is nonnegative, so it factors out of the absolute value
  have hGam0 : 0 ≤ Work.Spaces.Gam α θ :=
    (Work.Spaces.Gam_bounds α θ hα (Set.Ioo_subset_Icc_self hθ)).1
  -- the substitution `x = cos²θ` lies in `[0,1]`
  have hxc : Real.cos θ ^ 2 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨sq_nonneg _, by linarith [Real.cos_sq_le_one θ]⟩
  -- `4x(1-x) = sin²(2θ)`
  have hsin2 : 4 * Real.cos θ ^ 2 * (1 - Real.cos θ ^ 2) = Real.sin (2 * θ) ^ 2 := by
    rw [Real.sin_two_mul]
    ring_nf
    rw [Real.sin_sq]
    ring
  have hb := Bang_bound i hi1 hi4 (Real.cos θ ^ 2) α hxc hα hα1
  rw [bang_iter α hα i hi4 θ hθ]
  calc |Work.Spaces.Gam α θ * Bang i (Real.cos θ ^ 2) α|
      = Work.Spaces.Gam α θ * |Bang i (Real.cos θ ^ 2) α| := by
        rw [abs_mul, abs_of_nonneg hGam0]
    _ ≤ Work.Spaces.Gam α θ
          * (10 ^ 6 * (α + 4 * Real.cos θ ^ 2 * (1 - Real.cos θ ^ 2))) :=
        mul_le_mul_of_nonneg_left hb hGam0
    _ = 10 ^ 6 * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α) := by
        rw [hsin2]
        ring

end Work.FTS.Nonlinear.Pieces.RNP26
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.Atoms.DzIter_SR0_le5 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.H5.Atoms

open Work.FTS.StrongEps.ClassCRHS

/-! ## The level-`5` jet of the radial profile `SR0 z = 2z²/(1+z)³`

`AkRhoJetBasic.akJet4` computes the fourth `D_z`-iterate of `z ↦ 2z²/(1+z)³`; here we
differentiate it once more to obtain the fifth, and bound the result.  The constant is read
off from the coefficients of the numerator of the fifth iterate:

`D_z^5 SR0 = 2z²·(-z⁵ + 88z⁴ - 718z³ + 1208z² - 473z + 32)/(1+z)⁸`,
and `|z^k| ≤ (1+z)^5` for `z ≥ 0`, `k ≤ 5`, whence the numerator is dominated by
`2·2520·(1+z)^5 = 5040·(1+z)^5`, i.e. `|D_z^5 SR0| ≤ 5040·z²/(1+z)³`. -/

/-- The fifth `z∂_z`-iterate of the profile `z ↦ 2z²/(1+z)³`:
`D_z^5 (2z²/(1+z)³) = 2z²(-z⁵+88z⁴-718z³+1208z²-473z+32)/(1+z)^8`.

Obtained by differentiating the order-`4` formula `AkRhoJetBasic.akJet4`:
the derivative of `z²(2z⁴-82z³+342z²-262z+32)/(1+z)^7` is
`2z(-z⁵+88z⁴-718z³+1208z²-473z+32)/(1+z)^8`. -/
lemma SR0_akJet5 {z : ℝ} (hz : z ≠ -1) (θ : ℝ) :
    Work.Spaces.DzIter 5 (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z θ
      = 2 * z ^ 2 * (-z ^ 5 + 88 * z ^ 4 - 718 * z ^ 3 + 1208 * z ^ 2 - 473 * z + 32)
          / (1 + z) ^ 8 := by
  have hh : (1 : ℝ) + z ≠ 0 := by intro h; exact hz (by linarith)
  rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
  have hev : (fun z' : ℝ => Work.Spaces.DzIter 4 (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z' θ)
      =ᶠ[nhds z] fun z' : ℝ =>
          z' ^ 2 * (2 * z' ^ 4 - 82 * z' ^ 3 + 342 * z' ^ 2 - 262 * z' + 32) / (1 + z') ^ 7 := by
    filter_upwards [isOpen_ne.mem_nhds hz] with z' hz'
    exact Work.FTS.NonlinRows.AkRhoJetBasic.akJet4 hz' θ
  rw [hev.deriv_eq]
  have hd : HasDerivAt
      (fun z' : ℝ => z' ^ 2 * (2 * z' ^ 4 - 82 * z' ^ 3 + 342 * z' ^ 2 - 262 * z' + 32)
        / (1 + z') ^ 7)
      (2 * z * (-z ^ 5 + 88 * z ^ 4 - 718 * z ^ 3 + 1208 * z ^ 2 - 473 * z + 32)
        / (1 + z) ^ 8) z := by
    have hA : HasDerivAt (fun y : ℝ => 2 * y ^ 4) (2 * (4 * z ^ (4 - 1))) z :=
      (hasDerivAt_pow 4 z).const_mul 2
    have hB : HasDerivAt (fun y : ℝ => 82 * y ^ 3) (82 * (3 * z ^ (3 - 1))) z :=
      (hasDerivAt_pow 3 z).const_mul 82
    have hC : HasDerivAt (fun y : ℝ => 342 * y ^ 2) (342 * (2 * z ^ (2 - 1))) z :=
      (hasDerivAt_pow 2 z).const_mul 342
    have hD : HasDerivAt (fun y : ℝ => 262 * y) (262 * 1) z := by
      simpa using (hasDerivAt_id z).const_mul (262 : ℝ)
    have hq : HasDerivAt (fun y : ℝ => 2 * y ^ 4 - 82 * y ^ 3 + 342 * y ^ 2 - 262 * y + 32)
        (8 * z ^ 3 - 246 * z ^ 2 + 684 * z - 262) z := by
      have hc := (((hA.sub hB).add hC).sub hD).add_const 32
      convert hc using 1
      ring
    have hp : HasDerivAt (fun y : ℝ => y ^ 2) (2 * z) z := by
      simpa using hasDerivAt_pow 2 z
    have h1 : HasDerivAt
        (fun z' : ℝ => z' ^ 2 * (2 * z' ^ 4 - 82 * z' ^ 3 + 342 * z' ^ 2 - 262 * z' + 32))
        (12 * z ^ 5 - 410 * z ^ 4 + 1368 * z ^ 3 - 786 * z ^ 2 + 64 * z) z := by
      have h' := hp.mul hq
      convert h' using 1
      ring
    have h2 : HasDerivAt (fun z' : ℝ => (1 + z') ^ 7) (7 * (1 + z) ^ 6) z := by
      simpa using Work.FTS.NonlinRows.AkRhoJetBasic.hasDerivAt_one_add_pow 7 z
    have h3 : (1 + z) ^ 7 ≠ 0 := pow_ne_zero 7 hh
    have hdd := h1.div h2 h3
    convert hdd using 1
    · field_simp
      ring
  rw [hd.deriv]
  ring

/-- The numerator of the fifth iterate is dominated by `2520·(1+z)^5` for `z ≥ 0`
(the coefficient `ℓ¹`-norm of `-z⁵+88z⁴-718z³+1208z²-473z+32` is `2520`). -/
lemma SR0_num_le (z : ℝ) (hz : 0 ≤ z) :
    |(-z ^ 5 + 88 * z ^ 4 - 718 * z ^ 3 + 1208 * z ^ 2 - 473 * z + 32)|
      ≤ 2520 * (1 + z) ^ 5 := by
  have hzp : (1 : ℝ) ≤ 1 + z := by linarith
  have hzle : z ≤ 1 + z := by linarith
  have h5 : z ^ 5 ≤ (1 + z) ^ 5 := pow_le_pow_left₀ hz hzle 5
  have h4 : (1 + z) ^ 4 ≤ (1 + z) ^ 5 := pow_le_pow_right₀ hzp (by norm_num)
  have h3 : (1 + z) ^ 3 ≤ (1 + z) ^ 5 := pow_le_pow_right₀ hzp (by norm_num)
  have h2 : (1 + z) ^ 2 ≤ (1 + z) ^ 5 := pow_le_pow_right₀ hzp (by norm_num)
  have hone : (1 : ℝ) ≤ (1 + z) ^ 5 := one_le_pow₀ hzp
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg z, pow_nonneg hz 3, pow_nonneg hz 4, pow_nonneg hz 5]

/-- The quotient form of the level-`5` bound: a numerator dominated by `2520·(1+z)^5`
gives `|2z²·Q/(1+z)^8| ≤ 5040·z²/(1+z)³`. -/
lemma SR0_quot_le {z Q : ℝ} (hz : 0 ≤ z) (hQ : |Q| ≤ 2520 * (1 + z) ^ 5) :
    |2 * z ^ 2 * Q / (1 + z) ^ 8| ≤ 5040 * z ^ 2 / (1 + z) ^ 3 := by
  have hden8 : (0 : ℝ) < (1 + z) ^ 8 := by positivity
  have hden3 : (0 : ℝ) < (1 + z) ^ 3 := by positivity
  have hnum : |2 * z ^ 2 * Q| ≤ 5040 * z ^ 2 * (1 + z) ^ 5 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg (sq_nonneg z)]
    nlinarith [hQ, sq_nonneg z, pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + z) 5]
  rw [abs_div, abs_of_pos hden8]
  rw [div_le_div_iff₀ hden8 hden3]
  calc |2 * z ^ 2 * Q| * (1 + z) ^ 3
      ≤ (5040 * z ^ 2 * (1 + z) ^ 5) * (1 + z) ^ 3 :=
        mul_le_mul_of_nonneg_right hnum (by positivity)
    _ = 5040 * z ^ 2 * (1 + z) ^ 8 := by ring

/-- The `i = 5` case of the radial bound: `|D_z^5 SR0 z| ≤ 5040·z²/(1+z)³` for `z ≥ 0`. -/
lemma SR0_DzdIter_five_bound (z : ℝ) (hz : 0 ≤ z) :
    |Work.Elliptic.DzdIter 5 SR0 z| ≤ 5040 * z ^ 2 / (1 + z) ^ 3 := by
  have hz1 : z ≠ -1 := by linarith
  rw [← Work.Elliptic.DzIter_rad SR0 5 z 0]
  change |Work.Spaces.DzIter 5 (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z 0|
      ≤ 5040 * z ^ 2 / (1 + z) ^ 3
  rw [SR0_akJet5 hz1 0]
  exact SR0_quot_le hz (SR0_num_le z hz)

/-- The level-`5` radial iterates of `SR0 z = 2z²/(1+z)³` are bounded by `C·z²/(1+z)³`:
`D_z^i SR0 = z²·P_i(z)/(1+z)^(3+i)` with `deg P_i = i`, so `|D_z^i SR0 z| ≤ (Σ|c|)·z²/(1+z)³`.
(The level-`4` version with `C = 720` is `ClassCRHS.DzBoundR0`; this adds the `i = 5` case,
where `D_z^5 SR0 = z²(-z^5 + 88z^4 - 718z^3 + 1208z^2 - 473z + 32)·2/(1+z)^8`.) -/
theorem DzIter_SR0_le5 : ∃ C : ℝ, 0 < C ∧ ∀ i : ℕ, i ≤ 5 → ∀ z : ℝ, 0 ≤ z →
    |Work.Elliptic.DzdIter i Work.FTS.StrongEps.ClassCRHS.SR0 z| ≤ C * z ^ 2 / (1 + z) ^ 3 := by
  obtain ⟨C₀, hC₀, hb₀⟩ := Work.FTS.StrongEps.ClassCRHS.DzBoundR0
  refine ⟨max C₀ 5040, lt_max_of_lt_left hC₀, fun i hi z hz => ?_⟩
  have h1 : (0 : ℝ) < 1 + z := by linarith
  have hden : (0 : ℝ) ≤ (1 + z) ^ 3 := by positivity
  have hz2 : (0 : ℝ) ≤ z ^ 2 := sq_nonneg z
  by_cases h4 : i ≤ 4
  · exact le_trans (hb₀ i h4 z hz)
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left C₀ 5040) hz2) hden)
  · have hi5 : i = 5 := by omega
    rw [hi5]
    exact le_trans (SR0_DzdIter_five_bound z hz)
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right C₀ 5040) hz2) hden)

end Work.FTS.StrongEps.H5.Atoms
end
-- ===== merged: Submission.Work.FTS_EllLimOK.BoxDataH.CruxCore =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.BoxDataH

set_option autoImplicit false

/-- **The three staircases.**  From the box-uniform data of the family `H`, an Arzelà–Ascoli
extraction (`φ`, `g`) and the slice data of the members, the limit `G` has within-derivative
`ellCop (g·0) (g·1)` on the box, and its two components `g·0`, `g·1` have within-derivatives
`ellCop (g·2) (g·3)` and `ellCop (g·4) (g·5)`. -/
theorem staircase_data_of_boxUniform2_core {H : ℕ → ℝ → ℝ → ℝ} {G : ℝ → ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hU : BoxUniform2 a b H)
    {φ : ℕ → ℕ} {g : ℝ × ℝ → (Fin 6 → ℝ)}
    (hφ : Filter.Tendsto φ Filter.atTop Filter.atTop)
    (hcv : ∀ m : Fin 6, TendstoUniformlyOn
      (fun n p => wJet (cbox a b) (Function.uncurry (H (φ n))) p m)
      (fun p => g p m) Filter.atTop (cbox a b))
    (hcontg : ContinuousOn g (cbox a b))
    (hconv : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      Filter.Tendsto (fun n => H n z θ) Filter.atTop (𝓝 (G z θ)))
    (hslice : ∀ n, SliceData a b (Function.uncurry (H (φ n)))) :
    (∀ p ∈ cbox a b, HasFDerivWithinAt (Function.uncurry G)
        (ellCop (g p 0) (g p 1)) (cbox a b) p) ∧
    (∀ p ∈ cbox a b, HasFDerivWithinAt (Function.uncurry (fun z θ => g (z, θ) 0))
        (ellCop (g p 2) (g p 3)) (cbox a b) p) ∧
    (∀ p ∈ cbox a b, HasFDerivWithinAt (Function.uncurry (fun z θ => g (z, θ) 1))
        (ellCop (g p 4) (g p 5)) (cbox a b) p) := by
  obtain ⟨K, β, hβ, hsm, hb, hh⟩ := hU
  -- continuity of the members' within-partials on the box
  have hcontJ : ∀ (n : ℕ) (m : Fin 6), ContinuousOn
      (fun p : ℝ × ℝ => wJet (cbox a b) (Function.uncurry (H (φ n))) p m) (cbox a b) :=
    fun n m => continuousOn_wJet hab (hsm (φ n)) m
  have hcontP : ∀ n, ContinuousOn (Function.uncurry (fun z θ =>
      wPz (cbox a b) (Function.uncurry (H (φ n))) (z, θ))) (cbox a b) := by
    intro n
    change ContinuousOn (fun p : ℝ × ℝ =>
      wPz (cbox a b) (Function.uncurry (H (φ n))) p) (cbox a b)
    simpa only [wJet_apply_zero] using hcontJ n 0
  have hcontQ : ∀ n, ContinuousOn (Function.uncurry (fun z θ =>
      wPth (cbox a b) (Function.uncurry (H (φ n))) (z, θ))) (cbox a b) := by
    intro n
    change ContinuousOn (fun p : ℝ × ℝ =>
      wPth (cbox a b) (Function.uncurry (H (φ n))) p) (cbox a b)
    simpa only [wJet_apply_one] using hcontJ n 1
  have hcontPz : ∀ n, ContinuousOn (Function.uncurry (fun z θ =>
      wPzz (cbox a b) (Function.uncurry (H (φ n))) (z, θ))) (cbox a b) := by
    intro n
    change ContinuousOn (fun p : ℝ × ℝ =>
      wPzz (cbox a b) (Function.uncurry (H (φ n))) p) (cbox a b)
    simpa only [wJet_apply_two] using hcontJ n 2
  have hcontPt : ∀ n, ContinuousOn (Function.uncurry (fun z θ =>
      wPtz (cbox a b) (Function.uncurry (H (φ n))) (z, θ))) (cbox a b) := by
    intro n
    change ContinuousOn (fun p : ℝ × ℝ =>
      wPtz (cbox a b) (Function.uncurry (H (φ n))) p) (cbox a b)
    simpa only [wJet_apply_three] using hcontJ n 3
  have hcontQz : ∀ n, ContinuousOn (Function.uncurry (fun z θ =>
      wPzt (cbox a b) (Function.uncurry (H (φ n))) (z, θ))) (cbox a b) := by
    intro n
    change ContinuousOn (fun p : ℝ × ℝ =>
      wPzt (cbox a b) (Function.uncurry (H (φ n))) p) (cbox a b)
    simpa only [wJet_apply_four] using hcontJ n 4
  have hcontQt : ∀ n, ContinuousOn (Function.uncurry (fun z θ =>
      wPtt (cbox a b) (Function.uncurry (H (φ n))) (z, θ))) (cbox a b) := by
    intro n
    change ContinuousOn (fun p : ℝ × ℝ =>
      wPtt (cbox a b) (Function.uncurry (H (φ n))) p) (cbox a b)
    simpa only [wJet_apply_five] using hcontJ n 5
  -- continuity of the limit's components
  have hcontg0 : ContinuousOn (Function.uncurry (fun z θ => g (z, θ) 0)) (cbox a b) := by
    change ContinuousOn (fun p : ℝ × ℝ => g p 0) (cbox a b)
    exact (continuous_apply 0).comp_continuousOn hcontg
  have hcontg1 : ContinuousOn (Function.uncurry (fun z θ => g (z, θ) 1)) (cbox a b) := by
    change ContinuousOn (fun p : ℝ × ℝ => g p 1) (cbox a b)
    exact (continuous_apply 1).comp_continuousOn hcontg
  have hcontg2 : ContinuousOn (Function.uncurry (fun z θ => g (z, θ) 2)) (cbox a b) := by
    change ContinuousOn (fun p : ℝ × ℝ => g p 2) (cbox a b)
    exact (continuous_apply 2).comp_continuousOn hcontg
  have hcontg3 : ContinuousOn (Function.uncurry (fun z θ => g (z, θ) 3)) (cbox a b) := by
    change ContinuousOn (fun p : ℝ × ℝ => g p 3) (cbox a b)
    exact (continuous_apply 3).comp_continuousOn hcontg
  have hcontg4 : ContinuousOn (Function.uncurry (fun z θ => g (z, θ) 4)) (cbox a b) := by
    change ContinuousOn (fun p : ℝ × ℝ => g p 4) (cbox a b)
    exact (continuous_apply 4).comp_continuousOn hcontg
  have hcontg5 : ContinuousOn (Function.uncurry (fun z θ => g (z, θ) 5)) (cbox a b) := by
    change ContinuousOn (fun p : ℝ × ℝ => g p 5) (cbox a b)
    exact (continuous_apply 5).comp_continuousOn hcontg
  -- the first staircase: the values and their two first partials
  have hS0 : ∀ p ∈ cbox a b, HasFDerivWithinAt (Function.uncurry G)
      (ellCop (g p 0) (g p 1)) (cbox a b) p := by
    rintro ⟨z, θ⟩ hp
    obtain ⟨hz, hθ⟩ := mem_cbox.mp hp
    exact Work.FTS_EllLimOK.BoxRegAux.hasFDerivWithinAt_of_uniform_slice_partials
      (a := a) (b := b) (c := 0) (d := π / 2) (le_of_lt hab) (by positivity)
      (H := fun n => H (φ n)) (H₀ := G)
      (P := fun n z θ => wPz (cbox a b) (Function.uncurry (H (φ n))) (z, θ))
      (P₀ := fun z θ => g (z, θ) 0)
      (Q := fun n z θ => wPth (cbox a b) (Function.uncurry (H (φ n))) (z, θ))
      (Q₀ := fun z θ => g (z, θ) 1)
      (fun n => (hsm (φ n)).continuousOn)
      (fun n z hz θ hθ => (hslice n).1 z hz θ hθ)
      (fun n z hz θ hθ => (hslice n).2.1 z hz θ hθ)
      hcontP hcontQ
      (fun z hz θ hθ => (hconv z hz θ hθ).comp hφ)
      (hcv 0) (hcv 1) hcontg0 hcontg1 z hz θ hθ
  -- the second staircase: the partial `g·0` and its two first partials
  have hS1 : ∀ p ∈ cbox a b, HasFDerivWithinAt (Function.uncurry (fun z θ => g (z, θ) 0))
      (ellCop (g p 2) (g p 3)) (cbox a b) p := by
    rintro ⟨z, θ⟩ hp
    obtain ⟨hz, hθ⟩ := mem_cbox.mp hp
    exact Work.FTS_EllLimOK.BoxRegAux.hasFDerivWithinAt_of_uniform_slice_partials
      (a := a) (b := b) (c := 0) (d := π / 2) (le_of_lt hab) (by positivity)
      (H := fun n z θ => wPz (cbox a b) (Function.uncurry (H (φ n))) (z, θ))
      (H₀ := fun z θ => g (z, θ) 0)
      (P := fun n z θ => wPzz (cbox a b) (Function.uncurry (H (φ n))) (z, θ))
      (P₀ := fun z θ => g (z, θ) 2)
      (Q := fun n z θ => wPtz (cbox a b) (Function.uncurry (H (φ n))) (z, θ))
      (Q₀ := fun z θ => g (z, θ) 3)
      hcontP
      (fun n z hz θ hθ => (hslice n).2.2.1 z hz θ hθ)
      (fun n z hz θ hθ => (hslice n).2.2.2.1 z hz θ hθ)
      hcontPz hcontPt
      (fun z hz θ hθ => (hcv 0).tendsto_at ⟨hz, hθ⟩)
      (hcv 2) (hcv 3) hcontg2 hcontg3 z hz θ hθ
  -- the third staircase: the partial `g·1` and its two first partials
  have hS2 : ∀ p ∈ cbox a b, HasFDerivWithinAt (Function.uncurry (fun z θ => g (z, θ) 1))
      (ellCop (g p 4) (g p 5)) (cbox a b) p := by
    rintro ⟨z, θ⟩ hp
    obtain ⟨hz, hθ⟩ := mem_cbox.mp hp
    exact Work.FTS_EllLimOK.BoxRegAux.hasFDerivWithinAt_of_uniform_slice_partials
      (a := a) (b := b) (c := 0) (d := π / 2) (le_of_lt hab) (by positivity)
      (H := fun n z θ => wPth (cbox a b) (Function.uncurry (H (φ n))) (z, θ))
      (H₀ := fun z θ => g (z, θ) 1)
      (P := fun n z θ => wPzt (cbox a b) (Function.uncurry (H (φ n))) (z, θ))
      (P₀ := fun z θ => g (z, θ) 4)
      (Q := fun n z θ => wPtt (cbox a b) (Function.uncurry (H (φ n))) (z, θ))
      (Q₀ := fun z θ => g (z, θ) 5)
      hcontQ
      (fun n z hz θ hθ => (hslice n).2.2.2.2.1 z hz θ hθ)
      (fun n z hz θ hθ => (hslice n).2.2.2.2.2 z hz θ hθ)
      hcontQz hcontQt
      (fun z hz θ hθ => (hcv 1).tendsto_at ⟨hz, hθ⟩)
      (hcv 4) (hcv 5) hcontg4 hcontg5 z hz θ hθ
  exact ⟨hS0, hS1, hS2⟩

end Work.FTS_EllLimOK.BoxDataH
end
end
-- ===== merged: Submission.Work.Spaces.HProductRule_Badsummand =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## Private scaffolding -/











/-! ## The main lemma -/


end Work.Spaces
end
end
