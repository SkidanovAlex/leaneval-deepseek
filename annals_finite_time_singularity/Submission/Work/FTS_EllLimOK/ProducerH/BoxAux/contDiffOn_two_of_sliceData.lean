import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.ZCuts.zHardy_compact
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.ModalSol.Defs
import Submission.Work.FTS.H2.ModalSolR.thetaMomentSmooth
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.PhiStar.Honesty.radGreen_sq_w_sq_meas_engine
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.thetaHardyLeft
import Submission.Work.FTS_EllLimOK.BoxDataH.BoxUniform
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.PkgJets.pinBase
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.RPFresh.slice_sq_le
import Submission.Work.Spaces.BadTermSqBound
import Submission.Work.Spaces.HProductRule_Badsummand
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.EllSol.RPAe.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.RPAe

set_option autoImplicit false

/-- The constant of the level-`4` angular Poincaré estimate: the sum of the ten single-slice
constants of the levels `0 ≤ K ≤ 4` (both the `∂_θ²`- and the `∂_θ`-case) plus one. -/
def sliceCs : ℝ :=
  (∑ K ∈ Finset.range 5,
      (Classical.choose (VopAux.sliceF_le_sliceV K)
        + Classical.choose (VopAux.sliceF_deriv_le_sliceV K))) + 1

theorem sliceCs_pos : 0 < sliceCs := by
  have h1 : 0 < ∑ K ∈ Finset.range 5,
      (Classical.choose (VopAux.sliceF_le_sliceV K)
        + Classical.choose (VopAux.sliceF_deriv_le_sliceV K)) := by
    refine Finset.sum_pos (fun K _ => ?_) ⟨0, Finset.mem_range.mpr (by norm_num)⟩
    have a := (Classical.choose_spec (VopAux.sliceF_le_sliceV K)).1
    have b := (Classical.choose_spec (VopAux.sliceF_deriv_le_sliceV K)).1
    linarith
  rw [sliceCs]; linarith


theorem le_sliceCs_F (K : ℕ) (hK : K ≤ 4) :
    Classical.choose (VopAux.sliceF_le_sliceV K) ≤ sliceCs := by
  have hmem : K ∈ Finset.range 5 := Finset.mem_range.mpr (by omega)
  have hnonneg : ∀ i ∈ Finset.range 5,
      0 ≤ Classical.choose (VopAux.sliceF_le_sliceV i)
        + Classical.choose (VopAux.sliceF_deriv_le_sliceV i) := fun i _ => by
    have a := (Classical.choose_spec (VopAux.sliceF_le_sliceV i)).1
    have b := (Classical.choose_spec (VopAux.sliceF_deriv_le_sliceV i)).1
    linarith
  have hsingle : Classical.choose (VopAux.sliceF_le_sliceV K)
      ≤ ∑ i ∈ Finset.range 5, (Classical.choose (VopAux.sliceF_le_sliceV i)
          + Classical.choose (VopAux.sliceF_deriv_le_sliceV i)) := by
    refine le_trans ?_ (Finset.single_le_sum hnonneg hmem)
    have b := (Classical.choose_spec (VopAux.sliceF_deriv_le_sliceV K)).1
    linarith
  rw [sliceCs]
  linarith

theorem le_sliceCs_D (K : ℕ) (hK : K ≤ 4) :
    Classical.choose (VopAux.sliceF_deriv_le_sliceV K) ≤ sliceCs := by
  have hmem : K ∈ Finset.range 5 := Finset.mem_range.mpr (by omega)
  have hnonneg : ∀ i ∈ Finset.range 5,
      0 ≤ Classical.choose (VopAux.sliceF_le_sliceV i)
        + Classical.choose (VopAux.sliceF_deriv_le_sliceV i) := fun i _ => by
    have a := (Classical.choose_spec (VopAux.sliceF_le_sliceV i)).1
    have b := (Classical.choose_spec (VopAux.sliceF_deriv_le_sliceV i)).1
    linarith
  have hsingle : Classical.choose (VopAux.sliceF_deriv_le_sliceV K)
      ≤ ∑ i ∈ Finset.range 5, (Classical.choose (VopAux.sliceF_le_sliceV i)
          + Classical.choose (VopAux.sliceF_deriv_le_sliceV i)) := by
    refine le_trans ?_ (Finset.single_le_sum hnonneg hmem)
    have a := (Classical.choose_spec (VopAux.sliceF_le_sliceV K)).1
    linarith
  rw [sliceCs]
  linarith

/-- The `VopAux` single-slice `∂_θ²`-estimate, in the form used by the per-`z` comparison. -/
theorem sliceF_le_sliceV_apply (K : ℕ) (α : ℝ) (u : ℝ → ℝ)
    (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)))
    (hlim0 : Filter.Tendsto u (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hlim1 : Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hintV : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.sliceV u θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hintVm : ∀ m ∈ Finset.Icc 1 K, MeasureTheory.IntegrableOn (fun θ =>
      (Work.FTS.EllipticEst.LopIter m (Work.FTS.EllipticEst.sliceV u) θ) ^ 2
        * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        Work.Spaces.Iθ ∧
      (∀ i ∈ Finset.Icc 1 K, MeasureTheory.IntegrableOn (fun θ =>
        (Work.FTS.EllipticEst.LopIter i u θ) ^ 2 * Work.FTS.EllipticEst.thGam α θ)
        Work.Spaces.Iθ) ∧
      VopAux.sliceF K α u
        ≤ Classical.choose (VopAux.sliceF_le_sliceV K)
          * VopAux.sliceF K α (Work.FTS.EllipticEst.sliceV u) :=
  (Classical.choose_spec (VopAux.sliceF_le_sliceV K)).2 α u hα0 hα1 hu hlim0 hlim1 hintV hintVm

/-- The `VopAux` single-slice `∂_θ`-estimate, in the form used by the per-`z` comparison. -/
theorem sliceF_deriv_le_sliceV_apply (K : ℕ) (α : ℝ) (u : ℝ → ℝ)
    (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)))
    (hlim0 : Filter.Tendsto u (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hlim1 : Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hintV : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.sliceV u θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hintVm : ∀ m ∈ Finset.Icc 1 K, MeasureTheory.IntegrableOn (fun θ =>
      (Work.FTS.EllipticEst.LopIter m (Work.FTS.EllipticEst.sliceV u) θ) ^ 2
        * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        Work.Spaces.Iθ ∧
      (∀ i ∈ Finset.Icc 1 K, MeasureTheory.IntegrableOn (fun θ =>
        (Work.FTS.EllipticEst.LopIter i (deriv u) θ) ^ 2
          * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ) ∧
      VopAux.sliceF K α (deriv u)
        ≤ Classical.choose (VopAux.sliceF_deriv_le_sliceV K)
          * VopAux.sliceF K α (Work.FTS.EllipticEst.sliceV u) :=
  (Classical.choose_spec (VopAux.sliceF_deriv_le_sliceV K)).2 α u hα0 hα1 hu hlim0 hlim1 hintV hintVm

end Work.FTS.EllSol.RPAe
end
end
-- ===== merged: Submission.Work.FTS.H2.ModalSol.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.H2.ModalSol

set_option maxHeartbeats 1000000

local notation "Q0" => Work.FTS.EllipticEst.Q0
local notation "Iθ" => Work.Spaces.Iθ

/-! ## The `m = 0` coefficient -/

/-- `radGreen` of the zero source vanishes. -/
theorem radGreen_const_zero (α : ℝ) (m : ℕ) :
    Work.FTS.PhiStar.Radial.radGreen α m (fun _ => (0 : ℝ)) = fun _ => 0 := by
  funext z
  simp only [Work.FTS.PhiStar.Radial.radGreen]
  simp only [zero_mul, mul_zero, add_zero, zero_add,
    intervalIntegral.integral_zero, MeasureTheory.integral_zero]

theorem acoeff_zero_of_orth {F : ℝ → ℝ → ℝ} (horth : Work.Elliptic.OrthCond F) (α : ℝ) (z : ℝ) :
    Work.FTS.PhiStar.Series.acoeff α 0 F z = 0 := by
  have hcm : (fun t => Work.FTS.PhiStar.Series.cmode 0 F t) = fun _ => (0 : ℝ) :=
    funext (fun t => Work.FTS.PhiStar.Series.eFam_zero_moment F (horth t))
  show Work.FTS.PhiStar.Radial.radGreen α 0
    (fun t => Work.FTS.PhiStar.Series.cmode 0 F t) z = 0
  rw [hcm, radGreen_const_zero]

/-! ## Continuity -/

/-- The angular modes are continuous. -/
theorem continuous_eFam (m : ℕ) : Continuous (Work.FTS.PhiStar.Gegenbauer.eFam m) := by
  change Continuous (fun θ : ℝ =>
    Real.cos θ * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ))
  exact Real.continuous_cos.mul
    (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous).comp
      Real.continuous_sin)

/-- A finite sum of continuous functions of the plane, over `Finset.range`. -/
theorem continuousOn_sum_range (f : ℕ → ℝ × ℝ → ℝ) (n : ℕ)
    (hf : ∀ m : ℕ, ContinuousOn (f m) Q0) :
    ContinuousOn (fun p : ℝ × ℝ => ∑ m ∈ Finset.range n, f m p) Q0 := by
  induction n with
  | zero => simpa using (continuousOn_const : ContinuousOn (fun _ : ℝ × ℝ => (0 : ℝ)) Q0)
  | succ n ih =>
      show ContinuousOn (fun p : ℝ × ℝ => ∑ m ∈ Finset.range (n + 1), f m p) Q0
      have h2 : (fun p : ℝ × ℝ => ∑ m ∈ Finset.range (n + 1), f m p)
          = fun p : ℝ × ℝ => (∑ m ∈ Finset.range n, f m p) + f n p := by
        funext p
        rw [Finset.sum_range_succ]
      rw [h2]
      exact ih.add (hf n)

/-- Each mode term `acoeff α m F z · eFam m θ` is continuous on the open quadrant, provided the
radial coefficient is square integrable (its continuity being `radGreen_continuousOn`). -/
theorem continuousOn_acoeff_mul_eFam (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (hc : ∀ m : ℕ, MeasureTheory.IntegrableOn
      (fun t => Work.FTS.PhiStar.Series.cmode m F t ^ 2) (Set.Ioi 0)) (m : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.PhiStar.Series.acoeff α m F p.1 *
      Work.FTS.PhiStar.Gegenbauer.eFam m p.2) Q0 := by
  have h1 : ContinuousOn (fun z => Work.FTS.PhiStar.Series.acoeff α m F z) (Set.Ioi 0) :=
    radGreen_continuousOn α hα hα1 m (hc m)
  have h2 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m p.2) Q0 :=
    (continuous_eFam m).comp_continuousOn continuous_snd.continuousOn
  exact (h1.comp continuous_fst.continuousOn
    (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)).mul h2

/-- The partial sums of the mode series are continuous on the open quadrant. -/
theorem continuousOn_uncurry_psiTrunc (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (hc : ∀ m : ℕ, MeasureTheory.IntegrableOn
      (fun t => Work.FTS.PhiStar.Series.cmode m F t ^ 2) (Set.Ioi 0)) (N : ℕ) :
    ContinuousOn (Function.uncurry (Work.FTS.PhiStar.Series.psiTrunc α F N)) Q0 := by
  have hfun : Function.uncurry (Work.FTS.PhiStar.Series.psiTrunc α F N)
      = fun p : ℝ × ℝ => ∑ m ∈ Finset.range (N + 1),
          Work.FTS.PhiStar.Series.acoeff α m F p.1 *
            Work.FTS.PhiStar.Gegenbauer.eFam m p.2 := by
    funext p
    simp only [Function.uncurry, Work.FTS.PhiStar.Series.psiTrunc, Finset.sum_apply]
  rw [hfun]
  exact continuousOn_sum_range (fun m p => Work.FTS.PhiStar.Series.acoeff α m F p.1 *
    Work.FTS.PhiStar.Gegenbauer.eFam m p.2) (N + 1)
    (fun m => continuousOn_acoeff_mul_eFam α hα hα1 hc m)

/-! ## The pointwise bounds on the partial sums -/


/-- **The partial sums converge to `Psi`**, with the same `z ^ (-1/2)` weight. -/
theorem psiTrunc_tendsto_Psi (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (horth : Work.Elliptic.OrthCond F) (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < π / 2) :
    ∀ z, 0 < z → ∀ θ ∈ Set.Icc δ (π / 2 - δ),
      Filter.Tendsto (fun N : ℕ => Work.FTS.PhiStar.Series.psiTrunc α F N z θ) Filter.atTop
        (nhds (Psi α F z θ)) := by
  obtain ⟨C, b, hC0, hb0, hbT, hEst⟩ := Work.FTS.H2.ModalSol.TailBound.psiTrunc_tail α hα hα1 horth hsm hL2 δ hδ0 hδ1
  intro z hz θ hθ
  apply Psi_tendsto_of_cauchy
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hz' : 0 < z ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hz _
  have hCz : 0 < C * z ^ (-(1 / 2) : ℝ) := mul_pos hC0 hz'
  have hne : C * z ^ (-(1 / 2) : ℝ) ≠ 0 := ne_of_gt hCz
  have hε' : 0 < ε / (4 * (C * z ^ (-(1 / 2) : ℝ))) := by positivity
  have hev : ∀ᶠ N in Filter.atTop, b N < ε / (4 * (C * z ^ (-(1 / 2) : ℝ))) :=
    hbT.eventually (eventually_lt_nhds hε')
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨N₀, fun m hm n hn => ?_⟩
  rw [Real.dist_eq]
  have hmn := hEst m n z hz θ hθ
  have h1 : b m < ε / (4 * (C * z ^ (-(1 / 2) : ℝ))) := hN₀ m hm
  have h2 : b n < ε / (4 * (C * z ^ (-(1 / 2) : ℝ))) := hN₀ n hn
  have h3 : C * z ^ (-(1 / 2) : ℝ) * (b m + b n) < ε / 2 := by
    have hadd : b m + b n < ε / (4 * (C * z ^ (-(1 / 2) : ℝ)))
        + ε / (4 * (C * z ^ (-(1 / 2) : ℝ))) := add_lt_add h1 h2
    have h4 : C * z ^ (-(1 / 2) : ℝ) * (ε / (4 * (C * z ^ (-(1 / 2) : ℝ)))
        + ε / (4 * (C * z ^ (-(1 / 2) : ℝ)))) = ε / 2 := by
      field_simp
      ring
    calc C * z ^ (-(1 / 2) : ℝ) * (b m + b n)
        < C * z ^ (-(1 / 2) : ℝ) * (ε / (4 * (C * z ^ (-(1 / 2) : ℝ)))
            + ε / (4 * (C * z ^ (-(1 / 2) : ℝ)))) := mul_lt_mul_of_pos_left hadd hCz
      _ = ε / 2 := h4
  linarith

/-! ## Uniform convergence on a box, and continuity of the witness -/

/-- **Uniform convergence of the partial sums on a rectangular box inside the quadrant.** -/
theorem tendstoUniformlyOn_psiTrunc_box (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (horth : Work.Elliptic.OrthCond F) (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    {a b c d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc0 : 0 < c) (hcd : c ≤ d) (hd : d < π / 2) :
    TendstoUniformlyOn
      (fun N : ℕ => fun p : ℝ × ℝ => Work.FTS.PhiStar.Series.psiTrunc α F N p.1 p.2)
      (fun p : ℝ × ℝ => Psi α F p.1 p.2) Filter.atTop (Set.Icc a b ×ˢ Set.Icc c d) := by
  set δ : ℝ := min c (π / 2 - d) with hδdef
  have hδ0 : 0 < δ := lt_min hc0 (by linarith)
  have hδ1 : δ < π / 2 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδc : δ ≤ c := min_le_left _ _
  have hδd : δ ≤ π / 2 - d := min_le_right _ _
  obtain ⟨C, β, hC0, hβ0, hβT, hEst⟩ := Work.FTS.H2.ModalSol.TailBound.psiTrunc_tail α hα hα1 horth hsm hL2 δ hδ0 hδ1
  have hconv : ∀ z, 0 < z → ∀ θ ∈ Set.Icc δ (π / 2 - δ),
      Filter.Tendsto (fun N : ℕ => Work.FTS.PhiStar.Series.psiTrunc α F N z θ) Filter.atTop
        (nhds (Psi α F z θ)) := psiTrunc_tendsto_Psi α hα hα1 horth hsm hL2 δ hδ0 hδ1
  have hkey : ∀ (N : ℕ) (p : ℝ × ℝ), p ∈ Set.Icc a b ×ˢ Set.Icc c d →
      |Psi α F p.1 p.2 - Work.FTS.PhiStar.Series.psiTrunc α F N p.1 p.2|
        ≤ C * a ^ (-(1 / 2) : ℝ) * β N := by
    intro N p hp
    have hp1 : 0 < p.1 := lt_of_lt_of_le ha hp.1.1
    have hpl : δ ≤ p.2 := le_trans hδc hp.2.1
    have hpr : p.2 ≤ π / 2 - δ := le_trans hp.2.2 (by linarith)
    have hp2 : p.2 ∈ Set.Icc δ (π / 2 - δ) := ⟨hpl, hpr⟩
    have hlim := hconv p.1 hp1 p.2 hp2
    have hdiff : Filter.Tendsto
        (fun M : ℕ => |Work.FTS.PhiStar.Series.psiTrunc α F N p.1 p.2
          - Work.FTS.PhiStar.Series.psiTrunc α F M p.1 p.2|) Filter.atTop
        (nhds |Work.FTS.PhiStar.Series.psiTrunc α F N p.1 p.2 - Psi α F p.1 p.2|) :=
      ((tendsto_const_nhds.sub hlim).abs)
    have hbd : Filter.Tendsto
        (fun M : ℕ => C * p.1 ^ (-(1 / 2) : ℝ) * (β N + β M)) Filter.atTop
        (nhds (C * p.1 ^ (-(1 / 2) : ℝ) * (β N + 0))) :=
      ((tendsto_const_nhds.add hβT).const_mul _)
    have hle : |Work.FTS.PhiStar.Series.psiTrunc α F N p.1 p.2 - Psi α F p.1 p.2|
        ≤ C * p.1 ^ (-(1 / 2) : ℝ) * β N := by
      have := le_of_tendsto_of_tendsto' hdiff hbd (fun M => hEst N M p.1 hp1 p.2 hp2)
      simpa using this
    have hp1a : a ^ (-(1 / 2) : ℝ) ≥ p.1 ^ (-(1 / 2) : ℝ) := by
      refine Real.rpow_le_rpow_of_nonpos ha hp.1.1 (by norm_num)
    have hbz : 0 ≤ β N := hβ0 N
    have hCpos : 0 ≤ C := le_of_lt hC0
    calc |Psi α F p.1 p.2 - Work.FTS.PhiStar.Series.psiTrunc α F N p.1 p.2|
        = |Work.FTS.PhiStar.Series.psiTrunc α F N p.1 p.2 - Psi α F p.1 p.2| :=
            abs_sub_comm _ _
      _ ≤ C * p.1 ^ (-(1 / 2) : ℝ) * β N := hle
      _ ≤ C * a ^ (-(1 / 2) : ℝ) * β N := by
          refine mul_le_mul_of_nonneg_right ?_ hbz
          exact mul_le_mul_of_nonneg_left hp1a hCpos
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hCa : 0 < C * a ^ (-(1 / 2) : ℝ) := mul_pos hC0 (Real.rpow_pos_of_pos ha _)
  have hε' : 0 < ε / (C * a ^ (-(1 / 2) : ℝ)) := by positivity
  have hev : ∀ᶠ N in Filter.atTop, β N < ε / (C * a ^ (-(1 / 2) : ℝ)) :=
    hβT.eventually (eventually_lt_nhds hε')
  filter_upwards [hev] with N hN
  intro p hp
  rw [Real.dist_eq]
  have h := hkey N p hp
  have h2 : C * a ^ (-(1 / 2) : ℝ) * β N < ε := by
    rw [lt_div_iff₀ hCa] at hN
    linarith
  linarith


/-! ## The pointwise bound on the witness, and its decay -/




end Work.FTS.H2.ModalSol
end
end
-- ===== merged: Submission.Work.FTS.H2.ModalSolR.psiTruncTailBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.ModalSolR

open scoped Real BigOperators
open MeasureTheory Set Filter

noncomputable section

/-- The tail of the truncated mode series is the finite mode combination over
`Finset.Icc (M+1) N`. -/
lemma psitb_tail_diff (α : ℝ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) {M N : ℕ} (hMN : M ≤ N) :
    Work.FTS.PhiStar.Series.psiTrunc α F N z θ - Work.FTS.PhiStar.Series.psiTrunc α F M z θ
      = ∑ m ∈ Finset.Icc (M + 1) N,
          Work.FTS.PhiStar.Series.acoeff α m F z * Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
  have hsub : Finset.range (M + 1) ⊆ Finset.range (N + 1) := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  have hsdiff : Finset.range (N + 1) \ Finset.range (M + 1) = Finset.Icc (M + 1) N := by
    ext m
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Icc]
    omega
  have hsum := Finset.sum_sdiff hsub
    (f := fun m => Work.FTS.PhiStar.Series.acoeff α m F z
      * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
  rw [hsdiff] at hsum
  simp only [Work.FTS.PhiStar.Series.psiTrunc]
  linarith [hsum]


/-- The squared `L²(Iθ, cos θ dθ)` norm of `eFam m` is nonnegative. -/
lemma psitb_eNorm_nonneg (m : ℕ) :
    0 ≤ ∫ θ in Work.Spaces.Iθ,
      Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ := by
  rw [Work.Spaces.Iθ]
  refine MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => ?_)
  exact mul_nonneg (sq_nonneg _)
    (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)

/-- The eigenvalue `lam m = 2m(2m+5)` is nonnegative. -/
lemma psitb_lam_nonneg (m : ℕ) : 0 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
  simp only [Work.FTS.PhiStar.Gegenbauer.lam]
  have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  nlinarith

theorem psiTruncTailBound (α : ℝ) {F : ℝ → ℝ → ℝ} {c d : ℝ} (hcd : c < d) (hc : 0 < c)
    (hd : d < Real.pi / 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (z θ : ℝ) (M N : ℕ), θ ∈ Set.Icc c d → M ≤ N →
      |Work.FTS.PhiStar.Series.psiTrunc α F N z θ
          - Work.FTS.PhiStar.Series.psiTrunc α F M z θ|
        ≤ K * Real.sqrt
            ((∑ m ∈ Finset.Icc (M + 1) N,
                (∫ θ' in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ' ^ 2 * Real.cos θ')
                  * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2)
              + ∑ m ∈ Finset.Icc (M + 1) N,
                  Work.FTS.PhiStar.Gegenbauer.lam m
                    * (∫ θ' in Work.Spaces.Iθ,
                        Work.FTS.PhiStar.Gegenbauer.eFam m θ' ^ 2 * Real.cos θ')
                    * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2) := by
  obtain ⟨K, hKpos, hK⟩ := supBoundOfIntegrals (c := c) (d := d) hcd hc hd
  refine ⟨K * Real.sqrt 7, by positivity, ?_⟩
  intro z θ M N hθ hMN
  set a : ℕ → ℝ := fun m => Work.FTS.PhiStar.Series.acoeff α m F z with ha
  have ha' : ∀ m, a m = Work.FTS.PhiStar.Series.acoeff α m F z := fun m => congrFun ha m
  simp only [← ha']
  set S1 : ℝ := ∑ m ∈ Finset.Icc (M + 1) N,
      (∫ θ' in Work.Spaces.Iθ,
        Work.FTS.PhiStar.Gegenbauer.eFam m θ' ^ 2 * Real.cos θ') * (a m) ^ 2 with hS1
  set S2 : ℝ := ∑ m ∈ Finset.Icc (M + 1) N,
      Work.FTS.PhiStar.Gegenbauer.lam m
        * (∫ θ' in Work.Spaces.Iθ,
            Work.FTS.PhiStar.Gegenbauer.eFam m θ' ^ 2 * Real.cos θ') * (a m) ^ 2 with hS2
  -- the facts about the tail function
  obtain ⟨hC2raw, hzero, hpi, hI4, hI2, hI3⟩ := tailFacts a (Finset.Icc (M + 1) N)
  obtain ⟨-, hI1⟩ := lzero1FinSumAE a (Finset.Icc (M + 1) N)
  obtain ⟨hP1, hP2⟩ := tailParseval α F z hMN
  -- the weighted tail function
  set v : ℝ → ℝ := fun θ => ∑ m ∈ Finset.Icc (M + 1) N,
      a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ with hv
  have hC2 : ContDiffOn ℝ 2 v (Set.Icc 0 (Real.pi / 2)) := hC2raw
  have hv0 : v 0 = 0 := hzero
  have hvpi : v (Real.pi / 2) = 0 := hpi
  -- the two Parseval identities
  have hP1v : (∫ θ in Work.Spaces.Iθ, (v θ) ^ 2 * Real.cos θ) = S1 := by
    rw [hS1]
    simpa only [← ha', hv] using hP1
  have hP2v : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Lzero1 v θ * v θ * Real.cos θ)
      = S2 := by
    rw [hS2]
    have hb : Work.FTS.EllipticEst.Lzero1 v
        = fun θ => Work.Elliptic.Lzero (fun _ θ' => v θ') 0 θ :=
      Work.FTS.EllipticEst.Lzero1_eq_Lzero v 0
    rw [hb]
    simpa only [← ha', hv] using hP2
  -- the derivative bound
  have hT : (∫ θ in Work.Spaces.Iθ, (deriv v θ) ^ 2 * Real.cos θ) ≤ 6 * S1 + S2 := by
    have h := energyToDeriv hC2 hv0 hvpi hI1 hI2 hI3 hI4
    linarith [h, hP1v, hP2v]
  -- the sup bound on the interior interval
  have hcont : ContDiffOn ℝ 1 v (Set.Icc 0 (Real.pi / 2)) := hC2.of_le (by norm_num)
  have hAg := hK v hcont hI4 hI2 θ hθ
  rw [hP1v] at hAg
  -- nonnegativity of the two sums
  have hS1nn : 0 ≤ S1 := by
    rw [hS1]
    exact Finset.sum_nonneg fun m _ => mul_nonneg (psitb_eNorm_nonneg m) (sq_nonneg _)
  have hS2nn : 0 ≤ S2 := by
    rw [hS2]
    exact Finset.sum_nonneg fun m _ =>
      mul_nonneg (mul_nonneg (psitb_lam_nonneg m) (psitb_eNorm_nonneg m)) (sq_nonneg _)
  -- identification with the difference of the partial sums
  have hd1 : |Work.FTS.PhiStar.Series.psiTrunc α F N z θ
      - Work.FTS.PhiStar.Series.psiTrunc α F M z θ| = |v θ| := by
    rw [psitb_tail_diff α F z θ hMN]
  rw [hd1]
  -- final chain
  refine hAg.trans ?_
  have hstep : K * Real.sqrt (S1 + (∫ θ in Work.Spaces.Iθ, (deriv v θ) ^ 2 * Real.cos θ))
      ≤ K * Real.sqrt (S1 + (6 * S1 + S2)) := by
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hKpos.le
    linarith [hT]
  refine hstep.trans ?_
  have harg : S1 + (6 * S1 + S2) ≤ 7 * (S1 + S2) := by linarith
  refine (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt harg) hKpos.le).trans ?_
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 7), mul_assoc]

end

end Work.FTS.H2.ModalSolR
end
-- ===== merged: Submission.Work.FTS.H2.ModalSolR.sourceSideLimit =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.H2.ModalSolR

/-! ## The source-side limit -/

theorem sourceSideLimit {α : ℝ} {F φ : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hφ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ))
    (hφc : HasCompactSupport (Function.uncurry φ))
    (hφs : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    Filter.Tendsto (fun N : ℕ => ∫ p in Work.FTS.EllipticEst.Q0,
        (∑ m ∈ Finset.range (N + 1), Work.FTS.PhiStar.Series.cmode m F p.1
          * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) * φ p.1 p.2
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      Filter.atTop
      (nhds (∫ p in Work.FTS.EllipticEst.Q0,
        F p.1 p.2 * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2))) := by
  classical
  obtain ⟨a, b, c, d, ha, hab, hc, hcd, hd, hbox⟩ :=
    Work.EllipticEst.ModalSolution.box_of_compactSupport hφc hφs
  let K : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc c d
  have hab' : a ≤ b := le_of_lt hab
  have hcd' : c ≤ d := le_of_lt hcd
  have hKcomp : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKmeas : MeasurableSet K := hKcomp.isClosed.measurableSet
  have haK : K ⊆ Work.FTS.EllipticEst.Q0 := fun p hp =>
    Work.FTS.EllipticEst.mem_Q0.mpr
      ⟨lt_of_lt_of_le ha hp.1.1, lt_of_lt_of_le hc hp.2.1, lt_of_le_of_lt hp.2.2 hd⟩
  have hphi0 : ∀ p : ℝ × ℝ, p ∉ K → φ p.1 p.2 = 0 := fun p hp =>
    hbox p (fun hmem => hp ⟨⟨hmem.1.1.le, hmem.1.2.le⟩, ⟨hmem.2.1.le, hmem.2.2.le⟩⟩)
  have hvan : ∀ (h : ℝ × ℝ → ℝ), (∀ p ∈ Work.FTS.EllipticEst.Q0 \ K, h p = 0) →
      (∫ p in Work.FTS.EllipticEst.Q0, h p) = ∫ p in K, h p := fun h hh =>
    MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      Work.FTS.EllipticEst.isOpen_Q0.measurableSet haK hh
  let Φ : ℝ × ℝ → ℝ := fun p => φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2)
  let SN : ℕ → ℝ × ℝ → ℝ := fun N p => ∑ m ∈ Finset.range (N + 1),
      Work.FTS.PhiStar.Series.cmode m F p.1 * Work.FTS.PhiStar.Gegenbauer.eFam m p.2
  let RZ : ℕ → ℝ × ℝ → ℝ := fun N p => SN N p - F p.1 p.2
  let rN : ℕ → ℝ → ℝ := fun N z => (∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ)
      - ∑ m ∈ Finset.range (N + 1), (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
  have hΦcont : ContinuousOn Φ K := by
    dsimp only [Φ]
    refine ContinuousOn.mul ?_ (ContinuousOn.mul ?_ ?_)
    · exact (hφ 0).continuous.continuousOn
    · exact continuousOn_fst.rpow_const (fun p hp => Or.inl (ne_of_gt (lt_of_lt_of_le ha hp.1.1)))
    · exact (Real.continuous_cos.comp continuous_snd).continuousOn
  have hFcontK : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2 * Real.cos p.2) K :=
    ((hsm.continuousOn.mono haK).pow 2).mul
      (Real.continuous_cos.comp continuous_snd).continuousOn
  have hF2K : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2 * Real.cos p.2) K :=
    hFcontK.integrableOn_compact hKcomp
  have hΦ2K : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => Φ p ^ 2) K :=
    (hΦcont.pow 2).integrableOn_compact hKcomp
  have hRZaesm : ∀ N : ℕ, MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => RZ N p)
      ((MeasureTheory.volume : Measure (ℝ × ℝ)).restrict K) := fun N =>
    (SourceSide.joint_aesm_partialSum_residual hsm N).mono_set
      (show K ⊆ Set.Ioi 0 ×ˢ Set.Icc 0 (π / 2) from
        fun p hp => ⟨lt_of_lt_of_le ha hp.1.1, ⟨le_trans hc.le hp.2.1, le_trans hp.2.2 hd.le⟩⟩)
  have hFaesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => F p.1 p.2)
      ((MeasureTheory.volume : Measure (ℝ × ℝ)).restrict K) :=
    (hsm.continuousOn.mono haK).aestronglyMeasurable hKmeas
  have hSNaesm : ∀ N : ℕ, MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => SN N p)
      ((MeasureTheory.volume : Measure (ℝ × ℝ)).restrict K) := fun N =>
    ((hRZaesm N).add hFaesm).congr
      (Eventually.of_forall (fun p => by
        simp only [Pi.add_apply]
        dsimp only [RZ, SN]
        ring))
  have hSN2K : ∀ N : ℕ, MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => SN N p ^ 2 * Real.cos p.2) K := by
    intro N
    have hterm_int : ∀ m ∈ Finset.range (N + 1),
        MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.FTS.PhiStar.Series.cmode m F p.1) ^ 2
          * (Work.FTS.PhiStar.Gegenbauer.eFam m p.2 ^ 2 * Real.cos p.2)) K := fun m _ =>
      SourceSide.integrableOn_sq_mul_continuousOn
        (Work.EllipticEst.ModalSolution.cmode_memLp hsm hL2 m) ha hab' hc hcd'
        (((Work.EllipticEst.ModalSolution.continuous_eFam m).comp_continuousOn
            continuous_snd.continuousOn).pow 2 |>.mul
          (Real.continuous_cos.comp continuous_snd).continuousOn)
    have hdom : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => ((Finset.range (N + 1)).card : ℝ) *
        ∑ m ∈ Finset.range (N + 1), (Work.FTS.PhiStar.Series.cmode m F p.1) ^ 2
          * (Work.FTS.PhiStar.Gegenbauer.eFam m p.2 ^ 2 * Real.cos p.2)) K :=
      (integrable_finsetSum (Finset.range (N + 1)) (fun m hm => hterm_int m hm)).const_mul _
    refine MeasureTheory.Integrable.mono' hdom (((hSNaesm N).pow 2).mul
      (Real.continuous_cos.comp continuous_snd).aestronglyMeasurable) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (s := K) hKmeas] with p hp
    have hcos : 0 ≤ Real.cos p.2 := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hp.2.1, hc, Real.pi_pos], by linarith [hp.2.2, hd, Real.pi_pos]⟩
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hcos)]
    calc SN N p ^ 2 * Real.cos p.2
        = (∑ m ∈ Finset.range (N + 1), Work.FTS.PhiStar.Series.cmode m F p.1
            * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) ^ 2 * Real.cos p.2 := rfl
      _ ≤ ((Finset.range (N + 1)).card : ℝ) * (∑ m ∈ Finset.range (N + 1),
            (Work.FTS.PhiStar.Series.cmode m F p.1
              * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) ^ 2) * Real.cos p.2 :=
          mul_le_mul_of_nonneg_right sq_sum_le_card_mul_sum_sq hcos
      _ = ((Finset.range (N + 1)).card : ℝ) * ∑ m ∈ Finset.range (N + 1),
            (Work.FTS.PhiStar.Series.cmode m F p.1) ^ 2
              * (Work.FTS.PhiStar.Gegenbauer.eFam m p.2 ^ 2 * Real.cos p.2) := by
          rw [mul_assoc, Finset.sum_mul]
          congr 1
          exact Finset.sum_congr rfl (fun m _ => by ring)
  have hRQK : ∀ N : ℕ, MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => RZ N p ^ 2 * Real.cos p.2) K := by
    intro N
    refine MeasureTheory.Integrable.mono' (((hSN2K N).const_mul 2).add (hF2K.const_mul 2)) ?_ ?_
    · exact ((hRZaesm N).pow 2).mul (Real.continuous_cos.comp continuous_snd).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem (s := K) hKmeas] with p hp
      have hcos : 0 ≤ Real.cos p.2 := Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [hp.2.1, hc, Real.pi_pos], by linarith [hp.2.2, hd, Real.pi_pos]⟩
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hcos)]
      simp only [Pi.add_apply]
      dsimp only [RZ]
      nlinarith [mul_nonneg (sq_nonneg (SN N p + F p.1 p.2)) hcos]
  have hRZ2sq : ∀ N : ℕ, MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => RZ N p ^ 2) K := by
    intro N
    have hcdpos : 0 < Real.cos d := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hc, Real.pi_pos], by linarith [hd, Real.pi_pos]⟩
    refine MeasureTheory.Integrable.mono' ((hRQK N).const_mul (1 / Real.cos d)) ?_ ?_
    · exact (hRZaesm N).pow 2
    · filter_upwards [MeasureTheory.ae_restrict_mem (s := K) hKmeas] with p hp
      have hcosle : Real.cos d ≤ Real.cos p.2 := Real.cos_le_cos_of_nonneg_of_le_pi
        (by linarith [hp.2.1, hc, Real.pi_pos]) (by linarith [hd, Real.pi_pos]) hp.2.2
      rw [Real.norm_of_nonneg (sq_nonneg _), one_div, inv_mul_eq_div, le_div_iff₀ hcdpos]
      exact mul_le_mul_of_nonneg_left hcosle (sq_nonneg _)
  have hRZ2_le : ∀ N : ℕ, (∫ p in K, RZ N p ^ 2) ≤
      (1 / Real.cos d) * (∫ p in K, RZ N p ^ 2 * Real.cos p.2) := by
    intro N
    have hcdpos : 0 < Real.cos d := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hc, Real.pi_pos], by linarith [hd, Real.pi_pos]⟩
    have hptw : ∀ p ∈ K, RZ N p ^ 2 ≤ (1 / Real.cos d) * (RZ N p ^ 2 * Real.cos p.2) := by
      intro p hp
      have hcosle : Real.cos d ≤ Real.cos p.2 := Real.cos_le_cos_of_nonneg_of_le_pi
        (by linarith [hp.2.1, hc, Real.pi_pos]) (by linarith [hd, Real.pi_pos]) hp.2.2
      rw [one_div, inv_mul_eq_div, le_div_iff₀ hcdpos]
      exact mul_le_mul_of_nonneg_left hcosle (sq_nonneg _)
    have h1 := MeasureTheory.setIntegral_mono_on (hRZ2sq N) ((hRQK N).const_mul (1 / Real.cos d))
      hKmeas hptw
    rwa [MeasureTheory.integral_const_mul] at h1
  -- the a.e. bound on the algebraic residual energy
  have hrN_bnd : ∀ N : ℕ, ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      0 ≤ rN N z ∧ rN N z ≤ ∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ := by
    intro N
    filter_upwards [ae_slice_facts hsm hL2] with z hz
    obtain ⟨hzm, hzi⟩ := hz
    have hcosnn : 0 ≤ᵐ[(MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iθ]
        (fun θ => F z θ ^ 2 * Real.cos θ) := by
      filter_upwards [MeasureTheory.ae_restrict_mem (s := Work.Spaces.Iθ) measurableSet_Icc]
        with θ hθ
      exact mul_nonneg (sq_nonneg _)
        (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩)
    have hof := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hzi hcosnn
    have hb := Work.EllipticEst.ModalSolution.cmode_bessel F z N
    have hb' : ENNReal.ofReal (∑ m ∈ Finset.range (N + 1),
        (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ))
        ≤ ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ) := by
      rw [hof]
      refine le_of_eq_of_le ?_ hb
      congr 1
      refine Finset.sum_congr rfl (fun m _ => ?_)
      ring
    have hle : (∑ m ∈ Finset.range (N + 1), (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ))
        ≤ ∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ :=
      (ENNReal.ofReal_le_ofReal_iff (MeasureTheory.integral_nonneg_of_ae hcosnn)).mp hb'
    have hsumnn : 0 ≤ ∑ m ∈ Finset.range (N + 1), (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ) :=
      Finset.sum_nonneg (fun m _ => mul_nonneg (sq_nonneg _)
        (le_of_lt (Work.EllipticEst.ModalSolution.eNorm_pos m)))
    dsimp only [rN]
    exact ⟨sub_nonneg.mpr hle, by linarith⟩
  have hrN_aesm : ∀ N : ℕ, MeasureTheory.AEStronglyMeasurable (fun z => rN N z)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    intro N
    have hsum : MeasureTheory.AEStronglyMeasurable (fun z => ∑ m ∈ Finset.range (N + 1),
        (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ))
        (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
      (integrable_finsetSum (Finset.range (N + 1)) (fun m _ =>
        (Work.EllipticEst.ModalSolution.cmode_memLp hsm hL2 m).const_mul
          (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
        |>.congr (Eventually.of_forall (fun z => by ring)))).aestronglyMeasurable
    exact ((sigma_integrable hsm hL2).aestronglyMeasurable.sub hsum).congr
      (Eventually.of_forall (fun z => rfl))
  have hrN_int : ∀ N : ℕ, MeasureTheory.IntegrableOn (fun z => rN N z) (Set.Ioi 0) := by
    intro N
    refine MeasureTheory.Integrable.mono' (sigma_integrable hsm hL2) (hrN_aesm N) ?_
    filter_upwards [hrN_bnd N] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg hz.1]
    exact hz.2
  -- the box integral as an iterated integral
  have hFub : ∀ N : ℕ, (∫ p in K, RZ N p ^ 2 * Real.cos p.2)
      = ∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, RZ N (z, θ) ^ 2 * Real.cos θ := by
    intro N
    rw [MeasureTheory.Measure.volume_eq_prod]
    exact MeasureTheory.setIntegral_prod (fun p : ℝ × ℝ => RZ N p ^ 2 * Real.cos p.2) (hRQK N)
  -- the residual energy on the box is dominated by the integrated residual energy
  have hstep : ∀ N : ℕ,
      (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, RZ N (z, θ) ^ 2 * Real.cos θ)
        ≤ ∫ z in Set.Ioi 0, rN N z := by
    intro N
    have hinner : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Icc a b)),
        (∫ θ in Set.Icc c d, RZ N (z, θ) ^ 2 * Real.cos θ) ≤ rN N z := by
      have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun x hx => lt_of_lt_of_le ha hx.1
      have h1 : ∀ᵐ z ∂((MeasureTheory.volume.restrict (Set.Ioi 0)).restrict (Set.Icc a b)),
          (∫ θ in Set.Icc c d, RZ N (z, θ) ^ 2 * Real.cos θ) ≤ rN N z := by
        filter_upwards [MeasureTheory.ae_restrict_of_ae (ae_slice_facts hsm hL2)] with z hz
        obtain ⟨hzm, hzi⟩ := hz
        have hcontS : Continuous (fun θ : ℝ => SN N (z, θ)) := by
          dsimp only [SN]
          exact continuous_finsetSum _ (fun m _ => continuous_const.mul
            (Work.EllipticEst.ModalSolution.continuous_eFam m))
        have hS2int : MeasureTheory.IntegrableOn
            (fun θ : ℝ => SN N (z, θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ :=
          ((hcontS.pow 2).mul Real.continuous_cos).continuousOn.integrableOn_compact
            (by simpa only [Work.Spaces.Iθ] using isCompact_Icc)
        have hRZint : MeasureTheory.IntegrableOn
            (fun θ : ℝ => RZ N (z, θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ := by
          refine MeasureTheory.Integrable.mono' ((hS2int.const_mul 2).add (hzi.const_mul 2)) ?_ ?_
          · exact (((hcontS.aestronglyMeasurable.sub hzm).pow 2).mul
              Real.continuous_cos.aestronglyMeasurable)
          · filter_upwards [MeasureTheory.ae_restrict_mem (s := Work.Spaces.Iθ) measurableSet_Icc]
              with θ hθ
            have hcosθ : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc
              ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
            rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hcosθ)]
            simp only [Pi.add_apply]
            dsimp only [RZ]
            nlinarith [mul_nonneg (sq_nonneg (SN N (z, θ) + F z θ)) hcosθ]
        have hEq : (∫ θ in Work.Spaces.Iθ, RZ N (z, θ) ^ 2 * Real.cos θ) = rN N z := by
          have hpyth := Work.EllipticEst.ModalSolution.eFam_pythagoras_alt F z N hzm hzi
          rw [show rN N z = (∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ)
              - ∑ m ∈ Finset.range (N + 1), (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
                  * (∫ θ in Work.Spaces.Iθ,
                      Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ) from rfl,
            ← hpyth]
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
          dsimp only [RZ, SN]
          ring
        refine le_trans ?_ (le_of_eq hEq)
        refine MeasureTheory.setIntegral_mono_set hRZint ?_ ?_
        · filter_upwards [MeasureTheory.ae_restrict_mem (s := Work.Spaces.Iθ) measurableSet_Icc]
            with θ hθ
          exact mul_nonneg (sq_nonneg _) (Real.cos_nonneg_of_mem_Icc
            ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩)
        · exact Eventually.of_forall (fun x hx => ⟨le_trans hc.le hx.1, le_trans hx.2 hd.le⟩)
      rwa [Measure.restrict_restrict_of_subset hsub] at h1
    have hfi : MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Set.Icc c d, RZ N (z, θ) ^ 2 * Real.cos θ) (Set.Icc a b) := by
      have h2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => RZ N p ^ 2 * Real.cos p.2)
          ((MeasureTheory.volume.restrict (Set.Icc a b)).prod
            (MeasureTheory.volume.restrict (Set.Icc c d))) := by
        rw [MeasureTheory.Measure.prod_restrict]
        exact hRQK N
      exact h2.integral_prod_left
    have hgi : MeasureTheory.IntegrableOn (fun z => rN N z) (Set.Icc a b) :=
      (hrN_int N).mono_set (fun x hx => lt_of_lt_of_le ha hx.1)
    calc (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, RZ N (z, θ) ^ 2 * Real.cos θ)
        ≤ ∫ z in Set.Icc a b, rN N z :=
          MeasureTheory.setIntegral_mono_ae_restrict hfi hgi hinner
      _ ≤ ∫ z in Set.Ioi 0, rN N z :=
          MeasureTheory.setIntegral_mono_set (hrN_int N)
            ((hrN_bnd N).mono (fun z hz => hz.1))
            (Eventually.of_forall (fun x hx => lt_of_lt_of_le ha hx.1))
  have hres_lim : Filter.Tendsto (fun N : ℕ => ∫ p in K, RZ N p ^ 2 * Real.cos p.2)
      Filter.atTop (nhds 0) := by
    have hDCT : Filter.Tendsto (fun N : ℕ => ∫ z in Set.Ioi 0, rN N z) Filter.atTop (nhds 0) :=
      SourceSide.residualEnergyTendstoZero hsm hL2
    refine squeeze_zero' (Eventually.of_forall (fun N => ?_))
      (Eventually.of_forall (fun N => ?_)) hDCT
    · rw [hFub N]
      exact MeasureTheory.integral_nonneg_of_ae (Eventually.of_forall (fun z =>
        MeasureTheory.integral_nonneg_of_ae (by
          filter_upwards [MeasureTheory.ae_restrict_mem (s := Set.Icc c d) measurableSet_Icc]
            with θ hθ
          exact mul_nonneg (sq_nonneg _) (Real.cos_nonneg_of_mem_Icc
            ⟨by linarith [hθ.1, hc, Real.pi_pos], by linarith [hθ.2, hd, Real.pi_pos]⟩))))
    · rw [hFub N]
      exact hstep N
  -- integrability of the residual against the test function
  have hRZΦK : ∀ N : ℕ, MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => RZ N p * Φ p) K := by
    intro N
    refine MeasureTheory.Integrable.mono' (((hRZ2sq N).add (hΦ2K)).div_const 2) ?_ ?_
    · exact (hRZaesm N).mul (hΦcont.aestronglyMeasurable hKmeas)
    · filter_upwards with p
      simp only [Pi.add_apply]
      rw [Real.norm_eq_abs, abs_mul]
      nlinarith [sq_nonneg (|RZ N p| - |Φ p|), sq_abs (RZ N p), sq_abs (Φ p)]
  have hFΦK : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 * Φ p) K :=
    ((hsm.continuousOn.mono haK).mul hΦcont).integrableOn_compact hKcomp
  have hSNΦK : ∀ N : ℕ, MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => SN N p * Φ p) K := by
    intro N
    refine ((hRZΦK N).add hFΦK).congr_fun ?_ hKmeas
    intro p hp
    simp only [Pi.add_apply]
    dsimp only [RZ, SN]
    ring
  -- Cauchy–Schwarz on the box
  have hcs : ∀ N : ℕ, (∫ p in K, RZ N p * Φ p) ^ 2
      ≤ (∫ p in K, RZ N p ^ 2) * (∫ p in K, Φ p ^ 2) := fun N =>
    SourceSide.sq_integral_mul_le_of_integrable_sq (s := K)
      (u := fun p => RZ N p) (v := fun p => Φ p) (hRZ2sq N) (hΦ2K)
      (hRZaesm N) (hΦcont.aestronglyMeasurable hKmeas)
  have hbound : ∀ N : ℕ, ‖∫ p in K, RZ N p * Φ p‖ ≤
      Real.sqrt ((1 / Real.cos d) * (∫ p in K, RZ N p ^ 2 * Real.cos p.2))
        * Real.sqrt (∫ p in K, Φ p ^ 2) := by
    intro N
    have hcdpos : 0 < Real.cos d := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hc, Real.pi_pos], by linarith [hd, Real.pi_pos]⟩
    have hB : 0 ≤ ∫ p in K, Φ p ^ 2 :=
      MeasureTheory.integral_nonneg_of_ae (by
        filter_upwards [MeasureTheory.ae_restrict_mem (s := K) hKmeas] with p hp
        exact sq_nonneg _)
    have hX : 0 ≤ (1 / Real.cos d) * (∫ p in K, RZ N p ^ 2 * Real.cos p.2) :=
      mul_nonneg (le_of_lt (div_pos one_pos hcdpos))
        (MeasureTheory.integral_nonneg_of_ae (by
          filter_upwards [MeasureTheory.ae_restrict_mem (s := K) hKmeas] with p hp
          exact mul_nonneg (sq_nonneg _) (Real.cos_nonneg_of_mem_Icc
            ⟨by linarith [hp.2.1, hc, Real.pi_pos], by linarith [hp.2.2, hd, Real.pi_pos]⟩)))
    have h1 : (∫ p in K, RZ N p * Φ p) ^ 2
        ≤ ((1 / Real.cos d) * (∫ p in K, RZ N p ^ 2 * Real.cos p.2)) * (∫ p in K, Φ p ^ 2) :=
      le_trans (hcs N) (mul_le_mul_of_nonneg_right (hRZ2_le N) hB)
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact le_trans (Real.sqrt_le_sqrt h1) (le_of_eq (Real.sqrt_mul hX _))
  have hlimZero : Filter.Tendsto (fun N : ℕ => ∫ p in K, RZ N p * Φ p) Filter.atTop
      (nhds 0) := by
    have hnorm : Filter.Tendsto (fun N : ℕ => ‖∫ p in K, RZ N p * Φ p‖) Filter.atTop
        (nhds 0) := by
      refine squeeze_zero' (Eventually.of_forall (fun N => norm_nonneg _))
        (Eventually.of_forall (fun N => hbound N)) ?_
      have hA0 : Filter.Tendsto
          (fun N : ℕ => (1 / Real.cos d) * (∫ p in K, RZ N p ^ 2 * Real.cos p.2))
          Filter.atTop (nhds 0) := by
        simpa only [mul_zero] using hres_lim.const_mul (1 / Real.cos d)
      have hs : Filter.Tendsto (fun N : ℕ =>
          Real.sqrt ((1 / Real.cos d) * (∫ p in K, RZ N p ^ 2 * Real.cos p.2)))
          Filter.atTop (nhds 0) := by
        have hcont := Real.continuous_sqrt.tendsto 0
        simpa only [Function.comp_def, Real.sqrt_zero] using hcont.comp hA0
      have hprod : Filter.Tendsto (fun N : ℕ =>
          Real.sqrt ((1 / Real.cos d) * (∫ p in K, RZ N p ^ 2 * Real.cos p.2))
            * Real.sqrt (∫ p in K, Φ p ^ 2)) Filter.atTop
          (nhds (0 * Real.sqrt (∫ p in K, Φ p ^ 2))) :=
        hs.mul_const (Real.sqrt (∫ p in K, Φ p ^ 2))
      rwa [zero_mul] at hprod
    exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa using hnorm)
  have hdiff : ∀ N : ℕ, (∫ p in K, SN N p * Φ p) - (∫ p in K, F p.1 p.2 * Φ p)
      = ∫ p in K, RZ N p * Φ p := by
    intro N
    rw [← MeasureTheory.integral_sub (hSNΦK N) hFΦK]
    congr 1
    funext p
    dsimp only [RZ]
    ring
  have hlimSN : Filter.Tendsto (fun N : ℕ => ∫ p in K, SN N p * Φ p) Filter.atTop
      (nhds (∫ p in K, F p.1 p.2 * Φ p)) := by
    have hkey : (fun N : ℕ => ∫ p in K, SN N p * Φ p)
        = fun N => (∫ p in K, RZ N p * Φ p) + (∫ p in K, F p.1 p.2 * Φ p) := by
      funext N
      have h := hdiff N
      linarith
    rw [hkey]
    simpa using hlimZero.add (tendsto_const_nhds (x := ∫ p in K, F p.1 p.2 * Φ p))
  -- transfer the limit back to the quadrant
  have hvanN : ∀ N : ℕ, (∫ p in Work.FTS.EllipticEst.Q0,
        (∑ m ∈ Finset.range (N + 1), Work.FTS.PhiStar.Series.cmode m F p.1
          * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) * φ p.1 p.2
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) = ∫ p in K, SN N p * Φ p := by
    intro N
    rw [hvan (fun p => (∑ m ∈ Finset.range (N + 1), Work.FTS.PhiStar.Series.cmode m F p.1
          * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) * φ p.1 p.2
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
        (fun p hp => by rw [hphi0 p hp.2]; ring)]
    refine MeasureTheory.setIntegral_congr_fun hKmeas (fun p _ => ?_)
    dsimp only [SN, Φ]
    ring
  have hvanF : (∫ p in Work.FTS.EllipticEst.Q0,
        F p.1 p.2 * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      = ∫ p in K, F p.1 p.2 * Φ p := by
    rw [hvan (fun p => F p.1 p.2 * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
        (fun p hp => by rw [hphi0 p hp.2]; ring)]
    refine MeasureTheory.setIntegral_congr_fun hKmeas (fun p _ => ?_)
    dsimp only [Φ]
    ring
  rw [funext hvanN, hvanF]
  exact hlimSN

end Work.FTS.H2.ModalSolR
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.BoxDataH.Crux =====
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

/-- **The `C^{2,β}` Arzelà–Ascoli crux.**  A family with the uniform box data `BoxUniform2`, whose
values converge pointwise on the box to `G`, has a limit `G` which is `C²` within the box. -/
theorem contDiffOn_two_of_boxUniform2 {H : ℕ → ℝ → ℝ → ℝ} {G : ℝ → ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hU : BoxUniform2 a b H)
    (hconv : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      Filter.Tendsto (fun n => H n z θ) Filter.atTop (𝓝 (G z θ))) :
    ContDiffOn ℝ 2 (Function.uncurry G) (cbox a b) := by
  obtain ⟨K, β, hβ, hsm, hb, hh⟩ := hU
  have hU' : BoxUniform2 a b H := ⟨K, β, hβ, hsm, hb, hh⟩
  -- the Lipschitz bound of the two first-order components
  have hlip : ∀ n, ∀ p ∈ cbox a b, ∀ q ∈ cbox a b,
      (|wPz (cbox a b) (Function.uncurry (H n)) p
          - wPz (cbox a b) (Function.uncurry (H n)) q| ≤ K * ‖p - q‖ ∧
        |wPth (cbox a b) (Function.uncurry (H n)) p
          - wPth (cbox a b) (Function.uncurry (H n)) q| ≤ K * ‖p - q‖) :=
    fun n p hp q hq =>
      ⟨(wJet_lip hab (hsm n) (hb n 2 (by norm_num))).1 p hp q hq,
        (wJet_lip hab (hsm n) (hb n 2 (by norm_num))).2 p hp q hq⟩
  -- the Arzelà–Ascoli extraction of the six within-partials
  obtain ⟨φ, hφ, g, hcv, hcontg⟩ := wJet_subseq_extract hab hβ hsm hb hh hlip
  -- the three staircases
  obtain ⟨hS0, hS1, hS2⟩ :=
    staircase_data_of_boxUniform2_core hab hU' hφ.tendsto_atTop hcv hcontg hconv
      (fun n => wJet_slice hab (hsm (φ n)))
  -- continuity of the limit's components
  have hcontA : ContinuousOn (Function.uncurry (fun z θ => g (z, θ) 0)) (cbox a b) := by
    change ContinuousOn (fun p : ℝ × ℝ => g p 0) (cbox a b)
    exact (continuous_apply 0).comp_continuousOn hcontg
  have hcontB : ContinuousOn (Function.uncurry (fun z θ => g (z, θ) 1)) (cbox a b) := by
    change ContinuousOn (fun p : ℝ × ℝ => g p 1) (cbox a b)
    exact (continuous_apply 1).comp_continuousOn hcontg
  have hcontA₁ : ContinuousOn (Function.uncurry (fun z θ => g (z, θ) 2)) (cbox a b) := by
    change ContinuousOn (fun p : ℝ × ℝ => g p 2) (cbox a b)
    exact (continuous_apply 2).comp_continuousOn hcontg
  have hcontA₂ : ContinuousOn (Function.uncurry (fun z θ => g (z, θ) 3)) (cbox a b) := by
    change ContinuousOn (fun p : ℝ × ℝ => g p 3) (cbox a b)
    exact (continuous_apply 3).comp_continuousOn hcontg
  have hcontB₁ : ContinuousOn (Function.uncurry (fun z θ => g (z, θ) 4)) (cbox a b) := by
    change ContinuousOn (fun p : ℝ × ℝ => g p 4) (cbox a b)
    exact (continuous_apply 4).comp_continuousOn hcontg
  have hcontB₂ : ContinuousOn (Function.uncurry (fun z θ => g (z, θ) 5)) (cbox a b) := by
    change ContinuousOn (fun p : ℝ × ℝ => g p 5) (cbox a b)
    exact (continuous_apply 5).comp_continuousOn hcontg
  exact contDiffOn_two_of_fderivWithin_data (G := G)
    (A := fun z θ => g (z, θ) 0) (B := fun z θ => g (z, θ) 1)
    (A₁ := fun z θ => g (z, θ) 2) (A₂ := fun z θ => g (z, θ) 3)
    (B₁ := fun z θ => g (z, θ) 4) (B₂ := fun z θ => g (z, θ) 5)
    hab hcontA hcontB hcontA₁ hcontA₂ hcontB₁ hcontB₂ hS0 hS1 hS2

end Work.FTS_EllLimOK.BoxDataH
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.PkgJets.pinCs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.PkgJets

set_option autoImplicit false
set_option maxHeartbeats 1600000
/-! ## Elementary comparison of the two primitives -/


/-- Cauchy–Schwarz on a subinterval of the open quadrant, for continuous functions. -/
theorem cs_subinterval {u v : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hu : ContinuousOn u (Set.Icc a b)) (hv : ContinuousOn v (Set.Icc a b)) :
    (∫ t in a..b, u t * v t) ^ 2 ≤ (∫ t in a..b, u t ^ 2) * (∫ t in a..b, v t ^ 2) := by
  have hmu : MemLp u 2 (volume.restrict (Set.Icc a b)) := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq (hu.aestronglyMeasurable measurableSet_Icc)]
    exact (hu.pow 2).integrableOn_compact isCompact_Icc
  have hmv : MemLp v 2 (volume.restrict (Set.Icc a b)) := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq (hv.aestronglyMeasurable measurableSet_Icc)]
    exact (hv.pow 2).integrableOn_compact isCompact_Icc
  have hcs := Work.Spaces.cs_integral hmu hmv
  have h1 : (∫ t in a..b, u t * v t) = ∫ t in Set.Icc a b, u t * v t := by
    rw [intervalIntegral.integral_of_le hab.le]
    exact MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioc_ae_eq_Icc (μ := volume))
  have h2 : (∫ t in a..b, u t ^ 2) = ∫ t in Set.Icc a b, u t ^ 2 := by
    rw [intervalIntegral.integral_of_le hab.le]
    exact MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioc_ae_eq_Icc (μ := volume))
  have h3 : (∫ t in a..b, v t ^ 2) = ∫ t in Set.Icc a b, v t ^ 2 := by
    rw [intervalIntegral.integral_of_le hab.le]
    exact MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioc_ae_eq_Icc (μ := volume))
  rw [h1, h2, h3]
  exact hcs

/-! ## The boundary term at the singular end -/


end Work.FTS_EllLimOK.PkgJets
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.contDiffOn_two_of_sliceData =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.BoxAux

set_option autoImplicit false

/-! ## Step 1: the two within-slice derivatives give the within-Fréchet derivative -/

/-- **Staircase from within-slice data.**  If a function `F` of two variables has, on the box
`[a,b] × [0,π/2]`, `z`-slice within-derivative `A` and `θ`-slice within-derivative `B`, with
`F`, `A`, `B` continuous on the box, then `F` is within-Fréchet differentiable on the box with
derivative `ellCop (A p) (B p)`. -/
theorem hasFDerivWithinAt_uncurry_of_sliceData
    {F A B : ℝ → ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcontF : ContinuousOn (Function.uncurry F) (Work.FTS_EllLimOK.cbox a b))
    (hcontA : ContinuousOn (Function.uncurry A) (Work.FTS_EllLimOK.cbox a b))
    (hcontB : ContinuousOn (Function.uncurry B) (Work.FTS_EllLimOK.cbox a b))
    (hsz : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
      HasDerivWithinAt (fun z' => F z' θ) (A z θ) (Set.Icc a b) z)
    (hth : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
      HasDerivWithinAt (fun θ' => F z θ') (B z θ) (Set.Icc 0 (Real.pi / 2)) θ) :
    ∀ p ∈ Work.FTS_EllLimOK.cbox a b,
      HasFDerivWithinAt (Function.uncurry F)
        (Work.FTS_EllLimOK.ellCop (A p.1 p.2) (B p.1 p.2))
        (Work.FTS_EllLimOK.cbox a b) p := by
  have hcd : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  -- the constant sequence converges uniformly to itself
  have hunif : ∀ P : ℝ → ℝ → ℝ,
      TendstoUniformlyOn (fun (_ : ℕ) (p : ℝ × ℝ) => P p.1 p.2)
        (fun p : ℝ × ℝ => P p.1 p.2) Filter.atTop
        (Set.Icc a b ×ˢ Set.Icc 0 (Real.pi / 2)) := by
    intro P
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    exact Filter.Eventually.of_forall fun n p hp => by simpa using hε
  have hmain := Work.FTS_EllLimOK.BoxRegAux.hasFDerivWithinAt_of_uniform_slice_partials
    (a := a) (b := b) (c := 0) (d := Real.pi / 2) hab hcd
    (H := fun _ : ℕ => F) (H₀ := F) (P := fun _ : ℕ => A) (P₀ := A)
    (Q := fun _ : ℕ => B) (Q₀ := B)
    (fun _ => by simpa only [Work.FTS_EllLimOK.cbox, Function.uncurry] using hcontF)
    (fun _ z hz θ hθ => hsz z hz θ hθ)
    (fun _ z hz θ hθ => hth z hz θ hθ)
    (fun _ => by simpa only [Work.FTS_EllLimOK.cbox, Function.uncurry] using hcontA)
    (fun _ => by simpa only [Work.FTS_EllLimOK.cbox, Function.uncurry] using hcontB)
    (fun z hz θ hθ => tendsto_const_nhds)
    (hunif A) (hunif B)
    (by simpa only [Work.FTS_EllLimOK.cbox, Function.uncurry] using hcontA)
    (by simpa only [Work.FTS_EllLimOK.cbox, Function.uncurry] using hcontB)
  intro p hp
  obtain ⟨z, θ⟩ := p
  rw [Work.FTS_EllLimOK.mem_cbox] at hp
  exact hmain z hp.1 θ hp.2

/-! ## Step 2: the assembly (with `a ≤ b`, so that the degenerate box is covered) -/

/-- **The closed-box `C²` assembly from within-Fréchet data.**  This is
`BoxDataH.contDiffOn_two_of_fderivWithin_data` with `a ≤ b` in place of `a < b`; the proof is
that of the cited theorem, which does not use its `a < b` hypothesis. -/
theorem contDiffOn_two_of_fderivWithin_data_le {G A B A₁ A₂ B₁ B₂ : ℝ → ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hcontA : ContinuousOn (fun p : ℝ × ℝ => A p.1 p.2) (Work.FTS_EllLimOK.cbox a b))
    (hcontB : ContinuousOn (fun p : ℝ × ℝ => B p.1 p.2) (Work.FTS_EllLimOK.cbox a b))
    (hcontA₁ : ContinuousOn (fun p : ℝ × ℝ => A₁ p.1 p.2) (Work.FTS_EllLimOK.cbox a b))
    (hcontA₂ : ContinuousOn (fun p : ℝ × ℝ => A₂ p.1 p.2) (Work.FTS_EllLimOK.cbox a b))
    (hcontB₁ : ContinuousOn (fun p : ℝ × ℝ => B₁ p.1 p.2) (Work.FTS_EllLimOK.cbox a b))
    (hcontB₂ : ContinuousOn (fun p : ℝ × ℝ => B₂ p.1 p.2) (Work.FTS_EllLimOK.cbox a b))
    (hS0 : ∀ p ∈ Work.FTS_EllLimOK.cbox a b, HasFDerivWithinAt (Function.uncurry G)
      (Work.FTS_EllLimOK.ellCop (A p.1 p.2) (B p.1 p.2)) (Work.FTS_EllLimOK.cbox a b) p)
    (hS1 : ∀ p ∈ Work.FTS_EllLimOK.cbox a b, HasFDerivWithinAt (Function.uncurry A)
      (Work.FTS_EllLimOK.ellCop (A₁ p.1 p.2) (A₂ p.1 p.2)) (Work.FTS_EllLimOK.cbox a b) p)
    (hS2 : ∀ p ∈ Work.FTS_EllLimOK.cbox a b, HasFDerivWithinAt (Function.uncurry B)
      (Work.FTS_EllLimOK.ellCop (B₁ p.1 p.2) (B₂ p.1 p.2)) (Work.FTS_EllLimOK.cbox a b) p) :
    ContDiffOn ℝ 2 (Function.uncurry G) (Work.FTS_EllLimOK.cbox a b) := by
  -- `A` is `C¹` within the box (with derivative `ellCop A₁ A₂`)
  have hA_c1 : ∀ q ∈ Work.FTS_EllLimOK.cbox a b,
      ContDiffWithinAt ℝ 1 (fun y : ℝ × ℝ => A y.1 y.2) (Work.FTS_EllLimOK.cbox a b) q := by
    intro q hq
    have haux : ContDiffWithinAt ℝ ((0 : ℕ∞ω) + 1) (fun y : ℝ × ℝ => A y.1 y.2)
        (Work.FTS_EllLimOK.cbox a b) q := by
      refine (contDiffWithinAt_succ_iff_hasFDerivWithinAt' (n := 0) (by simp)).mpr ?_
      refine ⟨insert q (Work.FTS_EllLimOK.cbox a b), self_mem_nhdsWithin, subset_rfl,
        fun h => absurd h (by simp),
        (fun y : ℝ × ℝ => Work.FTS_EllLimOK.ellCop (A₁ y.1 y.2) (A₂ y.1 y.2)), ?_, ?_⟩
      · intro y hy
        have hy' : y ∈ Work.FTS_EllLimOK.cbox a b := by
          rcases Set.mem_insert_iff.mp hy with h | h
          · rw [h]; exact hq
          · exact h
        exact hS1 y hy'
      · refine (contDiffWithinAt_zero hq).2 ⟨Work.FTS_EllLimOK.cbox a b, self_mem_nhdsWithin, ?_⟩
        intro y hy
        exact Work.FTS_EllLimOK.continuousWithinAt_ellCop
          ((hcontA₁.continuousWithinAt hy.1).mono Set.inter_subset_left)
          ((hcontA₂.continuousWithinAt hy.1).mono Set.inter_subset_left)
    simpa using haux
  -- `B` is `C¹` within the box (with derivative `ellCop B₁ B₂`)
  have hB_c1 : ∀ q ∈ Work.FTS_EllLimOK.cbox a b,
      ContDiffWithinAt ℝ 1 (fun y : ℝ × ℝ => B y.1 y.2) (Work.FTS_EllLimOK.cbox a b) q := by
    intro q hq
    have haux : ContDiffWithinAt ℝ ((0 : ℕ∞ω) + 1) (fun y : ℝ × ℝ => B y.1 y.2)
        (Work.FTS_EllLimOK.cbox a b) q := by
      refine (contDiffWithinAt_succ_iff_hasFDerivWithinAt' (n := 0) (by simp)).mpr ?_
      refine ⟨insert q (Work.FTS_EllLimOK.cbox a b), self_mem_nhdsWithin, subset_rfl,
        fun h => absurd h (by simp),
        (fun y : ℝ × ℝ => Work.FTS_EllLimOK.ellCop (B₁ y.1 y.2) (B₂ y.1 y.2)), ?_, ?_⟩
      · intro y hy
        have hy' : y ∈ Work.FTS_EllLimOK.cbox a b := by
          rcases Set.mem_insert_iff.mp hy with h | h
          · rw [h]; exact hq
          · exact h
        exact hS2 y hy'
      · refine (contDiffWithinAt_zero hq).2 ⟨Work.FTS_EllLimOK.cbox a b, self_mem_nhdsWithin, ?_⟩
        intro y hy
        exact Work.FTS_EllLimOK.continuousWithinAt_ellCop
          ((hcontB₁.continuousWithinAt hy.1).mono Set.inter_subset_left)
          ((hcontB₂.continuousWithinAt hy.1).mono Set.inter_subset_left)
    simpa using haux
  -- the derivative family `y ↦ ellCop (A y) (B y)` is `C¹` within the box
  have hf'_c1 : ∀ q ∈ Work.FTS_EllLimOK.cbox a b,
      ContDiffWithinAt ℝ 1
        (fun u : ℝ × ℝ => Work.FTS_EllLimOK.ellCop (A u.1 u.2) (B u.1 u.2))
        (Work.FTS_EllLimOK.cbox a b) q := by
    intro q hq
    have hpair : ContDiffWithinAt ℝ 1 (fun y : ℝ × ℝ => (A y.1 y.2, B y.1 y.2))
        (Work.FTS_EllLimOK.cbox a b) q := (hA_c1 q hq).prodMk (hB_c1 q hq)
    have hg : ContDiffWithinAt ℝ 1 (fun w : ℝ × ℝ => Work.FTS_EllLimOK.copBilin w)
        (Set.univ : Set (ℝ × ℝ)) (A q.1 q.2, B q.1 q.2) :=
      (ContinuousLinearMap.contDiff Work.FTS_EllLimOK.copBilin).contDiffWithinAt
    have h2 : ContDiffWithinAt ℝ 1
        (fun y : ℝ × ℝ => Work.FTS_EllLimOK.copBilin (A y.1 y.2, B y.1 y.2))
        (Work.FTS_EllLimOK.cbox a b) q :=
      hg.comp q hpair (fun y _ => Set.mem_univ _)
    refine h2.congr (fun y _ => (Work.FTS_EllLimOK.copBilin_apply (A y.1 y.2) (B y.1 y.2)).symm)
      (Work.FTS_EllLimOK.copBilin_apply (A q.1 q.2) (B q.1 q.2)).symm
  -- the second-order conclusion, in the `n + 1` form
  have hmain : ∀ q ∈ Work.FTS_EllLimOK.cbox a b, ContDiffWithinAt ℝ ((1 : ℕ∞ω) + 1)
      (Function.uncurry G) (Work.FTS_EllLimOK.cbox a b) q := by
    intro q hq
    refine (contDiffWithinAt_succ_iff_hasFDerivWithinAt' (n := 1) (by simp)).mpr ?_
    refine ⟨insert q (Work.FTS_EllLimOK.cbox a b), self_mem_nhdsWithin, subset_rfl,
      fun h => absurd h (by simp),
      (fun u : ℝ × ℝ => Work.FTS_EllLimOK.ellCop (A u.1 u.2) (B u.1 u.2)), ?_, hf'_c1 q hq⟩
    intro y hy
    have hy' : y ∈ Work.FTS_EllLimOK.cbox a b := by
      rcases Set.mem_insert_iff.mp hy with h | h
      · rw [h]; exact hq
      · exact h
    exact hS0 y hy'
  intro p hp
  simpa [show ((1 : ℕ∞ω) + 1 : ℕ∞ω) = 2 from by norm_num] using hmain p hp

/-! ## Step 3: the requested theorem -/

theorem contDiffOn_two_of_sliceData
    {Ψ A B A₁ A₂ B₁ B₂ : ℝ → ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcontΨ : ContinuousOn (Function.uncurry Ψ) (Work.FTS_EllLimOK.cbox a b))
    (hcontA : ContinuousOn (Function.uncurry A) (Work.FTS_EllLimOK.cbox a b))
    (hcontB : ContinuousOn (Function.uncurry B) (Work.FTS_EllLimOK.cbox a b))
    (hcontA₁ : ContinuousOn (Function.uncurry A₁) (Work.FTS_EllLimOK.cbox a b))
    (hcontA₂ : ContinuousOn (Function.uncurry A₂) (Work.FTS_EllLimOK.cbox a b))
    (hcontB₁ : ContinuousOn (Function.uncurry B₁) (Work.FTS_EllLimOK.cbox a b))
    (hcontB₂ : ContinuousOn (Function.uncurry B₂) (Work.FTS_EllLimOK.cbox a b))
    (hszΨ : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
      HasDerivWithinAt (fun z' => Ψ z' θ) (A z θ) (Set.Icc a b) z)
    (hthΨ : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
      HasDerivWithinAt (fun θ' => Ψ z θ') (B z θ) (Set.Icc 0 (Real.pi / 2)) θ)
    (hszA : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
      HasDerivWithinAt (fun z' => A z' θ) (A₁ z θ) (Set.Icc a b) z)
    (hthA : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
      HasDerivWithinAt (fun θ' => A z θ') (A₂ z θ) (Set.Icc 0 (Real.pi / 2)) θ)
    (hszB : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
      HasDerivWithinAt (fun z' => B z' θ) (B₁ z θ) (Set.Icc a b) z)
    (hthB : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
      HasDerivWithinAt (fun θ' => B z θ') (B₂ z θ) (Set.Icc 0 (Real.pi / 2)) θ) :
    ContDiffOn ℝ 2 (Function.uncurry Ψ) (Work.FTS_EllLimOK.cbox a b) := by
  have hG : ∀ p ∈ Work.FTS_EllLimOK.cbox a b,
      HasFDerivWithinAt (Function.uncurry Ψ)
        (Work.FTS_EllLimOK.ellCop (A p.1 p.2) (B p.1 p.2))
        (Work.FTS_EllLimOK.cbox a b) p :=
    hasFDerivWithinAt_uncurry_of_sliceData hab hcontΨ hcontA hcontB hszΨ hthΨ
  have hA : ∀ p ∈ Work.FTS_EllLimOK.cbox a b,
      HasFDerivWithinAt (Function.uncurry A)
        (Work.FTS_EllLimOK.ellCop (A₁ p.1 p.2) (A₂ p.1 p.2))
        (Work.FTS_EllLimOK.cbox a b) p :=
    hasFDerivWithinAt_uncurry_of_sliceData hab hcontA hcontA₁ hcontA₂ hszA hthA
  have hB : ∀ p ∈ Work.FTS_EllLimOK.cbox a b,
      HasFDerivWithinAt (Function.uncurry B)
        (Work.FTS_EllLimOK.ellCop (B₁ p.1 p.2) (B₂ p.1 p.2))
        (Work.FTS_EllLimOK.cbox a b) p :=
    hasFDerivWithinAt_uncurry_of_sliceData hab hcontB hcontB₁ hcontB₂ hszB hthB
  exact contDiffOn_two_of_fderivWithin_data_le hab hcontA hcontB hcontA₁ hcontA₂ hcontB₁ hcontB₂
    hG hA hB

end Work.FTS_EllLimOK.ProducerH.BoxAux
end
end
