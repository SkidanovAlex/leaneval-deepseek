import Mathlib
import Submission.Commons.Analysis.Convolution.fderiv_moll_weakGrad
import Submission.Commons.Analysis.Convolution.tendsto_integral_sq_moll_sub_compact_measurable
import Submission.Commons.Analysis.Convolution.tendsto_integral_sq_moll_sub_compact_vec_measurable
import Submission.Commons.Analysis.Measure.locallyIntegrable_of_aestronglyMeasurable_of_integrableOn_sq
import Submission.Commons.Analysis.Convolution.contDiff_integral_smul_sub

namespace Commons.Analysis.GaussianMeasure

open MeasureTheory Filter
open scoped RealInnerProductSpace InnerProductSpace Topology

noncomputable section

set_option maxHeartbeats 4000000

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ## A concrete mollifier family on `EuclideanSpace ℝ (Fin n)` -/

/-- A sequence of smooth bump functions centred at `0` with `rOut = 1/(k+1)` and
`rIn = 1/(2(k+1))`. -/
noncomputable def weBump (n k : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
  ⟨(1 / ((k : ℝ) + 1)) / 2, 1 / ((k : ℝ) + 1), by positivity, by
    have h : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    linarith⟩

noncomputable def weRho (n k : ℕ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  (weBump n k).normed volume

@[simp] lemma weRho_smooth (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (weRho n k) :=
  (weBump n k).contDiff_normed

lemma weRho_cs (k : ℕ) : HasCompactSupport (weRho n k) :=
  (weBump n k).hasCompactSupport_normed

lemma weRho_nn (k : ℕ) (x : E) : 0 ≤ weRho n k x :=
  ContDiffBump.nonneg_normed (weBump n k) x

lemma weRho_int (k : ℕ) : (∫ x, weRho n k x ∂(volume : Measure E)) = 1 :=
  ContDiffBump.integral_normed (weBump n k)

lemma weRho_supp (k : ℕ) (x : E) (hx : (weBump n k).rOut < ‖x‖) : weRho n k x = 0 := by
  by_contra h
  have hmem : x ∈ Function.support (weRho n k) := Function.mem_support.mpr h
  rw [weRho, ContDiffBump.support_normed_eq] at hmem
  rw [Metric.mem_ball, dist_zero_right] at hmem
  linarith

lemma weRho_integrable (k : ℕ) : Integrable (weRho n k) (volume : Measure E) :=
  (weRho_smooth k).continuous.integrable_of_hasCompactSupport (weRho_cs k)

lemma weRout_tendsto (n : ℕ) :
    Tendsto (fun k : ℕ => (weBump n k).rOut) atTop (nhds 0) := by
  have h : Tendsto (fun k : ℕ => (1 : ℝ) / (k + 1)) atTop (nhds 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa [weBump] using h

/-! ## Scalar and vector mollifications -/

def mollS (ρ : E → ℝ) (u : E → ℝ) : E → ℝ := fun x => ∫ y, ρ y • u (x - y) ∂(volume : Measure E)
def mollV (ρ : E → ℝ) (u : E → E) : E → E := fun x => ∫ y, ρ y • u (x - y) ∂(volume : Measure E)

lemma mollS_eq_conv (ρ u : E → ℝ) :
    mollS ρ u = MeasureTheory.convolution ρ u (ContinuousLinearMap.mul ℝ ℝ) volume := by
  funext x
  rw [mollS, MeasureTheory.convolution_def]
  simp only [ContinuousLinearMap.mul_apply', smul_eq_mul]

lemma mollV_eq_conv (ρ : E → ℝ) (u : E → E) :
    mollV ρ u = MeasureTheory.convolution ρ u
        ((ContinuousLinearMap.smulRightL ℝ ℝ E (1 : ℝ →L[ℝ] ℝ)).flip) volume := by
  funext x
  rw [mollV, MeasureTheory.convolution_def]
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.smulRightL_apply_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply]

lemma mollS_smooth (ρ u : E → ℝ) (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hcρ : HasCompactSupport ρ)
    (hu : LocallyIntegrable u (volume : Measure E)) :
    ContDiff ℝ (⊤ : ℕ∞) (mollS ρ u) := by
  rw [mollS_eq_conv]
  exact hcρ.contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℝ) hρ hu

lemma mollV_smooth (ρ : E → ℝ) (u : E → E) (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hcρ : HasCompactSupport ρ) (hu : LocallyIntegrable u (volume : Measure E)) :
    ContDiff ℝ (⊤ : ℕ∞) (mollV ρ u) := by
  rw [mollV_eq_conv]
  exact hcρ.contDiff_convolution_left
    ((ContinuousLinearMap.smulRightL ℝ ℝ E (1 : ℝ →L[ℝ] ℝ)).flip) hρ hu

lemma mollS_eq_rho (ρ u : E → ℝ) :
    mollS ρ u = fun y => ∫ t, u t * ρ (y - t) ∂(volume : Measure E) := by
  funext y
  rw [mollS]
  have hfun : (fun t : E => ρ t • u (y - t))
      = (fun x : E => (fun s : E => u s * ρ (y - s)) (y - x)) := by
    funext t
    show ρ t • u (y - t) = u (y - t) * ρ (y - (y - t))
    rw [smul_eq_mul, show y - (y - t) = t from by abel]
    ring
  rw [hfun]
  exact integral_sub_left_eq_self (fun s : E => u s * ρ (y - s)) volume y

lemma mollV_subst (ρ : E → ℝ) (U : E → E) (y : E) :
    (∫ t, ρ (y - t) • U t ∂(volume : Measure E)) = mollV ρ U y := by
  rw [mollV]
  rw [← integral_sub_left_eq_self (fun t : E => ρ (y - t) • U t) volume y]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  show ρ (y - (y - t)) • U (y - t) = ρ t • U (y - t)
  rw [show y - (y - t) = t from by abel]

lemma hasCompactSupport_comp_subLeft {ρ : E → ℝ} (hcρ : HasCompactSupport ρ) (y : E) :
    HasCompactSupport (fun t : E => ρ (y - t)) := by
  rw [HasCompactSupport]
  change IsCompact (tsupport (ρ ∘ ⇑(Homeomorph.subLeft y)))
  rw [tsupport_comp_eq_preimage]
  exact (Homeomorph.isCompact_preimage (Homeomorph.subLeft y)).mpr hcρ

lemma fderiv_mollS_weakGrad (ρ u : E → ℝ) (G : E → E)
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hcρ : HasCompactSupport ρ)
    (hu : LocallyIntegrable u (volume : Measure E)) (hGint : LocallyIntegrable G (volume : Measure E))
    (hG : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∀ v : E, ∫ x, u x * (fderiv ℝ φ x) v ∂(volume : Measure E)
        = - ∫ x, φ x * ⟪G x, v⟫_ℝ ∂(volume : Measure E)) :
    ∀ y v : E, (fderiv ℝ (mollS ρ u) y) v = ∫ t, ρ (y - t) * ⟪G t, v⟫_ℝ ∂(volume : Measure E) := by
  intro y v
  have hFeq : mollS ρ u = fun y => ∫ t, u t * ρ (y - t) ∂(volume : Measure E) := mollS_eq_rho ρ u
  have hksupp : ∀ z ∈ tsupport ρ, (y - z) ∈ Set.image (Homeomorph.subLeft y) (tsupport ρ) := by
    intro z hz
    exact ⟨z, hz, rfl⟩
  have hG' : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      tsupport φ ⊆ Set.image (Homeomorph.subLeft y) (tsupport ρ) → ∀ v : E,
      ∫ x, u x * (fderiv ℝ φ x) v ∂(volume : Measure E)
        = - ∫ x, φ x * ⟪G x, v⟫_ℝ ∂(volume : Measure E) := by
    intro φ hφ hsub v
    have hK : IsCompact (Set.image (Homeomorph.subLeft y) (tsupport ρ)) :=
      hcρ.image (Homeomorph.subLeft y).continuous
    exact hG φ hφ (hK.of_isClosed_subset (isClosed_tsupport φ) hsub) v
  have hval := Commons.Analysis.Convolution.fderiv_moll_weakGrad ρ u G
    (Set.image (Homeomorph.subLeft y) (tsupport ρ)) y hρ hcρ hu hGint hksupp hG' v
  rw [hFeq]
  exact hval

lemma fderiv_mollS_eq_mollV (ρ u : E → ℝ) (G : E → E)
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hcρ : HasCompactSupport ρ)
    (hu : LocallyIntegrable u (volume : Measure E)) (hGint : LocallyIntegrable G (volume : Measure E))
    (hG : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∀ v : E, ∫ x, u x * (fderiv ℝ φ x) v ∂(volume : Measure E)
        = - ∫ x, φ x * ⟪G x, v⟫_ℝ ∂(volume : Measure E)) :
    ∀ y v : E, (fderiv ℝ (mollS ρ u) y) v = ⟪mollV ρ G y, v⟫_ℝ := by
  intro y v
  rw [fderiv_mollS_weakGrad ρ u G hρ hcρ hu hGint hG y v]
  have hcont : Continuous (fun t : E => ρ (y - t)) := hρ.continuous.comp (continuous_const.sub continuous_id)
  have hint : Integrable (fun t : E => ρ (y - t) • G t) volume :=
    hGint.integrable_smul_left_of_hasCompactSupport hcont (hasCompactSupport_comp_subLeft hcρ y)
  calc (∫ t, ρ (y - t) * ⟪G t, v⟫_ℝ)
      = ∫ t, inner ℝ v (ρ (y - t) • G t) := by
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        show ρ (y - t) * ⟪G t, v⟫_ℝ = inner ℝ v (ρ (y - t) • G t)
        rw [real_inner_smul_right, real_inner_comm]
    _ = inner ℝ v (∫ t, ρ (y - t) • G t) := integral_inner hint v
    _ = inner ℝ (∫ t, ρ (y - t) • G t) v := real_inner_comm _ _
    _ = ⟪mollV ρ G y, v⟫_ℝ := by rw [mollV_subst]

/-! ## Two elementary `L²`-convergence lemmas -/

lemma tendsto_integral_mul_of_tendsto_sq {ι : Type*} {l : Filter ι}
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {a u₀ : X → ℝ} {u : ι → X → ℝ}
    (ha : MemLp a 2 μ) (hu₀ : MemLp u₀ 2 μ) (hu : ∀ k, MemLp (u k) 2 μ)
    (h : Tendsto (fun k => ∫ x, (u k x - u₀ x) ^ 2 ∂μ) l (nhds 0)) :
    Tendsto (fun k => ∫ x, a x * u k x ∂μ) l (nhds (∫ x, a x * u₀ x ∂μ)) := by
  have hsub : ∀ k, MemLp (fun x => u k x - u₀ x) 2 μ := fun k => (hu k).sub hu₀
  have hsub' : ∀ k, MemLp (fun x => u k x - u₀ x) (ENNReal.ofReal 2) μ := fun k => by simpa using hsub k
  have ha' : MemLp a (ENNReal.ofReal 2) μ := by simpa using ha
  have hain : ∀ k, Integrable (fun x => a x * u k x) μ := fun k => ha.integrable_mul (hu k)
  have hai0 : Integrable (fun x => a x * u₀ x) μ := ha.integrable_mul hu₀
  have key : ∀ k, (∫ x, a x * u k x ∂μ) - (∫ x, a x * u₀ x ∂μ)
      = ∫ x, a x * (u k x - u₀ x) ∂μ := by
    intro k
    rw [← integral_sub (hain k) hai0]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    ring
  have hbound : ∀ k, |(∫ x, a x * u k x ∂μ) - (∫ x, a x * u₀ x ∂μ)|
      ≤ Real.sqrt (∫ x, a x ^ 2 ∂μ) * Real.sqrt (∫ x, (u k x - u₀ x) ^ 2 ∂μ) := by
    intro k
    have ha2 : (∫ x, ‖a x‖ ^ (2:ℝ) ∂μ) = ∫ x, a x ^ 2 ∂μ := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      show ‖a x‖ ^ (2:ℝ) = a x ^ 2
      rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
    have hs2 : (∫ x, ‖(fun x => u k x - u₀ x) x‖ ^ (2:ℝ) ∂μ)
        = ∫ x, (u k x - u₀ x) ^ 2 ∂μ := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      show ‖u k x - u₀ x‖ ^ (2:ℝ) = (u k x - u₀ x) ^ 2
      rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
    rw [key k]
    calc |∫ x, a x * (u k x - u₀ x) ∂μ|
        ≤ ∫ x, |a x * (u k x - u₀ x)| ∂μ := abs_integral_le_integral_abs
      _ = ∫ x, ‖a x‖ * ‖(fun x => u k x - u₀ x) x‖ ∂μ := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          show |a x * (u k x - u₀ x)| = ‖a x‖ * ‖u k x - u₀ x‖
          rw [abs_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ (∫ x, ‖a x‖ ^ (2:ℝ) ∂μ) ^ (1 / 2 : ℝ)
            * (∫ x, ‖(fun x => u k x - u₀ x) x‖ ^ (2:ℝ) ∂μ) ^ (1 / 2 : ℝ) :=
          integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two ha' (hsub' k)
      _ = Real.sqrt (∫ x, a x ^ 2 ∂μ) * Real.sqrt (∫ x, (u k x - u₀ x) ^ 2 ∂μ) := by
          rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
          exact congrArg₂ (fun p q => p * q) (congrArg Real.sqrt ha2) (congrArg Real.sqrt hs2)
  have htend : Tendsto (fun k => |(∫ x, a x * u k x ∂μ) - (∫ x, a x * u₀ x ∂μ)|)
      l (nhds 0) := by
    refine squeeze_zero (fun k => abs_nonneg _) hbound ?_
    have hsqrt : Tendsto (fun k => Real.sqrt (∫ x, (u k x - u₀ x) ^ 2 ∂μ)) l (nhds 0) := by
      have hc := (Real.continuous_sqrt.continuousAt).tendsto.comp h
      simpa only [Function.comp_def, Real.sqrt_zero] using hc
    simpa using (tendsto_const_nhds.mul hsqrt)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa [Real.norm_eq_abs] using htend

lemma tendsto_integral_smul_inner_of_tendsto_sq {ι : Type*} {l : Filter ι}
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {a : X → ℝ} {M : ℝ} (hM0 : 0 ≤ M) (ha : AEStronglyMeasurable a μ) (hM : ∀ x, ‖a x‖ ≤ M)
    {V : X → F} (hV : MemLp V 2 μ)
    {U : ι → X → F} (hU : ∀ k, MemLp (U k) 2 μ) {U₀ : X → F} (hU0 : MemLp U₀ 2 μ)
    (h : Tendsto (fun k => ∫ x, ‖U k x - U₀ x‖ ^ 2 ∂μ) l (nhds 0)) :
    Tendsto (fun k => ∫ x, a x * ⟪U k x, V x⟫ ∂μ) l (nhds (∫ x, a x * ⟪U₀ x, V x⟫ ∂μ)) := by
  have hsub : ∀ k, MemLp (fun x => U k x - U₀ x) 2 μ := fun k => (hU k).sub hU0
  have hsub' : ∀ k, MemLp (fun x => U k x - U₀ x) (ENNReal.ofReal 2) μ := fun k => by simpa using hsub k
  have hV' : MemLp V (ENNReal.ofReal 2) μ := by simpa using hV
  have hInt : ∀ k, Integrable (fun x => a x * ⟪U k x, V x⟫) μ := by
    intro k
    have hdom : Integrable (fun x => M * (‖U k x‖ * ‖V x‖)) μ :=
      ((hU k).norm.integrable_mul hV.norm).const_mul M
    refine hdom.mono' (ha.mul ((hU k).aestronglyMeasurable.inner hV.aestronglyMeasurable)) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul]
    calc ‖a x‖ * |⟪U k x, V x⟫| ≤ ‖a x‖ * (‖U k x‖ * ‖V x‖) := by
          gcongr; exact abs_real_inner_le_norm _ _
      _ ≤ M * (‖U k x‖ * ‖V x‖) := by gcongr; exact hM x
  have hInt0 : Integrable (fun x => a x * ⟪U₀ x, V x⟫) μ := by
    have hdom : Integrable (fun x => M * (‖U₀ x‖ * ‖V x‖)) μ :=
      (hU0.norm.integrable_mul hV.norm).const_mul M
    refine hdom.mono' (ha.mul (hU0.aestronglyMeasurable.inner hV.aestronglyMeasurable)) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul]
    calc ‖a x‖ * |⟪U₀ x, V x⟫| ≤ ‖a x‖ * (‖U₀ x‖ * ‖V x‖) := by
          gcongr; exact abs_real_inner_le_norm _ _
      _ ≤ M * (‖U₀ x‖ * ‖V x‖) := by gcongr; exact hM x
  have key : ∀ k, (∫ x, a x * ⟪U k x, V x⟫ ∂μ) - (∫ x, a x * ⟪U₀ x, V x⟫ ∂μ)
      = ∫ x, a x * ⟪U k x - U₀ x, V x⟫ ∂μ := by
    intro k
    rw [← integral_sub (hInt k) hInt0]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show a x * ⟪U k x, V x⟫ - a x * ⟪U₀ x, V x⟫ = a x * ⟪U k x - U₀ x, V x⟫
    rw [inner_sub_left]; ring
  have hbound : ∀ k, |(∫ x, a x * ⟪U k x, V x⟫ ∂μ) - (∫ x, a x * ⟪U₀ x, V x⟫ ∂μ)|
      ≤ M * (Real.sqrt (∫ x, ‖U k x - U₀ x‖ ^ 2 ∂μ) * Real.sqrt (∫ x, ‖V x‖ ^ 2 ∂μ)) := by
    intro k
    have hV2 : (∫ x, ‖V x‖ ^ (2:ℝ) ∂μ) = ∫ x, ‖V x‖ ^ 2 ∂μ := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      show ‖V x‖ ^ (2:ℝ) = ‖V x‖ ^ 2
      rw [Real.rpow_two]
    have hU2 : (∫ x, ‖U k x - U₀ x‖ ^ (2:ℝ) ∂μ) = ∫ x, ‖U k x - U₀ x‖ ^ 2 ∂μ := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      show ‖U k x - U₀ x‖ ^ (2:ℝ) = ‖U k x - U₀ x‖ ^ 2
      rw [Real.rpow_two]
    have hdom2 : Integrable (fun x => M * (‖U k x - U₀ x‖ * ‖V x‖)) μ :=
      ((hsub k).norm.integrable_mul hV.norm).const_mul M
    have hle : ∀ x, ‖a x * ⟪U k x - U₀ x, V x⟫‖ ≤ M * (‖U k x - U₀ x‖ * ‖V x‖) := by
      intro x
      rw [Real.norm_eq_abs, abs_mul]
      calc ‖a x‖ * |⟪U k x - U₀ x, V x⟫| ≤ ‖a x‖ * (‖U k x - U₀ x‖ * ‖V x‖) := by
            gcongr; exact abs_real_inner_le_norm _ _
        _ ≤ M * (‖U k x - U₀ x‖ * ‖V x‖) := by gcongr; exact hM x
    have hIntSigned : Integrable (fun x => a x * ⟪U k x - U₀ x, V x⟫) μ := by
      refine hdom2.mono' (ha.mul ((hsub k).aestronglyMeasurable.inner hV.aestronglyMeasurable)) ?_
      filter_upwards with x
      exact hle x
    rw [key k]
    calc |∫ x, a x * ⟪U k x - U₀ x, V x⟫ ∂μ|
        ≤ ∫ x, |a x * ⟪U k x - U₀ x, V x⟫| ∂μ := abs_integral_le_integral_abs
      _ = ∫ x, ‖a x * ⟪U k x - U₀ x, V x⟫‖ ∂μ := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          show |a x * ⟪U k x - U₀ x, V x⟫| = ‖a x * ⟪U k x - U₀ x, V x⟫‖
          rw [Real.norm_eq_abs]
      _ ≤ ∫ x, M * (‖U k x - U₀ x‖ * ‖V x‖) ∂μ := by
          refine integral_mono_ae hIntSigned.norm hdom2 ?_
          filter_upwards with x
          exact hle x
      _ = M * (∫ x, ‖U k x - U₀ x‖ * ‖V x‖ ∂μ) := integral_const_mul M _
      _ ≤ M * ((∫ x, ‖U k x - U₀ x‖ ^ (2:ℝ) ∂μ) ^ (1 / 2 : ℝ)
                * (∫ x, ‖V x‖ ^ (2:ℝ) ∂μ) ^ (1 / 2 : ℝ)) := by
          gcongr
          exact integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two (hsub' k) hV'
      _ = M * (Real.sqrt (∫ x, ‖U k x - U₀ x‖ ^ 2 ∂μ) * Real.sqrt (∫ x, ‖V x‖ ^ 2 ∂μ)) := by
          rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, hU2, hV2]
  have htend : Tendsto (fun k => |(∫ x, a x * ⟪U k x, V x⟫ ∂μ) - (∫ x, a x * ⟪U₀ x, V x⟫ ∂μ)|)
      l (nhds 0) := by
    refine squeeze_zero (fun k => abs_nonneg _) hbound ?_
    have hsqrt : Tendsto (fun k => Real.sqrt (∫ x, ‖U k x - U₀ x‖ ^ 2 ∂μ)) l (nhds 0) := by
      have hc := (Real.continuous_sqrt.continuousAt).tendsto.comp h
      simpa only [Function.comp_def, Real.sqrt_zero] using hc
    have hlim : Tendsto
        (fun k => M * (Real.sqrt (∫ x, ‖U k x - U₀ x‖ ^ 2 ∂μ) * Real.sqrt (∫ x, ‖V x‖ ^ 2 ∂μ)))
        l (nhds (M * (0 * Real.sqrt (∫ x, ‖V x‖ ^ 2 ∂μ)))) :=
      tendsto_const_nhds.mul (hsqrt.mul tendsto_const_nhds)
    simpa using hlim
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa [Real.norm_eq_abs] using htend

/-! ## Auxiliary lemmas -/

/-- Integrals agree with the restriction to a set on which the integrand is supported. -/
lemma integral_eq_integral_restrict_of_eq_zero_on_compl {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Set X} (hs : MeasurableSet s)
    {φ : X → F} (h : ∀ x, x ∉ s → φ x = 0) :
    (∫ x, φ x ∂μ) = ∫ x, φ x ∂(μ.restrict s) := by
  rw [← integral_indicator hs, Set.indicator_eq_self.mpr]
  intro x hx
  by_contra hc
  exact hx (h x hc)

/-- Vector version of `locallyIntegrable_of_aestronglyMeasurable_of_integrableOn_sq`. -/
lemma locallyIntegrable_vec_of_integrableOn_sq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {G : E → F}
    (hGm : AEStronglyMeasurable G (volume : Measure E))
    (hG : ∀ K : Set E, IsCompact K → IntegrableOn (fun x => ‖G x‖ ^ 2) K (volume : Measure E)) :
    LocallyIntegrable G (volume : Measure E) := by
  rw [locallyIntegrable_iff]
  intro K hK
  have hμK : (volume : Measure E) K < ⊤ := hK.measure_lt_top
  have hone : IntegrableOn (fun _ : E => (1 : ℝ)) K (volume : Measure E) :=
    integrableOn_const (hs := hμK.ne) (by simp)
  have hsum : IntegrableOn (fun x => ‖G x‖ ^ 2 + 1) K (volume : Measure E) :=
    (hG K hK).add hone
  have hbound : ∀ᵐ x ∂((volume : Measure E).restrict K), ‖G x‖ ≤ ‖G x‖ ^ 2 + 1 :=
    Filter.Eventually.of_forall fun x => by
      have h : ‖G x‖ ≤ ‖G x‖ ^ 2 + 1 := by
        nlinarith [sq_nonneg (‖G x‖ - 1 / 2), sq_nonneg ‖G x‖, norm_nonneg (G x)]
      simpa using h
  show Integrable G ((volume : Measure E).restrict K)
  exact hsum.mono' hGm.restrict hbound

/-- Derivative of `x ↦ η x ^ 2 * ξ x` in direction `G x`. -/
private lemma fderiv_mul_sq {n : ℕ} (η ξ : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n))
    (hη : DifferentiableAt ℝ η x) (hξ : DifferentiableAt ℝ ξ x) :
    (fderiv ℝ (fun y => η y ^ 2 * ξ y) x) (G x)
      = η x ^ 2 * (fderiv ℝ ξ x) (G x) + (2 * η x * (fderiv ℝ η x) (G x)) * ξ x := by
  have hfun : (fun y => η y ^ 2 * ξ y) = (η * η) * ξ := by
    funext y
    show η y ^ 2 * ξ y = (η y * η y) * ξ y
    ring
  rw [hfun, fderiv_mul (hη.mul hη) hξ]
  rw [fderiv_mul hη hη]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, Pi.mul_apply]
  ring

/-! ## The energy identity -/

private def weA1 (η : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (w : EuclideanSpace ℝ (Fin n) → ℝ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x => 2 * η x * (fderiv ℝ η x) (G x) * w x

private def weA2 (η : EuclideanSpace ℝ (Fin n) → ℝ)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x => η x ^ 2 * w x

private lemma energy_identity_aux
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (hgmeas : AEStronglyMeasurable g (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hGmeas : AEStronglyMeasurable G (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hwcont : Continuous w)
    (hgloc : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
      IntegrableOn (fun x => g x ^ 2) K (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hGloc : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
      IntegrableOn (fun x => ‖G x‖ ^ 2) K (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hweak : ∀ (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (v : EuclideanSpace ℝ (Fin n)),
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ x, ψ x * inner ℝ v (G x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))
        = -∫ x, (fderiv ℝ ψ x) v * g x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hdiv : ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ x, inner ℝ ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ ψ x)) (G x)
        * w x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 0)
    (η : EuclideanSpace ℝ (Fin n) → ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η) :
    ∫ x, η x ^ 2 * ‖G x‖ ^ 2 * w x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))
      = -2 * ∫ x, η x * g x * (fderiv ℝ η x) (G x) * w x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hgli : LocallyIntegrable g (volume : Measure E) :=
    Commons.Analysis.Measure.locallyIntegrable_of_aestronglyMeasurable_of_integrableOn_sq hgmeas hgloc
  have hGli : LocallyIntegrable G (volume : Measure E) :=
    locallyIntegrable_vec_of_integrableOn_sq hGmeas hGloc
  -- weak-gradient form
  have hGweak : ∀ (φ : E → ℝ) (v : E), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ x, g x * (fderiv ℝ φ x) v ∂(volume : Measure E)
        = - ∫ x, φ x * ⟪G x, v⟫_ℝ ∂(volume : Measure E) := by
    intro φ v hφ hφc
    have h := hweak φ v hφ hφc
    have hP : (∫ x, φ x * inner ℝ v (G x) ∂(volume : Measure E))
        = ∫ x, φ x * ⟪G x, v⟫_ℝ ∂(volume : Measure E) := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      show φ x * inner ℝ v (G x) = φ x * ⟪G x, v⟫_ℝ
      rw [real_inner_comm]
    have hQ : (∫ x, (fderiv ℝ φ x) v * g x ∂(volume : Measure E))
        = ∫ x, g x * (fderiv ℝ φ x) v ∂(volume : Measure E) := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      ring
    rw [hP, hQ] at h
    linarith [h]
  -- the compact set
  set K : Set E := tsupport η with hKdef
  have hK : IsCompact K := hηc
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hμfin : (volume : Measure E) K < ⊤ := hK.measure_lt_top
  haveI : IsFiniteMeasure ((volume : Measure E).restrict K) :=
    isFiniteMeasure_restrict.mpr hμfin.ne
  have hηzero : ∀ x : E, x ∉ K → η x = 0 := by
    intro x hx
    exact image_eq_zero_of_notMem_tsupport (by rwa [hKdef] at hx : x ∉ tsupport η)
  -- bounds
  obtain ⟨Mη0, hMη0⟩ := hη.continuous.bounded_above_of_compact_support hηc
  obtain ⟨Mdη0, hMdη0⟩ :=
    (hη.continuous_fderiv (by simp)).bounded_above_of_compact_support (hηc.fderiv ℝ)
  obtain ⟨Mw0, hMw0⟩ := hK.exists_bound_of_continuousOn hwcont.continuousOn
  obtain ⟨Mη, hMη, hMηnn⟩ : ∃ M : ℝ, (∀ x, ‖η x‖ ≤ M) ∧ 0 ≤ M :=
    ⟨max Mη0 0, fun x => le_trans (hMη0 x) (le_max_left _ _), le_max_right _ _⟩
  obtain ⟨Mdη, hMdη, hMdηnn⟩ : ∃ M : ℝ, (∀ x, ‖fderiv ℝ η x‖ ≤ M) ∧ 0 ≤ M :=
    ⟨max Mdη0 0, fun x => le_trans (hMdη0 x) (le_max_left _ _), le_max_right _ _⟩
  obtain ⟨Mw, hMw, hMwnn⟩ : ∃ M : ℝ, (∀ x ∈ K, ‖w x‖ ≤ M) ∧ 0 ≤ M :=
    ⟨max Mw0 0, fun x hx => le_trans (hMw0 x hx) (le_max_left _ _), le_max_right _ _⟩
  -- MemLp facts
  have hg_memLp : MemLp g 2 ((volume : Measure E).restrict K) :=
    (memLp_two_iff_integrable_sq hgmeas.restrict).mpr (hgloc K hK)
  have hG_memLp : MemLp G 2 ((volume : Measure E).restrict K) :=
    (memLp_two_iff_integrable_sq_norm hGmeas.restrict).mpr (hGloc K hK)
  have hGn_memLp : MemLp (fun x => ‖G x‖) 2 ((volume : Measure E).restrict K) := hG_memLp.norm
  -- bound for `weA1`
  have ha1_bound : ∀ x, ‖weA1 η G w x‖ ≤ (2 * Mη * Mdη * Mw) * ‖G x‖ := by
    intro x
    by_cases hx : x ∈ K
    · have h1 : ‖(fderiv ℝ η x) (G x)‖ ≤ Mdη * ‖G x‖ := by
        calc ‖(fderiv ℝ η x) (G x)‖ ≤ ‖fderiv ℝ η x‖ * ‖G x‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ Mdη * ‖G x‖ := by gcongr; exact hMdη x
      have habs : ‖weA1 η G w x‖ = 2 * ‖η x‖ * ‖(fderiv ℝ η x) (G x)‖ * ‖w x‖ := by
        simp only [weA1, norm_mul, Real.norm_eq_abs]
        rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      rw [habs]
      calc 2 * ‖η x‖ * ‖(fderiv ℝ η x) (G x)‖ * ‖w x‖
          ≤ 2 * Mη * (Mdη * ‖G x‖) * Mw := by
            gcongr
            · exact hMη x
            · exact hMw x hx
        _ = (2 * Mη * Mdη * Mw) * ‖G x‖ := by ring
    · have hz : weA1 η G w x = 0 := by
        simp only [weA1]
        rw [hηzero x hx]; ring
      rw [hz, norm_zero]
      exact mul_nonneg (by positivity) (norm_nonneg _)
  have hgrad_cont : Continuous (fun x : E => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ η x)) :=
    (LinearIsometryEquiv.continuous (InnerProductSpace.toDual ℝ E).symm).comp
      (hη.continuous_fderiv (by simp))
  have hLm : AEStronglyMeasurable (fun x => (fderiv ℝ η x) (G x)) (volume : Measure E) := by
    have h2 : AEStronglyMeasurable
        (fun x => ⟪(InnerProductSpace.toDual ℝ E).symm (fderiv ℝ η x), G x⟫_ℝ) (volume : Measure E) :=
      hgrad_cont.aestronglyMeasurable.inner hGmeas
    refine h2.congr (Eventually.of_forall fun x => ?_)
    show ⟪(InnerProductSpace.toDual ℝ E).symm (fderiv ℝ η x), G x⟫_ℝ = (fderiv ℝ η x) (G x)
    rw [InnerProductSpace.toDual_symm_apply]
  have ha1_aesm : AEStronglyMeasurable (weA1 η G w) (volume : Measure E) := by
    exact (((aestronglyMeasurable_const).mul hη.continuous.aestronglyMeasurable).mul hLm).mul
        hwcont.aestronglyMeasurable
  have ha1_memLp : MemLp (weA1 η G w) 2 ((volume : Measure E).restrict K) := by
    have hgC : MemLp (fun x => (2 * Mη * Mdη * Mw) * ‖G x‖) 2 ((volume : Measure E).restrict K) :=
      hGn_memLp.const_mul _
    refine MemLp.of_le hgC (ha1_aesm.mono_measure Measure.restrict_le_self) ?_
    filter_upwards with x
    have hb : (0:ℝ) ≤ (2 * Mη * Mdη * Mw) * ‖G x‖ :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hMηnn) hMdηnn) hMwnn) (norm_nonneg _)
    calc ‖weA1 η G w x‖ ≤ (2 * Mη * Mdη * Mw) * ‖G x‖ := ha1_bound x
      _ = ‖(2 * Mη * Mdη * Mw) * ‖G x‖‖ := by rw [Real.norm_eq_abs, abs_of_nonneg hb]
  -- bound for `weA2`
  have ha2_bound : ∀ x, ‖weA2 η w x‖ ≤ Mη ^ 2 * Mw := by
    intro x
    by_cases hx : x ∈ K
    · have h1 : η x ^ 2 ≤ Mη ^ 2 := by
        rw [sq_le_sq, abs_of_nonneg hMηnn, ← Real.norm_eq_abs]
        exact hMη x
      rw [weA2, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul h1 (by simpa [Real.norm_eq_abs] using hMw x hx) (abs_nonneg _) (by positivity)
    · have hz : weA2 η w x = 0 := by
        simp only [weA2]
        rw [hηzero x hx]; ring
      rw [hz, norm_zero]
      positivity
  have ha2_aesm : AEStronglyMeasurable (weA2 η w) (volume : Measure E) := by
    have h1 : AEStronglyMeasurable (fun x => η x ^ 2) (volume : Measure E) := by
      have h2 : (fun x => η x ^ 2) = η * η := by
        funext x
        show η x ^ 2 = η x * η x
        ring
      rw [h2]
      exact hη.continuous.aestronglyMeasurable.mul hη.continuous.aestronglyMeasurable
    exact h1.mul hwcont.aestronglyMeasurable
  have ha2_nonneg : 0 ≤ Mη ^ 2 * Mw := by positivity
  -- the mollified identity
  have hψ_smooth : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (fun x => η x ^ 2 * mollS (weRho n k) g x) := by
    intro k
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun x => η x ^ 2) := by
      have h2 : (fun x => η x ^ 2) = η * η := by
        funext x
        show η x ^ 2 = η x * η x
        ring
      rw [h2]; exact hη.mul hη
    exact h1.mul (mollS_smooth (weRho n k) g (weRho_smooth k) (weRho_cs k) hgli)
  have hψ_cs : ∀ k, HasCompactSupport (fun x => η x ^ 2 * mollS (weRho n k) g x) := by
    intro k
    have h1 : HasCompactSupport (fun x => η x ^ 2) := by
      have h2 : (fun x => η x ^ 2) = η * η := by
        funext x
        show η x ^ 2 = η x * η x
        ring
      rw [h2]; exact hηc.mul_right
    exact h1.mul_right
  have hmoll_id_vol : ∀ k, (∫ x,
        (weA1 η G w x * mollS (weRho n k) g x
          + weA2 η w x * ⟪mollV (weRho n k) G x, G x⟫_ℝ) ∂(volume : Measure E)) = 0 := by
    intro k
    have h := hdiv (fun x => η x ^ 2 * mollS (weRho n k) g x) (hψ_smooth k) (hψ_cs k)
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show weA1 η G w x * mollS (weRho n k) g x + weA2 η w x * ⟪mollV (weRho n k) G x, G x⟫_ℝ
      = inner ℝ ((InnerProductSpace.toDual ℝ E).symm
          (fderiv ℝ (fun y => η y ^ 2 * mollS (weRho n k) g y) x)) (G x) * w x
    rw [InnerProductSpace.toDual_symm_apply]
    rw [fderiv_mul_sq η (mollS (weRho n k) g) G x
        (hη.contDiffAt.differentiableAt (by norm_num))
        ((mollS_smooth (weRho n k) g (weRho_smooth k) (weRho_cs k) hgli).contDiffAt.differentiableAt
          (by norm_num))]
    rw [fderiv_mollS_eq_mollV (weRho n k) g G (weRho_smooth k) (weRho_cs k) hgli hGli
        (fun φ hφ hφc v => hGweak φ v hφ hφc) x (G x)]
    simp only [weA1, weA2]
    ring
  -- convert to the restricted measure
  have hmoll_id : ∀ k, (∫ x,
        (weA1 η G w x * mollS (weRho n k) g x
          + weA2 η w x * ⟪mollV (weRho n k) G x, G x⟫_ℝ)
            ∂((volume : Measure E).restrict K)) = 0 := by
    intro k
    rw [← hmoll_id_vol k]
    refine (integral_eq_integral_restrict_of_eq_zero_on_compl hKmeas (fun x hx => ?_)).symm
    have hz : η x = 0 := hηzero x hx
    simp only [weA1, weA2, hz]
    ring
  -- convergence
  have hconv_g : Tendsto (fun k => ∫ x,
        (mollS (weRho n k) g x - g x) ^ 2 ∂((volume : Measure E).restrict K)) atTop (nhds 0) :=
    Commons.Analysis.Convolution.tendsto_integral_sq_moll_sub_compact_measurable
      (fun k => weRho n k) (fun k => (weBump n k).rOut)
      (fun k x => weRho_nn k x) (fun k => weRho_integrable k) (fun k => weRho_int k)
      (fun k => (weBump n k).rOut_pos.le) (weRout_tendsto n) (fun k x hx => weRho_supp k x hx)
      g hgmeas hgloc K hK
  have hconv_G : Tendsto (fun k => ∫ x,
        ‖mollV (weRho n k) G x - G x‖ ^ 2 ∂((volume : Measure E).restrict K)) atTop (nhds 0) :=
    Commons.Analysis.Convolution.tendsto_integral_sq_moll_sub_compact_vec_measurable
      (fun k => weRho n k) (fun k => (weBump n k).rOut)
      (fun k x => weRho_nn k x) (fun k => weRho_integrable k) (fun k => weRho_int k)
      (fun k => (weBump n k).rOut_pos.le) (weRout_tendsto n) (fun k x hx => weRho_supp k x hx)
      G hGmeas hGloc K hK
  have hgk_memLp : ∀ k, MemLp (mollS (weRho n k) g) 2 ((volume : Measure E).restrict K) := by
    intro k
    have hcont : Continuous (mollS (weRho n k) g) :=
      (mollS_smooth (weRho n k) g (weRho_smooth k) (weRho_cs k) hgli).continuous
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
    refine MemLp.of_bound hcont.aestronglyMeasurable.restrict C ?_
    exact (ae_restrict_mem hKmeas).mono (fun x hx => hC x hx)
  have hGk_memLp : ∀ k, MemLp (mollV (weRho n k) G) 2 ((volume : Measure E).restrict K) := by
    intro k
    have hcont : Continuous (mollV (weRho n k) G) :=
      (mollV_smooth (weRho n k) G (weRho_smooth k) (weRho_cs k) hGli).continuous
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
    refine MemLp.of_bound hcont.aestronglyMeasurable.restrict C ?_
    exact (ae_restrict_mem hKmeas).mono (fun x hx => hC x hx)
  have hT1 : Tendsto (fun k => ∫ x, weA1 η G w x * mollS (weRho n k) g x
        ∂((volume : Measure E).restrict K)) atTop
      (nhds (∫ x, weA1 η G w x * g x ∂((volume : Measure E).restrict K))) :=
    tendsto_integral_mul_of_tendsto_sq (μ := (volume : Measure E).restrict K)
      ha1_memLp hg_memLp hgk_memLp hconv_g
  have hT2 : Tendsto (fun k => ∫ x, weA2 η w x * ⟪mollV (weRho n k) G x, G x⟫_ℝ
        ∂((volume : Measure E).restrict K)) atTop
      (nhds (∫ x, weA2 η w x * ⟪G x, G x⟫_ℝ ∂((volume : Measure E).restrict K))) :=
    tendsto_integral_smul_inner_of_tendsto_sq (μ := (volume : Measure E).restrict K)
      ha2_nonneg (ha2_aesm.mono_measure Measure.restrict_le_self) ha2_bound hG_memLp
      hGk_memLp hG_memLp hconv_G
  have hsplit : ∀ k, (∫ x, (weA1 η G w x * mollS (weRho n k) g x
          + weA2 η w x * ⟪mollV (weRho n k) G x, G x⟫_ℝ) ∂((volume : Measure E).restrict K))
      = (∫ x, weA1 η G w x * mollS (weRho n k) g x ∂((volume : Measure E).restrict K))
        + (∫ x, weA2 η w x * ⟪mollV (weRho n k) G x, G x⟫_ℝ
            ∂((volume : Measure E).restrict K)) := by
    intro k
    rw [integral_add]
    · exact ha1_memLp.integrable_mul (hgk_memLp k)
    · have hdom : Integrable (fun x => (Mη ^ 2 * Mw) * (‖mollV (weRho n k) G x‖ * ‖G x‖))
          ((volume : Measure E).restrict K) :=
        (((hGk_memLp k).norm.integrable_mul hGn_memLp)).const_mul _
      refine hdom.mono' ((ha2_aesm.mono_measure Measure.restrict_le_self).mul
        ((hGk_memLp k).aestronglyMeasurable.inner hG_memLp.aestronglyMeasurable)) ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul]
      calc ‖weA2 η w x‖ * |⟪mollV (weRho n k) G x, G x⟫|
          ≤ (Mη ^ 2 * Mw) * (‖mollV (weRho n k) G x‖ * ‖G x‖) := by
            apply mul_le_mul
            · exact ha2_bound x
            · exact abs_real_inner_le_norm _ _
            · exact abs_nonneg _
            · positivity
        _ = (Mη ^ 2 * Mw) * (‖mollV (weRho n k) G x‖ * ‖G x‖) := rfl
  have hTsum : Tendsto (fun k => ∫ x, (weA1 η G w x * mollS (weRho n k) g x
        + weA2 η w x * ⟪mollV (weRho n k) G x, G x⟫_ℝ) ∂((volume : Measure E).restrict K))
      atTop (nhds ((∫ x, weA1 η G w x * g x ∂((volume : Measure E).restrict K))
        + (∫ x, weA2 η w x * ⟪G x, G x⟫_ℝ ∂((volume : Measure E).restrict K)))) :=
    (hT1.add hT2).congr' (Eventually.of_forall fun k => (hsplit k).symm)
  have hzero : (∫ x, weA1 η G w x * g x ∂((volume : Measure E).restrict K))
      + (∫ x, weA2 η w x * ⟪G x, G x⟫_ℝ ∂((volume : Measure E).restrict K)) = 0 := by
    have hconst : (fun k => ∫ x, (weA1 η G w x * mollS (weRho n k) g x
          + weA2 η w x * ⟪mollV (weRho n k) G x, G x⟫_ℝ) ∂((volume : Measure E).restrict K))
        = fun _ => (0 : ℝ) := by
      funext k; exact hmoll_id k
    rw [hconst] at hTsum
    exact (tendsto_nhds_unique tendsto_const_nhds hTsum).symm
  -- final algebra
  have hL1 : (∫ x, weA1 η G w x * g x ∂((volume : Measure E).restrict K))
      = 2 * (∫ x, η x * g x * (fderiv ℝ η x) (G x) * w x ∂((volume : Measure E).restrict K)) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [weA1]; ring
  have hL2 : (∫ x, weA2 η w x * ⟪G x, G x⟫_ℝ ∂((volume : Measure E).restrict K))
      = (∫ x, η x ^ 2 * ‖G x‖ ^ 2 * w x ∂((volume : Measure E).restrict K)) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [weA2, real_inner_self_eq_norm_sq]
    ring
  rw [hL1, hL2] at hzero
  have hfinal : (∫ x, η x ^ 2 * ‖G x‖ ^ 2 * w x ∂((volume : Measure E).restrict K))
      = -2 * ∫ x, η x * g x * (fderiv ℝ η x) (G x) * w x
          ∂((volume : Measure E).restrict K) := by
    linarith [hzero]
  -- transfer back to the full measure
  have hA : (∫ x, η x ^ 2 * ‖G x‖ ^ 2 * w x ∂(volume : Measure E))
      = ∫ x, η x ^ 2 * ‖G x‖ ^ 2 * w x ∂((volume : Measure E).restrict K) :=
    integral_eq_integral_restrict_of_eq_zero_on_compl hKmeas (fun x hx => by
      rw [hηzero x hx]; ring)
  have hB : (∫ x, η x * g x * (fderiv ℝ η x) (G x) * w x ∂(volume : Measure E))
      = ∫ x, η x * g x * (fderiv ℝ η x) (G x) * w x ∂((volume : Measure E).restrict K) :=
    integral_eq_integral_restrict_of_eq_zero_on_compl hKmeas (fun x hx => by
      rw [hηzero x hx]; ring)
  rw [hA, hB]
  exact hfinal

theorem weighted_energy_identity_moll_measurable {n : ℕ}
    (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hgmeas : MeasureTheory.AEStronglyMeasurable g (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))))
    (hGmeas : MeasureTheory.AEStronglyMeasurable G (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))))
    (hf : ContDiff ℝ 2 f)
    (hgloc : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
      MeasureTheory.IntegrableOn (fun x => g x ^ 2) K (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))))
    (hGloc : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
      MeasureTheory.IntegrableOn (fun x => ‖G x‖ ^ 2) K (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))))
    (hweak : ∀ (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (v : EuclideanSpace ℝ (Fin n)),
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ x, ψ x * inner ℝ v (G x) ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))
        = -∫ x, (fderiv ℝ ψ x) v * g x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))))
    (hdiv : ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ x, inner ℝ ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ ψ x)) (G x)
        * Real.exp (-(f x)) ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) = 0)
    (η : EuclideanSpace ℝ (Fin n) → ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η) :
    ∫ x, η x ^ 2 * ‖G x‖ ^ 2 * Real.exp (-(f x)) ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))
      = -2 * ∫ x, η x * g x * (fderiv ℝ η x) (G x) * Real.exp (-(f x))
          ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) := by
  exact energy_identity_aux g G (fun x => Real.exp (-(f x))) hgmeas hGmeas
    (Real.continuous_exp.comp hf.continuous.neg) hgloc hGloc hweak
    (fun ψ hψ hψc => by simpa using hdiv ψ hψ hψc) η hη hηc
end
end Commons.Analysis.GaussianMeasure
