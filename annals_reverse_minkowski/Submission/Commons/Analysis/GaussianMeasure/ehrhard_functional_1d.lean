import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.GaussianMeasure.gaussian_cdf_strictMono
import Submission.Commons.Analysis.GaussianMeasure.heatFlow_contdiff
import Submission.Commons.Analysis.GaussianMeasure.heatFlow_heat_eq
import Submission.Commons.Analysis.Calculus.localMin_second_deriv_nonneg
import Submission.Commons.Analysis.Calculus.parabolic_min_principle_diagonal
import Submission.Commons.Analysis.GaussianMeasure.heatExtension_zero_uniform_atTop
import Submission.Commons.Analysis.Convolution.lipschitzWith_sSup_sub_abs_div
import Submission.Commons.Topology.Order.upperSemicontinuous_sSup_minkowski_section
import Submission.Commons.MeasureTheory.Real.staircase_pointwise_bounds
import Submission.Commons.MeasureTheory.Real.exists_ucs_approx

set_option maxHeartbeats 4000000

noncomputable section
open MeasureTheory Set Real Filter
open scoped Topology

namespace Commons.Analysis.GaussianMeasure

open Commons.Analysis.GaussianMeasure (gaussian_cdf_strictMono)

/-! ## The one-dimensional Gaussian cdf and its inverse -/

def gPhi (a : ℝ) : ℝ := ∫ x in Set.Iic a, Real.exp (-Real.pi * x ^ 2)

lemma gPhi_strictMono : StrictMono gPhi := gaussian_cdf_strictMono

lemma integrable_gauss : Integrable (fun x : ℝ => Real.exp (-Real.pi * x ^ 2)) :=
  integrable_exp_neg_mul_sq Real.pi_pos

lemma gauss_cont_aux : Continuous (fun x : ℝ => Real.exp (-Real.pi * x ^ 2)) := by fun_prop

lemma integral_gauss : (∫ x : ℝ, Real.exp (-Real.pi * x ^ 2)) = 1 := by
  rw [integral_gaussian, div_self (ne_of_gt Real.pi_pos), Real.sqrt_one]

lemma gPhi_pos (a : ℝ) : 0 < gPhi a := by
  rw [gPhi]
  have hint : IntegrableOn (fun x : ℝ => Real.exp (-Real.pi * x ^ 2)) (Set.Iic a) :=
    integrable_gauss.integrableOn
  have hf : 0 ≤ᵐ[volume.restrict (Set.Iic a)] (fun x : ℝ => Real.exp (-Real.pi * x ^ 2)) :=
    Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le)
  have hsupp : Function.support (fun x : ℝ => Real.exp (-Real.pi * x ^ 2)) = Set.univ := by
    ext x; simp [Function.mem_support]
  have hpos := setIntegral_pos_iff_support_of_nonneg_ae hf hint
  rw [hpos, hsupp, Set.univ_inter, Real.volume_Iic]
  exact ENNReal.zero_lt_top

lemma gPhi_lt_one (a : ℝ) : gPhi a < 1 := by
  have hsplit : (∫ x : ℝ, Real.exp (-Real.pi * x ^ 2))
      = gPhi a + ∫ x in Set.Ioi a, Real.exp (-Real.pi * x ^ 2) := by
    rw [gPhi, ← integral_add_compl measurableSet_Iic integrable_gauss]
    congr 1
    rw [Set.compl_Iic]
  have hpos : 0 < ∫ x in Set.Ioi a, Real.exp (-Real.pi * x ^ 2) := by
    have hint : IntegrableOn (fun x : ℝ => Real.exp (-Real.pi * x ^ 2)) (Set.Ioi a) :=
      integrable_gauss.integrableOn
    have hf : 0 ≤ᵐ[volume.restrict (Set.Ioi a)] (fun x : ℝ => Real.exp (-Real.pi * x ^ 2)) :=
      Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le)
    have hsupp : Function.support (fun x : ℝ => Real.exp (-Real.pi * x ^ 2)) = Set.univ := by
      ext x; simp [Function.mem_support]
    have hpos := setIntegral_pos_iff_support_of_nonneg_ae hf hint
    rw [hpos, hsupp, Set.univ_inter, Real.volume_Ioi]
    exact ENNReal.zero_lt_top
  rw [integral_gauss] at hsplit
  linarith

lemma gPhi_continuous : Continuous gPhi := by
  have hf : gPhi = fun t => gPhi 0 + ∫ x in (0:ℝ)..t, Real.exp (-Real.pi * x ^ 2) := by
    funext t
    have h := intervalIntegral.integral_Iic_sub_Iic (μ := (volume : Measure ℝ)) (a := (0:ℝ))
      (b := t) (f := fun x : ℝ => Real.exp (-Real.pi * x ^ 2)) integrable_gauss.integrableOn
      integrable_gauss.integrableOn
    unfold gPhi
    linarith
  rw [hf]
  exact (integrable_gauss.continuous_primitive (0:ℝ)).const_add _

lemma gPhi_tendsto_atTop : Tendsto gPhi atTop (𝓝 1) := by
  have hmono : Monotone (fun i : ℝ => Set.Iic i) := fun i j h => Set.Iic_subset_Iic.mpr h
  have h := tendsto_setIntegral_of_monotone (μ := volume)
    (f := fun x : ℝ => Real.exp (-Real.pi * x ^ 2))
    (s := fun i : ℝ => Set.Iic i) (fun i => measurableSet_Iic) hmono (by
      rw [Set.iUnion_Iic]; exact integrable_gauss.integrableOn)
  rw [Set.iUnion_Iic, setIntegral_univ, integral_gauss] at h
  exact h

lemma gPhi_tendsto_atBot : Tendsto gPhi atBot (𝓝 0) := by
  have h : Tendsto (fun a : ℝ => 1 - gPhi (-a)) atBot (𝓝 (1 - 1)) :=
    tendsto_const_nhds.sub (gPhi_tendsto_atTop.comp tendsto_neg_atBot_atTop)
  rw [sub_self] at h
  have heq : (fun a : ℝ => 1 - gPhi (-a)) = fun a => gPhi a := by
    funext a
    have h1 : (∫ x in Set.Iic (-a), Real.exp (-Real.pi * x ^ 2))
        = ∫ x in Set.Ioi a, Real.exp (-Real.pi * x ^ 2) := by
      rw [← integral_comp_neg_Ioi a (fun x => Real.exp (-Real.pi * x ^ 2))]
      refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
      simp
    have h2 : (∫ x in Set.Iic a, Real.exp (-Real.pi * x ^ 2))
        + ∫ x in Set.Ioi a, Real.exp (-Real.pi * x ^ 2) = 1 := by
      rw [← integral_gauss, ← integral_add_compl measurableSet_Iic integrable_gauss]
      congr 1
      rw [Set.compl_Iic]
    have := h1
    unfold gPhi
    rw [this]
    linarith
  rwa [heq] at h

def gphi (y : ℝ) : ℝ := sInf {x : ℝ | y ≤ gPhi x}

lemma gphi_spec (y : ℝ) (hy0 : 0 < y) (hy1 : y < 1) : gPhi (gphi y) = y := by
  set S : Set ℝ := {x : ℝ | y ≤ gPhi x} with hS
  have hne : S.Nonempty := by
    have h := (gPhi_tendsto_atTop.eventually (isOpen_Ioi.mem_nhds (show (1:ℝ) ∈ Set.Ioi y from hy1)))
    rw [eventually_atTop] at h
    obtain ⟨R, hR⟩ := h
    exact ⟨R, le_of_lt (hR R le_rfl)⟩
  have hbdd : BddBelow S := by
    have h := (gPhi_tendsto_atBot.eventually (isOpen_Iio.mem_nhds (show (0:ℝ) ∈ Set.Iio y from hy0)))
    rw [eventually_atBot] at h
    obtain ⟨R, hR⟩ := h
    exact ⟨R, fun x hx => by
      by_contra hlt
      rw [not_le] at hlt
      exact absurd hx (not_le.mpr (hR x hlt.le))⟩
  have hcl : IsClosed S := isClosed_le continuous_const gPhi_continuous
  have hmem : gphi y ∈ S := hcl.csInf_mem hne hbdd
  have hge : y ≤ gPhi (gphi y) := hmem
  have hle : gPhi (gphi y) ≤ y := by
    have htend : Tendsto (fun n : ℕ => (gphi y - 1/(n+1))) atTop (𝓝 (gphi y)) := by
      simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 0))
    have hcont := (gPhi_continuous.continuousAt.tendsto).comp htend
    refine le_of_tendsto hcont ?_
    filter_upwards with n
    have hlt : gphi y - 1/((n:ℝ)+1) < gphi y := by
      have : (0:ℝ) < 1/((n:ℝ)+1) := by positivity
      linarith
    have hmem' : gphi y - 1/((n:ℝ)+1) ∉ S := by
      intro hc
      have hgs : gphi y = sInf S := by rw [hS]; rfl
      have := csInf_le hbdd hc
      linarith [hgs, this, hlt]
    rw [hS] at hmem'
    exact le_of_lt (not_le.mp hmem')
  exact le_antisymm hle hge

lemma gphi_gPhi (x : ℝ) : gphi (gPhi x) = x := by
  have h1 : gPhi (gphi (gPhi x)) = gPhi x := gphi_spec (gPhi x) (gPhi_pos x) (gPhi_lt_one x)
  exact gPhi_strictMono.injective h1

lemma gphi_strictMonoOn : StrictMonoOn gphi (Set.Ioo (0:ℝ) 1) := by
  intro y hy z hz hyz
  refine gPhi_strictMono.lt_iff_lt.mp ?_
  rw [gphi_spec y hy.1 hy.2, gphi_spec z hz.1 hz.2]
  exact hyz

lemma gphi_continuousAt (y : ℝ) (hy0 : 0 < y) (hy1 : y < 1) : ContinuousAt gphi y := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  set a : ℝ := gphi y with ha
  have hspec : gPhi a = y := gphi_spec y hy0 hy1
  have hlt1 : gPhi (a - ε) < y := by rw [← hspec]; exact gPhi_strictMono (by linarith)
  have hlt2 : y < gPhi (a + ε) := by rw [← hspec]; exact gPhi_strictMono (by linarith)
  set δ : ℝ := min (y - gPhi (a - ε)) (gPhi (a + ε) - y) with hδ
  have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
  refine ⟨δ, hδpos, fun z hz => ?_⟩
  rw [Real.dist_eq] at hz
  rw [Real.dist_eq]
  rw [abs_sub_lt_iff] at hz ⊢
  have hz0 : 0 < z := by
    have h2 : δ ≤ y - gPhi (a - ε) := min_le_left _ _
    have hp := gPhi_pos (a - ε)
    linarith [hz.2]
  have hz1 : z < 1 := by
    have h2 : δ ≤ gPhi (a + ε) - y := min_le_right _ _
    have hp := gPhi_lt_one (a + ε)
    linarith [hz.1]
  have hzl : gPhi (a - ε) < z := by
    have h2 : δ ≤ y - gPhi (a - ε) := min_le_left _ _
    linarith [hz.2]
  have hzr : z < gPhi (a + ε) := by
    have h2 : δ ≤ gPhi (a + ε) - y := min_le_right _ _
    linarith [hz.1]
  have hleft : a - ε < gphi z := by
    have h := gphi_strictMonoOn (a := gPhi (a - ε)) (b := z)
      ⟨gPhi_pos _, gPhi_lt_one _⟩ ⟨hz0, hz1⟩ hzl
    rwa [gphi_gPhi] at h
  have hright : gphi z < a + ε := by
    have h := gphi_strictMonoOn (a := z) (b := gPhi (a + ε))
      ⟨hz0, hz1⟩ ⟨gPhi_pos _, gPhi_lt_one _⟩ hzr
    rwa [gphi_gPhi] at h
  exact ⟨by linarith, by linarith⟩

lemma gphi_hasDerivAt (y : ℝ) (hy0 : 0 < y) (hy1 : y < 1) :
    HasDerivAt gphi ((Real.exp (-Real.pi * (gphi y) ^ 2))⁻¹) y := by
  have hprim : HasDerivAt (fun t : ℝ => ∫ x in (0:ℝ)..t, Real.exp (-Real.pi * x ^ 2))
      (Real.exp (-Real.pi * (gphi y) ^ 2)) (gphi y) :=
    intervalIntegral.integral_hasDerivAt_right integrable_gauss.intervalIntegrable
      (gauss_cont_aux.aestronglyMeasurable.stronglyMeasurableAtFilter)
      gauss_cont_aux.continuousAt
  have hderiv : HasDerivAt gPhi (Real.exp (-Real.pi * (gphi y) ^ 2)) (gphi y) := by
    have hg : gPhi = (fun t : ℝ => gPhi 0 + ∫ x in (0:ℝ)..t, Real.exp (-Real.pi * x ^ 2)) := by
      funext t
      have h := intervalIntegral.integral_Iic_sub_Iic (μ := (volume : Measure ℝ)) (a := (0:ℝ))
        (b := t) (f := fun x : ℝ => Real.exp (-Real.pi * x ^ 2)) integrable_gauss.integrableOn
        integrable_gauss.integrableOn
      unfold gPhi; linarith
    rw [hg]; exact hprim.const_add _
  have hne : Real.exp (-Real.pi * (gphi y) ^ 2) ≠ 0 := Real.exp_ne_zero _
  have hcont : ContinuousAt gphi y := gphi_continuousAt y hy0 hy1
  have hfg : ∀ᶠ z in 𝓝 y, gPhi (gphi z) = z := by
    filter_upwards [isOpen_Ioo.mem_nhds (show y ∈ Set.Ioo (0:ℝ) 1 from ⟨hy0, hy1⟩)] with z hz
    exact gphi_spec z hz.1 hz.2
  exact HasDerivAt.of_local_left_inverse hcont hderiv hne hfg


def gphiD (u : ℝ) : ℝ := (Real.exp (-Real.pi * u ^ 2))⁻¹
def gphiD2 (u : ℝ) : ℝ := 2 * Real.pi * u * (gphiD u) ^ 2

lemma gphi_hasDerivAt' (y : ℝ) (hy0 : 0 < y) (hy1 : y < 1) :
    HasDerivAt gphi (gphiD (gphi y)) y := by
  simpa only [gphiD] using gphi_hasDerivAt y hy0 hy1

lemma gphi_hasDerivAt_deriv (y : ℝ) (hy0 : 0 < y) (hy1 : y < 1) :
    HasDerivAt (deriv gphi) (gphiD2 (gphi y)) y := by
  have hev : deriv gphi =ᶠ[𝓝 y] fun z => (Real.exp (-Real.pi * (gphi z) ^ 2))⁻¹ := by
    filter_upwards [isOpen_Ioo.mem_nhds (show y ∈ Set.Ioo (0:ℝ) 1 from ⟨hy0, hy1⟩)] with z hz
    exact (gphi_hasDerivAt z hz.1 hz.2).deriv
  rw [hev.hasDerivAt_iff]
  have hmul : HasDerivAt (fun z : ℝ => gphi z * gphi z)
      ((Real.exp (-Real.pi * (gphi y) ^ 2))⁻¹ * gphi y
        + gphi y * (Real.exp (-Real.pi * (gphi y) ^ 2))⁻¹) y :=
    (gphi_hasDerivAt y hy0 hy1).mul (gphi_hasDerivAt y hy0 hy1)
  have hsd : HasDerivAt (fun z : ℝ => gphi z ^ 2)
      (2 * gphi y * (Real.exp (-Real.pi * (gphi y) ^ 2))⁻¹) y := by
    convert hmul using 1
    · ext z; ring
    · ring
  have h1 : HasDerivAt (fun z : ℝ => -Real.pi * gphi z ^ 2)
      (-Real.pi * (2 * gphi y * (Real.exp (-Real.pi * (gphi y) ^ 2))⁻¹)) y :=
    hsd.const_mul (-Real.pi)
  have h2 : HasDerivAt (fun z : ℝ => Real.exp (-Real.pi * gphi z ^ 2))
      (Real.exp (-Real.pi * gphi y ^ 2) *
        (-Real.pi * (2 * gphi y * (Real.exp (-Real.pi * (gphi y) ^ 2))⁻¹))) y := h1.exp
  have h3 := h2.inv (Real.exp_ne_zero _)
  have hval : -(Real.exp (-Real.pi * gphi y ^ 2) *
        (-Real.pi * (2 * gphi y * (Real.exp (-Real.pi * (gphi y) ^ 2))⁻¹))) /
        (Real.exp (-Real.pi * gphi y ^ 2)) ^ 2
      = gphiD2 (gphi y) := by
    simp only [gphiD2, gphiD]
    have hA : Real.exp (-Real.pi * gphi y ^ 2) ≠ 0 := Real.exp_ne_zero _
    field_simp
  rw [hval] at h3
  exact h3


lemma gphiD_eq (u : ℝ) : gphiD u = Real.exp (Real.pi * u ^ 2) := by
  simp only [gphiD, ← Real.exp_neg]
  congr 1
  ring

lemma gphiD2_eq (u : ℝ) : gphiD2 u = 2 * Real.pi * u * Real.exp (2 * Real.pi * u ^ 2) := by
  simp only [gphiD2, gphiD_eq, ← Real.exp_nat_mul]
  ring_nf

lemma gphiD_pos (u : ℝ) : 0 < gphiD u := by rw [gphiD_eq]; exact Real.exp_pos _

lemma hasDerivAt_gphiD_gphi (y : ℝ) (hy0 : 0 < y) (hy1 : y < 1) :
    HasDerivAt (fun z => gphiD (gphi z)) (gphiD2 (gphi y)) y := by
  have hev : deriv gphi =ᶠ[𝓝 y] fun z => gphiD (gphi z) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show y ∈ Set.Ioo (0:ℝ) 1 from ⟨hy0, hy1⟩)] with z hz
    rw [(gphi_hasDerivAt z hz.1 hz.2).deriv]
    simp only [gphiD]
  rw [← hev.hasDerivAt_iff]
  exact gphi_hasDerivAt_deriv y hy0 hy1

/-! ## The heat flow and the transformed function `U` -/

def heatFlow (q : ℝ → ℝ) (t x : ℝ) : ℝ :=
  ∫ z, q (x + Real.sqrt t * z) * Real.exp (-Real.pi * z ^ 2)

lemma heatFlow_contDiffOn (q : ℝ → ℝ) (hq : ∀ x, |q x| ≤ 1) :
    ContDiffOn ℝ 2 (fun p : ℝ × ℝ => heatFlow q p.1 p.2) {p : ℝ × ℝ | 0 < p.1} :=
  Commons.Analysis.GaussianMeasure.heatFlow_contdiff q hq

lemma heatFlow_heat (q : ℝ → ℝ) (hq : ∀ x, |q x| ≤ 1) :
    ∀ t : ℝ, 0 < t → ∀ x : ℝ,
      deriv (fun y : ℝ => deriv (fun y' : ℝ => heatFlow q t y') y) x
        = 4 * Real.pi * deriv (fun s : ℝ => heatFlow q s x) t :=
  Commons.Analysis.GaussianMeasure.heatFlow_heat_eq q hq

lemma heatFlow_zero (q : ℝ → ℝ) (x : ℝ) : heatFlow q 0 x = q x := by
  unfold heatFlow
  simp only [Real.sqrt_zero, zero_mul, add_zero]
  rw [integral_const_mul, integral_gaussian, div_self (ne_of_gt Real.pi_pos), Real.sqrt_one, mul_one]

lemma heatFlow_bounds (q : ℝ → ℝ) {δ α : ℝ} (hqd : ∀ x, δ ≤ q x) (hqu : ∀ x, q x ≤ α)
    (hqm : Measurable q) (t x : ℝ) :
    δ ≤ heatFlow q t x ∧ heatFlow q t x ≤ α := by
  have hE : Integrable (fun z : ℝ => Real.exp (-Real.pi * z ^ 2)) := integrable_gauss
  set C : ℝ := max |δ| |α| with hC
  have hCm : 0 ≤ C := le_trans (abs_nonneg _) (le_max_left _ _)
  have hi : Integrable (fun z : ℝ => q (x + Real.sqrt t * z) * Real.exp (-Real.pi * z ^ 2)) := by
    refine Integrable.mono' (hE.const_mul C) ?_ ?_
    · exact AEMeasurable.aestronglyMeasurable
        (((hqm.comp ((measurable_const.mul measurable_id).const_add x)).mul
        gauss_cont_aux.measurable).aemeasurable)
    · filter_upwards with z
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have hqC : |q (x + Real.sqrt t * z)| ≤ C := by
        rw [abs_le]
        refine ⟨?_, ?_⟩
        · have h1 : |δ| ≤ C := le_max_left _ _
          have h2 : -|δ| ≤ δ := neg_abs_le δ
          linarith [hqd (x + Real.sqrt t * z)]
        · have h1 : α ≤ C := le_trans (le_abs_self α) (le_max_right _ _)
          linarith [hqu (x + Real.sqrt t * z)]
      exact mul_le_mul_of_nonneg_right hqC (Real.exp_pos _).le
  have hlow : (∫ z : ℝ, δ * Real.exp (-Real.pi * z ^ 2)) ≤ heatFlow q t x := by
    unfold heatFlow
    refine integral_mono (hE.const_mul δ) hi (fun z => ?_)
    exact mul_le_mul_of_nonneg_right (hqd _) (Real.exp_pos _).le
  have hup : heatFlow q t x ≤ ∫ z : ℝ, α * Real.exp (-Real.pi * z ^ 2) := by
    unfold heatFlow
    refine integral_mono hi (hE.const_mul α) (fun z => ?_)
    exact mul_le_mul_of_nonneg_right (hqu _) (Real.exp_pos _).le
  have hl : (∫ z : ℝ, δ * Real.exp (-Real.pi * z ^ 2)) = δ := by
    rw [integral_const_mul, integral_gauss, mul_one]
  have hu : (∫ z : ℝ, α * Real.exp (-Real.pi * z ^ 2)) = α := by
    rw [integral_const_mul, integral_gauss, mul_one]
  rw [hl] at hlow; rw [hu] at hup
  exact ⟨hlow, hup⟩

lemma slice_contDiff (q : ℝ → ℝ) (hq : ∀ x, |q x| ≤ 1) {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ 2 (fun x' : ℝ => heatFlow q t x') := by
  have hF := heatFlow_contDiffOn q hq
  rw [contDiff_iff_contDiffAt]
  intro x
  have hcat : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => heatFlow q p.1 p.2) (t, x) :=
    hF.contDiffAt ((isOpen_lt continuous_const continuous_fst).mem_nhds (by simpa using ht))
  have hslice : ContDiffAt ℝ 2 (fun x' : ℝ => (t, x')) x := by fun_prop
  have hcomp := hcat.comp x hslice
  refine hcomp.congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall (fun x' => rfl)

lemma tslice_contDiff (q : ℝ → ℝ) (hq : ∀ x, |q x| ≤ 1) (x : ℝ) :
    ∀ t : ℝ, 0 < t → ContDiffAt ℝ 2 (fun s : ℝ => heatFlow q s x) t := by
  intro t ht
  have hF := heatFlow_contDiffOn q hq
  have hcat : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => heatFlow q p.1 p.2) (t, x) :=
    hF.contDiffAt ((isOpen_lt continuous_const continuous_fst).mem_nhds (by simpa using ht))
  have hslice : ContDiffAt ℝ 2 (fun s : ℝ => (s, x)) t := by fun_prop
  have hcomp := hcat.comp t hslice
  refine hcomp.congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall (fun s => rfl)

lemma heatFlow_derivs (q : ℝ → ℝ) (hq : ∀ x, |q x| ≤ 1) :
    (∀ t : ℝ, 0 < t → ∀ x : ℝ,
      HasDerivAt (fun x' : ℝ => heatFlow q t x') (deriv (fun x' : ℝ => heatFlow q t x') x) x) ∧
    (∀ t : ℝ, 0 < t → ∀ x : ℝ,
      HasDerivAt (fun s : ℝ => heatFlow q s x) (deriv (fun s : ℝ => heatFlow q s x) t) t) ∧
    (∀ t : ℝ, 0 < t → ∀ x : ℝ,
      HasDerivAt (fun x' : ℝ => deriv (fun x'' : ℝ => heatFlow q t x'') x')
        (deriv (fun x' : ℝ => deriv (fun x'' : ℝ => heatFlow q t x'') x') x) x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht x
    exact (((slice_contDiff q hq ht).differentiable (by norm_num)) x).hasDerivAt
  · intro t ht x
    exact ((tslice_contDiff q hq x t ht).differentiableAt (by norm_num)).hasDerivAt
  · intro t ht x
    have h1 : ContDiff ℝ 1 (deriv (fun x' : ℝ => heatFlow q t x')) :=
      (slice_contDiff q hq ht).deriv'
    exact ((h1.differentiable (by norm_num)) x).hasDerivAt

def U (q : ℝ → ℝ) (t x : ℝ) : ℝ := gphi (heatFlow q t x)


def IsNice (q : ℝ → ℝ) (δ α : ℝ) : Prop :=
  Measurable q ∧ (∀ x, δ ≤ q x) ∧ (∀ x, q x ≤ α) ∧ 0 < δ ∧ α < 1

lemma IsNice.abs_le {q : ℝ → ℝ} {δ α : ℝ} (h : IsNice q δ α) : ∀ x, |q x| ≤ 1 := by
  intro x
  rw [abs_of_pos (lt_of_lt_of_le h.2.2.2.1 (h.2.1 x))]
  linarith [h.2.2.1 x, h.2.2.2.2]

lemma IsNice.mem {q : ℝ → ℝ} {δ α : ℝ} (h : IsNice q δ α) (t x : ℝ) : heatFlow q t x ∈ Set.Ioo 0 1 := by
  obtain ⟨hl, hu⟩ := heatFlow_bounds q h.2.1 h.2.2.1 h.1 t x
  exact ⟨lt_of_lt_of_le h.2.2.2.1 hl, lt_of_le_of_lt hu h.2.2.2.2⟩

lemma U_hasDerivAt_x {q : ℝ → ℝ} {δ α : ℝ} (h : IsNice q δ α) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun x' => U q t x') (gphiD (U q t x) * deriv (fun x' => heatFlow q t x') x) x := by
  have hmem := h.mem t x
  have hd := (gphi_hasDerivAt' (heatFlow q t x) hmem.1 hmem.2).comp x
    ((heatFlow_derivs q h.abs_le).1 t ht x)
  change HasDerivAt (gphi ∘ fun x' => heatFlow q t x')
    (gphiD (gphi (heatFlow q t x)) * deriv (fun x' => heatFlow q t x') x) x
  exact hd

lemma U_hasDerivAt_t {q : ℝ → ℝ} {δ α : ℝ} (h : IsNice q δ α) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => U q s x) (gphiD (U q t x) * deriv (fun s => heatFlow q s x) t) t := by
  have hmem := h.mem t x
  have hd := (gphi_hasDerivAt' (heatFlow q t x) hmem.1 hmem.2).comp t
    ((heatFlow_derivs q h.abs_le).2.1 t ht x)
  change HasDerivAt (gphi ∘ fun s => heatFlow q s x)
    (gphiD (gphi (heatFlow q t x)) * deriv (fun s => heatFlow q s x) t) t
  exact hd

lemma U_deriv_x_eq {q : ℝ → ℝ} {δ α : ℝ} (h : IsNice q δ α) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    deriv (fun x' => U q t x') x = gphiD (U q t x) * deriv (fun x' => heatFlow q t x') x :=
  (U_hasDerivAt_x h ht x).deriv

lemma U_deriv_t_eq {q : ℝ → ℝ} {δ α : ℝ} (h : IsNice q δ α) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    deriv (fun s => U q s x) t = gphiD (U q t x) * deriv (fun s => heatFlow q s x) t :=
  (U_hasDerivAt_t h ht x).deriv

lemma U_hasDerivAt_xx {q : ℝ → ℝ} {δ α : ℝ} (h : IsNice q δ α) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun x' => deriv (fun x'' => U q t x'') x')
      (gphiD2 (U q t x) * (deriv (fun x' => heatFlow q t x') x) ^ 2
        + gphiD (U q t x)
          * deriv (fun x' => deriv (fun x'' => heatFlow q t x'') x') x) x := by
  have hev : (fun x' => deriv (fun x'' => U q t x'') x')
      =ᶠ[𝓝 x] fun x' => gphiD (U q t x') * deriv (fun x'' => heatFlow q t x'') x' :=
    Filter.Eventually.of_forall (fun x' => U_deriv_x_eq h ht x')
  rw [hev.hasDerivAt_iff]
  have h1 : HasDerivAt (fun x' => gphiD (U q t x'))
      (gphiD2 (U q t x) * deriv (fun x' => heatFlow q t x') x) x := by
    have hmem := h.mem t x
    have hd := (hasDerivAt_gphiD_gphi (heatFlow q t x) hmem.1 hmem.2).comp x
      ((heatFlow_derivs q h.abs_le).1 t ht x)
    change HasDerivAt ((fun z => gphiD (gphi z)) ∘ fun x' => heatFlow q t x')
      (gphiD2 (gphi (heatFlow q t x)) * deriv (fun x' => heatFlow q t x') x) x
    exact hd
  have h2 : HasDerivAt (fun x' => deriv (fun x'' => heatFlow q t x'') x')
      (deriv (fun x' => deriv (fun x'' => heatFlow q t x'') x') x) x :=
    (heatFlow_derivs q h.abs_le).2.2 t ht x
  have h3 : HasDerivAt (fun x' => gphiD (U q t x') * deriv (fun x'' => heatFlow q t x'') x')
      (gphiD2 (U q t x) * deriv (fun x' => heatFlow q t x') x * deriv (fun x'' => heatFlow q t x'') x
        + gphiD (U q t x) * deriv (fun x' => deriv (fun x'' => heatFlow q t x'') x') x) x :=
    h1.mul h2
  simpa only [sq, mul_assoc] using h3

lemma U_deriv_deriv_x_eq {q : ℝ → ℝ} {δ α : ℝ} (h : IsNice q δ α) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    deriv (fun x' => deriv (fun x'' => U q t x'') x') x
      = gphiD2 (U q t x) * (deriv (fun x' => heatFlow q t x') x) ^ 2
        + gphiD (U q t x)
          * deriv (fun x' => deriv (fun x'' => heatFlow q t x'') x') x :=
  (U_hasDerivAt_xx h ht x).deriv

lemma gphiD2_ratio (u : ℝ) : gphiD2 u = 2 * Real.pi * u * (gphiD u) ^ 2 := rfl

lemma U_pde {q : ℝ → ℝ} {δ α : ℝ} (h : IsNice q δ α) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    deriv (fun x' => deriv (fun x'' => U q t x'') x') x
      = 4 * Real.pi * deriv (fun s => U q s x) t
        + 2 * Real.pi * U q t x * (deriv (fun x' => U q t x') x) ^ 2 := by
  rw [U_deriv_deriv_x_eq h ht x, heatFlow_heat q h.abs_le t ht x]
  have hxt := U_deriv_x_eq h ht x
  have htt := U_deriv_t_eq h ht x
  have hpos : gphiD (U q t x) ≠ 0 := ne_of_gt (gphiD_pos _)
  have hUx : deriv (fun x' => heatFlow q t x') x
      = deriv (fun x' => U q t x') x / gphiD (U q t x) := by
    rw [hxt]; field_simp
  rw [hUx, gphiD2_ratio, htt]
  field_simp
  ring



/-! ## The test function `Chat` and its derivatives -/

/-- Borell's test function `U h t (λx+(1-λ)y) - (λ U f t x + (1-λ) U g t y)`. -/
def Chat (f g h : ℝ → ℝ) (lam t x y : ℝ) : ℝ :=
  U h t (lam * x + (1 - lam) * y) - (lam * U f t x + (1 - lam) * U g t y)

lemma Chat_hasDerivAt_t {f g h : ℝ → ℝ} {δf αf δg αg δh αh : ℝ}
    (hf : IsNice f δf αf) (hg : IsNice g δg αg) (hh : IsNice h δh αh)
    (lam : ℝ) {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    HasDerivAt (fun s => Chat f g h lam s x y)
      (deriv (fun s => U h s (lam * x + (1 - lam) * y)) t
        - (lam * deriv (fun s => U f s x) t + (1 - lam) * deriv (fun s => U g s y) t)) t := by
  have hh' : HasDerivAt (fun s => U h s (lam * x + (1 - lam) * y))
      (deriv (fun s => U h s (lam * x + (1 - lam) * y)) t) t := by
    have h0 := U_hasDerivAt_t (q := h) hh ht (lam * x + (1 - lam) * y)
    rw [← U_deriv_t_eq hh ht (lam * x + (1 - lam) * y)] at h0
    exact h0
  have hf' : HasDerivAt (fun s => U f s x) (deriv (fun s => U f s x) t) t := by
    have h0 := U_hasDerivAt_t (q := f) hf ht x
    rw [← U_deriv_t_eq hf ht x] at h0
    exact h0
  have hg' : HasDerivAt (fun s => U g s y) (deriv (fun s => U g s y) t) t := by
    have h0 := U_hasDerivAt_t (q := g) hg ht y
    rw [← U_deriv_t_eq hg ht y] at h0
    exact h0
  have h2 : HasDerivAt (fun s => lam * U f s x + (1 - lam) * U g s y)
      (lam * deriv (fun s => U f s x) t + (1 - lam) * deriv (fun s => U g s y) t) t :=
    (hf'.const_mul lam).add (hg'.const_mul (1 - lam))
  refine (hh'.sub h2).congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s => ?_))
  simp only [Pi.sub_apply, Chat]

lemma Chat_deriv_t_eq {f g h : ℝ → ℝ} {δf αf δg αg δh αh : ℝ}
    (hf : IsNice f δf αf) (hg : IsNice g δg αg) (hh : IsNice h δh αh)
    (lam : ℝ) {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    deriv (fun s => Chat f g h lam s x y) t
      = deriv (fun s => U h s (lam * x + (1 - lam) * y)) t
        - (lam * deriv (fun s => U f s x) t + (1 - lam) * deriv (fun s => U g s y) t) :=
  (Chat_hasDerivAt_t hf hg hh lam ht x y).deriv

lemma Chat_hasDerivAt_slice {f g h : ℝ → ℝ} {δf αf δg αg δh αh : ℝ}
    (hf : IsNice f δf αf) (hg : IsNice g δg αg) (hh : IsNice h δh αh)
    (lam : ℝ) {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    HasDerivAt (fun s => Chat f g h lam t (x + s) (y + s))
      (deriv (fun z => U h t z) (lam * x + (1 - lam) * y)
        - (lam * deriv (fun z => U f t z) x + (1 - lam) * deriv (fun z => U g t z) y)) 0 := by
  have hUh : HasDerivAt (fun s => U h t (lam * (x + s) + (1 - lam) * (y + s)))
      (deriv (fun z => U h t z) (lam * x + (1 - lam) * y)) 0 := by
    have h1 : HasDerivAt (fun z => U h t z) (deriv (fun z => U h t z) (lam * x + (1 - lam) * y))
        (lam * x + (1 - lam) * y + 0) := by
      rw [add_zero]
      have h0 := U_hasDerivAt_x (q := h) hh ht (lam * x + (1 - lam) * y)
      rw [← U_deriv_x_eq hh ht (lam * x + (1 - lam) * y)] at h0
      exact h0
    have h2 := h1.comp_const_add (lam * x + (1 - lam) * y) 0
    refine h2.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall (fun s => by congr 1; ring)
  have hUf : HasDerivAt (fun s => U f t (x + s)) (deriv (fun z => U f t z) x) 0 := by
    have h1 : HasDerivAt (fun z => U f t z) (deriv (fun z => U f t z) x) (x + 0) := by
      rw [add_zero]
      have h0 := U_hasDerivAt_x (q := f) hf ht x
      rw [← U_deriv_x_eq hf ht x] at h0
      exact h0
    exact h1.comp_const_add x 0
  have hUg : HasDerivAt (fun s => U g t (y + s)) (deriv (fun z => U g t z) y) 0 := by
    have h1 : HasDerivAt (fun z => U g t z) (deriv (fun z => U g t z) y) (y + 0) := by
      rw [add_zero]
      have h0 := U_hasDerivAt_x (q := g) hg ht y
      rw [← U_deriv_x_eq hg ht y] at h0
      exact h0
    exact h1.comp_const_add y 0
  have h2 : HasDerivAt (fun s => lam * U f t (x + s) + (1 - lam) * U g t (y + s))
      (lam * deriv (fun z => U f t z) x + (1 - lam) * deriv (fun z => U g t z) y) 0 :=
    (hUf.const_mul lam).add (hUg.const_mul (1 - lam))
  have hfin := hUh.sub h2
  refine hfin.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s => ?_))
  simp only [Pi.sub_apply, Chat]

lemma Chat_slice_deriv_eq {f g h : ℝ → ℝ} {δf αf δg αg δh αh : ℝ}
    (hf : IsNice f δf αf) (hg : IsNice g δg αg) (hh : IsNice h δh αh)
    (lam : ℝ) {t : ℝ} (ht : 0 < t) (x y s : ℝ) :
    deriv (fun s' => Chat f g h lam t (x + s') (y + s')) s
      = deriv (fun z => U h t z) (lam * x + (1 - lam) * y + s)
        - (lam * deriv (fun z => U f t z) (x + s)
            + (1 - lam) * deriv (fun z => U g t z) (y + s)) := by
  have hbase := Chat_hasDerivAt_slice hf hg hh lam ht (x + s) (y + s)
  have harg : lam * (x + s) + (1 - lam) * (y + s) = lam * x + (1 - lam) * y + s := by ring
  rw [harg] at hbase
  have hbase' : HasDerivAt (fun u => Chat f g h lam t (x + (s + u)) (y + (s + u)))
      (deriv (fun z => U h t z) (lam * x + (1 - lam) * y + s)
        - (lam * deriv (fun z => U f t z) (x + s)
            + (1 - lam) * deriv (fun z => U g t z) (y + s))) 0 := by
    refine hbase.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall (fun u => by simp only [add_assoc])
  have hcomp := deriv_comp_const_add (f := fun s' => Chat f g h lam t (x + s') (y + s')) s (0 : ℝ)
  simp only [add_zero] at hcomp
  have hEq : (fun u : ℝ => (fun s' => Chat f g h lam t (x + s') (y + s')) (s + u))
      = fun u => Chat f g h lam t (x + (s + u)) (y + (s + u)) := rfl
  rw [hEq] at hcomp
  rw [← hcomp]
  exact hbase'.deriv

lemma Chat_slice_second_deriv_eq {f g h : ℝ → ℝ} {δf αf δg αg δh αh : ℝ}
    (hf : IsNice f δf αf) (hg : IsNice g δg αg) (hh : IsNice h δh αh)
    (lam : ℝ) {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    deriv (fun s => deriv (fun s' => Chat f g h lam t (x + s') (y + s')) s) 0
      = deriv (fun w => deriv (fun z => U h t z) w) (lam * x + (1 - lam) * y)
        - (lam * deriv (fun w => deriv (fun z => U f t z) w) x
            + (1 - lam) * deriv (fun w => deriv (fun z => U g t z) w) y) := by
  have hE : (fun s => deriv (fun s' => Chat f g h lam t (x + s') (y + s')) s)
      =ᶠ[nhds 0] (fun s => deriv (fun z => U h t z) (lam * x + (1 - lam) * y + s)
        - (lam * deriv (fun z => U f t z) (x + s)
            + (1 - lam) * deriv (fun z => U g t z) (y + s))) :=
    Filter.Eventually.of_forall (fun s => Chat_slice_deriv_eq hf hg hh lam ht x y s)
  rw [hE.deriv_eq]
  have hG : HasDerivAt (fun w => deriv (fun z => U h t z) w)
      (deriv (fun w => deriv (fun z => U h t z) w) (lam * x + (1 - lam) * y))
      (lam * x + (1 - lam) * y) := by
    have h0 := U_hasDerivAt_xx (q := h) hh ht (lam * x + (1 - lam) * y)
    rw [← U_deriv_deriv_x_eq hh ht (lam * x + (1 - lam) * y)] at h0
    exact h0
  have hAd : HasDerivAt (fun s => deriv (fun z => U h t z) (lam * x + (1 - lam) * y + s))
      (deriv (fun w => deriv (fun z => U h t z) w) (lam * x + (1 - lam) * y)) 0 := by
    have h1 : HasDerivAt (fun w => deriv (fun z => U h t z) w)
        (deriv (fun w => deriv (fun z => U h t z) w) (lam * x + (1 - lam) * y))
        (lam * x + (1 - lam) * y + 0) := by rw [add_zero]; exact hG
    exact h1.comp_const_add (lam * x + (1 - lam) * y) 0
  have hGf : HasDerivAt (fun w => deriv (fun z => U f t z) w)
      (deriv (fun w => deriv (fun z => U f t z) w) x) x := by
    have h0 := U_hasDerivAt_xx (q := f) hf ht x
    rw [← U_deriv_deriv_x_eq hf ht x] at h0
    exact h0
  have hBd : HasDerivAt (fun s => deriv (fun z => U f t z) (x + s))
      (deriv (fun w => deriv (fun z => U f t z) w) x) 0 := by
    have h1 : HasDerivAt (fun w => deriv (fun z => U f t z) w)
        (deriv (fun w => deriv (fun z => U f t z) w) x) (x + 0) := by rw [add_zero]; exact hGf
    exact h1.comp_const_add x 0
  have hGg : HasDerivAt (fun w => deriv (fun z => U g t z) w)
      (deriv (fun w => deriv (fun z => U g t z) w) y) y := by
    have h0 := U_hasDerivAt_xx (q := g) hg ht y
    rw [← U_deriv_deriv_x_eq hg ht y] at h0
    exact h0
  have hCd : HasDerivAt (fun s => deriv (fun z => U g t z) (y + s))
      (deriv (fun w => deriv (fun z => U g t z) w) y) 0 := by
    have h1 : HasDerivAt (fun w => deriv (fun z => U g t z) w)
        (deriv (fun w => deriv (fun z => U g t z) w) y) (y + 0) := by rw [add_zero]; exact hGg
    exact h1.comp_const_add y 0
  have hBC : HasDerivAt
      (fun s => lam * deriv (fun z => U f t z) (x + s) + (1 - lam) * deriv (fun z => U g t z) (y + s))
      (lam * deriv (fun w => deriv (fun z => U f t z) w) x
        + (1 - lam) * deriv (fun w => deriv (fun z => U g t z) w) y) 0 :=
    (hBd.const_mul lam).add (hCd.const_mul (1 - lam))
  have hEd : HasDerivAt
      (fun s => deriv (fun z => U h t z) (lam * x + (1 - lam) * y + s)
        - (lam * deriv (fun z => U f t z) (x + s) + (1 - lam) * deriv (fun z => U g t z) (y + s)))
      (deriv (fun w => deriv (fun z => U h t z) w) (lam * x + (1 - lam) * y)
        - (lam * deriv (fun w => deriv (fun z => U f t z) w) x
            + (1 - lam) * deriv (fun w => deriv (fun z => U g t z) w) y)) 0 :=
    hAd.sub hBC
  exact hEd.deriv

/-- At a critical point with the three spatial derivatives agreeing, the second derivative of the
diagonal slice of `Chat` satisfies the parabolic identity. -/
lemma Chat_slice_second_eq {f g h : ℝ → ℝ} {δf αf δg αg δh αh : ℝ}
    (hf : IsNice f δf αf) (hg : IsNice g δg αg) (hh : IsNice h δh αh)
    (lam : ℝ) {t : ℝ} (ht : 0 < t) (x y : ℝ)
    (hv : deriv (fun z => U h t z) (lam * x + (1 - lam) * y) = deriv (fun z => U f t z) x)
    (hv' : deriv (fun z => U h t z) (lam * x + (1 - lam) * y) = deriv (fun z => U g t z) y) :
    deriv (fun s => deriv (fun s' => Chat f g h lam t (x + s') (y + s')) s) 0
      = 4 * Real.pi * deriv (fun s => Chat f g h lam s x y) t
        + 2 * Real.pi * (deriv (fun z => U h t z) (lam * x + (1 - lam) * y)) ^ 2
            * Chat f g h lam t x y := by
  rw [Chat_slice_second_deriv_eq hf hg hh lam ht x y]
  rw [U_pde hh ht (lam * x + (1 - lam) * y), U_pde hf ht x, U_pde hg ht y]
  have hvg : deriv (fun z => U g t z) y = deriv (fun z => U f t z) x := hv'.symm.trans hv
  rw [hv, hvg]
  rw [Chat_deriv_t_eq hf hg hh lam ht x y]
  simp only [Chat]
  ring



/-! ## Continuity of the heat flow up to time `0`, and the parabolic maximum principle -/

lemma heatFlow_continuousAt_zero (q : ℝ → ℝ) (hqc : Continuous q) (hqb : ∀ x, |q x| ≤ 1)
    (x₀ : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ => ∫ z, q (p.2 + Real.sqrt p.1 * z) * Real.exp (-Real.pi * z ^ 2))
      (0, x₀) := by
  rw [ContinuousAt]
  have hval : (∫ z : ℝ, q (((0 : ℝ), x₀).2 + Real.sqrt (((0 : ℝ), x₀).1) * z)
      * Real.exp (-Real.pi * z ^ 2)) = q x₀ := by
    have h : (∫ z : ℝ, q (((0 : ℝ), x₀).2 + Real.sqrt (((0 : ℝ), x₀).1) * z)
        * Real.exp (-Real.pi * z ^ 2)) = ∫ z : ℝ, q x₀ * Real.exp (-Real.pi * z ^ 2) := by
      congr 1 with z
      simp [Real.sqrt_zero]
    rw [h, integral_const_mul, integral_gauss, mul_one]
  rw [hval]
  have hlim : Tendsto (fun p : ℝ × ℝ => ∫ z, q (p.2 + Real.sqrt p.1 * z) * Real.exp (-Real.pi * z ^ 2))
      (𝓝 (0, x₀)) (𝓝 (∫ z, q x₀ * Real.exp (-Real.pi * z ^ 2))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (bound := fun z => Real.exp (-Real.pi * z ^ 2)) ?_ ?_ integrable_gauss ?_
    · exact Filter.Eventually.of_forall (fun p =>
        ((hqc.comp (continuous_const.add (continuous_const.mul continuous_id))).mul
          gauss_cont_aux).aestronglyMeasurable)
    · refine Filter.Eventually.of_forall (fun p => Filter.Eventually.of_forall (fun z => ?_))
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_left (Real.exp_pos _).le (hqb _)
    · refine Filter.Eventually.of_forall (fun z => ?_)
      have hcont : Continuous (fun p : ℝ × ℝ => p.2 + Real.sqrt p.1 * z) := by fun_prop
      have h1 : Tendsto (fun p : ℝ × ℝ => p.2 + Real.sqrt p.1 * z) (𝓝 (0, x₀))
          (𝓝 (x₀ + Real.sqrt 0 * z)) := by
        convert hcont.tendsto (0, x₀) using 1
      have h2 : Tendsto (fun p : ℝ × ℝ => q (p.2 + Real.sqrt p.1 * z)) (𝓝 (0, x₀))
          (𝓝 (q (x₀ + Real.sqrt 0 * z))) := (hqc.tendsto _).comp h1
      have h3 : Tendsto (fun p : ℝ × ℝ => q (p.2 + Real.sqrt p.1 * z) * Real.exp (-Real.pi * z ^ 2))
          (𝓝 (0, x₀)) (𝓝 (q (x₀ + Real.sqrt 0 * z) * Real.exp (-Real.pi * z ^ 2))) :=
        h2.mul_const _
      simpa [Real.sqrt_zero] using h3
  rw [show (∫ z : ℝ, q x₀ * Real.exp (-Real.pi * z ^ 2)) = q x₀ from by
    rw [integral_const_mul, integral_gauss, mul_one]] at hlim
  exact hlim

lemma heatFlow_continuousOn_nonneg (q : ℝ → ℝ) (hqc : Continuous q) (hqb : ∀ x, |q x| ≤ 1) :
    ContinuousOn (fun p : ℝ × ℝ => ∫ z, q (p.2 + Real.sqrt p.1 * z) * Real.exp (-Real.pi * z ^ 2))
      {p : ℝ × ℝ | 0 ≤ p.1} := by
  rintro ⟨t, x⟩ hp
  change 0 ≤ t at hp
  rcases lt_or_eq_of_le hp with hp' | hp'
  · have hF := heatFlow_contDiffOn q hqb
    have hcat : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => heatFlow q p.1 p.2) (t, x) :=
      hF.contDiffAt ((isOpen_lt continuous_const continuous_fst).mem_nhds (by simpa using hp'))
    exact hcat.continuousAt.continuousWithinAt
  · subst hp'
    exact (heatFlow_continuousAt_zero q hqc hqb x).continuousWithinAt


lemma continuousOn_gphi : ContinuousOn gphi (Set.Ioo (0 : ℝ) 1) :=
  fun y hy => (gphi_continuousAt y hy.1 hy.2).continuousWithinAt

lemma continuousOn_U (q : ℝ → ℝ) (hqc : Continuous q) (hqb : ∀ x, |q x| ≤ 1) {δ α : ℝ}
    (h : IsNice q δ α) :
    ContinuousOn (fun p : ℝ × ℝ => U q p.1 p.2) {p : ℝ × ℝ | 0 ≤ p.1} := by
  have hHF : ContinuousOn (fun p : ℝ × ℝ => heatFlow q p.1 p.2) {p : ℝ × ℝ | 0 ≤ p.1} := by
    simpa only [heatFlow] using heatFlow_continuousOn_nonneg q hqc hqb
  have hmap : Set.MapsTo (fun p : ℝ × ℝ => heatFlow q p.1 p.2) {p : ℝ × ℝ | 0 ≤ p.1}
      (Set.Ioo (0 : ℝ) 1) := fun p _ => h.mem p.1 p.2
  have hcomp := continuousOn_gphi.comp hHF hmap
  simpa only [Function.comp_def, U] using hcomp

lemma continuousOn_Chat {f g h : ℝ → ℝ} {δf αf δg αg δh αh : ℝ}
    (hf : IsNice f δf αf) (hg : IsNice g δg αg) (hh : IsNice h δh αh)
    (hfc : Continuous f) (hgc : Continuous g) (hhc : Continuous h) (lam : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => Chat f g h lam p.1 p.2.1 p.2.2)
      {p : ℝ × ℝ × ℝ | 0 ≤ p.1} := by
  set S : Set (ℝ × ℝ × ℝ) := {p | 0 ≤ p.1} with hS
  have hφh : Continuous (fun p : ℝ × ℝ × ℝ => ((p.1, lam * p.2.1 + (1 - lam) * p.2.2) : ℝ × ℝ)) := by
    fun_prop
  have hφf : Continuous (fun p : ℝ × ℝ × ℝ => ((p.1, p.2.1) : ℝ × ℝ)) := by fun_prop
  have hφg : Continuous (fun p : ℝ × ℝ × ℝ => ((p.1, p.2.2) : ℝ × ℝ)) := by fun_prop
  have hUh : ContinuousOn (fun p : ℝ × ℝ × ℝ => U h p.1 (lam * p.2.1 + (1 - lam) * p.2.2)) S :=
    (continuousOn_U h hhc (IsNice.abs_le hh) hh).comp hφh.continuousOn (fun p hp => hp)
  have hUf : ContinuousOn (fun p : ℝ × ℝ × ℝ => U f p.1 p.2.1) S :=
    (continuousOn_U f hfc (IsNice.abs_le hf) hf).comp hφf.continuousOn (fun p hp => hp)
  have hUg : ContinuousOn (fun p : ℝ × ℝ × ℝ => U g p.1 p.2.2) S :=
    (continuousOn_U g hgc (IsNice.abs_le hg) hg).comp hφg.continuousOn (fun p hp => hp)
  have h2 : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      lam * U f p.1 p.2.1 + (1 - lam) * U g p.1 p.2.2) S :=
    (hUf.const_mul lam).add (hUg.const_mul (1 - lam))
  have h3 : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      U h p.1 (lam * p.2.1 + (1 - lam) * p.2.2)
        - (lam * U f p.1 p.2.1 + (1 - lam) * U g p.1 p.2.2)) S := hUh.sub h2
  simpa only [Chat] using h3


lemma U_bounds {q : ℝ → ℝ} {δ α : ℝ} (h : IsNice q δ α) (t x : ℝ) :
    gphi δ ≤ U q t x ∧ U q t x ≤ gphi α := by
  obtain ⟨hl, hu⟩ := heatFlow_bounds q h.2.1 h.2.2.1 h.1 t x
  have hδ1 : δ < 1 := lt_of_le_of_lt (le_trans (h.2.1 0) (h.2.2.1 0)) h.2.2.2.2
  have hα0 : 0 < α := lt_of_lt_of_le h.2.2.2.1 (le_trans (h.2.1 0) (h.2.2.1 0))
  exact ⟨gphi_strictMonoOn.monotoneOn ⟨h.2.2.2.1, hδ1⟩ (h.mem t x) hl,
          gphi_strictMonoOn.monotoneOn (h.mem t x) ⟨hα0, h.2.2.2.2⟩ hu⟩

lemma Chat_lower {f g h : ℝ → ℝ} {δf αf δg αg δh αh : ℝ}
    (hf : IsNice f δf αf) (hg : IsNice g δg αg) (hh : IsNice h δh αh)
    (lam : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (t x y : ℝ) :
    gphi δh - (lam * gphi αf + (1 - lam) * gphi αg) ≤ Chat f g h lam t x y := by
  have hh' := (U_bounds hh t (lam * x + (1 - lam) * y)).1
  have hf' := (U_bounds hf t x).2
  have hg' := (U_bounds hg t y).2
  simp only [Chat]
  nlinarith [mul_le_mul_of_nonneg_left hf' hl0, mul_le_mul_of_nonneg_left hg' (sub_nonneg.mpr hl1)]

lemma Chat_zero_nonneg {f g h : ℝ → ℝ} {δh αh : ℝ} (hh : IsNice h δh αh) (lam : ℝ)
    (hHP : ∀ a b, gPhi (lam * gphi (f a) + (1 - lam) * gphi (g b)) ≤ h (lam * a + (1 - lam) * b)) :
    ∀ x y, 0 ≤ Chat f g h lam 0 x y := by
  intro x y
  simp only [Chat, U, heatFlow_zero]
  set w : ℝ := lam * gphi (f x) + (1 - lam) * gphi (g y) with hw
  have h2 : gPhi w ≤ h (lam * x + (1 - lam) * y) := by rw [hw]; exact hHP x y
  have hlow : gPhi w ∈ Set.Ioo (0 : ℝ) 1 := ⟨gPhi_pos w, gPhi_lt_one w⟩
  have hupp : h (lam * x + (1 - lam) * y) ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_of_lt_of_le hh.2.2.2.1 (hh.2.1 _), lt_of_le_of_lt (hh.2.2.1 _) hh.2.2.2.2⟩
  have h3 : gphi (gPhi w) ≤ gphi (h (lam * x + (1 - lam) * y)) :=
    gphi_strictMonoOn.monotoneOn hlow hupp h2
  rw [gphi_gPhi] at h3
  linarith [h3]

lemma Chat_hasDerivAt_x {f g h : ℝ → ℝ} {δf αf δg αg δh αh : ℝ}
    (hf : IsNice f δf αf) (hg : IsNice g δg αg) (hh : IsNice h δh αh)
    (lam : ℝ) {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    HasDerivAt (fun x' => Chat f g h lam t x' y)
      (lam * deriv (fun z => U h t z) (lam * x + (1 - lam) * y)
        - lam * deriv (fun z => U f t z) x) x := by
  have hUh : HasDerivAt (fun x' => U h t (lam * x' + (1 - lam) * y))
      (lam * deriv (fun z => U h t z) (lam * x + (1 - lam) * y)) x := by
    have h1 : HasDerivAt (fun z => U h t z) (deriv (fun z => U h t z) (lam * x + (1 - lam) * y))
        (lam * x + (1 - lam) * y) := by
      have h0 := U_hasDerivAt_x (q := h) hh ht (lam * x + (1 - lam) * y)
      rwa [← U_deriv_x_eq hh ht (lam * x + (1 - lam) * y)] at h0
    have h2 : HasDerivAt (fun x' : ℝ => lam * x' + (1 - lam) * y) lam x := by
      have h3 := (hasDerivAt_id x).const_mul lam
      simpa only [id_eq, one_mul, mul_one] using h3.add_const ((1 - lam) * y)
    have h4 := h1.comp x h2
    have hv : deriv (fun z => U h t z) (lam * x + (1 - lam) * y) * lam
        = lam * deriv (fun z => U h t z) (lam * x + (1 - lam) * y) := by ring
    rw [hv] at h4
    simpa only [Function.comp_def] using h4
  have hUf : HasDerivAt (fun x' => U f t x') (deriv (fun z => U f t z) x) x := by
    have h0 := U_hasDerivAt_x (q := f) hf ht x
    rwa [← U_deriv_x_eq hf ht x] at h0
  have h2' : HasDerivAt (fun x' => lam * U f t x' + (1 - lam) * U g t y)
      (lam * deriv (fun z => U f t z) x) x :=
    (hUf.const_mul lam).add_const ((1 - lam) * U g t y)
  have hfin := hUh.sub h2'
  refine hfin.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun x' => ?_))
  simp only [Pi.sub_apply, Chat]

lemma Chat_hasDerivAt_y {f g h : ℝ → ℝ} {δf αf δg αg δh αh : ℝ}
    (hf : IsNice f δf αf) (hg : IsNice g δg αg) (hh : IsNice h δh αh)
    (lam : ℝ) {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    HasDerivAt (fun y' => Chat f g h lam t x y')
      ((1 - lam) * deriv (fun z => U h t z) (lam * x + (1 - lam) * y)
        - (1 - lam) * deriv (fun z => U g t z) y) y := by
  have hUh : HasDerivAt (fun y' => U h t (lam * x + (1 - lam) * y'))
      ((1 - lam) * deriv (fun z => U h t z) (lam * x + (1 - lam) * y)) y := by
    have h1 : HasDerivAt (fun z => U h t z) (deriv (fun z => U h t z) (lam * x + (1 - lam) * y))
        (lam * x + (1 - lam) * y) := by
      have h0 := U_hasDerivAt_x (q := h) hh ht (lam * x + (1 - lam) * y)
      rwa [← U_deriv_x_eq hh ht (lam * x + (1 - lam) * y)] at h0
    have h2 : HasDerivAt (fun y' : ℝ => lam * x + (1 - lam) * y') (1 - lam) y := by
      have h3 := (hasDerivAt_id y).const_mul (1 - lam)
      simpa only [id_eq, one_mul, mul_one] using h3.const_add (lam * x)
    have h4 := h1.comp y h2
    have hv : deriv (fun z => U h t z) (lam * x + (1 - lam) * y) * (1 - lam)
        = (1 - lam) * deriv (fun z => U h t z) (lam * x + (1 - lam) * y) := by ring
    rw [hv] at h4
    simpa only [Function.comp_def] using h4
  have hUg : HasDerivAt (fun y' => U g t y') (deriv (fun z => U g t z) y) y := by
    have h0 := U_hasDerivAt_x (q := g) hg ht y
    rwa [← U_deriv_x_eq hg ht y] at h0
  have h2' : HasDerivAt (fun y' => lam * U f t x + (1 - lam) * U g t y')
      ((1 - lam) * deriv (fun z => U g t z) y) y :=
    (hUg.const_mul (1 - lam)).const_add (lam * U f t x)
  have hfin := hUh.sub h2'
  refine hfin.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y' => ?_))
  simp only [Pi.sub_apply, Chat]


lemma heatFlow_mono_simple {g h : ℝ → ℝ} (hgm : Measurable g) (hhm : Measurable h)
    (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1) (hh0 : ∀ x, 0 ≤ h x) (hh1 : ∀ x, h x ≤ 1)
    (hle : ∀ x, g x ≤ h x) (t y : ℝ) : heatFlow g t y ≤ heatFlow h t y := by
  unfold heatFlow
  have hint : ∀ q : ℝ → ℝ, (∀ x, 0 ≤ q x) → (∀ x, q x ≤ 1) → Measurable q →
      Integrable (fun z : ℝ => q (y + Real.sqrt t * z) * Real.exp (-Real.pi * z ^ 2)) := by
    intro q hq0 hq1 hqm
    refine Integrable.mono' integrable_gauss
      ((hqm.comp (measurable_const.add (measurable_const.mul measurable_id))).mul
        gauss_cont_aux.measurable).aestronglyMeasurable (Filter.Eventually.of_forall (fun z => ?_))
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (Real.exp_pos _).le (by rw [abs_of_nonneg (hq0 _)]; exact hq1 _)
  exact integral_mono (hint g hg0 hg1 hgm) (hint h hh0 hh1 hhm)
    (fun z => mul_le_mul_of_nonneg_right (hle _) (Real.exp_pos _).le)


lemma Chat_deriv_x_eq {f g h : ℝ → ℝ} {δf αf δg αg δh αh : ℝ}
    (hf : IsNice f δf αf) (hg : IsNice g δg αg) (hh : IsNice h δh αh)
    (lam : ℝ) {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    deriv (fun x' => Chat f g h lam t x' y) x
      = lam * deriv (fun z => U h t z) (lam * x + (1 - lam) * y)
        - lam * deriv (fun z => U f t z) x :=
  (Chat_hasDerivAt_x hf hg hh lam ht x y).deriv

lemma Chat_deriv_y_eq {f g h : ℝ → ℝ} {δf αf δg αg δh αh : ℝ}
    (hf : IsNice f δf αf) (hg : IsNice g δg αg) (hh : IsNice h δh αh)
    (lam : ℝ) {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    deriv (fun y' => Chat f g h lam t x y') y
      = (1 - lam) * deriv (fun z => U h t z) (lam * x + (1 - lam) * y)
        - (1 - lam) * deriv (fun z => U g t z) y :=
  (Chat_hasDerivAt_y hf hg hh lam ht x y).deriv

/-- At a continuous local minimum, the iterated second derivative is nonnegative. -/
lemma localMin_second_deriv_nonneg_of_continuous {f : ℝ → ℝ} {x : ℝ}
    (hmin : IsLocalMin f x) (hf : Continuous f) : 0 ≤ deriv (deriv f) x := by
  by_contra h
  push_neg at h
  have hx0 : deriv f x = 0 := hmin.deriv_eq_zero
  have hsign : ∀ᶠ y in 𝓝 x, SignType.sign (deriv f y) = SignType.sign (x - y) :=
    eventually_nhdsWithin_sign_eq_of_deriv_neg h hx0
  let W : Set ℝ := {y | SignType.sign (deriv f y) = SignType.sign (x - y) ∧ f x ≤ f y}
  have hW : W ∈ 𝓝 x := by
    filter_upwards [hsign, hmin] with y h1 h2 using ⟨h1, h2⟩
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hW
  set δ := ε / 2 with hδdef
  have hδpos : 0 < δ := by positivity
  have hδlt : δ < ε := by rw [hδdef]; linarith
  have hxδ : x < x + δ := by linarith
  have hball : Icc x (x + δ) ⊆ Metric.ball x ε := by
    intro y hy
    rw [Metric.mem_ball, Real.dist_eq]
    have : |y - x| ≤ δ := by
      rw [abs_of_nonneg (by linarith [hy.1])]
      linarith [hy.2]
    linarith
  have hcont : ContinuousOn f (Icc x (x + δ)) := hf.continuousOn
  have hderiv : ∀ y ∈ interior (Icc x (x + δ)), deriv f y < 0 := by
    rw [interior_Icc]
    intro y hy
    have hyW : y ∈ W := hsub (hball ⟨le_of_lt hy.1, le_of_lt hy.2⟩)
    rw [← sign_eq_neg_one_iff, hyW.1, sign_eq_neg_one_iff]
    linarith [hy.1]
  have hanti : StrictAntiOn f (Icc x (x + δ)) :=
    strictAntiOn_of_deriv_neg (convex_Icc x (x + δ)) hcont hderiv
  have hlt : f (x + δ) < f x :=
    hanti ⟨le_refl x, le_of_lt hxδ⟩ ⟨le_of_lt hxδ, le_refl _⟩ hxδ
  have hle : f x ≤ f (x + δ) := by
    have hb : x + δ ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, Real.dist_eq, show x + δ - x = δ by ring, abs_of_pos hδpos]
      exact hδlt
    exact (hsub hb).2
  linarith

lemma Chat_nonneg_of_continuous_interior {f g h : ℝ → ℝ} {δf αf δg αg δh αh : ℝ}
    (hf : IsNice f δf αf) (hg : IsNice g δg αg) (hh : IsNice h δh αh)
    (hfc : Continuous f) (hgc : Continuous g) (hhc : Continuous h)
    {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1)
    (hHP : ∀ a b, gPhi (lam * gphi (f a) + (1 - lam) * gphi (g b)) ≤ h (lam * a + (1 - lam) * b))
    (hbound : ∃ R : ℝ, ∀ t : ℝ, 0 ≤ t → ∀ x y : ℝ, R ≤ |x| + |y| → 0 ≤ Chat f g h lam t x y) :
    ∀ t : ℝ, 0 < t → ∀ x y : ℝ, 0 ≤ Chat f g h lam t x y := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨t₀, ht₀, x₀, y₀, hneg⟩ := hcon
  set e : ℝ := -Chat f g h lam t₀ x₀ y₀ / (2 * t₀) with he
  have hepos : 0 < e := by rw [he]; exact div_pos (neg_pos.mpr hneg) (by positivity)
  have hψ0 : e * t₀ + Chat f g h lam t₀ x₀ y₀ < 0 := by
    have h2 : e * t₀ = -Chat f g h lam t₀ x₀ y₀ / 2 := by rw [he]; field_simp
    rw [h2]; linarith
  obtain ⟨R, hR⟩ := hbound
  set C : ℝ := gphi δh - (lam * gphi αf + (1 - lam) * gphi αg) with hC
  have hClow : ∀ t x y, C ≤ Chat f g h lam t x y := by
    intro t x y; rw [hC]; exact Chat_lower hf hg hh lam hl0.le hl1.le t x y
  set ψ : ℝ × ℝ × ℝ → ℝ := fun p => e * p.1 + Chat f g h lam p.1 p.2.1 p.2.2 with hψ
  have hψu : ∀ t x y, ψ (t, x, y) = e * t + Chat f g h lam t x y := by
    intro t x y; rw [hψ]
  have hψcont : ContinuousOn ψ {p : ℝ × ℝ × ℝ | 0 ≤ p.1} := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ × ℝ => e * p.1) {p : ℝ × ℝ × ℝ | 0 ≤ p.1} :=
      (continuous_const.mul continuous_fst).continuousOn
    have h2 := continuousOn_Chat hf hg hh hfc hgc hhc lam
    rw [hψ]; exact h1.add h2
  set T' : ℝ := t₀ + (|e * t₀ + Chat f g h lam t₀ x₀ y₀ - C| + 1) / e with hT'
  have hT'gt : t₀ < T' := by
    rw [hT']; exact lt_add_of_pos_right _ (div_pos (by positivity) hepos)
  have hT'bound : e * t₀ + Chat f g h lam t₀ x₀ y₀ < e * T' + C := by
    have h1 : e * T' = e * t₀ + (|e * t₀ + Chat f g h lam t₀ x₀ y₀ - C| + 1) := by
      rw [hT']; field_simp
    rw [h1]
    have h2 : e * t₀ + Chat f g h lam t₀ x₀ y₀ - C ≤ |e * t₀ + Chat f g h lam t₀ x₀ y₀ - C| :=
      le_abs_self _
    have het : 0 < e * t₀ := mul_pos hepos ht₀
    linarith
  set M : ℝ := max R (max |x₀| |y₀|) + 1 with hM
  have hMpos : 0 < M := by
    rw [hM]; have := le_max_right R (max |x₀| |y₀|); have := le_max_left |x₀| |y₀|
    have := abs_nonneg x₀; linarith
  have hRM : R < M := by
    rw [hM]; have := le_max_left R (max |x₀| |y₀|); linarith
  have hMx0 : |x₀| < M := by
    rw [hM]; have := le_max_right R (max |x₀| |y₀|); have := le_max_left |x₀| |y₀|; linarith
  have hMy0 : |y₀| < M := by
    rw [hM]; have := le_max_right R (max |x₀| |y₀|); have := le_max_right |x₀| |y₀|; linarith
  set K : Set (ℝ × ℝ × ℝ) := Set.Icc 0 T' ×ˢ (Set.Icc (-M) M ×ˢ Set.Icc (-M) M) with hK
  have hKcomp : IsCompact K := by
    rw [hK]; exact isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hKmem0 : ((0 : ℝ), (0 : ℝ), (0 : ℝ)) ∈ K := by
    rw [hK]; simp only [Set.mem_prod, Set.mem_Icc]
    exact ⟨⟨le_refl 0, by linarith [ht₀, hT'gt]⟩,
      ⟨neg_nonpos.mpr hMpos.le, hMpos.le⟩, ⟨neg_nonpos.mpr hMpos.le, hMpos.le⟩⟩
  have hKmem : (t₀, x₀, y₀) ∈ K := by
    rw [hK]; simp only [Set.mem_prod, Set.mem_Icc]
    exact ⟨⟨le_of_lt ht₀, by linarith [ht₀, hT'gt]⟩,
      ⟨(abs_le.mp hMx0.le).1, (abs_le.mp hMx0.le).2⟩,
      ⟨(abs_le.mp hMy0.le).1, (abs_le.mp hMy0.le).2⟩⟩
  obtain ⟨P, hPK, hPmin⟩ := hKcomp.exists_isMinOn ⟨_, hKmem0⟩
    (hψcont.mono (fun p hp => by rw [hK] at hp; exact hp.1.1))
  obtain ⟨tP, xP, yP⟩ := P
  rw [hK] at hPK
  simp only [Set.mem_prod, Set.mem_Icc] at hPK
  obtain ⟨⟨htP0, htPT⟩, ⟨hxPm, hxPM⟩, ⟨hyPm, hyPM⟩⟩ := hPK
  have hPle : ψ (tP, xP, yP) ≤ ψ (t₀, x₀, y₀) := hPmin hKmem
  have hPlt : e * tP + Chat f g h lam tP xP yP < 0 := by
    have h1 : ψ (tP, xP, yP) < 0 := by
      refine lt_of_le_of_lt hPle ?_
      rw [hψu]; exact hψ0
    rwa [hψu] at h1
  have hChat0 : ∀ x y, 0 ≤ Chat f g h lam 0 x y := Chat_zero_nonneg hh lam hHP
  have htPpos : 0 < tP := by
    rcases lt_or_eq_of_le htP0 with hlt | heq
    · exact hlt
    · exfalso
      have hge : 0 ≤ e * tP + Chat f g h lam tP xP yP := by
        rw [← heq, mul_zero, zero_add]; exact hChat0 xP yP
      linarith
  have htPT' : tP < T' := by
    rcases lt_or_eq_of_le htPT with hlt | heq
    · exact hlt
    · exfalso
      have hge : e * T' + C ≤ e * tP + Chat f g h lam tP xP yP := by
        rw [heq]; linarith [hClow T' xP yP]
      linarith [hT'bound, hge]
  have hxPabs : |xP| < M := by
    by_contra hge
    push_neg at hge
    have hb : R ≤ |xP| + |yP| := by linarith [abs_nonneg yP, hRM]
    have hCh := hR tP htPpos.le xP yP hb
    have : 0 ≤ e * tP + Chat f g h lam tP xP yP := by
      have := mul_pos hepos htPpos
      linarith
    linarith
  have hyPabs : |yP| < M := by
    by_contra hge
    push_neg at hge
    have hb : R ≤ |xP| + |yP| := by linarith [abs_nonneg xP, hRM]
    have hCh := hR tP htPpos.le xP yP hb
    have : 0 ≤ e * tP + Chat f g h lam tP xP yP := by
      have := mul_pos hepos htPpos
      linarith
    linarith
  have hboxopen : IsOpen (Set.Ioo (0 : ℝ) T' ×ˢ (Set.Ioo (-M) M ×ˢ Set.Ioo (-M) M)) :=
    isOpen_Ioo.prod (isOpen_Ioo.prod isOpen_Ioo)
  have hPbox : (tP, xP, yP) ∈ Set.Ioo (0 : ℝ) T' ×ˢ (Set.Ioo (-M) M ×ˢ Set.Ioo (-M) M) :=
    ⟨⟨htPpos, htPT'⟩, ⟨(abs_lt.mp hxPabs).1, (abs_lt.mp hxPabs).2⟩,
      ⟨(abs_lt.mp hyPabs).1, (abs_lt.mp hyPabs).2⟩⟩
  have hKnhds : K ∈ 𝓝 (tP, xP, yP) := by
    refine Filter.mem_of_superset (hboxopen.mem_nhds hPbox) ?_
    intro q hq
    rw [hK]
    exact ⟨⟨le_of_lt hq.1.1, le_of_lt hq.1.2⟩, ⟨le_of_lt hq.2.1.1, le_of_lt hq.2.1.2⟩,
      ⟨le_of_lt hq.2.2.1, le_of_lt hq.2.2.2⟩⟩
  have hmin : IsLocalMin ψ (tP, xP, yP) :=
    Filter.Eventually.mono hKnhds (fun q hq => hPmin hq)
  have hmin_t : IsLocalMin (fun t : ℝ => ψ (t, xP, yP)) tP :=
    hmin.comp_continuous (g := fun t : ℝ => (t, xP, yP))
      (by fun_prop : ContinuousAt (fun t : ℝ => (t, xP, yP)) tP)
  have hmin_x : IsLocalMin (fun x : ℝ => ψ (tP, x, yP)) xP :=
    hmin.comp_continuous (g := fun x : ℝ => (tP, x, yP))
      (by fun_prop : ContinuousAt (fun x : ℝ => (tP, x, yP)) xP)
  have hmin_y : IsLocalMin (fun y : ℝ => ψ (tP, xP, y)) yP :=
    hmin.comp_continuous (g := fun y : ℝ => (tP, xP, y))
      (by fun_prop : ContinuousAt (fun y : ℝ => (tP, xP, y)) yP)
  have hmin_d : IsLocalMin (fun s : ℝ => ψ (tP, xP + s, yP + s)) 0 := by
    have h2 : IsLocalMin ψ ((tP, xP + (0:ℝ), yP + (0:ℝ)) : ℝ × ℝ × ℝ) := by
      have hEq : ((tP, xP + (0:ℝ), yP + (0:ℝ)) : ℝ × ℝ × ℝ) = (tP, xP, yP) := by simp
      rwa [hEq]
    exact h2.comp_continuous (g := fun s : ℝ => (tP, xP + s, yP + s))
      (by fun_prop : ContinuousAt (fun s : ℝ => (tP, xP + s, yP + s)) 0)
  have hdt : deriv (fun t : ℝ => Chat f g h lam t xP yP) tP = -e := by
    have hder : HasDerivAt (fun s : ℝ => Chat f g h lam s xP yP)
        (deriv (fun t : ℝ => Chat f g h lam t xP yP) tP) tP := by
      have h0 := Chat_hasDerivAt_t hf hg hh lam htPpos xP yP
      rwa [← (Chat_hasDerivAt_t hf hg hh lam htPpos xP yP).deriv] at h0
    have hderψ : HasDerivAt (fun s : ℝ => ψ (s, xP, yP))
        (e + deriv (fun t : ℝ => Chat f g h lam t xP yP) tP) tP := by
      change HasDerivAt (fun s : ℝ => e * s + Chat f g h lam s xP yP) _ tP
      have h1 : HasDerivAt (fun s : ℝ => e * s) e tP := by
        simpa using (hasDerivAt_id tP).const_mul e
      exact (h1.add hder).congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s => rfl))
    have hzero : deriv (fun s : ℝ => ψ (s, xP, yP)) tP = 0 := by
      rw [← fderiv_apply_one_eq_deriv, hmin_t.fderiv_eq_zero]; simp
    rw [hderψ.deriv] at hzero
    linarith
  have hdx : deriv (fun x : ℝ => Chat f g h lam tP x yP) xP = 0 := by
    have hder : HasDerivAt (fun x : ℝ => Chat f g h lam tP x yP)
        (deriv (fun x : ℝ => Chat f g h lam tP x yP) xP) xP := by
      have h0 := Chat_hasDerivAt_x hf hg hh lam htPpos xP yP
      rwa [← (Chat_hasDerivAt_x hf hg hh lam htPpos xP yP).deriv] at h0
    have hderψ : HasDerivAt (fun x : ℝ => ψ (tP, x, yP))
        (deriv (fun x : ℝ => Chat f g h lam tP x yP) xP) xP := by
      change HasDerivAt (fun x : ℝ => e * tP + Chat f g h lam tP x yP) _ xP
      exact (hder.add_const (e * tP)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun x => add_comm _ _))
    have hzero : deriv (fun x : ℝ => ψ (tP, x, yP)) xP = 0 := by
      rw [← fderiv_apply_one_eq_deriv, hmin_x.fderiv_eq_zero]; simp
    rwa [hderψ.deriv] at hzero
  have hdy : deriv (fun y : ℝ => Chat f g h lam tP xP y) yP = 0 := by
    have hder : HasDerivAt (fun y : ℝ => Chat f g h lam tP xP y)
        (deriv (fun y : ℝ => Chat f g h lam tP xP y) yP) yP := by
      have h0 := Chat_hasDerivAt_y hf hg hh lam htPpos xP yP
      rwa [← (Chat_hasDerivAt_y hf hg hh lam htPpos xP yP).deriv] at h0
    have hderψ : HasDerivAt (fun y : ℝ => ψ (tP, xP, y))
        (deriv (fun y : ℝ => Chat f g h lam tP xP y) yP) yP := by
      change HasDerivAt (fun y : ℝ => e * tP + Chat f g h lam tP xP y) _ yP
      exact (hder.add_const (e * tP)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun y => add_comm _ _))
    have hzero : deriv (fun y : ℝ => ψ (tP, xP, y)) yP = 0 := by
      rw [← fderiv_apply_one_eq_deriv, hmin_y.fderiv_eq_zero]; simp
    rwa [hderψ.deriv] at hzero
  have hv1 : deriv (fun z => U h tP z) (lam * xP + (1 - lam) * yP) = deriv (fun z => U f tP z) xP := by
    have h := hdx
    rw [Chat_deriv_x_eq hf hg hh lam htPpos xP yP] at h
    nlinarith [h, hl0]
  have hv2 : deriv (fun z => U h tP z) (lam * xP + (1 - lam) * yP) = deriv (fun z => U g tP z) yP := by
    have h := hdy
    rw [Chat_deriv_y_eq hf hg hh lam htPpos xP yP] at h
    nlinarith [h, hl1]
  have hsec := Chat_slice_second_eq hf hg hh lam htPpos xP yP hv1 hv2
  have hslicecont : Continuous (fun s : ℝ => ψ (tP, xP + s, yP + s)) := by
    have hg : Continuous (fun s : ℝ => (tP, xP + s, yP + s)) := by fun_prop
    have := hψcont.comp_continuous hg (fun s => by simp only [Set.mem_ofPred_eq]; linarith [htPpos])
    simpa only [Function.comp_def] using this
  have hd2ψ : 0 ≤ deriv (deriv (fun s : ℝ => ψ (tP, xP + s, yP + s))) 0 :=
    localMin_second_deriv_nonneg_of_continuous hmin_d hslicecont
  have heq : deriv (deriv (fun s : ℝ => ψ (tP, xP + s, yP + s))) 0
      = deriv (deriv (fun s : ℝ => Chat f g h lam tP (xP + s) (yP + s))) 0 := by
    have hslice_eq : (fun s : ℝ => ψ (tP, xP + s, yP + s))
        = (fun s : ℝ => e * tP + Chat f g h lam tP (xP + s) (yP + s)) := by
      funext s; rw [hψu]
    rw [hslice_eq, deriv_const_add' (e * tP)]
  have hd2 : 0 ≤ deriv (deriv (fun s : ℝ => Chat f g h lam tP (xP + s) (yP + s))) 0 := by
    rwa [← heq]
  have hneg : deriv (deriv (fun s : ℝ => Chat f g h lam tP (xP + s) (yP + s))) 0 < 0 := by
    rw [hsec, hdt]
    have het : 0 < e * tP := mul_pos hepos htPpos
    have hChneg : Chat f g h lam tP xP yP < 0 := by linarith
    have hprod : (deriv (fun z => U h tP z) (lam * xP + (1 - lam) * yP)) ^ 2
        * Chat f g h lam tP xP yP ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hChneg.le
    have hpi := Real.pi_pos
    nlinarith [hprod, hepos, hpi]
  exact absurd hd2 (not_le.mpr hneg)


lemma Chat_nonneg_of_continuous {f g h : ℝ → ℝ} {δf αf δg αg δh αh : ℝ}
    (hf : IsNice f δf αf) (hg : IsNice g δg αg) (hh : IsNice h δh αh)
    (hfc : Continuous f) (hgc : Continuous g) (hhc : Continuous h)
    {lam : ℝ} (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1)
    (hHP : ∀ a b, gPhi (lam * gphi (f a) + (1 - lam) * gphi (g b)) ≤ h (lam * a + (1 - lam) * b))
    (hbound : ∃ R : ℝ, ∀ t : ℝ, 0 ≤ t → ∀ x y : ℝ, R ≤ |x| + |y| → 0 ≤ Chat f g h lam t x y) :
    ∀ t : ℝ, 0 < t → ∀ x y : ℝ, 0 ≤ Chat f g h lam t x y := by
  rcases eq_or_lt_of_le hl0 with h0 | h0
  · subst h0
    have hgh : ∀ b, g b ≤ h b := by
      intro b
      have h1 := hHP 0 b
      simp only [zero_mul, zero_add, one_mul, add_zero, sub_zero] at h1
      have hspec : gPhi (gphi (g b)) = g b :=
        gphi_spec (g b) (lt_of_lt_of_le hg.2.2.2.1 (hg.2.1 b))
          (lt_of_le_of_lt (hg.2.2.1 b) hg.2.2.2.2)
      rwa [hspec] at h1
    intro t ht x y
    have hmono : heatFlow g t y ≤ heatFlow h t y :=
      heatFlow_mono_simple hg.1 hh.1 (fun z => le_of_lt (lt_of_lt_of_le hg.2.2.2.1 (hg.2.1 z)))
        (fun z => le_of_lt (lt_of_le_of_lt (hg.2.2.1 z) hg.2.2.2.2))
        (fun z => le_of_lt (lt_of_lt_of_le hh.2.2.2.1 (hh.2.1 z)))
        (fun z => le_of_lt (lt_of_le_of_lt (hh.2.2.1 z) hh.2.2.2.2)) hgh t y
    have hU : gphi (heatFlow g t y) ≤ gphi (heatFlow h t y) :=
      gphi_strictMonoOn.monotoneOn (hg.mem t y) (hh.mem t y) hmono
    simp only [Chat, U, zero_mul, zero_add, one_mul, add_zero, sub_zero]
    linarith [hU]
  · rcases eq_or_lt_of_le hl1 with h1 | h1
    · subst h1
      have hfh : ∀ b, f b ≤ h b := by
        intro b
        have h1 := hHP b 0
        simp only [one_mul, mul_zero, zero_mul, add_zero, zero_add, sub_zero, sub_self] at h1
        have hspec : gPhi (gphi (f b)) = f b :=
          gphi_spec (f b) (lt_of_lt_of_le hf.2.2.2.1 (hf.2.1 b))
            (lt_of_le_of_lt (hf.2.2.1 b) hf.2.2.2.2)
        rwa [hspec] at h1
      intro t ht x y
      have hmono : heatFlow f t x ≤ heatFlow h t x :=
        heatFlow_mono_simple hf.1 hh.1 (fun z => le_of_lt (lt_of_lt_of_le hf.2.2.2.1 (hf.2.1 z)))
          (fun z => le_of_lt (lt_of_le_of_lt (hf.2.2.1 z) hf.2.2.2.2))
          (fun z => le_of_lt (lt_of_lt_of_le hh.2.2.2.1 (hh.2.1 z)))
          (fun z => le_of_lt (lt_of_le_of_lt (hh.2.2.1 z) hh.2.2.2.2)) hfh t x
      have hU : gphi (heatFlow f t x) ≤ gphi (heatFlow h t x) :=
        gphi_strictMonoOn.monotoneOn (hf.mem t x) (hh.mem t x) hmono
      simp only [Chat, U, one_mul, mul_zero, zero_mul, add_zero, zero_add, sub_zero, sub_self]
      linarith [hU]
    · exact Chat_nonneg_of_continuous_interior hf hg hh hfc hgc hhc h0 h1 hHP hbound


/-- The functional Ehrhard inequality for continuous data, obtained by applying the maximum
principle at time `t = 1`, `x = y = 0`. -/
lemma eh_nice_of_boundary {f g h : ℝ → ℝ} {δf αf δg αg δh αh : ℝ}
    (hf : IsNice f δf αf) (hg : IsNice g δg αg) (hh : IsNice h δh αh)
    (hfc : Continuous f) (hgc : Continuous g) (hhc : Continuous h)
    {lam : ℝ} (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1)
    (hHP : ∀ a b, gPhi (lam * gphi (f a) + (1 - lam) * gphi (g b)) ≤ h (lam * a + (1 - lam) * b))
    (hbound : ∃ R : ℝ, ∀ t : ℝ, 0 ≤ t → ∀ x y : ℝ, R ≤ |x| + |y| → 0 ≤ Chat f g h lam t x y) :
    gPhi (lam * gphi (∫ x, f x * Real.exp (-Real.pi * x ^ 2))
        + (1 - lam) * gphi (∫ x, g x * Real.exp (-Real.pi * x ^ 2)))
      ≤ ∫ x, h x * Real.exp (-Real.pi * x ^ 2) := by
  have hChat := Chat_nonneg_of_continuous hf hg hh hfc hgc hhc hl0 hl1 hHP hbound 1 one_pos 0 0
  have hfq : heatFlow f 1 0 = ∫ x, f x * Real.exp (-Real.pi * x ^ 2) := by
    simp only [heatFlow, Real.sqrt_one, zero_mul, add_zero, one_mul, zero_add]
  have hgq : heatFlow g 1 0 = ∫ x, g x * Real.exp (-Real.pi * x ^ 2) := by
    simp only [heatFlow, Real.sqrt_one, zero_mul, add_zero, one_mul, zero_add]
  have hhq : heatFlow h 1 0 = ∫ x, h x * Real.exp (-Real.pi * x ^ 2) := by
    simp only [heatFlow, Real.sqrt_one, zero_mul, add_zero, one_mul, zero_add]
  rw [Chat] at hChat
  simp only [U, mul_zero, add_zero] at hChat
  rw [hfq, hgq, hhq] at hChat
  have h2 : lam * gphi (∫ x, f x * Real.exp (-Real.pi * x ^ 2))
      + (1 - lam) * gphi (∫ x, g x * Real.exp (-Real.pi * x ^ 2))
      ≤ gphi (∫ x, h x * Real.exp (-Real.pi * x ^ 2)) := by linarith [hChat]
  have h3 := gPhi_strictMono.monotone h2
  obtain ⟨hl, hu⟩ := heatFlow_bounds h hh.2.1 hh.2.2.1 hh.1 1 0
  rw [hhq] at hl hu
  rw [gphi_spec _ (lt_of_lt_of_le hh.2.2.2.1 hl) (lt_of_le_of_lt hu hh.2.2.2.2)] at h3
  exact h3

/-!
## Roadmap for the remaining proof (Borell's heat-flow argument)

Everything above is verified.  What remains, in order:

1. `Chat f g h lam t x y := U h t (lam*x+(1-lam)*y) - (lam*U f t x + (1-lam)*U g t y)`
   together with the three differentiation identities
   * `HasDerivAt (fun s => Chat f g h lam s x y) (...) t`              (time derivative)
   * `HasDerivAt (fun s => Chat f g h lam t (x+s) (y+s)) (...) 0`      (space derivative along the slice)
   * `HasDerivAt (fun s => deriv (fun s' => Chat ... t (x+s') (y+s')) s) (...) 0` (second derivative)
   and the key identity (using `U_pde` and the agreement of the three first spatial
   derivatives coming from the vanishing of the space derivative):
   `deriv (deriv (slice)) 0 = 4*pi * deriv (fun s => Chat ... s x y) t
        + 2*pi * (deriv (fun z => U h t z) (lam*x+(1-lam)*y))^2 * Chat f g h lam t x y`.

2. Maximum principle: if `Chat` were negative somewhere with `t > 0`, then `eps*t + Chat`
   attains a strictly negative minimum at some `P = (t0,x0,y0)` with `t0 > 0`
   (needs: `Chat 0 x y >= 0` from the pointwise hypothesis, plus
   `liminf_{|x|+|y| -> oo} inf_{t in [0,T]} Chat >= 0`).  At `P`:
   `deriv_t Chat = -eps`, the space derivative vanishes, and the second derivative
   of the slice is `>= 0` (local minimum), while the identity of 1. gives
   `=-4*pi*eps + 2*pi*v^2*Chat(P) < 0`, a contradiction.  Hence `Chat >= 0` everywhere,
   and evaluating at `t = 1, x = y = 0` (where `heatFlow q 1 0 = ∫ q dgamma`) yields
   the Ehrhard inequality for nice `f,g,h`.

3. Sup-convolution `h(x) = gPhi (sSup {w | ∃ s t, lam*s+(1-lam)*t = x ∧
   w = lam*gphi(f s)+(1-lam)*gphi(g t)})`:  it is `>= δ`, `<= α`, satisfies the
   pointwise hypothesis, and `liminf_{|z|->oo}` of it equals
   `gPhi (max (lam*gphi α + (1-lam)*gphi δ) (lam*gphi δ + (1-lam)*gphi α))`,
   which is exactly what makes 2. work.  (Take `s` over a countable dense set and
   `f`,`g` continuous to get measurability.)

4. Reduction: `h_orig >= h_supconv` pointwise, so `∫ h_orig >= ∫ h_supconv`; approximate
   general measurable `f,g` by `clamp(f,1/m,1-1/N)` made constant outside `[-R,R]`,
   apply 2.-3. to the approximations and pass to the limit (dominated convergence).
-/


/-! ## The Gaussian density, positivity of the heat extension, and the test function -/

/-- The Gaussian density in the `pi`-normalisation, `x ↦ exp (-pi x²)`. -/
noncomputable def gdens (x : ℝ) : ℝ := Real.exp (-Real.pi * x ^ 2)

lemma gdens_pos (x : ℝ) : 0 < gdens x := by unfold gdens; exact Real.exp_pos _

lemma gdens_cont : Continuous gdens := by unfold gdens; fun_prop

lemma gdens_hasDerivAt (y : ℝ) :
    HasDerivAt gdens (gdens y * (-(2 * Real.pi * y))) y := by
  have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * y) y := by
    have h := hasDerivAt_pow 2 y
    norm_num at h
    exact h
  have h3 := (((h2.const_mul (-Real.pi)).exp))
  have hval : Real.exp (-Real.pi * y ^ 2) * ((-Real.pi) * (2 * y))
      = gdens y * (-(2 * Real.pi * y)) := by
    simp only [gdens]; ring
  rw [hval] at h3
  exact h3

lemma integrable_gdens : Integrable gdens := by unfold gdens; exact integrable_gauss

lemma gPhi_hasDerivAt (y : ℝ) : HasDerivAt gPhi (gdens y) y := by
  have hprim : HasDerivAt (fun t : ℝ => ∫ x in (0 : ℝ)..t, Real.exp (-Real.pi * x ^ 2))
      (Real.exp (-Real.pi * y ^ 2)) y :=
    intervalIntegral.integral_hasDerivAt_right integrable_gauss.intervalIntegrable
      (gauss_cont_aux.aestronglyMeasurable.stronglyMeasurableAtFilter)
      gauss_cont_aux.continuousAt
  have hg : gPhi = (fun t : ℝ => gPhi 0 + ∫ x in (0 : ℝ)..t, Real.exp (-Real.pi * x ^ 2)) := by
    funext t
    have h := intervalIntegral.integral_Iic_sub_Iic (μ := (volume : Measure ℝ)) (a := (0 : ℝ))
      (b := t) (f := fun x : ℝ => Real.exp (-Real.pi * x ^ 2)) integrable_gauss.integrableOn
      integrable_gauss.integrableOn
    unfold gPhi
    linarith
  rw [hg]
  exact hprim.const_add _

lemma gPhi_deriv (y : ℝ) : deriv gPhi y = gdens y := (gPhi_hasDerivAt y).deriv

/-- Admissible data: measurable, strictly positive pointwise, bounded above by `1 - η`. -/
def IsAdm (q : ℝ → ℝ) (η : ℝ) : Prop :=
  Measurable q ∧ (∀ x, 0 < q x) ∧ (∀ x, q x ≤ 1 - η) ∧ 0 < η

lemma IsAdm.abs_le {q : ℝ → ℝ} {η : ℝ} (h : IsAdm q η) : ∀ x, |q x| ≤ 1 := by
  intro x
  rw [abs_of_pos (h.2.1 x)]
  linarith [h.2.2.1 x, h.2.2.2]

lemma heatFlow_integrand_integrable {q : ℝ → ℝ} (hqm : Measurable q) (hqb : ∀ x, |q x| ≤ 1)
    (t x : ℝ) :
    Integrable (fun z : ℝ => q (x + Real.sqrt t * z) * Real.exp (-Real.pi * z ^ 2)) := by
  refine Integrable.mono' integrable_gauss ?_ ?_
  · exact ((hqm.comp ((measurable_const.mul measurable_id).const_add x)).mul
      gauss_cont_aux.measurable).aestronglyMeasurable
  · filter_upwards with z
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (Real.exp_pos _).le (hqb _)

lemma heatFlow_pos {q : ℝ → ℝ} (hqm : Measurable q) (hq : ∀ x, 0 < q x) (hqb : ∀ x, |q x| ≤ 1)
    (t x : ℝ) : 0 < heatFlow q t x := by
  have hint := heatFlow_integrand_integrable hqm hqb t x
  have hpos : (0 : ℝ) < ∫ z, q (x + Real.sqrt t * z) * Real.exp (-Real.pi * z ^ 2) := by
    rw [integral_pos_iff_support_of_nonneg
      (fun z => mul_nonneg (le_of_lt (hq _)) (Real.exp_pos _).le) hint]
    have hsupp : Function.support
        (fun z : ℝ => q (x + Real.sqrt t * z) * Real.exp (-Real.pi * z ^ 2)) = Set.univ := by
      refine Set.eq_univ_of_forall (fun z => ?_)
      exact Function.mem_support.mpr (mul_ne_zero (ne_of_gt (hq _)) (Real.exp_ne_zero _))
    rw [hsupp]
    have h1 : 0 < volume (Set.Iic (0 : ℝ)) := by
      rw [Real.volume_Iic]; exact ENNReal.zero_lt_top
    exact lt_of_lt_of_le h1 (measure_mono (Set.subset_univ _))
  simpa only [heatFlow] using hpos

lemma heatFlow_lt_one {q : ℝ → ℝ} {η : ℝ} (hqm : Measurable q) (hb : ∀ x, |q x| ≤ 1)
    (hq : ∀ x, q x ≤ 1 - η) (hη : 0 < η) (t x : ℝ) : heatFlow q t x < 1 := by
  have hint1 := heatFlow_integrand_integrable hqm hb t x
  have hconst : Integrable (fun z : ℝ => η * Real.exp (-Real.pi * z ^ 2)) :=
    integrable_gauss.const_mul η
  have hsub : Integrable (fun z : ℝ => (1 - q (x + Real.sqrt t * z)) * Real.exp (-Real.pi * z ^ 2)) := by
    have h1 : (fun z : ℝ => (1 - q (x + Real.sqrt t * z)) * Real.exp (-Real.pi * z ^ 2))
        = (fun z : ℝ => Real.exp (-Real.pi * z ^ 2)
            - q (x + Real.sqrt t * z) * Real.exp (-Real.pi * z ^ 2)) := by
      funext z; ring
    rw [h1]
    exact integrable_gauss.sub hint1
  have hmono : (∫ z : ℝ, η * Real.exp (-Real.pi * z ^ 2))
      ≤ ∫ z : ℝ, (1 - q (x + Real.sqrt t * z)) * Real.exp (-Real.pi * z ^ 2) := by
    refine integral_mono hconst hsub (fun z => ?_)
    have := hq (x + Real.sqrt t * z)
    nlinarith [Real.exp_pos (-Real.pi * z ^ 2)]
  rw [integral_const_mul, integral_gauss, mul_one] at hmono
  have hsplit : (∫ z : ℝ, (1 - q (x + Real.sqrt t * z)) * Real.exp (-Real.pi * z ^ 2))
      = 1 - heatFlow q t x := by
    have h1 : (fun z : ℝ => (1 - q (x + Real.sqrt t * z)) * Real.exp (-Real.pi * z ^ 2))
        = (fun z : ℝ => Real.exp (-Real.pi * z ^ 2)
            - q (x + Real.sqrt t * z) * Real.exp (-Real.pi * z ^ 2)) := by
      funext z; ring
    rw [h1, integral_sub integrable_gauss hint1, integral_gauss, heatFlow]
  linarith [hmono, hsplit]

lemma IsAdm.mem {q : ℝ → ℝ} {η : ℝ} (h : IsAdm q η) (t x : ℝ) :
    heatFlow q t x ∈ Set.Ioo 0 1 :=
  ⟨heatFlow_pos h.1 h.2.1 h.abs_le t x, heatFlow_lt_one h.1 h.abs_le h.2.2.1 h.2.2.2 t x⟩

lemma continuousOn_U' {q : ℝ → ℝ} {η : ℝ} (h : IsAdm q η) (hqc : Continuous q) :
    ContinuousOn (fun p : ℝ × ℝ => U q p.1 p.2) {p : ℝ × ℝ | 0 ≤ p.1} := by
  have hHF : ContinuousOn (fun p : ℝ × ℝ => heatFlow q p.1 p.2) {p : ℝ × ℝ | 0 ≤ p.1} := by
    simpa only [heatFlow] using heatFlow_continuousOn_nonneg q hqc h.abs_le
  have hmap : Set.MapsTo (fun p : ℝ × ℝ => heatFlow q p.1 p.2) {p : ℝ × ℝ | 0 ≤ p.1}
      (Set.Ioo (0 : ℝ) 1) := fun p _ => h.mem p.1 p.2
  have hcomp := continuousOn_gphi.comp hHF hmap
  simpa only [Function.comp_def, U] using hcomp

/-- The argument of the outer `gPhi`: `lam Φ⁻¹(P_t f x) + (1-lam) Φ⁻¹(P_t g y)`. -/
def Bmix (lam : ℝ) (f g : ℝ → ℝ) (t x y : ℝ) : ℝ :=
  lam * U f t x + (1 - lam) * U g t y

/-- `P_t h (lam x + (1-lam) y) - gPhi (lam Φ⁻¹ (P_t f x) + (1-lam) Φ⁻¹ (P_t g y))`. -/
def EhrV (lam : ℝ) (f g h : ℝ → ℝ) (t x y : ℝ) : ℝ :=
  heatFlow h t (lam * x + (1 - lam) * y) - gPhi (Bmix lam f g t x y)

lemma EhrV_zero (lam : ℝ) (f g h : ℝ → ℝ) (x y : ℝ) :
    EhrV lam f g h 0 x y
      = h (lam * x + (1 - lam) * y) - gPhi (lam * gphi (f x) + (1 - lam) * gphi (g y)) := by
  simp only [EhrV, Bmix, U, heatFlow_zero]




/-! ### Shifted derivatives -/

lemma U_hasDerivAt_x' {q : ℝ → ℝ} {η : ℝ} (h : IsAdm q η) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun x' => U q t x') (gphiD (U q t x) * deriv (fun x' => heatFlow q t x') x) x := by
  have hmem := h.mem t x
  have hd := (gphi_hasDerivAt' (heatFlow q t x) hmem.1 hmem.2).comp x
    ((heatFlow_derivs q h.abs_le).1 t ht x)
  change HasDerivAt (gphi ∘ fun x' => heatFlow q t x')
    (gphiD (gphi (heatFlow q t x)) * deriv (fun x' => heatFlow q t x') x) x
  exact hd

lemma U_hasDerivAt_t' {q : ℝ → ℝ} {η : ℝ} (h : IsAdm q η) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => U q s x) (gphiD (U q t x) * deriv (fun s => heatFlow q s x) t) t := by
  have hmem := h.mem t x
  have hd := (gphi_hasDerivAt' (heatFlow q t x) hmem.1 hmem.2).comp t
    ((heatFlow_derivs q h.abs_le).2.1 t ht x)
  change HasDerivAt (gphi ∘ fun s => heatFlow q s x)
    (gphiD (gphi (heatFlow q t x)) * deriv (fun s => heatFlow q s x) t) t
  exact hd

lemma U_deriv_t_eq' {q : ℝ → ℝ} {η : ℝ} (h : IsAdm q η) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    deriv (fun s => U q s x) t = gphiD (U q t x) * deriv (fun s => heatFlow q s x) t :=
  (U_hasDerivAt_t' h ht x).deriv

lemma U_deriv_x_eq' {q : ℝ → ℝ} {η : ℝ} (h : IsAdm q η) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    deriv (fun x' => U q t x') x = gphiD (U q t x) * deriv (fun x' => heatFlow q t x') x :=
  (U_hasDerivAt_x' h ht x).deriv

lemma heatFlow_shift_hasDerivAt {q : ℝ → ℝ} (hqb : ∀ x, |q x| ≤ 1) {t : ℝ} (ht : 0 < t)
    (x s : ℝ) :
    HasDerivAt (fun s' : ℝ => heatFlow q t (x + s')) (deriv (fun u => heatFlow q t u) (x + s)) s := by
  have hinner : HasDerivAt (fun s' : ℝ => x + s') 1 s := (hasDerivAt_id s).const_add x
  have hd := ((heatFlow_derivs q hqb).1 t ht (x + s)).comp s hinner
  simpa only [Function.comp_def, one_mul, mul_one] using hd

lemma heatFlow_shift_hasDerivAt_deriv {q : ℝ → ℝ} (hqb : ∀ x, |q x| ≤ 1) {t : ℝ} (ht : 0 < t)
    (x s : ℝ) :
    HasDerivAt (fun s' : ℝ => deriv (fun u => heatFlow q t u) (x + s'))
      (deriv (fun u => deriv (fun u' => heatFlow q t u') u) (x + s)) s := by
  have hinner : HasDerivAt (fun s' : ℝ => x + s') 1 s := (hasDerivAt_id s).const_add x
  have hd := ((heatFlow_derivs q hqb).2.2 t ht (x + s)).comp s hinner
  simpa only [Function.comp_def, one_mul, mul_one] using hd

lemma U_shift_hasDerivAt {q : ℝ → ℝ} {η : ℝ} (h : IsAdm q η) {t : ℝ} (ht : 0 < t)
    (x s : ℝ) :
    HasDerivAt (fun s' : ℝ => U q t (x + s'))
      (gphiD (U q t (x + s)) * deriv (fun u => heatFlow q t u) (x + s)) s := by
  have hinner : HasDerivAt (fun s' : ℝ => x + s') 1 s := (hasDerivAt_id s).const_add x
  have hd := (U_hasDerivAt_x' h ht (x + s)).comp s hinner
  simpa only [Function.comp_def, one_mul, mul_one] using hd

lemma gphiD_U_shift_hasDerivAt {q : ℝ → ℝ} {η : ℝ} (h : IsAdm q η) {t : ℝ} (ht : 0 < t)
    (x s : ℝ) :
    HasDerivAt (fun s' : ℝ => gphiD (U q t (x + s')))
      (gphiD2 (U q t (x + s)) * deriv (fun u => heatFlow q t u) (x + s)) s := by
  have hinner : HasDerivAt (fun s' : ℝ => x + s') 1 s := (hasDerivAt_id s).const_add x
  have hmem := h.mem t (x + s)
  have hd := (hasDerivAt_gphiD_gphi (heatFlow q t (x + s)) hmem.1 hmem.2).comp (x + s)
    ((heatFlow_derivs q h.abs_le).1 t ht (x + s))
  have hd2 := hd.comp s hinner
  simpa only [Function.comp_def, U, one_mul, mul_one] using hd2

lemma gphiD_U_shift_mul_hasDerivAt {q : ℝ → ℝ} {η : ℝ} (h : IsAdm q η) {t : ℝ} (ht : 0 < t)
    (x s : ℝ) :
    HasDerivAt (fun s' : ℝ => gphiD (U q t (x + s')) * deriv (fun u => heatFlow q t u) (x + s'))
      (gphiD2 (U q t (x + s)) * (deriv (fun u => heatFlow q t u) (x + s)) ^ 2
        + gphiD (U q t (x + s))
          * deriv (fun u => deriv (fun u' => heatFlow q t u') u) (x + s)) s := by
  have h := (gphiD_U_shift_hasDerivAt h ht x s).mul (heatFlow_shift_hasDerivAt_deriv h.abs_le ht x s)
  have hv : gphiD2 (U q t (x + s)) * deriv (fun u => heatFlow q t u) (x + s)
        * deriv (fun u => heatFlow q t u) (x + s)
      + gphiD (U q t (x + s)) * deriv (fun u => deriv (fun u' => heatFlow q t u') u) (x + s)
      = gphiD2 (U q t (x + s)) * (deriv (fun u => heatFlow q t u) (x + s)) ^ 2
      + gphiD (U q t (x + s)) * deriv (fun u => deriv (fun u' => heatFlow q t u') u) (x + s) := by
    ring
  rw [hv] at h
  exact h

lemma gphiD2_U_eq {q : ℝ → ℝ} (t ξ : ℝ) :
    gphiD2 (U q t ξ) = 2 * Real.pi * U q t ξ * (gphiD (U q t ξ)) ^ 2 :=
  gphiD2_ratio _



/-! ### The derivative in time -/

lemma EhrV_hasDerivAt_t (lam : ℝ) {f g h : ℝ → ℝ} {ηf ηg : ℝ} (hf : IsAdm f ηf) (hg : IsAdm g ηg)
    (hb : ∀ x, |h x| ≤ 1) {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    HasDerivAt (fun u : ℝ => EhrV lam f g h u x y)
      (deriv (fun u : ℝ => heatFlow h u (lam * x + (1 - lam) * y)) t
        - gdens (Bmix lam f g t x y)
          * (lam * deriv (fun u : ℝ => U f u x) t
             + (1 - lam) * deriv (fun u : ℝ => U g u y) t)) t := by
  have hh' : HasDerivAt (fun u : ℝ => heatFlow h u (lam * x + (1 - lam) * y))
      (deriv (fun u : ℝ => heatFlow h u (lam * x + (1 - lam) * y)) t) t :=
    (heatFlow_derivs h hb).2.1 t ht (lam * x + (1 - lam) * y)
  have hf' : HasDerivAt (fun u : ℝ => U f u x) (deriv (fun u : ℝ => U f u x) t) t := by
    have h0 := U_hasDerivAt_t' hf ht x
    rwa [← U_deriv_t_eq' hf ht x] at h0
  have hg' : HasDerivAt (fun u : ℝ => U g u y) (deriv (fun u : ℝ => U g u y) t) t := by
    have h0 := U_hasDerivAt_t' hg ht y
    rwa [← U_deriv_t_eq' hg ht y] at h0
  have h2 : HasDerivAt (fun u : ℝ => lam * U f u x + (1 - lam) * U g u y)
      (lam * deriv (fun u : ℝ => U f u x) t + (1 - lam) * deriv (fun u : ℝ => U g u y) t) t :=
    (hf'.const_mul lam).add (hg'.const_mul (1 - lam))
  have hb2 : HasDerivAt (fun u : ℝ => Bmix lam f g u x y)
      (lam * deriv (fun u : ℝ => U f u x) t + (1 - lam) * deriv (fun u : ℝ => U g u y) t) t := by
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun u => ?_))
    simp only [Bmix, Pi.add_apply]
  have h3 : HasDerivAt (fun u : ℝ => gPhi (Bmix lam f g u x y))
      (gdens (Bmix lam f g t x y) * (lam * deriv (fun u : ℝ => U f u x) t
        + (1 - lam) * deriv (fun u : ℝ => U g u y) t)) t := by
    have hc := (gPhi_hasDerivAt (Bmix lam f g t x y)).comp t hb2
    simpa only [Function.comp_def] using hc
  refine (hh'.sub h3).congr_of_eventuallyEq (Filter.Eventually.of_forall (fun u => ?_))
  simp only [Pi.sub_apply, EhrV]

lemma heatFlow_time_deriv_eq {q : ℝ → ℝ} (hqb : ∀ x, |q x| ≤ 1) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    deriv (fun u : ℝ => heatFlow q u x) t
      = (1 / (4 * Real.pi)) * deriv (fun u => deriv (fun u' => heatFlow q t u') u) x := by
  have h := heatFlow_heat q hqb t ht x
  have h4 : (4 * Real.pi : ℝ) ≠ 0 := by positivity
  rw [h]
  field_simp

lemma EhrV_deriv_t_eq (lam : ℝ) {f g h : ℝ → ℝ} {ηf ηg : ℝ} (hf : IsAdm f ηf) (hg : IsAdm g ηg)
    (hb : ∀ x, |h x| ≤ 1) {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    deriv (fun u : ℝ => EhrV lam f g h u x y) t
      = (1 / (4 * Real.pi))
        * (deriv (fun u => deriv (fun u' => heatFlow h t u') u) (lam * x + (1 - lam) * y)
            - gdens (Bmix lam f g t x y)
              * (lam * (gphiD (U f t x) * deriv (fun u => deriv (fun u' => heatFlow f t u') u) x)
                + (1 - lam) * (gphiD (U g t y)
                  * deriv (fun u => deriv (fun u' => heatFlow g t u') u) y))) := by
  have h1 := (EhrV_hasDerivAt_t lam hf hg hb ht x y).deriv
  have h2 := U_deriv_t_eq' hf ht x
  have h3 := U_deriv_t_eq' hg ht y
  have h4 := heatFlow_time_deriv_eq hb ht (lam * x + (1 - lam) * y)
  have h5 := heatFlow_time_deriv_eq hf.abs_le ht x
  have h6 := heatFlow_time_deriv_eq hg.abs_le ht y
  rw [h1, h2, h3, h4, h5, h6]
  ring

/-! ### The derivative in space and the critical point relations -/

lemma EhrV_hasDerivAt_x (lam : ℝ) {f g h : ℝ → ℝ} {ηf ηg : ℝ} (hf : IsAdm f ηf) (hg : IsAdm g ηg)
    (hb : ∀ x, |h x| ≤ 1) {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    HasDerivAt (fun x' : ℝ => EhrV lam f g h t x' y)
      (lam * deriv (fun u => heatFlow h t u) (lam * x + (1 - lam) * y)
        - gdens (Bmix lam f g t x y)
          * (lam * (gphiD (U f t x) * deriv (fun u => heatFlow f t u) x))) x := by
  have h1 : HasDerivAt (fun x' : ℝ => heatFlow h t (lam * x' + (1 - lam) * y))
      (lam * deriv (fun u => heatFlow h t u) (lam * x + (1 - lam) * y)) x := by
    have h0 := (heatFlow_derivs h hb).1 t ht (lam * x + (1 - lam) * y)
    have hinner : HasDerivAt (fun x' : ℝ => lam * x' + (1 - lam) * y) lam x := by
      have h3 := (hasDerivAt_id x).const_mul lam
      simpa only [id_eq, one_mul, mul_one] using h3.add_const ((1 - lam) * y)
    have h4 := h0.comp x hinner
    have hv : deriv (fun u => heatFlow h t u) (lam * x + (1 - lam) * y) * lam
        = lam * deriv (fun u => heatFlow h t u) (lam * x + (1 - lam) * y) := by ring
    rw [hv] at h4
    simpa only [Function.comp_def] using h4
  have hf' : HasDerivAt (fun x' : ℝ => U f t x')
      (gphiD (U f t x) * deriv (fun u => heatFlow f t u) x) x :=
    U_hasDerivAt_x' hf ht x
  have h2 : HasDerivAt (fun x' : ℝ => lam * U f t x' + (1 - lam) * U g t y)
      (lam * (gphiD (U f t x) * deriv (fun u => heatFlow f t u) x)) x :=
    (hf'.const_mul lam).add_const ((1 - lam) * U g t y)
  have hb2 : HasDerivAt (fun x' : ℝ => Bmix lam f g t x' y)
      (lam * (gphiD (U f t x) * deriv (fun u => heatFlow f t u) x)) x := by
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun x' => ?_))
    simp only [Bmix, Pi.add_apply]
  have h3 : HasDerivAt (fun x' : ℝ => gPhi (Bmix lam f g t x' y))
      (gdens (Bmix lam f g t x y)
        * (lam * (gphiD (U f t x) * deriv (fun u => heatFlow f t u) x))) x := by
    have hc := (gPhi_hasDerivAt (Bmix lam f g t x y)).comp x hb2
    simpa only [Function.comp_def] using hc
  refine (h1.sub h3).congr_of_eventuallyEq (Filter.Eventually.of_forall (fun x' => ?_))
  simp only [Pi.sub_apply, EhrV]

lemma EhrV_hasDerivAt_y (lam : ℝ) {f g h : ℝ → ℝ} {ηf ηg : ℝ} (hf : IsAdm f ηf) (hg : IsAdm g ηg)
    (hb : ∀ x, |h x| ≤ 1) {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    HasDerivAt (fun y' : ℝ => EhrV lam f g h t x y')
      ((1 - lam) * deriv (fun u => heatFlow h t u) (lam * x + (1 - lam) * y)
        - gdens (Bmix lam f g t x y)
          * ((1 - lam) * (gphiD (U g t y) * deriv (fun u => heatFlow g t u) y))) y := by
  have h1 : HasDerivAt (fun y' : ℝ => heatFlow h t (lam * x + (1 - lam) * y'))
      ((1 - lam) * deriv (fun u => heatFlow h t u) (lam * x + (1 - lam) * y)) y := by
    have h0 := (heatFlow_derivs h hb).1 t ht (lam * x + (1 - lam) * y)
    have hinner : HasDerivAt (fun y' : ℝ => lam * x + (1 - lam) * y') (1 - lam) y := by
      have h3 := (hasDerivAt_id y).const_mul (1 - lam)
      simpa only [id_eq, one_mul, mul_one] using h3.const_add (lam * x)
    have h4 := h0.comp y hinner
    have hv : deriv (fun u => heatFlow h t u) (lam * x + (1 - lam) * y) * (1 - lam)
        = (1 - lam) * deriv (fun u => heatFlow h t u) (lam * x + (1 - lam) * y) := by ring
    rw [hv] at h4
    simpa only [Function.comp_def] using h4
  have hg' : HasDerivAt (fun y' : ℝ => U g t y')
      (gphiD (U g t y) * deriv (fun u => heatFlow g t u) y) y :=
    U_hasDerivAt_x' hg ht y
  have h2 : HasDerivAt (fun y' : ℝ => lam * U f t x + (1 - lam) * U g t y')
      ((1 - lam) * (gphiD (U g t y) * deriv (fun u => heatFlow g t u) y)) y :=
    (hg'.const_mul (1 - lam)).const_add (lam * U f t x)
  have hb2 : HasDerivAt (fun y' : ℝ => Bmix lam f g t x y')
      ((1 - lam) * (gphiD (U g t y) * deriv (fun u => heatFlow g t u) y)) y := by
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y' => ?_))
    simp only [Bmix, Pi.add_apply]
  have h3 : HasDerivAt (fun y' : ℝ => gPhi (Bmix lam f g t x y'))
      (gdens (Bmix lam f g t x y)
        * ((1 - lam) * (gphiD (U g t y) * deriv (fun u => heatFlow g t u) y))) y := by
    have hc := (gPhi_hasDerivAt (Bmix lam f g t x y)).comp y hb2
    simpa only [Function.comp_def] using hc
  refine (h1.sub h3).congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y' => ?_))
  simp only [Pi.sub_apply, EhrV]



/-! ### The second derivative of the diagonal slice -/

/-- The derivative of the diagonal slice `s ↦ EhrV lam f g h t (x+s) (y+s)`. -/
def SliceD (lam : ℝ) (f g h : ℝ → ℝ) (t x y : ℝ) : ℝ → ℝ :=
  fun s => deriv (fun u => heatFlow h t u) (lam * x + (1 - lam) * y + s)
    - gdens (Bmix lam f g t (x + s) (y + s))
      * (lam * (gphiD (U f t (x + s)) * deriv (fun u => heatFlow f t u) (x + s))
         + (1 - lam) * (gphiD (U g t (y + s)) * deriv (fun u => heatFlow g t u) (y + s)))

/-- The derivative of `s ↦ Bmix lam f g t (x+s) (y+s)`. -/
def BW (lam : ℝ) (f g : ℝ → ℝ) (t x y : ℝ) (s : ℝ) : ℝ :=
  lam * (gphiD (U f t (x + s)) * deriv (fun u => heatFlow f t u) (x + s))
    + (1 - lam) * (gphiD (U g t (y + s)) * deriv (fun u => heatFlow g t u) (y + s))

lemma Bmix_shift_hasDerivAt (lam : ℝ) {f g : ℝ → ℝ} {ηf ηg : ℝ} (hf : IsAdm f ηf)
    (hg : IsAdm g ηg) {t : ℝ} (ht : 0 < t) (x y s : ℝ) :
    HasDerivAt (fun s' : ℝ => Bmix lam f g t (x + s') (y + s')) (BW lam f g t x y s) s := by
  have h1 : HasDerivAt (fun s' : ℝ => lam * U f t (x + s'))
      (lam * (gphiD (U f t (x + s)) * deriv (fun u => heatFlow f t u) (x + s))) s :=
    (U_shift_hasDerivAt hf ht x s).const_mul lam
  have h2 : HasDerivAt (fun s' : ℝ => (1 - lam) * U g t (y + s'))
      ((1 - lam) * (gphiD (U g t (y + s)) * deriv (fun u => heatFlow g t u) (y + s))) s :=
    (U_shift_hasDerivAt hg ht y s).const_mul (1 - lam)
  have hc := h1.add h2
  refine hc.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s' => ?_))
  simp only [Bmix, BW, Pi.add_apply]

lemma BW_hasDerivAt (lam : ℝ) {f g : ℝ → ℝ} {ηf ηg : ℝ} (hf : IsAdm f ηf) (hg : IsAdm g ηg)
    {t : ℝ} (ht : 0 < t) (x y s : ℝ) :
    HasDerivAt (BW lam f g t x y)
      (lam * (gphiD2 (U f t (x + s)) * (deriv (fun u => heatFlow f t u) (x + s)) ^ 2
          + gphiD (U f t (x + s)) * deriv (fun u => deriv (fun u' => heatFlow f t u') u) (x + s))
        + (1 - lam) * (gphiD2 (U g t (y + s)) * (deriv (fun u => heatFlow g t u) (y + s)) ^ 2
          + gphiD (U g t (y + s))
            * deriv (fun u => deriv (fun u' => heatFlow g t u') u) (y + s))) s := by
  have hf1 : HasDerivAt (fun s' : ℝ =>
      lam * (gphiD (U f t (x + s')) * deriv (fun u => heatFlow f t u) (x + s')))
      (lam * (gphiD2 (U f t (x + s)) * (deriv (fun u => heatFlow f t u) (x + s)) ^ 2
        + gphiD (U f t (x + s))
          * deriv (fun u => deriv (fun u' => heatFlow f t u') u) (x + s))) s :=
    (gphiD_U_shift_mul_hasDerivAt hf ht x s).const_mul lam
  have hg1 : HasDerivAt (fun s' : ℝ =>
      (1 - lam) * (gphiD (U g t (y + s')) * deriv (fun u => heatFlow g t u) (y + s')))
      ((1 - lam) * (gphiD2 (U g t (y + s)) * (deriv (fun u => heatFlow g t u) (y + s)) ^ 2
        + gphiD (U g t (y + s))
          * deriv (fun u => deriv (fun u' => heatFlow g t u') u) (y + s))) s :=
    (gphiD_U_shift_mul_hasDerivAt hg ht y s).const_mul (1 - lam)
  have hc := hf1.add hg1
  refine hc.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s' => ?_))
  simp only [BW, Pi.add_apply]

lemma EhrV_slice_deriv (lam : ℝ) {f g h : ℝ → ℝ} {ηf ηg : ℝ} (hf : IsAdm f ηf) (hg : IsAdm g ηg)
    (hb : ∀ x, |h x| ≤ 1) {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    deriv (fun s : ℝ => EhrV lam f g h t (x + s) (y + s)) = SliceD lam f g h t x y := by
  funext s
  have h1 : HasDerivAt (fun s' : ℝ => heatFlow h t (lam * x + (1 - lam) * y + s'))
      (deriv (fun u => heatFlow h t u) (lam * x + (1 - lam) * y + s)) s :=
    heatFlow_shift_hasDerivAt hb ht (lam * x + (1 - lam) * y) s
  have hB := Bmix_shift_hasDerivAt lam hf hg ht x y s
  have h2 : HasDerivAt (fun s' : ℝ => gPhi (Bmix lam f g t (x + s') (y + s')))
      (gdens (Bmix lam f g t (x + s) (y + s)) * BW lam f g t x y s) s := by
    have hc := (gPhi_hasDerivAt (Bmix lam f g t (x + s) (y + s))).comp s hB
    simpa only [Function.comp_def] using hc
  have hfin : HasDerivAt (fun s' : ℝ => EhrV lam f g h t (x + s') (y + s'))
      (SliceD lam f g h t x y s) s := by
    refine (h1.sub h2).congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s' => ?_))
    simp only [Pi.sub_apply, EhrV, SliceD, BW]
    have harg : lam * (x + s') + (1 - lam) * (y + s') = lam * x + (1 - lam) * y + s' := by ring
    rw [harg]
  rw [hfin.deriv]

lemma SliceD_hasDerivAt (lam : ℝ) {f g h : ℝ → ℝ} {ηf ηg : ℝ} (hf : IsAdm f ηf)
    (hg : IsAdm g ηg) (hb : ∀ x, |h x| ≤ 1) {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    HasDerivAt (SliceD lam f g h t x y)
      (deriv (fun u => deriv (fun u' => heatFlow h t u') u) (lam * x + (1 - lam) * y)
        - gdens (Bmix lam f g t x y) * (-(2 * Real.pi * Bmix lam f g t x y))
            * (BW lam f g t x y 0) ^ 2
        - gdens (Bmix lam f g t x y)
            * (lam * (gphiD2 (U f t x) * (deriv (fun u => heatFlow f t u) x) ^ 2
                + gphiD (U f t x) * deriv (fun u => deriv (fun u' => heatFlow f t u') u) x)
              + (1 - lam) * (gphiD2 (U g t y) * (deriv (fun u => heatFlow g t u) y) ^ 2
                + gphiD (U g t y) * deriv (fun u => deriv (fun u' => heatFlow g t u') u) y))) 0 := by
  have hT1 : HasDerivAt (fun s : ℝ => deriv (fun u => heatFlow h t u) (lam * x + (1 - lam) * y + s))
      (deriv (fun u => deriv (fun u' => heatFlow h t u') u) (lam * x + (1 - lam) * y + 0)) 0 :=
    heatFlow_shift_hasDerivAt_deriv hb ht (lam * x + (1 - lam) * y) 0
  have hB0 := Bmix_shift_hasDerivAt lam hf hg ht x y 0
  have hgB : HasDerivAt (fun s : ℝ => gdens (Bmix lam f g t (x + s) (y + s)))
      (gdens (Bmix lam f g t (x + 0) (y + 0)) * (-(2 * Real.pi * Bmix lam f g t (x + 0) (y + 0)))
        * BW lam f g t x y 0) 0 := by
    have hc := (gdens_hasDerivAt (Bmix lam f g t (x + 0) (y + 0))).comp 0 hB0
    rw [Function.comp_def] at hc
    exact hc
  have hW := BW_hasDerivAt lam hf hg ht x y 0
  have hprod := hgB.mul hW
  have hfin : HasDerivAt (SliceD lam f g h t x y)
      (deriv (fun u => deriv (fun u' => heatFlow h t u') u) (lam * x + (1 - lam) * y + 0)
        - (gdens (Bmix lam f g t (x + 0) (y + 0)) * (-(2 * Real.pi * Bmix lam f g t (x + 0) (y + 0)))
              * BW lam f g t x y 0 * BW lam f g t x y 0
            + gdens (Bmix lam f g t (x + 0) (y + 0))
              * (lam * (gphiD2 (U f t (x + 0)) * (deriv (fun u => heatFlow f t u) (x + 0)) ^ 2
                  + gphiD (U f t (x + 0))
                    * deriv (fun u => deriv (fun u' => heatFlow f t u') u) (x + 0))
                + (1 - lam) * (gphiD2 (U g t (y + 0)) * (deriv (fun u => heatFlow g t u) (y + 0)) ^ 2
                  + gphiD (U g t (y + 0))
                    * deriv (fun u => deriv (fun u' => heatFlow g t u') u) (y + 0))))) 0 := by
    refine (hT1.sub hprod).congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s' => ?_))
    simp only [Pi.sub_apply, Pi.mul_apply, SliceD, BW]
  have hval : deriv (fun u => deriv (fun u' => heatFlow h t u') u) (lam * x + (1 - lam) * y + 0)
        - (gdens (Bmix lam f g t (x + 0) (y + 0)) * (-(2 * Real.pi * Bmix lam f g t (x + 0) (y + 0)))
              * BW lam f g t x y 0 * BW lam f g t x y 0
            + gdens (Bmix lam f g t (x + 0) (y + 0))
              * (lam * (gphiD2 (U f t (x + 0)) * (deriv (fun u => heatFlow f t u) (x + 0)) ^ 2
                  + gphiD (U f t (x + 0))
                    * deriv (fun u => deriv (fun u' => heatFlow f t u') u) (x + 0))
                + (1 - lam) * (gphiD2 (U g t (y + 0)) * (deriv (fun u => heatFlow g t u) (y + 0)) ^ 2
                  + gphiD (U g t (y + 0))
                    * deriv (fun u => deriv (fun u' => heatFlow g t u') u) (y + 0))))
      = deriv (fun u => deriv (fun u' => heatFlow h t u') u) (lam * x + (1 - lam) * y)
        - gdens (Bmix lam f g t x y) * (-(2 * Real.pi * Bmix lam f g t x y))
            * (BW lam f g t x y 0) ^ 2
        - gdens (Bmix lam f g t x y)
            * (lam * (gphiD2 (U f t x) * (deriv (fun u => heatFlow f t u) x) ^ 2
                + gphiD (U f t x) * deriv (fun u => deriv (fun u' => heatFlow f t u') u) x)
              + (1 - lam) * (gphiD2 (U g t y) * (deriv (fun u => heatFlow g t u) y) ^ 2
                + gphiD (U g t y) * deriv (fun u => deriv (fun u' => heatFlow g t u') u) y)) := by
    simp only [add_zero]
    ring
  rw [hval] at hfin
  exact hfin


/-! ### Limits of `gphi` at `0+` and the uniform spatial decay -/

lemma bddBelow_gphi_set {y : ℝ} (hy : 0 < y) : BddBelow {x : ℝ | y ≤ gPhi x} := by
  have h := (gPhi_tendsto_atBot.eventually (isOpen_Iio.mem_nhds (show (0 : ℝ) ∈ Set.Iio y from hy)))
  rw [eventually_atBot] at h
  obtain ⟨R, hR⟩ := h
  exact ⟨R, fun x hx => by
    by_contra hlt
    rw [not_le] at hlt
    exact absurd hx (not_le.mpr (hR x hlt.le))⟩

lemma gphi_le_of_lt {M y : ℝ} (hy0 : 0 < y) (hy : y < gPhi M) : gphi y ≤ M := by
  have h := csInf_le (bddBelow_gphi_set hy0) (le_of_lt hy)
  simpa only [gphi] using h

lemma tendsto_gphi_nhdsGT_zero_atBot :
    Tendsto gphi (𝓝[>] (0 : ℝ)) atBot := by
  rw [tendsto_atBot]
  intro M
  filter_upwards [show Set.Iio (gPhi M) ∈ 𝓝[>] (0 : ℝ) from
    Filter.mem_of_superset (Ioo_mem_nhdsGT (gPhi_pos M)) (fun x hx => hx.2),
    self_mem_nhdsWithin] with y hyM hy0
  exact gphi_le_of_lt hy0 hyM

/-- Reflection identity for the heat extension. -/
lemma heatFlow_neg {f : ℝ → ℝ} (hf : Measurable f) (t x : ℝ) :
    heatFlow (fun y => f (-y)) t (-x) = heatFlow f t x := by
  have hmap := MeasureTheory.Measure.map_neg_eq_self (volume : Measure ℝ)
  have h1 : heatFlow (fun y => f (-y)) t (-x)
      = ∫ z : ℝ, f (x - Real.sqrt t * z) * Real.exp (-Real.pi * z ^ 2) := by
    rw [heatFlow]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    show f (-(-x + Real.sqrt t * z)) * Real.exp (-Real.pi * z ^ 2)
      = f (x - Real.sqrt t * z) * Real.exp (-Real.pi * z ^ 2)
    rw [show -(-x + Real.sqrt t * z) = x - Real.sqrt t * z from by ring]
  have h2 : heatFlow f t x
      = ∫ z : ℝ, f (x - Real.sqrt t * z) * Real.exp (-Real.pi * z ^ 2) := by
    rw [heatFlow]
    have key := MeasureTheory.integral_map (μ := volume) (φ := fun z : ℝ => -z)
      measurable_neg.aemeasurable
      (f := fun z : ℝ => f (x + Real.sqrt t * z) * Real.exp (-Real.pi * z ^ 2)) (by
        rw [hmap]
        exact ((hf.comp (measurable_const.add (measurable_const.mul measurable_id))).mul
          gauss_cont_aux.measurable).aestronglyMeasurable)
    rw [hmap] at key
    rw [key]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    show f (x + Real.sqrt t * -z) * Real.exp (-Real.pi * (-z) ^ 2)
      = f (x - Real.sqrt t * z) * Real.exp (-Real.pi * z ^ 2)
    have hz : x + Real.sqrt t * -z = x - Real.sqrt t * z := by ring
    have he : Real.exp (-Real.pi * (-z) ^ 2) = Real.exp (-Real.pi * z ^ 2) := by
      congr 1; ring
    rw [hz, he]
  rw [h1, h2]

/-- Uniform decay of the heat extension for `x → -∞`. -/
lemma heatExtension_zero_uniform_atBot {f : ℝ → ℝ} (hf0 : ∀ x, |f x| ≤ 1) (hfm : Measurable f)
    (hfinf : ∀ ε > 0, ∃ R : ℝ, ∀ x, R ≤ |x| → |f x| ≤ ε) :
    ∀ T > 0, ∀ ε > 0, ∃ R : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : ℝ, x ≤ -R →
      |∫ z : ℝ, f (x + Real.sqrt t * z) * Real.exp (-Real.pi * z ^ 2)| ≤ ε := by
  intro T hT ε hε
  obtain ⟨R, hR⟩ := heatExtension_zero_uniform_atTop (fun x => f (-x))
    (fun x => by simpa only [abs_neg] using hf0 (-x)) (fun ε hε => by
      obtain ⟨R, hR⟩ := hfinf ε hε
      exact ⟨R, fun x hx => hR (-x) (by rw [abs_neg]; exact hx)⟩) T hT ε hε
  refine ⟨R, fun t ht x hx => ?_⟩
  have h := hR t ht (-x) (by linarith)
  have h' : |heatFlow (fun y => f (-y)) t (-x)| ≤ ε := by simpa only [heatFlow] using h
  rwa [heatFlow_neg hfm t x] at h'


/-! ### Continuity of the test function on the half space `t ≥ 0` -/

lemma EhrV_continuousOn (lam : ℝ) {f g h : ℝ → ℝ} {ηf ηg : ℝ} (hf : IsAdm f ηf)
    (hg : IsAdm g ηg) (hfc : Continuous f) (hgc : Continuous g) (hhc : Continuous h)
    (hb : ∀ x, |h x| ≤ 1) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => EhrV lam f g h p.2.2 p.1 p.2.1)
      {p : ℝ × ℝ × ℝ | 0 ≤ p.2.2} := by
  have h1 : ContinuousOn
      (fun p : ℝ × ℝ × ℝ => heatFlow h p.2.2 (lam * p.1 + (1 - lam) * p.2.1))
      {p : ℝ × ℝ × ℝ | 0 ≤ p.2.2} := by
    have hHF : ContinuousOn (fun q : ℝ × ℝ => heatFlow h q.1 q.2) {q : ℝ × ℝ | 0 ≤ q.1} := by
      simpa only [heatFlow] using heatFlow_continuousOn_nonneg h hhc hb
    have hm : Continuous
        (fun p : ℝ × ℝ × ℝ => ((p.2.2, lam * p.1 + (1 - lam) * p.2.1) : ℝ × ℝ)) := by fun_prop
    exact hHF.comp hm.continuousOn (fun p hp => by simpa using hp)
  have h2 : ContinuousOn (fun p : ℝ × ℝ × ℝ => Bmix lam f g p.2.2 p.1 p.2.1)
      {p : ℝ × ℝ × ℝ | 0 ≤ p.2.2} := by
    have hUf : ContinuousOn (fun p : ℝ × ℝ × ℝ => U f p.2.2 p.1) {p : ℝ × ℝ × ℝ | 0 ≤ p.2.2} :=
      (continuousOn_U' hf hfc).comp
        (by fun_prop : Continuous fun p : ℝ × ℝ × ℝ => ((p.2.2, p.1) : ℝ × ℝ)).continuousOn
        (fun p hp => by simpa using hp)
    have hUg : ContinuousOn (fun p : ℝ × ℝ × ℝ => U g p.2.2 p.2.1) {p : ℝ × ℝ × ℝ | 0 ≤ p.2.2} :=
      (continuousOn_U' hg hgc).comp
        (by fun_prop : Continuous fun p : ℝ × ℝ × ℝ => ((p.2.2, p.2.1) : ℝ × ℝ)).continuousOn
        (fun p hp => by simpa using hp)
    refine ContinuousOn.congr ((hUf.const_mul lam).add (hUg.const_mul (1 - lam)))
      (fun p hp => ?_)
    simp only [Bmix, Pi.add_apply]
  have h3 : ContinuousOn (fun p : ℝ × ℝ × ℝ => gPhi (Bmix lam f g p.2.2 p.1 p.2.1))
      {p : ℝ × ℝ × ℝ | 0 ≤ p.2.2} := gPhi_continuous.comp_continuousOn h2
  refine ContinuousOn.congr (h1.sub h3) (fun p hp => ?_)
  simp only [EhrV, Pi.sub_apply]

/-! ### The condition at infinity -/

/-- Given any bound `c` there is `ε ∈ (0,1)` with `gphi ε ≤ c`. -/
lemma exists_gphi_le (c : ℝ) : ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ gphi ε ≤ c := by
  have h1 : 0 < gPhi c := gPhi_pos c
  have h2 : gPhi c < 1 := gPhi_lt_one c
  exact ⟨gPhi c / 2, by linarith, by linarith, gphi_le_of_lt (by linarith) (by linarith)⟩

lemma IsAdm.eta_lt_one {q : ℝ → ℝ} {η : ℝ} (h : IsAdm q η) : η < 1 := by
  have h1 := h.2.2.1 0
  have h2 := h.2.1 0
  linarith

/-- Uniform-in-`t` smallness of the heat extension. -/
lemma heatFlow_uniform_small {q : ℝ → ℝ} {η : ℝ} (hq : IsAdm q η)
    (hqint : ∀ ε > 0, ∃ R : ℝ, ∀ x, R ≤ |x| → q x ≤ ε) :
    ∀ T > 0, ∀ ε > 0, ∃ R : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : ℝ, R ≤ |x| →
      heatFlow q t x ≤ ε := by
  intro T hT ε hε
  have hfinf : ∀ ε' > 0, ∃ R : ℝ, ∀ x, R ≤ |x| → |q x| ≤ ε' := by
    intro ε' hε'
    obtain ⟨R, hR⟩ := hqint ε' hε'
    exact ⟨R, fun x hx => by rw [abs_of_pos (hq.2.1 x)]; exact hR x hx⟩
  obtain ⟨R1, hR1⟩ := heatExtension_zero_uniform_atTop q hq.abs_le hfinf T hT ε hε
  obtain ⟨R2, hR2⟩ := heatExtension_zero_uniform_atBot hq.abs_le hq.1 hfinf T hT ε hε
  refine ⟨max R1 R2, fun t ht x hx => ?_⟩
  by_cases hx0 : 0 ≤ x
  · have hx' : R1 ≤ x := by
      have h1 : R1 ≤ |x| := le_trans (le_max_left _ _) hx
      rwa [abs_of_nonneg hx0] at h1
    exact le_trans (le_abs_self _) (hR1 t ht x hx')
  · have hx' : x ≤ -R2 := by
      have h1 : R2 ≤ |x| := le_trans (le_max_right _ _) hx
      rw [abs_of_neg (by linarith)] at h1
      linarith
    exact le_trans (le_abs_self _) (hR2 t ht x hx')

lemma EhrV_inf (lam : ℝ) (hl0 : 0 < lam) (hl1 : lam < 1) {f g h : ℝ → ℝ} {ηf ηg : ℝ}
    (hf : IsAdm f ηf) (hg : IsAdm g ηg) (hh0 : ∀ x, 0 ≤ h x) (hb : ∀ x, |h x| ≤ 1)
    (hhm : Measurable h)
    (hfint : ∀ ε > 0, ∃ R : ℝ, ∀ x, R ≤ |x| → f x ≤ ε)
    (hgint : ∀ ε > 0, ∃ R : ℝ, ∀ x, R ≤ |x| → g x ≤ ε)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {T : ℝ} (hT : 0 < T) :
    ∃ R : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x y : ℝ, R ≤ |x| + |y| →
      -δ ≤ EhrV lam f g h t x y := by
  obtain ⟨ε1, hε1a, hε1b, hε1c⟩ :=
    exists_gphi_le ((gphi δ - (1 - lam) * gphi (1 - ηg)) / lam)
  obtain ⟨ε2, hε2a, hε2b, hε2c⟩ :=
    exists_gphi_le ((gphi δ - lam * gphi (1 - ηf)) / (1 - lam))
  have hbound1 : lam * gphi ε1 + (1 - lam) * gphi (1 - ηg) ≤ gphi δ := by
    have h := mul_le_mul_of_nonneg_left hε1c hl0.le
    have h2 : lam * ((gphi δ - (1 - lam) * gphi (1 - ηg)) / lam)
        = gphi δ - (1 - lam) * gphi (1 - ηg) :=
      mul_div_cancel₀ _ (ne_of_gt hl0)
    rw [h2] at h
    linarith
  have hbound2 : lam * gphi (1 - ηf) + (1 - lam) * gphi ε2 ≤ gphi δ := by
    have h := mul_le_mul_of_nonneg_left hε2c (by linarith : (0 : ℝ) ≤ 1 - lam)
    have h2 : (1 - lam) * ((gphi δ - lam * gphi (1 - ηf)) / (1 - lam))
        = gphi δ - lam * gphi (1 - ηf) :=
      mul_div_cancel₀ _ (ne_of_gt (by linarith : (0 : ℝ) < 1 - lam))
    rw [h2] at h
    linarith
  obtain ⟨Rf, hRf⟩ := heatFlow_uniform_small hf hfint T hT ε1 hε1a
  obtain ⟨Rg, hRg⟩ := heatFlow_uniform_small hg hgint T hT ε2 hε2a
  refine ⟨2 * max Rf Rg, fun t ht x y hxy => ?_⟩
  have hspec : gPhi (gphi δ) = δ := gphi_spec δ hδ0 hδ1
  have hmem1 : heatFlow f t x ∈ Set.Ioo (0 : ℝ) 1 := hf.mem t x
  have hmem2 : heatFlow g t y ∈ Set.Ioo (0 : ℝ) 1 := hg.mem t y
  have hηf : 1 - ηf ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hf.eta_lt_one], by linarith [hf.2.2.2]⟩
  have hηg : 1 - ηg ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hg.eta_lt_one], by linarith [hg.2.2.2]⟩
  have hgf1 : heatFlow f t x ≤ 1 - ηf := (heatFlow_bounds f (fun z => (hf.2.1 z).le) hf.2.2.1 hf.1 t x).2
  have hgg1 : heatFlow g t y ≤ 1 - ηg := (heatFlow_bounds g (fun z => (hg.2.1 z).le) hg.2.2.1 hg.1 t y).2
  have hG : gPhi (Bmix lam f g t x y) ≤ δ := by
    have hB : Bmix lam f g t x y
        = lam * gphi (heatFlow f t x) + (1 - lam) * gphi (heatFlow g t y) := rfl
    rw [hB, ← hspec]
    refine gPhi_strictMono.monotone ?_
    by_cases hx : max Rf Rg ≤ |x|
    · have h1 : gphi (heatFlow f t x) ≤ gphi ε1 :=
        gphi_strictMonoOn.monotoneOn hmem1 ⟨hε1a, hε1b⟩
          (hRf t ht x (le_trans (le_max_left _ _) hx))
      have h2 : gphi (heatFlow g t y) ≤ gphi (1 - ηg) :=
        gphi_strictMonoOn.monotoneOn hmem2 hηg hgg1
      have h1' := mul_le_mul_of_nonneg_left h1 hl0.le
      have h2' := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 1 - lam)
      linarith
    · have hy : max Rf Rg ≤ |y| := by
        push_neg at hx
        by_contra hcon
        push_neg at hcon
        linarith
      have h1 : gphi (heatFlow f t x) ≤ gphi (1 - ηf) :=
        gphi_strictMonoOn.monotoneOn hmem1 hηf hgf1
      have h2 : gphi (heatFlow g t y) ≤ gphi ε2 :=
        gphi_strictMonoOn.monotoneOn hmem2 ⟨hε2a, hε2b⟩
          (hRg t ht y (le_trans (le_max_right _ _) hy))
      have h1' := mul_le_mul_of_nonneg_left h1 hl0.le
      have h2' := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 1 - lam)
      linarith
  have hnn : 0 ≤ heatFlow h t (lam * x + (1 - lam) * y) :=
    (heatFlow_bounds h (fun z => hh0 z) (fun z => (abs_le.mp (hb z)).2) hhm t
      (lam * x + (1 - lam) * y)).1
  have hE : EhrV lam f g h t x y = heatFlow h t (lam * x + (1 - lam) * y)
      - gPhi (Bmix lam f g t x y) := rfl
  rw [hE]
  linarith


/-! ### The hill property and the continuous case -/

lemma EhrV_deriv_x_eq (lam : ℝ) {f g h : ℝ → ℝ} {ηf ηg : ℝ} (hf : IsAdm f ηf)
    (hg : IsAdm g ηg) (hb : ∀ x, |h x| ≤ 1) {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    deriv (fun x' : ℝ => EhrV lam f g h t x' y) x
      = lam * (deriv (fun u => heatFlow h t u) (lam * x + (1 - lam) * y)
          - gdens (Bmix lam f g t x y)
            * (gphiD (U f t x) * deriv (fun u => heatFlow f t u) x)) := by
  rw [(EhrV_hasDerivAt_x lam hf hg hb ht x y).deriv]; ring

lemma EhrV_deriv_y_eq (lam : ℝ) {f g h : ℝ → ℝ} {ηf ηg : ℝ} (hf : IsAdm f ηf)
    (hg : IsAdm g ηg) (hb : ∀ x, |h x| ≤ 1) {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    deriv (fun y' : ℝ => EhrV lam f g h t x y') y
      = (1 - lam) * (deriv (fun u => heatFlow h t u) (lam * x + (1 - lam) * y)
          - gdens (Bmix lam f g t x y)
            * (gphiD (U g t y) * deriv (fun u => heatFlow g t u) y)) := by
  rw [(EhrV_hasDerivAt_y lam hf hg hb ht x y).deriv]; ring

lemma EhrV_slice_second (lam : ℝ) {f g h : ℝ → ℝ} {ηf ηg : ℝ} (hf : IsAdm f ηf)
    (hg : IsAdm g ηg) (hb : ∀ x, |h x| ≤ 1) {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    deriv (deriv (fun s : ℝ => EhrV lam f g h t (x + s) (y + s))) 0
      = deriv (SliceD lam f g h t x y) 0 := by
  rw [EhrV_slice_deriv lam hf hg hb ht x y]

lemma EhrV_slice_second_eq (lam : ℝ) (hl0 : 0 < lam) (hl1 : lam < 1)
    {f g h : ℝ → ℝ} {ηf ηg : ℝ} (hf : IsAdm f ηf) (hg : IsAdm g ηg)
    (hb : ∀ x, |h x| ≤ 1) {t : ℝ} (ht : 0 < t) (x y : ℝ)
    (hcx : deriv (fun x' : ℝ => EhrV lam f g h t x' y) x = 0)
    (hcy : deriv (fun y' : ℝ => EhrV lam f g h t x y') y = 0) :
    deriv (deriv (fun s : ℝ => EhrV lam f g h t (x + s) (y + s))) 0
      = 4 * Real.pi * deriv (fun u : ℝ => EhrV lam f g h u x y) t := by
  rw [EhrV_slice_second lam hf hg hb ht x y, (SliceD_hasDerivAt lam hf hg hb ht x y).deriv,
    EhrV_deriv_t_eq lam hf hg hb ht x y]
  have hcx' := hcx
  rw [EhrV_deriv_x_eq lam hf hg hb ht x y] at hcx'
  have hcy' := hcy
  rw [EhrV_deriv_y_eq lam hf hg hb ht x y] at hcy'
  have hG : 0 < gdens (Bmix lam f g t x y) := gdens_pos _
  have hk1 : deriv (fun u => heatFlow h t u) (lam * x + (1 - lam) * y)
      = gdens (Bmix lam f g t x y)
        * (gphiD (U f t x) * deriv (fun u => heatFlow f t u) x) := by
    rw [mul_eq_zero] at hcx'
    rcases hcx' with h | h
    · exact absurd h (ne_of_gt hl0)
    · linarith
  have hk2 : deriv (fun u => heatFlow h t u) (lam * x + (1 - lam) * y)
      = gdens (Bmix lam f g t x y)
        * (gphiD (U g t y) * deriv (fun u => heatFlow g t u) y) := by
    rw [mul_eq_zero] at hcy'
    rcases hcy' with h | h
    · exact absurd h (ne_of_gt (by linarith : (0 : ℝ) < 1 - lam))
    · linarith
  have hpq : gphiD (U f t x) * deriv (fun u => heatFlow f t u) x
      = gphiD (U g t y) * deriv (fun u => heatFlow g t u) y :=
    mul_left_cancel₀ (ne_of_gt hG) (hk1.symm.trans hk2)
  have hkey1 : gphiD2 (U f t x) * (deriv (fun u => heatFlow f t u) x) ^ 2
      = 2 * Real.pi * U f t x * (gphiD (U f t x) * deriv (fun u => heatFlow f t u) x) ^ 2 := by
    rw [gphiD2_ratio]; ring
  have hkey2 : gphiD2 (U g t y) * (deriv (fun u => heatFlow g t u) y) ^ 2
      = 2 * Real.pi * U g t y * (gphiD (U g t y) * deriv (fun u => heatFlow g t u) y) ^ 2 := by
    rw [gphiD2_ratio]; ring
  have hBW : BW lam f g t x y 0
      = lam * (gphiD (U f t x) * deriv (fun u => heatFlow f t u) x)
        + (1 - lam) * (gphiD (U g t y) * deriv (fun u => heatFlow g t u) y) := by
    simp only [BW, add_zero]
  have hB : Bmix lam f g t x y = lam * U f t x + (1 - lam) * U g t y := rfl
  rw [hkey1, hkey2, hBW, hpq, hB]
  have h4 : (4 * Real.pi) * (1 / (4 * Real.pi)) = 1 := by
    rw [one_div, mul_inv_cancel₀ (by positivity : (4 : ℝ) * Real.pi ≠ 0)]
  conv_rhs => rw [← mul_assoc, h4]
  rw [one_mul]
  have harg : lam * x + (1 - lam) * y = lam * x - lam * y + y := by ring
  rw [harg]
  ring

lemma EhrV_hill (lam : ℝ) (hl0 : 0 < lam) (hl1 : lam < 1) {f g h : ℝ → ℝ} {ηf ηg : ℝ}
    (hf : IsAdm f ηf) (hg : IsAdm g ηg) (hb : ∀ x, |h x| ≤ 1) :
    ∀ t x y, 0 < t → IsLocalMin (fun p : ℝ × ℝ => EhrV lam f g h t p.1 p.2) (x, y) →
      deriv (deriv (fun s : ℝ => EhrV lam f g h t (x + s) (y + s))) 0
        ≤ 4 * Real.pi * deriv (fun u : ℝ => EhrV lam f g h u x y) t := by
  intro t x y ht hmin
  have hminx : IsLocalMin (fun x' : ℝ => EhrV lam f g h t x' y) x :=
    hmin.comp_continuous (g := fun x' : ℝ => (x', y))
      (by fun_prop : ContinuousAt (fun x' : ℝ => (x', y)) x)
  have hminy : IsLocalMin (fun y' : ℝ => EhrV lam f g h t x y') y :=
    hmin.comp_continuous (g := fun y' : ℝ => (x, y'))
      (by fun_prop : ContinuousAt (fun y' : ℝ => (x, y')) y)
  rw [EhrV_slice_second_eq lam hl0 hl1 hf hg hb ht x y hminx.deriv_eq_zero hminy.deriv_eq_zero]

/-! ### The continuous case of the functional Ehrhard inequality -/

lemma EhrV_nonneg (lam : ℝ) (hl0 : 0 < lam) (hl1 : lam < 1) {f g h : ℝ → ℝ} {ηf ηg : ℝ}
    (hf : IsAdm f ηf) (hg : IsAdm g ηg) (hfc : Continuous f) (hgc : Continuous g)
    (hhc : Continuous h) (hh0 : ∀ x, 0 ≤ h x) (hb : ∀ x, |h x| ≤ 1)
    (hfint : ∀ ε > 0, ∃ R : ℝ, ∀ x, R ≤ |x| → f x ≤ ε)
    (hgint : ∀ ε > 0, ∃ R : ℝ, ∀ x, R ≤ |x| → g x ≤ ε)
    (hHP : ∀ x y, gPhi (lam * gphi (f x) + (1 - lam) * gphi (g y))
      ≤ h (lam * x + (1 - lam) * y)) :
    ∀ x y t : ℝ, 0 ≤ t → 0 ≤ EhrV lam f g h t x y := by
  have hhm : Measurable h := hhc.measurable
  have h0 : ∀ x y : ℝ, 0 ≤ EhrV lam f g h 0 x y := by
    intro x y
    rw [EhrV_zero]
    linarith [hHP x y]
  have hinf : ∀ δ > 0, ∀ T > 0, ∃ R : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x y : ℝ,
      R ≤ |x| + |y| → -δ ≤ EhrV lam f g h t x y := by
    intro δ hδ0 T hT
    by_cases h1 : 1 ≤ δ
    · refine ⟨0, fun t ht x y _ => ?_⟩
      have hle : EhrV lam f g h t x y ≥ -gPhi (Bmix lam f g t x y) := by
        have hnn : 0 ≤ heatFlow h t (lam * x + (1 - lam) * y) :=
          (heatFlow_bounds h hh0 (fun z => (abs_le.mp (hb z)).2) hhm t
            (lam * x + (1 - lam) * y)).1
        have hE : EhrV lam f g h t x y = heatFlow h t (lam * x + (1 - lam) * y)
            - gPhi (Bmix lam f g t x y) := rfl
        rw [hE]; linarith
      have hg1 : gPhi (Bmix lam f g t x y) ≤ 1 := (gPhi_lt_one _).le
      linarith
    · exact EhrV_inf lam hl0 hl1 hf hg hh0 hb hhm hfint hgint hδ0 (not_le.mp h1) hT
  have hderivt : ∀ x y t : ℝ, 0 < t → HasDerivAt
      (fun u : ℝ => EhrV lam f g h u x y) (deriv (fun u : ℝ => EhrV lam f g h u x y) t) t := by
    intro x y t ht
    have h := EhrV_hasDerivAt_t lam hf hg hb ht x y
    rw [h.deriv]
    exact h
  exact Commons.Analysis.Calculus.parabolic_min_principle_diagonal (fun p : ℝ × ℝ × ℝ => EhrV lam f g h p.2.2 p.1 p.2.1)
    (EhrV_continuousOn lam hf hg hfc hgc hhc hb) h0 hinf hderivt
    (EhrV_hill lam hl0 hl1 hf hg hb)

lemma integrable_mul_gauss {q : ℝ → ℝ} (hqm : Measurable q) (hqb : ∀ x, |q x| ≤ 1) :
    Integrable (fun y : ℝ => q y * Real.exp (-Real.pi * y ^ 2)) := by
  refine Integrable.mono' integrable_gauss ?_ ?_
  · exact (hqm.mul gauss_cont_aux.measurable).aestronglyMeasurable
  · filter_upwards with y
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (Real.exp_pos _).le (hqb y)

lemma ehrhard_continuous (lam : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) {f g h : ℝ → ℝ}
    {ηf ηg : ℝ} (hf : IsAdm f ηf) (hg : IsAdm g ηg) (hfc : Continuous f) (hgc : Continuous g)
    (hhc : Continuous h) (hh0 : ∀ x, 0 ≤ h x) (hb : ∀ x, |h x| ≤ 1)
    (hfint : ∀ ε > 0, ∃ R : ℝ, ∀ x, R ≤ |x| → f x ≤ ε)
    (hgint : ∀ ε > 0, ∃ R : ℝ, ∀ x, R ≤ |x| → g x ≤ ε)
    (hHP : ∀ x y, gPhi (lam * gphi (f x) + (1 - lam) * gphi (g y))
      ≤ h (lam * x + (1 - lam) * y)) :
    gPhi (lam * gphi (∫ x, f x * Real.exp (-Real.pi * x ^ 2))
        + (1 - lam) * gphi (∫ x, g x * Real.exp (-Real.pi * x ^ 2)))
      ≤ ∫ x, h x * Real.exp (-Real.pi * x ^ 2) := by
  have hfm : Measurable f := hfc.measurable
  have hgm : Measurable g := hgc.measurable
  have hhm : Measurable h := hhc.measurable
  have hfg : ∀ x, |f x| ≤ 1 := hf.abs_le
  have hgg : ∀ x, |g x| ≤ 1 := hg.abs_le
  have hfA : heatFlow f 1 0 = ∫ x, f x * Real.exp (-Real.pi * x ^ 2) := by
    simp only [heatFlow, Real.sqrt_one, zero_mul, add_zero, one_mul, zero_add]
  have hgA : heatFlow g 1 0 = ∫ x, g x * Real.exp (-Real.pi * x ^ 2) := by
    simp only [heatFlow, Real.sqrt_one, zero_mul, add_zero, one_mul, zero_add]
  have hA0 : 0 < ∫ x, f x * Real.exp (-Real.pi * x ^ 2) := by
    rw [← hfA]; exact heatFlow_pos hfm hf.2.1 hfg 1 0
  have hA1 : ∫ x, f x * Real.exp (-Real.pi * x ^ 2) < 1 := by
    rw [← hfA]; exact heatFlow_lt_one hfm hfg hf.2.2.1 hf.2.2.2 1 0
  have hB0 : 0 < ∫ x, g x * Real.exp (-Real.pi * x ^ 2) := by
    rw [← hgA]; exact heatFlow_pos hgm hg.2.1 hgg 1 0
  have hB1 : ∫ x, g x * Real.exp (-Real.pi * x ^ 2) < 1 := by
    rw [← hgA]; exact heatFlow_lt_one hgm hgg hg.2.2.1 hg.2.2.2 1 0
  rcases eq_or_lt_of_le hl0 with h0 | h0
  · subst h0
    have hle : ∀ y, g y ≤ h y := by
      intro y
      have h1 := hHP 0 y
      simp only [zero_mul, zero_add, one_mul, add_zero, sub_zero] at h1
      rwa [gphi_spec (g y) (hg.2.1 y) (by linarith [hg.2.2.1 y, hg.2.2.2])] at h1
    have hmono : (∫ y, g y * Real.exp (-Real.pi * y ^ 2))
        ≤ ∫ y, h y * Real.exp (-Real.pi * y ^ 2) :=
      integral_mono (integrable_mul_gauss hgm hgg) (integrable_mul_gauss hhm hb)
        (fun y => mul_le_mul_of_nonneg_right (hle y) (Real.exp_pos _).le)
    have hspec : gPhi (gphi (∫ x, g x * Real.exp (-Real.pi * x ^ 2)))
        = ∫ x, g x * Real.exp (-Real.pi * x ^ 2) :=
      gphi_spec _ hB0 hB1
    simp only [zero_mul, zero_add, one_mul, sub_zero]
    rw [hspec]
    exact hmono
  · rcases eq_or_lt_of_le hl1 with h1 | h1
    · subst h1
      have hle : ∀ x, f x ≤ h x := by
        intro x
        have h1 := hHP x 0
        simp only [one_mul, mul_zero, zero_mul, add_zero, zero_add, sub_zero, sub_self] at h1
        rwa [gphi_spec (f x) (hf.2.1 x) (by linarith [hf.2.2.1 x, hf.2.2.2])] at h1
      have hmono : (∫ x, f x * Real.exp (-Real.pi * x ^ 2))
          ≤ ∫ x, h x * Real.exp (-Real.pi * x ^ 2) :=
        integral_mono (integrable_mul_gauss hfm hfg) (integrable_mul_gauss hhm hb)
          (fun x => mul_le_mul_of_nonneg_right (hle x) (Real.exp_pos _).le)
      have hspec : gPhi (gphi (∫ x, f x * Real.exp (-Real.pi * x ^ 2)))
          = ∫ x, f x * Real.exp (-Real.pi * x ^ 2) :=
        gphi_spec _ hA0 hA1
      simp only [one_mul, mul_zero, zero_mul, add_zero, zero_add, sub_zero, sub_self]
      rw [hspec]
      exact hmono
    · have hV := EhrV_nonneg lam h0 h1 hf hg hfc hgc hhc hh0 hb hfint hgint hHP 0 0 1
        (by norm_num)
      have hEq : EhrV lam f g h 1 0 0 = heatFlow h 1 0
          - gPhi (lam * gphi (heatFlow f 1 0) + (1 - lam) * gphi (heatFlow g 1 0)) := by
        simp only [EhrV, Bmix, U, mul_zero, add_zero]
      have hhh : heatFlow h 1 0 = ∫ x, h x * Real.exp (-Real.pi * x ^ 2) := by
        simp only [heatFlow, Real.sqrt_one, zero_mul, add_zero, one_mul, zero_add]
      rw [hEq, hfA, hgA, hhh] at hV
      linarith


/-! ### From the distribution-function hypothesis to the pointwise hypothesis -/

lemma hp_of_hcond (lam : ℝ) {f g h : ℝ → ℝ} (hh0 : ∀ x, 0 ≤ h x)
    (hcond : ∀ a b s t, gPhi a ≤ f s → gPhi b ≤ g t →
      gPhi (lam * a + (1 - lam) * b) ≤ h (lam * s + (1 - lam) * t)) :
    ∀ x y, 0 < f x → f x < 1 → 0 < g y → g y < 1 →
      gPhi (lam * gphi (f x) + (1 - lam) * gphi (g y)) ≤ h (lam * x + (1 - lam) * y) := by
  intro x y hfx0 hfx1 hgy0 hgy1
  exact hcond (gphi (f x)) (gphi (g y)) x y
    (le_of_eq (gphi_spec (f x) hfx0 hfx1)) (le_of_eq (gphi_spec (g y) hgy0 hgy1))
/-! ## Moreau / sup-convolution envelopes -/

/-- The potential `sup_{y : ψ y > 0} (gphi (ψ y) - |x - y| / s)`. -/
def moreauF (ψ : ℝ → ℝ) (s x : ℝ) : ℝ :=
  sSup ((fun y : ℝ => gphi (ψ y) - |x - y| / s) '' {y : ℝ | 0 < ψ y})

/-- The Moreau envelope of `ψ` at scale `s`, valued in `(0,1)`. -/
def moreau (ψ : ℝ → ℝ) (s x : ℝ) : ℝ := gPhi (moreauF ψ s x)

lemma moreau_eq (ψ : ℝ → ℝ) (s x : ℝ) :
    moreau ψ s x = gPhi (moreauF ψ s x) := rfl

lemma gphi_moreau (ψ : ℝ → ℝ) (s x : ℝ) : gphi (moreau ψ s x) = moreauF ψ s x := by
  rw [moreau_eq, gphi_gPhi]

lemma moreauF_eq (ψ : ℝ → ℝ) (s x : ℝ) :
    moreauF ψ s x = sSup ((fun y : ℝ => gphi (ψ y) - |x - y| / s) '' {y : ℝ | 0 < ψ y}) := rfl

/-- Monotonicity of `gphi` on `(0,1)`. -/
lemma gphi_le_of_le {a b : ℝ} (ha0 : 0 < a) (hb1 : b < 1) (hab : a ≤ b) : gphi a ≤ gphi b :=
  gphi_strictMonoOn.monotoneOn ⟨ha0, lt_of_le_of_lt hab hb1⟩ ⟨lt_of_lt_of_le ha0 hab, hb1⟩ hab

lemma bddAbove_gphi_image {ψ : ℝ → ℝ} {η : ℝ} (hη0 : 0 < η) (hη1 : ∀ x, ψ x ≤ 1 - η) :
    BddAbove ((fun y : ℝ => gphi (ψ y)) '' {y : ℝ | 0 < ψ y}) := by
  refine ⟨gphi (1 - η), ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact gphi_le_of_le hy (sub_lt_self 1 hη0) (hη1 y)

lemma bddAbove_moreauF {ψ : ℝ → ℝ} {η s : ℝ} (hs : 0 < s) (hη0 : 0 < η)
    (hη1 : ∀ x, ψ x ≤ 1 - η) (x : ℝ) :
    BddAbove ((fun y : ℝ => gphi (ψ y) - |x - y| / s) '' {y : ℝ | 0 < ψ y}) := by
  obtain ⟨M, hM⟩ := bddAbove_gphi_image hη0 hη1
  refine ⟨M, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have h1 : 0 ≤ |x - y| / s := div_nonneg (abs_nonneg _) hs.le
  linarith [hM ⟨y, hy, rfl⟩]

lemma moreauF_lipschitz {ψ : ℝ → ℝ} {s : ℝ} (hs : 0 < s)
    (hne : {y : ℝ | 0 < ψ y}.Nonempty)
    (hbd : BddAbove ((fun y : ℝ => gphi (ψ y)) '' {y : ℝ | 0 < ψ y})) :
    LipschitzWith ⟨s⁻¹, inv_nonneg.mpr hs.le⟩ (moreauF ψ s) :=
  Commons.Analysis.Convolution.lipschitzWith_sSup_sub_abs_div (fun y : ℝ => gphi (ψ y)) {y : ℝ | 0 < ψ y} s hs hne hbd

lemma moreauF_continuous {ψ : ℝ → ℝ} {s : ℝ} (hs : 0 < s)
    (hne : {y : ℝ | 0 < ψ y}.Nonempty)
    (hbd : BddAbove ((fun y : ℝ => gphi (ψ y)) '' {y : ℝ | 0 < ψ y})) :
    Continuous (moreauF ψ s) :=
  (moreauF_lipschitz hs hne hbd).continuous

lemma moreau_continuous {ψ : ℝ → ℝ} {s : ℝ} (hs : 0 < s)
    (hne : {y : ℝ | 0 < ψ y}.Nonempty)
    (hbd : BddAbove ((fun y : ℝ => gphi (ψ y)) '' {y : ℝ | 0 < ψ y})) :
    Continuous (moreau ψ s) :=
  gPhi_continuous.comp (moreauF_continuous hs hne hbd)

lemma moreau_pos (ψ : ℝ → ℝ) (s x : ℝ) : 0 < moreau ψ s x := by
  rw [moreau_eq]; exact gPhi_pos _

lemma moreau_le {ψ : ℝ → ℝ} {η s : ℝ} (hs : 0 < s) (hη0 : 0 < η) (hη1 : ∀ x, ψ x ≤ 1 - η)
    (hne : {y : ℝ | 0 < ψ y}.Nonempty) (x : ℝ) : moreau ψ s x ≤ 1 - η := by
  rw [moreau_eq]
  have h : moreauF ψ s x ≤ gphi (1 - η) := by
    rw [moreauF_eq]
    apply csSup_le (hne.image _)
    rintro _ ⟨y, hy, rfl⟩
    have h1 : 0 ≤ |x - y| / s := div_nonneg (abs_nonneg _) hs.le
    have h2 := gphi_le_of_le hy (sub_lt_self 1 hη0) (hη1 y)
    linarith
  have hy0' : ∃ y : ℝ, 0 < ψ y := hne
  obtain ⟨y0, hy0⟩ := hy0'
  have hηpos : 0 < 1 - η := lt_of_lt_of_le hy0 (hη1 y0)
  calc gPhi (moreauF ψ s x) ≤ gPhi (gphi (1 - η)) := gPhi_strictMono.monotone h
    _ = 1 - η := gphi_spec (1 - η) hηpos (by linarith)

lemma le_moreau {ψ : ℝ → ℝ} {η s : ℝ} (hs : 0 < s) (hη0 : 0 < η)
    (hη1 : ∀ x, ψ x ≤ 1 - η) (hψ0 : ∀ x, 0 ≤ ψ x) (x : ℝ) : ψ x ≤ moreau ψ s x := by
  rw [moreau_eq]
  rcases eq_or_lt_of_le (hψ0 x) with h0 | h0
  · rw [← h0]; exact (gPhi_pos _).le
  · have hmem : gphi (ψ x) ∈ ((fun y : ℝ => gphi (ψ y) - |x - y| / s) '' {y : ℝ | 0 < ψ y}) := by
      refine ⟨x, h0, ?_⟩; simp
    have hbdd := bddAbove_moreauF (ψ := ψ) hs hη0 hη1 x
    have hle : gphi (ψ x) ≤ moreauF ψ s x := le_csSup hbdd hmem
    calc ψ x = gPhi (gphi (ψ x)) := (gphi_spec (ψ x) h0 (by linarith [hη1 x])).symm
      _ ≤ gPhi (moreauF ψ s x) := gPhi_strictMono.monotone hle


/-- One-sided upper bound: if `c > ψ x` and `c < 1 - η`, then for small positive `s` the
Moreau envelope is `≤ c`. -/
lemma eventually_moreau_le {ψ : ℝ → ℝ} (hψ : UpperSemicontinuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    {η : ℝ} (hη0 : 0 < η) (hη1 : ∀ x, ψ x ≤ 1 - η)
    (hne : {y : ℝ | 0 < ψ y}.Nonempty) {x c : ℝ} (hxc : ψ x < c) (hc : c < 1 - η) :
    ∀ᶠ s in nhdsWithin (0:ℝ) (Set.Ioi 0), moreau ψ s x ≤ c := by
  have hc0 : 0 < c := lt_of_le_of_lt (hψ0 x) hxc
  have hc1 : c < 1 := lt_of_lt_of_le hc (by linarith)
  have hy0' : ∃ y : ℝ, 0 < ψ y := hne
  obtain ⟨y0, hy0⟩ := hy0'
  have hηpos : 0 < 1 - η := lt_of_lt_of_le hy0 (hη1 y0)
  have hstep : ψ x < (ψ x + c) / 2 := by linarith
  have hstep2 : (ψ x + c) / 2 < c := by linarith
  have hev := (upperSemicontinuousAt_iff.mp (hψ.upperSemicontinuousAt x)) ((ψ x + c) / 2) hstep
  obtain ⟨δ, hδ0, hδ⟩ := Metric.mem_nhds_iff.mp hev
  have hdiff : 0 < gphi (1 - η) - gphi c := by
    have hlt := (gphi_strictMonoOn.lt_iff_lt ⟨hc0, hc1⟩ ⟨hηpos, by linarith⟩).mpr hc
    linarith
  have hcε : (0:ℝ) < δ / (gphi (1 - η) - gphi c) := div_pos hδ0 hdiff
  filter_upwards [self_mem_nhdsWithin (s := Set.Ioi (0:ℝ)) (a := (0:ℝ)),
    Filter.mem_of_superset (nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hcε)) (fun s hs => hs)]
    with s hs hslt
  have hs0 : 0 < s := hs
  have hsup : moreauF ψ s x ≤ gphi c := by
    rw [moreauF_eq]
    have hneImg : ((fun y : ℝ => gphi (ψ y) - |x - y| / s) '' {y : ℝ | 0 < ψ y}).Nonempty :=
      hne.image _
    apply csSup_le hneImg
    rintro _ ⟨y, hy, rfl⟩
    by_cases hxy : |x - y| < δ
    · have hψy : ψ y < (ψ x + c) / 2 :=
        hδ (show y ∈ Metric.ball x δ from by rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm]; exact hxy)
      have hle : gphi (ψ y) ≤ gphi c := gphi_le_of_le hy hc1 (le_of_lt (lt_trans hψy hstep2))
      have h7 : 0 ≤ |x - y| / s := div_nonneg (abs_nonneg _) hs0.le
      linarith
    · push_neg at hxy
      have hM : gphi (ψ y) ≤ gphi (1 - η) := gphi_le_of_le hy (sub_lt_self 1 hη0) (hη1 y)
      have h3 : gphi (1 - η) - gphi c ≤ |x - y| / s := by
        rw [le_div_iff₀ hs0]
        have h4 : s * (gphi (1 - η) - gphi c) < δ := by
          have := mul_lt_mul_of_pos_right hslt hdiff
          rwa [div_mul_cancel₀ δ (ne_of_gt hdiff)] at this
        nlinarith [h4, hxy]
      linarith
  calc moreau ψ s x = gPhi (moreauF ψ s x) := moreau_eq ψ s x
    _ ≤ gPhi (gphi c) := gPhi_strictMono.monotone hsup
    _ = c := gphi_spec c hc0 hc1

/-- Pointwise convergence of the Moreau envelope to `ψ` for upper semicontinuous `ψ`. -/
lemma tendsto_moreau {ψ : ℝ → ℝ} (hψ : UpperSemicontinuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    {η : ℝ} (hη0 : 0 < η) (hη1 : ∀ x, ψ x ≤ 1 - η)
    (hne : {y : ℝ | 0 < ψ y}.Nonempty) (x : ℝ) :
    Tendsto (fun s : ℝ => moreau ψ s x) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (ψ x)) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    filter_upwards [self_mem_nhdsWithin (s := Set.Ioi (0:ℝ)) (a := (0:ℝ))] with s hs
    exact lt_of_lt_of_le ha (le_moreau hs hη0 hη1 hψ0 x)
  · intro a ha
    rcases lt_or_ge ((ψ x + a) / 2) (1 - η) with hc | hc
    · have hH : ∀ᶠ s in nhdsWithin (0:ℝ) (Set.Ioi 0), moreau ψ s x ≤ (ψ x + a) / 2 :=
        eventually_moreau_le (c := (ψ x + a) / 2) hψ hψ0 hη0 hη1 hne (by linarith) hc
      filter_upwards [hH] with s hs
      linarith
    · filter_upwards [self_mem_nhdsWithin (s := Set.Ioi (0:ℝ)) (a := (0:ℝ))] with s hs
      have hle := moreau_le hs hη0 hη1 hne x
      linarith

/-- The Moreau envelope of a compactly supported `ψ` is small at infinity. -/
lemma moreau_small_at_infinity {ψ : ℝ → ℝ} {η : ℝ} (hη0 : 0 < η) (hη1 : ∀ x, ψ x ≤ 1 - η)
    (hne : {y : ℝ | 0 < ψ y}.Nonempty) (hbd : ∃ R, ∀ y, 0 < ψ y → |y| ≤ R)
    {s : ℝ} (hs : 0 < s) {ε : ℝ} (hε : 0 < ε) :
    ∃ R', ∀ x, R' ≤ |x| → moreau ψ s x ≤ ε := by
  by_cases hεη : 1 - η ≤ ε
  · exact ⟨0, fun x _ => le_trans (moreau_le hs hη0 hη1 hne x) hεη⟩
  · push_neg at hεη
    obtain ⟨R, hR⟩ := hbd
    have hy0' : ∃ y : ℝ, 0 < ψ y := hne
    obtain ⟨y0, hy0⟩ := hy0'
    have hηpos : 0 < 1 - η := lt_of_lt_of_le hy0 (hη1 y0)
    have hε1 : ε < 1 := by linarith
    have hdiff : 0 < gphi (1 - η) - gphi ε := by
      have hlt := (gphi_strictMonoOn.lt_iff_lt ⟨hε, hε1⟩ ⟨hηpos, sub_lt_self 1 hη0⟩).mpr hεη
      linarith
    refine ⟨R + s * (gphi (1 - η) - gphi ε), fun x hx => ?_⟩
    have hsup : moreauF ψ s x ≤ gphi ε := by
      rw [moreauF_eq]
      have hneImg : ((fun y : ℝ => gphi (ψ y) - |x - y| / s) '' {y : ℝ | 0 < ψ y}).Nonempty :=
        hne.image _
      apply csSup_le hneImg
      rintro _ ⟨y, hy, rfl⟩
      have hyR := hR y hy
      have hxy : |x| - R ≤ |x - y| := le_trans (by linarith [hyR]) (abs_sub_abs_le_abs_sub x y)
      have hM : gphi (ψ y) ≤ gphi (1 - η) := gphi_le_of_le hy (sub_lt_self 1 hη0) (hη1 y)
      have h3 : gphi (1 - η) - gphi ε ≤ |x - y| / s := by
        rw [le_div_iff₀ hs]
        nlinarith [hx, hxy]
      linarith
    calc moreau ψ s x = gPhi (moreauF ψ s x) := moreau_eq ψ s x
      _ ≤ gPhi (gphi ε) := gPhi_strictMono.monotone hsup
      _ = ε := gphi_spec ε hε hε1


/-! ## The sup-convolution `h̄` and its upper semicontinuity -/

/-- The values whose supremum defines the sup-convolution. -/
def supconvSet (lam : ℝ) (f g : ℝ → ℝ) (z : ℝ) : Set ℝ :=
  {t : ℝ | ∃ a b : ℝ, 0 < f a ∧ 0 < g b ∧ lam * a + (1 - lam) * b = z ∧
    t = gPhi (lam * gphi (f a) + (1 - lam) * gphi (g b))}

/-- Sup-convolution in the sense of Ehrhard. -/
def supconv (lam : ℝ) (f g : ℝ → ℝ) (z : ℝ) : ℝ := sSup (supconvSet lam f g z)

lemma supconv_bddAbove {lam : ℝ} {f g : ℝ → ℝ} {η : ℝ} (hη0 : 0 < η) (hη : η < 1)
    (hf1 : ∀ x, f x ≤ 1 - η) (hg1 : ∀ x, g x ≤ 1 - η) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (z : ℝ) :
    BddAbove (supconvSet lam f g z) := by
  refine ⟨1 - η, ?_⟩
  rintro t ⟨a, b, hfa, hgb, hz, rfl⟩
  have h1η : 0 < 1 - η := by linarith
  have hfa' : gphi (f a) ≤ gphi (1 - η) := gphi_le_of_le hfa (by linarith) (hf1 a)
  have hgb' : gphi (g b) ≤ gphi (1 - η) := gphi_le_of_le hgb (by linarith) (hg1 b)
  have hsum : lam * gphi (f a) + (1 - lam) * gphi (g b) ≤ gphi (1 - η) := by
    nlinarith [hfa', hgb', hl0, hl1]
  calc gPhi (lam * gphi (f a) + (1 - lam) * gphi (g b))
      ≤ gPhi (gphi (1 - η)) := gPhi_strictMono.monotone hsum
    _ = 1 - η := gphi_spec (1 - η) h1η (by linarith)

lemma supconv_nonneg {lam : ℝ} {f g : ℝ → ℝ} {η : ℝ} (hη0 : 0 < η) (hη : η < 1)
    (hf1 : ∀ x, f x ≤ 1 - η) (hg1 : ∀ x, g x ≤ 1 - η) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (z : ℝ) :
    0 ≤ supconv lam f g z := by
  rw [supconv]
  by_cases hne : (supconvSet lam f g z).Nonempty
  · obtain ⟨t, ht⟩ := hne
    have ht0 : 0 ≤ t := by rcases ht with ⟨a, b, _, _, _, rfl⟩; exact (gPhi_pos _).le
    exact le_trans ht0 (le_csSup (supconv_bddAbove hη0 hη hf1 hg1 hl0 hl1 z) ht)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]

lemma le_supconv {lam : ℝ} {f g : ℝ → ℝ} {η : ℝ} (hη0 : 0 < η) (hη : η < 1)
    (hf1 : ∀ x, f x ≤ 1 - η) (hg1 : ∀ x, g x ≤ 1 - η) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1)
    {a b : ℝ} (hfa : 0 < f a) (hgb : 0 < g b) :
    gPhi (lam * gphi (f a) + (1 - lam) * gphi (g b))
      ≤ supconv lam f g (lam * a + (1 - lam) * b) := by
  rw [supconv]
  exact le_csSup (supconv_bddAbove hη0 hη hf1 hg1 hl0 hl1 _) ⟨a, b, hfa, hgb, rfl, rfl⟩

lemma supconv_le_of_le {lam : ℝ} {f g h : ℝ → ℝ} (hh0 : ∀ z, 0 ≤ h z)
    (hHP : ∀ a b, 0 < f a → 0 < g b →
      gPhi (lam * gphi (f a) + (1 - lam) * gphi (g b)) ≤ h (lam * a + (1 - lam) * b)) (z : ℝ) :
    supconv lam f g z ≤ h z := by
  rw [supconv]
  refine Real.sSup_le ?_ (hh0 z)
  rintro t ⟨a, b, hfa, hgb, hz, rfl⟩
  rw [← hz]
  exact hHP a b hfa hgb

/-- `gphi ∘ f` is upper semicontinuous on a set where `f` is positive and upper semicontinuous. -/
lemma upperSemicontinuousOn_gphi_comp {f : ℝ → ℝ} {K : Set ℝ} {η : ℝ} (hη0 : 0 < η) (hη : η < 1)
    (hf : UpperSemicontinuousOn f K) (hpos : ∀ x ∈ K, 0 < f x) (hle : ∀ x, f x ≤ 1 - η) :
    UpperSemicontinuousOn (fun x => gphi (f x)) K := by
  rw [upperSemicontinuousOn_iff]
  intro x0 hx0
  rw [upperSemicontinuousWithinAt_iff]
  intro y hy
  have hfx0 : 0 < f x0 := hpos x0 hx0
  have hfx0lt : f x0 < 1 := by linarith [hle x0]
  have hev1 : ∀ᶠ z in 𝓝 (f x0), gphi z < y :=
    (tendsto_order.mp (gphi_continuousAt (f x0) hfx0 hfx0lt)).2 y hy
  obtain ⟨δ, hδ0, hδ⟩ := Metric.mem_nhds_iff.mp hev1
  set ε : ℝ := min δ (1 - f x0) / 2 with hε
  have hε0 : 0 < ε := by
    rw [hε]; positivity
  have hεδ : ε < δ := by
    rw [hε]; have := min_le_left δ (1 - f x0); linarith
  have hε1 : f x0 + ε < 1 := by
    rw [hε]; have := min_le_right δ (1 - f x0); linarith
  have hgpy : gphi (f x0 + ε) < y := by
    apply hδ
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hev2 : ∀ᶠ x in 𝓝[K] x0, f x < f x0 + ε :=
    (upperSemicontinuousWithinAt_iff.mp (hf x0 hx0)) (f x0 + ε) (by linarith)
  filter_upwards [hev2, self_mem_nhdsWithin] with x hx hxK
  have h1 : 0 < f x := hpos x hxK
  have h2 : f x < f x0 + ε := hx
  have h3 : gphi (f x) < gphi (f x0 + ε) :=
    (gphi_strictMonoOn.lt_iff_lt ⟨h1, by linarith [hle x]⟩ ⟨by linarith, hε1⟩).mpr h2
  exact lt_trans h3 hgpy

lemma supconv_upperSemicontinuous {lam : ℝ} {f g : ℝ → ℝ} {η : ℝ} (hη0 : 0 < η) (hη : η < 1)
    (hf : UpperSemicontinuous f) (hg : UpperSemicontinuous g)
    (hf1 : ∀ x, f x ≤ 1 - η) (hg1 : ∀ x, g x ≤ 1 - η)
    (hK : IsCompact {x | 0 < f x}) (hL : IsCompact {y | 0 < g y})
    (hl0 : 0 < lam) (hl1 : lam < 1) :
    UpperSemicontinuous (supconv lam f g) := by
  have hF : UpperSemicontinuousOn (fun x => gphi (f x)) {x | 0 < f x} :=
    upperSemicontinuousOn_gphi_comp hη0 hη (hf.upperSemicontinuousOn _) (fun x hx => hx) hf1
  have hG : UpperSemicontinuousOn (fun y => gphi (g y)) {y | 0 < g y} :=
    upperSemicontinuousOn_gphi_comp hη0 hη (hg.upperSemicontinuousOn _) (fun y hy => hy) hg1
  have hFw : UpperSemicontinuousOn (fun x => lam * gphi (f x)) {x | 0 < f x} :=
    (continuous_const.mul continuous_id).comp_upperSemicontinuousOn hF
      (fun a b h => mul_le_mul_of_nonneg_left h hl0.le)
  have hGw : UpperSemicontinuousOn (fun y => (1 - lam) * gphi (g y)) {y | 0 < g y} :=
    (continuous_const.mul continuous_id).comp_upperSemicontinuousOn hG
      (fun a b h => mul_le_mul_of_nonneg_left h (by linarith))
  have hFG : UpperSemicontinuousOn
      (fun p : ℝ × ℝ => lam * gphi (f p.1) + (1 - lam) * gphi (g p.2))
      ({x | 0 < f x} ×ˢ {y | 0 < g y}) := by
    have h1 : UpperSemicontinuousOn (fun p : ℝ × ℝ => lam * gphi (f p.1))
        ({x | 0 < f x} ×ˢ {y | 0 < g y}) :=
      hFw.comp continuousOn_fst (fun p hp => hp.1)
    have h2 : UpperSemicontinuousOn (fun p : ℝ × ℝ => (1 - lam) * gphi (g p.2))
        ({x | 0 < f x} ×ˢ {y | 0 < g y}) :=
      hGw.comp continuousOn_snd (fun p hp => hp.2)
    exact h1.add h2
  have hmain := Commons.Topology.Order.upperSemicontinuous_sSup_minkowski_section
    gPhi (fun a => lam * gphi (f a)) (fun b => (1 - lam) * gphi (g b)) gPhi_continuous
    gPhi_strictMono.monotone (fun t => (gPhi_pos t).le) hK hL hFG lam hl0 hl1
  have hfil (z : ℝ) : {t : ℝ | ∃ a ∈ {x | 0 < f x}, ∃ b ∈ {y | 0 < g y},
        lam * a + (1 - lam) * b = z ∧ t = gPhi (lam * gphi (f a) + (1 - lam) * gphi (g b))}
      = supconvSet lam f g z := by
    ext t
    simp only [supconvSet, mem_setOf_eq, mem_setOf]
    constructor
    · rintro ⟨a, ha, b, hb, hz, ht⟩
      exact ⟨a, b, ha, hb, hz, ht⟩
    · rintro ⟨a, b, ha, hb, hz, ht⟩
      exact ⟨a, ha, b, hb, hz, ht⟩
  have : (fun z : ℝ => sSup {t : ℝ | ∃ a ∈ {x | 0 < f x}, ∃ b ∈ {y | 0 < g y},
        lam * a + (1 - lam) * b = z ∧ t = gPhi (lam * gphi (f a) + (1 - lam) * gphi (g b))})
      = supconv lam f g := by
    funext z; rw [supconv, hfil z]
  rwa [this] at hmain

/-- Sup-additivity in the form needed for the Moreau envelope. -/
lemma mul_csSup_add_le_of {A B : Set ℝ} {c lam : ℝ} (hA : A.Nonempty) (hB : B.Nonempty)
    (hAb : BddAbove A) (hBb : BddAbove B) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1)
    (h : ∀ a ∈ A, ∀ b ∈ B, lam * a + (1 - lam) * b ≤ c) :
    lam * sSup A + (1 - lam) * sSup B ≤ c := by
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  obtain ⟨a, haA, ha⟩ := exists_lt_of_lt_csSup hA (show sSup A - ε < sSup A by linarith)
  obtain ⟨b, hbB, hb⟩ := exists_lt_of_lt_csSup hB (show sSup B - ε < sSup B by linarith)
  have h1 : lam * sSup A ≤ lam * (a + ε) :=
    mul_le_mul_of_nonneg_left (by linarith) hl0
  have h2 : (1 - lam) * sSup B ≤ (1 - lam) * (b + ε) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h3 : lam * (a + ε) + (1 - lam) * (b + ε) = lam * a + (1 - lam) * b + ε := by ring
  have h4 := h a haA b hbB
  linarith [h1, h2, h3, h4]

/-- The Ehrhard hypothesis is preserved by the Moreau smoothing. -/
lemma hp_moreau {lam s : ℝ} (hs : 0 < s) (hl0 : 0 < lam) (hl1 : lam < 1)
    {f g hb : ℝ → ℝ} {η : ℝ} (hη0 : 0 < η) (hη : η < 1)
    (hf1 : ∀ x, f x ≤ 1 - η) (hg1 : ∀ x, g x ≤ 1 - η)
    (hhb0 : ∀ x, 0 ≤ hb x) (hhb1 : ∀ x, hb x ≤ 1 - η)
    (hHP : ∀ a b, 0 < f a → 0 < g b →
      gPhi (lam * gphi (f a) + (1 - lam) * gphi (g b)) ≤ hb (lam * a + (1 - lam) * b))
    (hne_f : {a : ℝ | 0 < f a}.Nonempty) (hne_g : {b : ℝ | 0 < g b}.Nonempty)
    (hne_hb : {z : ℝ | 0 < hb z}.Nonempty) :
    ∀ x y, gPhi (lam * gphi (moreau f s x) + (1 - lam) * gphi (moreau g s y))
      ≤ moreau hb s (lam * x + (1 - lam) * y) := by
  intro x y
  rw [gphi_moreau, gphi_moreau, moreau_eq]
  apply gPhi_strictMono.monotone
  refine mul_csSup_add_le_of (hne_f.image _) (hne_g.image _)
    (bddAbove_moreauF hs hη0 hf1 x) (bddAbove_moreauF hs hη0 hg1 y) hl0.le hl1.le ?_
  rintro t ⟨a, hfa, rfl⟩ u ⟨b, hgb, rfl⟩
  set U : ℝ := lam * gphi (f a) + (1 - lam) * gphi (g b) with hU
  have hUV : gPhi U ≤ hb (lam * a + (1 - lam) * b) := hHP a b hfa hgb
  have hVpos : 0 < hb (lam * a + (1 - lam) * b) :=
    lt_of_lt_of_le (gPhi_pos U) hUV
  have hVlt : hb (lam * a + (1 - lam) * b) < 1 := by
    have := hhb1 (lam * a + (1 - lam) * b); linarith
  have hUle : U ≤ gphi (hb (lam * a + (1 - lam) * b)) := by
    rw [show U = gphi (gPhi U) from (gphi_gPhi U).symm]
    exact gphi_le_of_le (gPhi_pos U) hVlt hUV
  have htri : |lam * x + (1 - lam) * y - (lam * a + (1 - lam) * b)|
      ≤ lam * |x - a| + (1 - lam) * |y - b| := by
    have heq : lam * x + (1 - lam) * y - (lam * a + (1 - lam) * b)
        = lam * (x - a) + (1 - lam) * (y - b) := by ring
    rw [heq]
    calc |lam * (x - a) + (1 - lam) * (y - b)|
        ≤ |lam * (x - a)| + |(1 - lam) * (y - b)| := abs_add_le _ _
      _ = lam * |x - a| + (1 - lam) * |y - b| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (show (0:ℝ) ≤ lam from hl0.le),
            abs_of_nonneg (show (0:ℝ) ≤ 1 - lam by linarith [hl1])]
  have hmem : gphi (hb (lam * a + (1 - lam) * b))
        - |lam * x + (1 - lam) * y - (lam * a + (1 - lam) * b)| / s
      ∈ ((fun b' : ℝ => gphi (hb b') - |(lam * x + (1 - lam) * y) - b'| / s)
          '' {b' : ℝ | 0 < hb b'}) :=
    ⟨lam * a + (1 - lam) * b, hVpos, rfl⟩
  have hle : gphi (hb (lam * a + (1 - lam) * b))
        - |lam * x + (1 - lam) * y - (lam * a + (1 - lam) * b)| / s
      ≤ moreauF hb s (lam * x + (1 - lam) * y) :=
    le_csSup (bddAbove_moreauF hs hη0 hhb1 _) hmem
  have hkey : lam * (gphi (f a) - |x - a| / s) + (1 - lam) * (gphi (g b) - |y - b| / s)
      = U - (lam * |x - a| + (1 - lam) * |y - b|) / s := by
    rw [hU]; ring
  have hdiv : |lam * x + (1 - lam) * y - (lam * a + (1 - lam) * b)| / s
      ≤ (lam * |x - a| + (1 - lam) * |y - b|) / s :=
    div_le_div_of_nonneg_right htri hs.le
  linarith [hUle, hkey, hdiv, hle]

/-- The `s`-smoothed Ehrhard inequality, `s > 0` fixed. -/
theorem ehrhard_nice_step {lam s : ℝ} (hs : 0 < s) (hl0 : 0 < lam) (hl1 : lam < 1)
    {f g : ℝ → ℝ} {η : ℝ} (hη0 : 0 < η) (hη : η < 1)
    (hf : UpperSemicontinuous f) (hg : UpperSemicontinuous g)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1 - η)
    (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1 - η)
    (hK : IsCompact {x : ℝ | 0 < f x}) (hL : IsCompact {y : ℝ | 0 < g y})
    (hKn : ({x : ℝ | 0 < f x}).Nonempty) (hLn : ({y : ℝ | 0 < g y}).Nonempty) :
    gPhi (lam * gphi (∫ x, moreau f s x * gdens x)
        + (1 - lam) * gphi (∫ x, moreau g s x * gdens x))
      ≤ ∫ x, moreau (supconv lam f g) s x * gdens x := by
  have hhb_usc : UpperSemicontinuous (supconv lam f g) :=
    supconv_upperSemicontinuous hη0 hη hf hg hf1 hg1 hK hL hl0 hl1
  have hhb0 : ∀ z, 0 ≤ supconv lam f g z := supconv_nonneg hη0 hη hf1 hg1 hl0.le hl1.le
  have hhb1 : ∀ z, supconv lam f g z ≤ 1 - η := by
    intro z
    rw [supconv]
    refine Real.sSup_le ?_ (by linarith [hη0])
    rintro t ⟨a, b, hfa, hgb, hz, rfl⟩
    have h1 := gphi_le_of_le hfa (by linarith) (hf1 a)
    have h2 := gphi_le_of_le hgb (by linarith) (hg1 b)
    have hU : lam * gphi (f a) + (1 - lam) * gphi (g b) ≤ gphi (1 - η) := by
      nlinarith [h1, h2, hl0.le, hl1.le]
    calc gPhi (lam * gphi (f a) + (1 - lam) * gphi (g b))
        ≤ gPhi (gphi (1 - η)) := gPhi_strictMono.monotone hU
      _ = 1 - η := gphi_spec (1 - η) (by linarith) (by linarith)
  have hHP : ∀ a b, 0 < f a → 0 < g b →
      gPhi (lam * gphi (f a) + (1 - lam) * gphi (g b))
        ≤ supconv lam f g (lam * a + (1 - lam) * b) :=
    fun a b ha hb => le_supconv hη0 hη hf1 hg1 hl0.le hl1.le ha hb
  have hne_hb : {z : ℝ | 0 < supconv lam f g z}.Nonempty := by
    obtain ⟨a, ha⟩ := hKn
    obtain ⟨b, hb⟩ := hLn
    exact ⟨lam * a + (1 - lam) * b, lt_of_lt_of_le (gPhi_pos _) (hHP a b ha hb)⟩
  have hbdd_f : ∃ R : ℝ, ∀ y : ℝ, 0 < f y → |y| ≤ R := by
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hK.isBounded
    exact ⟨R, fun y hy => by simpa [Real.norm_eq_abs] using hR y hy⟩
  have hbdd_g : ∃ R : ℝ, ∀ y : ℝ, 0 < g y → |y| ≤ R := by
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hL.isBounded
    exact ⟨R, fun y hy => by simpa [Real.norm_eq_abs] using hR y hy⟩
  have hbdd_f' : BddAbove ((fun a : ℝ => gphi (f a)) '' {a : ℝ | 0 < f a}) :=
    bddAbove_gphi_image hη0 hf1
  have hbdd_g' : BddAbove ((fun b : ℝ => gphi (g b)) '' {b : ℝ | 0 < g b}) :=
    bddAbove_gphi_image hη0 hg1
  have hbdd_hb : BddAbove ((fun z : ℝ => gphi (supconv lam f g z)) '' {z : ℝ | 0 < supconv lam f g z}) :=
    bddAbove_gphi_image hη0 hhb1
  have hAdm_f : IsAdm (moreau f s) η :=
    ⟨(moreau_continuous hs hKn hbdd_f').measurable, fun x => moreau_pos f s x,
      fun x => moreau_le hs hη0 hf1 hKn x, hη0⟩
  have hAdm_g : IsAdm (moreau g s) η :=
    ⟨(moreau_continuous hs hLn hbdd_g').measurable, fun x => moreau_pos g s x,
      fun x => moreau_le hs hη0 hg1 hLn x, hη0⟩
  have hcont_f : Continuous (moreau f s) := moreau_continuous hs hKn hbdd_f'
  have hcont_g : Continuous (moreau g s) := moreau_continuous hs hLn hbdd_g'
  have hcont_h : Continuous (moreau (supconv lam f g) s) :=
    moreau_continuous hs hne_hb hbdd_hb
  have hint_f : ∀ ε > 0, ∃ R : ℝ, ∀ x, R ≤ |x| → moreau f s x ≤ ε :=
    fun ε hε => moreau_small_at_infinity hη0 hf1 hKn hbdd_f hs hε
  have hint_g : ∀ ε > 0, ∃ R : ℝ, ∀ x, R ≤ |x| → moreau g s x ≤ ε :=
    fun ε hε => moreau_small_at_infinity hη0 hg1 hLn hbdd_g hs hε
  have hHPs : ∀ x y, gPhi (lam * gphi (moreau f s x) + (1 - lam) * gphi (moreau g s y))
      ≤ moreau (supconv lam f g) s (lam * x + (1 - lam) * y) :=
    hp_moreau hs hl0 hl1 hη0 hη hf1 hg1 hhb0 hhb1 hHP hKn hLn hne_hb
  exact ehrhard_continuous lam hl0.le hl1.le hAdm_f hAdm_g hcont_f hcont_g hcont_h
    (fun x => (moreau_pos _ _ _).le)
    (fun x => by
      rw [abs_of_pos (moreau_pos _ _ _), moreau_eq]
      exact le_of_lt (gPhi_lt_one _))
    hint_f hint_g hHPs

/-- Dominated convergence for the Moreau envelope integrals. -/
lemma tendsto_integral_moreau {ψ : ℝ → ℝ} (hψ : UpperSemicontinuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    {η : ℝ} (hη0 : 0 < η) (hη1 : ∀ x, ψ x ≤ 1 - η)
    (hne : {y : ℝ | 0 < ψ y}.Nonempty) :
    Tendsto (fun n : ℕ => ∫ x, moreau ψ ((1:ℝ)/((n:ℝ)+1)) x * gdens x) atTop
      (nhds (∫ x, ψ x * gdens x)) := by
  have hs_n : Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)) atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat, by
      filter_upwards with n
      exact div_pos one_pos (by positivity : (0:ℝ) < (n:ℝ) + 1)⟩
  have hbdd : BddAbove ((fun y : ℝ => gphi (ψ y)) '' {y : ℝ | 0 < ψ y}) :=
    bddAbove_gphi_image hη0 hη1
  refine MeasureTheory.tendsto_integral_of_dominated_convergence gdens ?_ integrable_gdens ?_ ?_
  · intro n
    exact (((moreau_continuous (s := (1:ℝ)/((n:ℝ)+1)) (by positivity) hne hbdd)).mul
      gdens_cont).aestronglyMeasurable
  · intro n
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (gdens_pos x)]
    refine mul_le_of_le_one_left (gdens_pos x).le ?_
    rw [abs_of_pos (moreau_pos _ _ _), moreau_eq]
    exact (gPhi_lt_one _).le
  · filter_upwards with x
    exact ((tendsto_moreau hψ hψ0 hη0 hη1 hne x).comp hs_n).mul tendsto_const_nhds

/-- The intrinsic Ehrhard inequality for nice (upper semicontinuous, compactly supported) data. -/
theorem ehrhard_nice_intrinsic {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1)
    {f g : ℝ → ℝ} {η : ℝ} (hη0 : 0 < η) (hη : η < 1)
    (hf : UpperSemicontinuous f) (hg : UpperSemicontinuous g)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1 - η)
    (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1 - η)
    (hK : IsCompact {x : ℝ | 0 < f x}) (hL : IsCompact {y : ℝ | 0 < g y})
    (hKn : ({x : ℝ | 0 < f x}).Nonempty) (hLn : ({y : ℝ | 0 < g y}).Nonempty)
    (hA0 : 0 < ∫ x, f x * gdens x) (hB0 : 0 < ∫ x, g x * gdens x) :
    gPhi (lam * gphi (∫ x, f x * gdens x) + (1 - lam) * gphi (∫ x, g x * gdens x))
      ≤ ∫ x, supconv lam f g x * gdens x := by
  have hhb1 : ∀ z, supconv lam f g z ≤ 1 - η := by
    intro z
    rw [supconv]
    refine Real.sSup_le ?_ (by linarith [hη0])
    rintro t ⟨a, b, hfa, hgb, hz, rfl⟩
    have h1 := gphi_le_of_le hfa (by linarith) (hf1 a)
    have h2 := gphi_le_of_le hgb (by linarith) (hg1 b)
    have hU : lam * gphi (f a) + (1 - lam) * gphi (g b) ≤ gphi (1 - η) := by
      nlinarith [h1, h2, hl0.le, hl1.le]
    calc gPhi (lam * gphi (f a) + (1 - lam) * gphi (g b))
        ≤ gPhi (gphi (1 - η)) := gPhi_strictMono.monotone hU
      _ = 1 - η := gphi_spec (1 - η) (by linarith) (by linarith)
  have hhb0 : ∀ z, 0 ≤ supconv lam f g z := supconv_nonneg hη0 hη hf1 hg1 hl0.le hl1.le
  have hhb_usc : UpperSemicontinuous (supconv lam f g) :=
    supconv_upperSemicontinuous hη0 hη hf hg hf1 hg1 hK hL hl0 hl1
  have hne_hb : {z : ℝ | 0 < supconv lam f g z}.Nonempty := by
    obtain ⟨a, ha⟩ := hKn
    obtain ⟨b, hb⟩ := hLn
    exact ⟨lam * a + (1 - lam) * b,
      lt_of_lt_of_le (gPhi_pos _) (le_supconv hη0 hη hf1 hg1 hl0.le hl1.le ha hb)⟩
  have hA := tendsto_integral_moreau hf hf0 hη0 hf1 hKn
  have hB := tendsto_integral_moreau hg hg0 hη0 hg1 hLn
  have hC := tendsto_integral_moreau hhb_usc hhb0 hη0 hhb1 hne_hb
  have hint_f : Integrable (fun x => f x * gdens x) :=
    integrable_mul_gauss hf.measurable (fun x => by
      rw [abs_of_nonneg (hf0 x)]; linarith [hf1 x, hη0])
  have hint_g : Integrable (fun x => g x * gdens x) :=
    integrable_mul_gauss hg.measurable (fun x => by
      rw [abs_of_nonneg (hg0 x)]; linarith [hg1 x, hη0])
  have hint_c : Integrable (fun x => (1 - η) * gdens x) :=
    integrable_mul_gauss measurable_const (fun x => by
      rw [abs_of_nonneg (show (0:ℝ) ≤ 1 - η by linarith [hη])]; linarith [hη0])
  have hconst : ∫ x, (1 - η) * gdens x = 1 - η := by
    rw [integral_const_mul]
    simp only [gdens, integral_gauss, mul_one]
  have hA1 : ∫ x, f x * gdens x < 1 := by
    have hle : ∫ x, f x * gdens x ≤ ∫ x, (1 - η) * gdens x :=
      integral_mono hint_f hint_c (fun x => by
        simp only [gdens]
        exact mul_le_mul_of_nonneg_right (hf1 x) (Real.exp_pos _).le)
    rw [hconst] at hle; linarith
  have hB1 : ∫ x, g x * gdens x < 1 := by
    have hle : ∫ x, g x * gdens x ≤ ∫ x, (1 - η) * gdens x :=
      integral_mono hint_g hint_c (fun x => by
        simp only [gdens]
        exact mul_le_mul_of_nonneg_right (hg1 x) (Real.exp_pos _).le)
    rw [hconst] at hle; linarith
  have hgA : Tendsto (fun n : ℕ => gphi (∫ x, moreau f ((1:ℝ)/((n:ℝ)+1)) x * gdens x)) atTop
      (nhds (gphi (∫ x, f x * gdens x))) := by
    have h1 : Tendsto gphi (nhds (∫ x, f x * gdens x)) (nhds (gphi (∫ x, f x * gdens x))) :=
      ContinuousAt.tendsto (gphi_continuousAt (∫ x, f x * gdens x) hA0 hA1)
    exact h1.comp hA
  have hgB : Tendsto (fun n : ℕ => gphi (∫ x, moreau g ((1:ℝ)/((n:ℝ)+1)) x * gdens x)) atTop
      (nhds (gphi (∫ x, g x * gdens x))) := by
    have h1 : Tendsto gphi (nhds (∫ x, g x * gdens x)) (nhds (gphi (∫ x, g x * gdens x))) :=
      ContinuousAt.tendsto (gphi_continuousAt (∫ x, g x * gdens x) hB0 hB1)
    exact h1.comp hB
  have hTendLHS : Tendsto
      (fun n : ℕ => gPhi (lam * gphi (∫ x, moreau f ((1:ℝ)/((n:ℝ)+1)) x * gdens x)
        + (1 - lam) * gphi (∫ x, moreau g ((1:ℝ)/((n:ℝ)+1)) x * gdens x))) atTop
      (nhds (gPhi (lam * gphi (∫ x, f x * gdens x) + (1 - lam) * gphi (∫ x, g x * gdens x)))) :=
    (gPhi_continuous.tendsto _).comp
      ((Filter.Tendsto.add (Filter.Tendsto.const_mul lam hgA)
        (Filter.Tendsto.const_mul (1 - lam) hgB)))
  exact le_of_tendsto_of_tendsto' hTendLHS hC
    (fun n => ehrhard_nice_step (by positivity) hl0 hl1 hη0 hη hf hg hf0 hf1 hg0 hg1 hK hL hKn hLn)

/-! ## The Gaussian measure and the reduction to the nice case -/

/-- The standard Gaussian measure on `ℝ` (with density `exp (-π x²)`). -/
noncomputable def gaussMeasure : Measure ℝ :=
  volume.withDensity (fun x : ℝ => ENNReal.ofReal (gdens x))

lemma gaussMeasure_integral (g : ℝ → ℝ) :
    ∫ x, g x ∂gaussMeasure = ∫ x, g x * gdens x := by
  have h := integral_withDensity_eq_integral_toReal_smul (μ := volume)
    (f := fun x : ℝ => ENNReal.ofReal (gdens x))
    (ENNReal.measurable_ofReal.comp gdens_cont.measurable)
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)) g
  rw [gaussMeasure, h]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  show (ENNReal.ofReal (gdens x)).toReal • g x = g x * gdens x
  rw [ENNReal.toReal_ofReal (gdens_pos x).le, smul_eq_mul, mul_comm]

lemma gaussMeasure_univ_ne_top : gaussMeasure Set.univ ≠ ⊤ := by
  rw [gaussMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal integrable_gdens
      (Filter.Eventually.of_forall (fun x => (gdens_pos x).le))]
  rw [show (∫ x : ℝ, gdens x) = 1 from by simpa only [gdens] using integral_gauss,
    ENNReal.ofReal_one]
  exact ENNReal.one_ne_top

local instance gaussMeasure.instFiniteMeasure : MeasureTheory.IsFiniteMeasure gaussMeasure :=
  ⟨by rw [lt_top_iff_ne_top]; exact gaussMeasure_univ_ne_top⟩

/-- `gphi y → +∞` as `y → 1⁻`. -/
lemma tendsto_gphi_nhdsWithin_one : Tendsto gphi (nhdsWithin (1:ℝ) (Set.Iio 1)) atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (gPhi_lt_one b)), self_mem_nhdsWithin]
    with y hy hy1
  have hy0 : 0 < y := lt_of_lt_of_le (gPhi_pos b) hy.le
  have hspec : gPhi (gphi y) = y := gphi_spec y hy0 hy1
  exact le_of_lt (gPhi_strictMono.lt_iff_lt.mp (by rw [hspec]; exact hy))

/-- `gphi y → -∞` as `y → 0⁺`. -/
lemma tendsto_gphi_nhdsWithin_zero : Tendsto gphi (nhdsWithin (0:ℝ) (Set.Ioi 0)) atBot := by
  rw [tendsto_atBot]
  intro b
  filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (gPhi_pos b)), self_mem_nhdsWithin]
    with y hy hy0
  have hy1 : y < 1 := lt_of_le_of_lt hy.le (gPhi_lt_one b)
  have hspec : gPhi (gphi y) = y := gphi_spec y hy0 hy1
  exact le_of_lt (gPhi_strictMono.lt_iff_lt.mp (by rw [hspec]; exact hy))

lemma gdens_integral_one : ∫ x, gdens x = 1 := by
  simpa only [gdens] using integral_gauss

/-- For `0 ≤ q ≤ 1 - η`, `∫ q dγ ≤ 1 - η`. -/
lemma integral_mul_gdens_le {q : ℝ → ℝ} (hqm : Measurable q) (hq0 : ∀ x, 0 ≤ q x)
    {η : ℝ} (hη : 0 < η) (hη1' : η < 1) (hq : ∀ x, q x ≤ 1 - η) :
    ∫ x, q x * gdens x ≤ 1 - η := by
  have hη1 : (0:ℝ) ≤ 1 - η := by linarith [hη1']
  have h1 : ∫ x, q x * gdens x ≤ ∫ x, (1 - η) * gdens x :=
    integral_mono
      (integrable_mul_gauss hqm (fun x => by
        rw [abs_of_nonneg (hq0 x)]; have := hq x; linarith))
      (integrable_mul_gauss measurable_const (fun x => by
        rw [abs_of_nonneg hη1]; linarith [hη]))
      (fun x => mul_le_mul_of_nonneg_right (hq x) (gdens_pos x).le)
  rwa [integral_const_mul, gdens_integral_one, mul_one] at h1

/-- For `0 ≤ q ≤ 1`, `∫ q dγ ≤ 1`. -/
lemma integral_mul_gdens_le_one {q : ℝ → ℝ} (hqm : Measurable q) (hq0 : ∀ x, 0 ≤ q x)
    (hq : ∀ x, q x ≤ 1) : ∫ x, q x * gdens x ≤ 1 := by
  have h1 : ∫ x, q x * gdens x ≤ ∫ x, (1:ℝ) * gdens x :=
    integral_mono (integrable_mul_gauss hqm (fun x => by
        rw [abs_of_nonneg (hq0 x)]; linarith [hq x]))
      (integrable_mul_gauss measurable_const (fun x => by simp))
      (fun x => mul_le_mul_of_nonneg_right (hq x) (gdens_pos x).le)
  rwa [integral_const_mul, gdens_integral_one, mul_one] at h1

/-- `supconv` of two functions bounded by `1 - η` is bounded by `1 - η`. -/
lemma supconv_le_one_sub {lam : ℝ} {f g : ℝ → ℝ} {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    (hf1 : ∀ x, f x ≤ 1 - η) (hg1 : ∀ x, g x ≤ 1 - η)
    (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (z : ℝ) : supconv lam f g z ≤ 1 - η := by
  rw [supconv]
  refine Real.sSup_le ?_ (by linarith [hη1])
  rintro t ⟨a, b, hfa, hgb, hz, rfl⟩
  have h1 := gphi_le_of_le hfa (by linarith [hη0]) (hf1 a)
  have h2 := gphi_le_of_le hgb (by linarith [hη0]) (hg1 b)
  have hU : lam * gphi (f a) + (1 - lam) * gphi (g b) ≤ gphi (1 - η) := by
    nlinarith [h1, h2, hl0, hl1]
  calc gPhi (lam * gphi (f a) + (1 - lam) * gphi (g b))
      ≤ gPhi (gphi (1 - η)) := gPhi_strictMono.monotone hU
    _ = 1 - η := gphi_spec (1 - η) (by linarith [hη1]) (by linarith [hη0])

/-- The key intermediate inequality for a fixed `n`. -/
theorem ehrhard_measurable_step {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1)
    {f g h : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g) (hhm : Measurable h)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1)
    (hh0 : ∀ x, 0 ≤ h x) (hhb : ∀ x, |h x| ≤ 1)
    (hcond : ∀ a b s t, gPhi a ≤ f s → gPhi b ≤ g t →
        gPhi (lam * a + (1 - lam) * b) ≤ h (lam * s + (1 - lam) * t))
    {F G : ℕ → ℝ → ℝ}
    (hFusc : ∀ n, UpperSemicontinuous (F n)) (hF0 : ∀ n x, 0 ≤ F n x)
    (hFle : ∀ n x, F n x ≤ f x) (hFK : ∀ n, IsCompact {x : ℝ | 0 < F n x})
    (hF1 : ∀ n x, F n x ≤ 1 - 1/((n:ℝ)+1))
    (hGusc : ∀ n, UpperSemicontinuous (G n)) (hG0 : ∀ n x, 0 ≤ G n x)
    (hGle : ∀ n x, G n x ≤ g x) (hGK : ∀ n, IsCompact {x : ℝ | 0 < G n x})
    (hG1 : ∀ n x, G n x ≤ 1 - 1/((n:ℝ)+1))
    (n : ℕ) (hFn : 0 < ∫ x, F n x * gdens x) (hGn : 0 < ∫ x, G n x * gdens x) :
    gPhi (lam * gphi (∫ x, F n x * gdens x) + (1 - lam) * gphi (∫ x, G n x * gdens x))
      ≤ ∫ x, h x * gdens x := by
  have hη0 : (0:ℝ) < 1/((n:ℝ)+2) := by positivity
  have hη1 : (1:ℝ)/((n:ℝ)+2) < 1 := by
    rw [div_lt_one (by positivity : (0:ℝ) < (n:ℝ) + 2)]
    have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith
  have hη1' : 1 - 1/((n:ℝ)+2) < 1 := sub_lt_self 1 hη0
  have hFx : ∀ x, F n x ≤ 1 - 1/((n:ℝ)+2) := fun x => by
    have h1 : 1/((n:ℝ)+2) ≤ 1/((n:ℝ)+1) :=
      one_div_le_one_div_of_le (by positivity : (0:ℝ) < (n:ℝ)+1) (by linarith)
    linarith [hF1 n x, h1]
  have hGx : ∀ x, G n x ≤ 1 - 1/((n:ℝ)+2) := fun x => by
    have h1 : 1/((n:ℝ)+2) ≤ 1/((n:ℝ)+1) :=
      one_div_le_one_div_of_le (by positivity : (0:ℝ) < (n:ℝ)+1) (by linarith)
    linarith [hG1 n x, h1]
  have hneF : {x : ℝ | 0 < F n x}.Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have h0 : ∀ x, F n x = 0 := by
      intro x
      have hx : x ∉ {x : ℝ | 0 < F n x} := by rw [hcon]; exact Set.notMem_empty x
      exact le_antisymm (not_lt.mp hx) (hF0 n x)
    have : ∫ x, F n x * gdens x = 0 := by simp only [h0, zero_mul, integral_zero]
    rw [this] at hFn; exact absurd hFn (lt_irrefl 0)
  have hneG : {x : ℝ | 0 < G n x}.Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have h0 : ∀ x, G n x = 0 := by
      intro x
      have hx : x ∉ {x : ℝ | 0 < G n x} := by rw [hcon]; exact Set.notMem_empty x
      exact le_antisymm (not_lt.mp hx) (hG0 n x)
    have : ∫ x, G n x * gdens x = 0 := by simp only [h0, zero_mul, integral_zero]
    rw [this] at hGn; exact absurd hGn (lt_irrefl 0)
  have hsc_usc : UpperSemicontinuous (supconv lam (F n) (G n)) :=
    supconv_upperSemicontinuous hη0 hη1 (hFusc n) (hGusc n) hFx hGx (hFK n) (hGK n)
      hl0 hl1
  have hsc0 : ∀ z, 0 ≤ supconv lam (F n) (G n) z :=
    supconv_nonneg hη0 hη1 hFx hGx hl0.le hl1.le
  have hHPn : ∀ s t, 0 < F n s → 0 < G n t →
      gPhi (lam * gphi (F n s) + (1 - lam) * gphi (G n t)) ≤ h (lam * s + (1 - lam) * t) := by
    intro s t hfs hgt
    have hfs1 : F n s < 1 := lt_of_le_of_lt (hFx s) hη1'
    have hgt1 : G n t < 1 := lt_of_le_of_lt (hGx t) hη1'
    refine hcond (gphi (F n s)) (gphi (G n t)) s t ?_ ?_
    · rw [gphi_spec _ hfs hfs1]; exact hFle n s
    · rw [gphi_spec _ hgt hgt1]; exact hGle n t
  have hint := ehrhard_nice_intrinsic (η := 1/((n:ℝ)+2)) hl0 hl1 hη0 hη1
    (hFusc n) (hGusc n) (hF0 n) hFx (hG0 n) hGx (hFK n) (hGK n) hneF hneG hFn hGn
  have hscle : ∀ z, supconv lam (F n) (G n) z ≤ h z :=
    supconv_le_of_le hh0 (fun s t hs ht => hHPn s t hs ht)
  have hint2 : (∫ x, supconv lam (F n) (G n) x * gdens x) ≤ ∫ x, h x * gdens x :=
    integral_mono
      (integrable_mul_gauss hsc_usc.measurable (fun x => by
        rw [abs_of_nonneg (hsc0 x)]
        exact le_of_lt (lt_of_le_of_lt (supconv_le_one_sub hη0 hη1
          hFx hGx hl0.le hl1.le x) (by linarith [hη0]))))
      (integrable_mul_gauss hhm hhb)
      (fun x => mul_le_mul_of_nonneg_right (hscle x) (gdens_pos x).le)
  linarith [hint, hint2]

theorem ehrhard_measurable_main {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1)
    {f g h : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g) (hhm : Measurable h)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1)
    (hh0 : ∀ x, 0 ≤ h x) (hhb : ∀ x, |h x| ≤ 1)
    (hcond : ∀ a b s t, gPhi a ≤ f s → gPhi b ≤ g t →
        gPhi (lam * a + (1 - lam) * b) ≤ h (lam * s + (1 - lam) * t)) :
    ∀ a b, gPhi a ≤ ∫ x, f x * gdens x → gPhi b ≤ ∫ x, g x * gdens x →
      gPhi (lam * a + (1 - lam) * b) ≤ ∫ x, h x * gdens x := by
  intro a b ha hb
  have hA0 : 0 < ∫ x, f x * gdens x := lt_of_lt_of_le (gPhi_pos a) ha
  have hB0 : 0 < ∫ x, g x * gdens x := lt_of_lt_of_le (gPhi_pos b) hb
  have hA1 : ∫ x, f x * gdens x ≤ 1 := integral_mul_gdens_le_one hf hf0 hf1
  have hB1 : ∫ x, g x * gdens x ≤ 1 := integral_mul_gdens_le_one hg hg0 hg1
  obtain ⟨F, hFusc, hF0, hFle, hFK, hF1, hFlim⟩ := Commons.MeasureTheory.Real.exists_ucs_approx gaussMeasure f hf hf0 hf1
  obtain ⟨G, hGusc, hG0, hGle, hGK, hG1, hGlim⟩ := Commons.MeasureTheory.Real.exists_ucs_approx gaussMeasure g hg hg0 hg1
  have hη0 : ∀ n : ℕ, (0:ℝ) < 1/((n:ℝ)+2) := fun n => by positivity
  have hη1 : ∀ n : ℕ, (1:ℝ)/((n:ℝ)+2) < 1 := fun n => by
    rw [div_lt_one (by positivity : (0:ℝ) < (n:ℝ) + 2)]
    have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith
  have hFx : ∀ n x, F n x ≤ 1 - 1/((n:ℝ)+2) := fun n x => by
    have h1 : 1/((n:ℝ)+2) ≤ 1/((n:ℝ)+1) :=
      one_div_le_one_div_of_le (by positivity : (0:ℝ) < (n:ℝ)+1) (by linarith)
    linarith [hF1 n x, h1]
  have hGx : ∀ n x, G n x ≤ 1 - 1/((n:ℝ)+2) := fun n x => by
    have h1 : 1/((n:ℝ)+2) ≤ 1/((n:ℝ)+1) :=
      one_div_le_one_div_of_le (by positivity : (0:ℝ) < (n:ℝ)+1) (by linarith)
    linarith [hG1 n x, h1]
  have hFlim' : Tendsto (fun n => ∫ x, F n x * gdens x) atTop (nhds (∫ x, f x * gdens x)) := by
    simpa only [gaussMeasure_integral] using hFlim
  have hGlim' : Tendsto (fun n => ∫ x, G n x * gdens x) atTop (nhds (∫ x, g x * gdens x)) := by
    simpa only [gaussMeasure_integral] using hGlim
  have hFev : ∀ᶠ n in atTop, 0 < ∫ x, F n x * gdens x := hFlim'.eventually (Ioi_mem_nhds hA0)
  have hGev : ∀ᶠ n in atTop, 0 < ∫ x, G n x * gdens x := hGlim'.eventually (Ioi_mem_nhds hB0)
  have hkey : ∀ᶠ n in atTop,
      gPhi (lam * gphi (∫ x, F n x * gdens x) + (1 - lam) * gphi (∫ x, G n x * gdens x))
        ≤ ∫ x, h x * gdens x :=
    (hFev.and hGev).mono (fun n hn => ehrhard_measurable_step hl0 hl1 hf hg hhm hf0 hf1 hg0 hg1
      hh0 hhb hcond hFusc hF0 hFle hFK hF1 hGusc hG0 hGle hGK hG1 n hn.1 hn.2)
  by_cases hcase : (∫ x, f x * gdens x) = 1 ∨ (∫ x, g x * gdens x) = 1
  · have hcle : 1 ≤ ∫ x, h x * gdens x := by
      rcases hcase with hf1 | hg1
      · have hFlt : ∀ n, ∫ x, F n x * gdens x < 1 := fun n =>
          lt_of_le_of_lt (integral_mul_gdens_le (hFusc n).measurable (hF0 n) (hη0 n) (hη1 n)
            (hFx n)) (sub_lt_self 1 (hη0 n))
        have hFlim1 : Tendsto (fun n => ∫ x, F n x * gdens x) atTop (nhdsWithin 1 (Set.Iio 1)) := by
          rw [tendsto_nhdsWithin_iff]
          exact ⟨by rw [← hf1]; exact hFlim', Filter.Eventually.of_forall hFlt⟩
        have hAtop : Tendsto (fun n => gphi (∫ x, F n x * gdens x)) atTop atTop :=
          tendsto_gphi_nhdsWithin_one.comp hFlim1
        have hBg : ∀ᶠ n in atTop,
            gphi ((∫ x, g x * gdens x) / 2) ≤ gphi (∫ x, G n x * gdens x) := by
          have h1 : ∀ᶠ n in atTop, (∫ x, g x * gdens x) / 2 ≤ ∫ x, G n x * gdens x :=
            hGlim'.eventually (Ici_mem_nhds (half_lt_self hB0))
          filter_upwards [h1] with n hn
          have hGl : ∫ x, G n x * gdens x < 1 :=
            lt_of_le_of_lt (integral_mul_gdens_le (hGusc n).measurable (hG0 n) (hη0 n) (hη1 n)
              (hGx n)) (sub_lt_self 1 (hη0 n))
          exact gphi_le_of_le (half_pos hB0) hGl hn
        have hR : ∀ R : ℝ, gPhi R ≤ ∫ x, h x * gdens x := by
          intro R
          have hAev : ∀ᶠ n in atTop,
              (R - (1 - lam) * gphi ((∫ x, g x * gdens x) / 2)) / lam
                ≤ gphi (∫ x, F n x * gdens x) :=
            (tendsto_atTop.mp hAtop) ((R - (1 - lam) * gphi ((∫ x, g x * gdens x) / 2)) / lam)
          obtain ⟨n, hn⟩ := ((hkey.and hAev).and hBg).exists
          obtain ⟨⟨hkn, hAn⟩, hBn⟩ := hn
          have hge : R ≤ lam * gphi (∫ x, F n x * gdens x)
              + (1 - lam) * gphi (∫ x, G n x * gdens x) := by
            have h1 := mul_le_mul_of_nonneg_left hAn hl0.le
            have h2 := mul_le_mul_of_nonneg_left hBn (by linarith : (0:ℝ) ≤ 1 - lam)
            have h3 : lam * ((R - (1 - lam) * gphi ((∫ x, g x * gdens x) / 2)) / lam)
                = R - (1 - lam) * gphi ((∫ x, g x * gdens x) / 2) :=
              mul_div_cancel₀ _ (ne_of_gt hl0)
            linarith
          exact le_trans (gPhi_strictMono.monotone hge) hkn
        exact le_of_tendsto gPhi_tendsto_atTop (Filter.Eventually.of_forall hR)
      · have hGlt : ∀ n, ∫ x, G n x * gdens x < 1 := fun n =>
          lt_of_le_of_lt (integral_mul_gdens_le (hGusc n).measurable (hG0 n) (hη0 n) (hη1 n)
            (hGx n)) (sub_lt_self 1 (hη0 n))
        have hGlim1 : Tendsto (fun n => ∫ x, G n x * gdens x) atTop (nhdsWithin 1 (Set.Iio 1)) := by
          rw [tendsto_nhdsWithin_iff]
          exact ⟨by rw [← hg1]; exact hGlim', Filter.Eventually.of_forall hGlt⟩
        have hBtop : Tendsto (fun n => gphi (∫ x, G n x * gdens x)) atTop atTop :=
          tendsto_gphi_nhdsWithin_one.comp hGlim1
        have hAf : ∀ᶠ n in atTop,
            gphi ((∫ x, f x * gdens x) / 2) ≤ gphi (∫ x, F n x * gdens x) := by
          have h1 : ∀ᶠ n in atTop, (∫ x, f x * gdens x) / 2 ≤ ∫ x, F n x * gdens x :=
            hFlim'.eventually (Ici_mem_nhds (half_lt_self hA0))
          filter_upwards [h1] with n hn
          have hFl : ∫ x, F n x * gdens x < 1 :=
            lt_of_le_of_lt (integral_mul_gdens_le (hFusc n).measurable (hF0 n) (hη0 n) (hη1 n)
              (hFx n)) (sub_lt_self 1 (hη0 n))
          exact gphi_le_of_le (half_pos hA0) hFl hn
        have hR : ∀ R : ℝ, gPhi R ≤ ∫ x, h x * gdens x := by
          intro R
          have hBev : ∀ᶠ n in atTop,
              (R - lam * gphi ((∫ x, f x * gdens x) / 2)) / (1 - lam)
                ≤ gphi (∫ x, G n x * gdens x) :=
            (tendsto_atTop.mp hBtop) ((R - lam * gphi ((∫ x, f x * gdens x) / 2)) / (1 - lam))
          obtain ⟨n, hn⟩ := ((hkey.and hBev).and hAf).exists
          obtain ⟨⟨hkn, hBn⟩, hAn⟩ := hn
          have hge : R ≤ lam * gphi (∫ x, F n x * gdens x)
              + (1 - lam) * gphi (∫ x, G n x * gdens x) := by
            have h1 := mul_le_mul_of_nonneg_left hBn (by linarith : (0:ℝ) ≤ 1 - lam)
            have h2 := mul_le_mul_of_nonneg_left hAn hl0.le
            have h3 : (1 - lam) * ((R - lam * gphi ((∫ x, f x * gdens x) / 2)) / (1 - lam))
                = R - lam * gphi ((∫ x, f x * gdens x) / 2) :=
              mul_div_cancel₀ _ (ne_of_gt (by linarith : (0:ℝ) < 1 - lam))
            linarith
          exact le_trans (gPhi_strictMono.monotone hge) hkn
        exact le_of_tendsto gPhi_tendsto_atTop (Filter.Eventually.of_forall hR)
    calc gPhi (lam * a + (1 - lam) * b) ≤ 1 := (gPhi_lt_one _).le
      _ ≤ ∫ x, h x * gdens x := hcle
  · push_neg at hcase
    have hflt : ∫ x, f x * gdens x < 1 := lt_of_le_of_ne hA1 hcase.1
    have hglt : ∫ x, g x * gdens x < 1 := lt_of_le_of_ne hB1 hcase.2
    have hAt : Tendsto (fun n => gphi (∫ x, F n x * gdens x)) atTop
        (nhds (gphi (∫ x, f x * gdens x))) := by
      have h1 : Tendsto gphi (nhds (∫ x, f x * gdens x)) (nhds (gphi (∫ x, f x * gdens x))) :=
        (gphi_continuousAt (∫ x, f x * gdens x) hA0 hflt).tendsto
      exact h1.comp hFlim'
    have hBt : Tendsto (fun n => gphi (∫ x, G n x * gdens x)) atTop
        (nhds (gphi (∫ x, g x * gdens x))) := by
      have h1 : Tendsto gphi (nhds (∫ x, g x * gdens x)) (nhds (gphi (∫ x, g x * gdens x))) :=
        (gphi_continuousAt (∫ x, g x * gdens x) hB0 hglt).tendsto
      exact h1.comp hGlim'
    have hLt : Tendsto (fun n => gPhi (lam * gphi (∫ x, F n x * gdens x)
        + (1 - lam) * gphi (∫ x, G n x * gdens x))) atTop
        (nhds (gPhi (lam * gphi (∫ x, f x * gdens x) + (1 - lam) * gphi (∫ x, g x * gdens x)))) :=
      (gPhi_continuous.tendsto _).comp (Filter.Tendsto.add
        (Filter.Tendsto.const_mul lam hAt) (Filter.Tendsto.const_mul (1 - lam) hBt))
    have hlim : gPhi (lam * gphi (∫ x, f x * gdens x) + (1 - lam) * gphi (∫ x, g x * gdens x))
        ≤ ∫ x, h x * gdens x := le_of_tendsto hLt hkey
    have ha' : a ≤ gphi (∫ x, f x * gdens x) := by
      have h2 : gPhi a ≤ gPhi (gphi (∫ x, f x * gdens x)) := by
        rw [gphi_spec _ hA0 hflt]; exact ha
      exact gPhi_strictMono.le_iff_le.mp h2
    have hb' : b ≤ gphi (∫ x, g x * gdens x) := by
      have h2 : gPhi b ≤ gPhi (gphi (∫ x, g x * gdens x)) := by
        rw [gphi_spec _ hB0 hglt]; exact hb
      exact gPhi_strictMono.le_iff_le.mp h2
    refine le_trans ?_ hlim
    apply gPhi_strictMono.monotone
    have h1 := mul_le_mul_of_nonneg_left ha' hl0.le
    have h2 := mul_le_mul_of_nonneg_left hb' (by linarith : (0:ℝ) ≤ 1 - lam)
    linarith

lemma exists_pos_of_integral_pos {q : ℝ → ℝ} (hq0 : ∀ x, 0 ≤ q x)
    (h : 0 < ∫ x, q x * gdens x) : ∃ s, 0 < q s := by
  by_contra hcon
  push_neg at hcon
  have hz : q = fun _ => 0 := funext (fun x => le_antisymm (hcon x) (hq0 x))
  rw [hz] at h; simp at h

/-- **One-dimensional functional Ehrhard inequality.** -/
theorem ehrhard_functional_1d
    (f g h : ℝ → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1)
    (hh0 : ∀ x, 0 ≤ h x) (hh1 : ∀ x, h x ≤ 1)
    (lam : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1)
    (hcond : ∀ a b s t,
       (∫ x in Set.Iic a, Real.exp (-Real.pi * x ^ 2)) ≤ f s →
       (∫ x in Set.Iic b, Real.exp (-Real.pi * x ^ 2)) ≤ g t →
       (∫ x in Set.Iic (lam * a + (1 - lam) * b), Real.exp (-Real.pi * x ^ 2)) ≤ h (lam * s + (1 - lam) * t)) :
    ∀ a b,
       (∫ x in Set.Iic a, Real.exp (-Real.pi * x ^ 2)) ≤ ∫ x, f x * Real.exp (-Real.pi * x ^ 2) →
       (∫ x in Set.Iic b, Real.exp (-Real.pi * x ^ 2)) ≤ ∫ x, g x * Real.exp (-Real.pi * x ^ 2) →
       (∫ x in Set.Iic (lam * a + (1 - lam) * b), Real.exp (-Real.pi * x ^ 2)) ≤
         ∫ x, h x * Real.exp (-Real.pi * x ^ 2) := by
  have hcond' : ∀ a b s t, gPhi a ≤ f s → gPhi b ≤ g t →
      gPhi (lam * a + (1 - lam) * b) ≤ h (lam * s + (1 - lam) * t) := hcond
  show ∀ a b, gPhi a ≤ ∫ x, f x * gdens x → gPhi b ≤ ∫ x, g x * gdens x →
      gPhi (lam * a + (1 - lam) * b) ≤ ∫ x, h x * gdens x
  intro a b ha hb
  rcases eq_or_lt_of_le hl0 with h0 | h0
  · subst h0
    have hb' : gPhi b ≤ ∫ x, h x * gdens x := by
      have hA0 : 0 < ∫ x, f x * gdens x := lt_of_lt_of_le (gPhi_pos a) ha
      obtain ⟨s₀, hs₀⟩ := exists_pos_of_integral_pos hf0 hA0
      obtain ⟨a₀, ha₀lt⟩ := (gPhi_tendsto_atBot.eventually (Iio_mem_nhds hs₀)).exists
      have ha₀ : gPhi a₀ ≤ f s₀ := ha₀lt.le
      have hgt : ∀ t, g t ≤ h t := by
        intro t
        rcases lt_or_eq_of_le (hg1 t) with hlt | heq
        · rcases eq_or_lt_of_le (hg0 t) with h0' | hpos
          · rw [← h0']; exact hh0 t
          · have h1 : gPhi (gphi (g t)) ≤ h t := by
              have h2 := hcond' a₀ (gphi (g t)) s₀ t ha₀
                (le_of_eq (gphi_spec (g t) hpos hlt))
              simpa only [zero_mul, sub_zero, one_mul, add_zero, zero_add] using h2
            rwa [gphi_spec (g t) hpos hlt] at h1
        · rw [heq]
          refine le_of_tendsto gPhi_tendsto_atTop ?_
          filter_upwards with b'
          have h2 := hcond' a₀ b' s₀ t ha₀ ((gPhi_lt_one b').le.trans (le_of_eq heq.symm))
          simpa only [zero_mul, sub_zero, one_mul, add_zero, zero_add] using h2
      calc gPhi b = gPhi b := rfl
        _ ≤ ∫ x, g x * gdens x := hb
        _ ≤ ∫ x, h x * gdens x := integral_mono
            (integrable_mul_gauss hg (fun x => by
              rw [abs_of_nonneg (hg0 x)]; linarith [hg1 x]))
            (integrable_mul_gauss hh (fun x => by
              rw [abs_of_nonneg (hh0 x)]; linarith [hh1 x]))
            (fun x => mul_le_mul_of_nonneg_right (hgt x) (gdens_pos x).le)
    simpa only [zero_mul, sub_zero, one_mul, add_zero, zero_add] using hb'
  · rcases eq_or_lt_of_le hl1 with h1 | h1
    · subst h1
      have ha' : gPhi a ≤ ∫ x, h x * gdens x := by
        have hB0 : 0 < ∫ x, g x * gdens x := lt_of_lt_of_le (gPhi_pos b) hb
        obtain ⟨t₀, ht₀⟩ := exists_pos_of_integral_pos hg0 hB0
        obtain ⟨b₀, hb₀lt⟩ := (gPhi_tendsto_atBot.eventually (Iio_mem_nhds ht₀)).exists
        have hb₀ : gPhi b₀ ≤ g t₀ := hb₀lt.le
        have hft : ∀ s, f s ≤ h s := by
          intro s
          rcases lt_or_eq_of_le (hf1 s) with hlt | heq
          · rcases eq_or_lt_of_le (hf0 s) with h0' | hpos
            · rw [← h0']; exact hh0 s
            · have h2 : gPhi (gphi (f s)) ≤ h s := by
                have h3 := hcond' (gphi (f s)) b₀ s t₀
                  (le_of_eq (gphi_spec (f s) hpos hlt)) hb₀
                simpa only [one_mul, sub_self, zero_mul, add_zero] using h3
              rwa [gphi_spec (f s) hpos hlt] at h2
          · rw [heq]
            refine le_of_tendsto gPhi_tendsto_atTop ?_
            filter_upwards with a'
            have h3 := hcond' a' b₀ s t₀ ((gPhi_lt_one a').le.trans (le_of_eq heq.symm)) hb₀
            simpa only [one_mul, sub_self, zero_mul, add_zero] using h3
        calc gPhi a = gPhi a := rfl
          _ ≤ ∫ x, f x * gdens x := ha
          _ ≤ ∫ x, h x * gdens x := integral_mono
              (integrable_mul_gauss hf (fun x => by
                rw [abs_of_nonneg (hf0 x)]; linarith [hf1 x]))
              (integrable_mul_gauss hh (fun x => by
                rw [abs_of_nonneg (hh0 x)]; linarith [hh1 x]))
              (fun x => mul_le_mul_of_nonneg_right (hft x) (gdens_pos x).le)
      simpa only [one_mul, sub_self, zero_mul, add_zero] using ha'
    · exact ehrhard_measurable_main h0 h1 hf hg hh hf0 hf1 hg0 hg1 hh0
        (fun x => by rw [abs_of_nonneg (hh0 x)]; exact hh1 x) hcond' a b ha hb

end Commons.Analysis.GaussianMeasure