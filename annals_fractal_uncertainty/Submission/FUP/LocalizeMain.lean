import Submission.FUP.LocalizeEntire
import Submission.FUP.LocalizeScaleAux
import Submission.Commons.Analysis.Fourier.strip_lintegral_entire_le
import Submission.Commons.Analysis.Fourier.truncation_high_le
import Submission.Commons.Analysis.Fourier.truncation_low_le
import Submission.Commons.Analysis.Fourier.exists_compactlySupported_kernel_of_bandlimited
import Submission.Commons.Analysis.Fourier.LogvinenkoSereda.bandlimited_entire_extension_cube

open MeasureTheory Metric Set Complex Filter
open scoped ENNReal BigOperators Topology FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Han–Schlag §4: the single-scale localisation estimate and its modulation sum

This module assembles Han–Schlag's Lemma 4.3 (`lem:mainlem`) and Corollary 4.2 (`cor:UPY`)
from the band-limit-free localisation estimate `localization_entire`.  See
`Submission/FUP/ROADMAP.md`, Session 60 §3 for the plan (`P1`–`P6`).
-/

namespace Submission.FUP

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)


/-! ## Transfer between `EuclideanSpace ℝ (Fin d)` and `Fin d → ℝ` -/

/-- Transfer of an `lintegral` between `EuclideanSpace ℝ (Fin d)` and `Fin d → ℝ`. -/
lemma lintegral_euclidean_eq_pi {φ : (Fin d → ℝ) → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ x : ℝᵈ, φ (fun i => x i) = ∫⁻ x : Fin d → ℝ, φ x :=
  (PiLp.volume_preserving_ofLp (Fin d)).lintegral_comp hφ

/-- Transfer of a set-`lintegral` between `EuclideanSpace ℝ (Fin d)` and `Fin d → ℝ`. -/
lemma lintegral_set_euclidean_eq_pi {S : Set (Fin d → ℝ)} (hS : MeasurableSet S)
    {φ : (Fin d → ℝ) → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ y : ℝᵈ in {y : ℝᵈ | (fun i => y i) ∈ S}, φ (fun i => y i)
      = ∫⁻ x : Fin d → ℝ in S, φ x := by
  have hset : ∀ y : ℝᵈ, ({y : ℝᵈ | (fun i => y i) ∈ S}).indicator (fun y => φ (fun i => y i)) y
      = S.indicator φ (fun i => y i) := by
    intro y
    have hy' : y ∈ {y : ℝᵈ | (fun i => y i) ∈ S} ↔ (fun i => y i) ∈ S := Iff.rfl
    by_cases hy : (fun i => y i) ∈ S
    · rw [Set.indicator_of_mem (hy'.mpr hy), Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem (fun h => hy (hy'.mp h)), Set.indicator_of_notMem hy]
  have hmeas : MeasurableSet {y : ℝᵈ | (fun i => y i) ∈ S} :=
    hS.preimage (WithLp.measurable_ofLp 2 (Fin d → ℝ))
  rw [← lintegral_indicator hmeas]
  simp only [hset]
  rw [← lintegral_indicator hS]
  exact lintegral_euclidean_eq_pi (hφ.indicator hS)

/-- **`localization_entire` in the coordinates of `EuclideanSpace ℝ (Fin d)`.** -/
theorem localization_entire_euclidean {q ε δ H η c₁ r : ℝ} {γ : ℝᵈ}
    (hd : 1 ≤ d) (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hδ0 : 0 < δ) (hδ3 : δ < 1 / 3) (hH0 : 0 < H) (hH1 : H ≤ 1)
    (hη0 : 0 < η) (hc₁ : 0 < c₁) (hr0 : 0 < r)
    (hητ : 1 ≤ η * phiLens q ε (1 - 3 * δ))
    (hIbig : ENNReal.ofReal ((η * zpLamMax q ε) ^ d * (2 * (20 ^ d * H)))
      ≤ ENNReal.ofReal ((2 * c₁) ^ d))
    {F : (Fin d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F Set.univ)
    (a : (Fin d → ℤ) → Fin d → ℝ)
    (ha : ∀ n : Fin d → ℤ, ∀ i : Fin d,
      2 * (n i : ℝ) + γ i ≤ a n i ∧ a n i + 2 * c₁ ≤ 2 * (n i : ℝ) + γ i + 2) :
    ∫⁻ x : ℝᵈ, ENNReal.ofReal (‖F (fun i => (x i : ℂ))‖ ^ 2)
      ≤ ENNReal.ofReal (cellZConst q ε δ H η c₁ d)
        * (ENNReal.ofReal ((η * phiLens q ε 1 + r + 1) ^ d * ((Real.pi * r ^ 2) ^ d)⁻¹)
          * ∫⁻ z in {z : Fin d → ℂ | ∀ i, |(z i).im| ≤ η * q + r}, ENNReal.ofReal (‖F z‖ ^ 2))
          ^ (1 - zpKappa δ H d)
        * (∫⁻ x in locCubes c₁ a, ENNReal.ofReal (‖F (fun i => (x i : ℂ))‖ ^ 2))
            ^ (zpKappa δ H d) := by
  classical
  have hFc : Continuous F := (differentiableOn_univ.mp hF.differentiableOn).continuous
  have hmeasψ : Measurable (fun x : Fin d → ℝ =>
      ENNReal.ofReal (‖F (fun i => (x i : ℂ))‖ ^ 2)) :=
    ((hFc.measurable.comp (measurable_pi_lambda _ (fun i =>
      Complex.measurable_ofReal.comp (measurable_pi_apply i)))).norm.pow_const 2).ennreal_ofReal
  have hmain := localization_entire (d := d) (F := F) hd hq hε0 hε1 hδ0 hδ3 hH0 hH1 hη0 hc₁ hr0
    hητ hIbig hF (a := a) ha
  have h1 : ∫⁻ x : ℝᵈ, ENNReal.ofReal (‖F (fun i => (x i : ℂ))‖ ^ 2)
      = ∫⁻ x : Fin d → ℝ, ENNReal.ofReal (‖F (fun i => (x i : ℂ))‖ ^ 2) :=
    lintegral_euclidean_eq_pi hmeasψ
  have h2 : ∫⁻ x in locCubes c₁ a, ENNReal.ofReal (‖F (fun i => (x i : ℂ))‖ ^ 2)
      = ∫⁻ x in (⋃ n : Fin d → ℤ,
            Set.pi Set.univ (fun i : Fin d => Set.Icc (a n i) (a n i + 2 * c₁))),
          ENNReal.ofReal (‖F (fun i => (x i : ℂ))‖ ^ 2) := by
    have hset : locCubes c₁ a
        = {y : ℝᵈ | (fun i => y i) ∈ (⋃ n : Fin d → ℤ,
            Set.pi Set.univ (fun i : Fin d => Set.Icc (a n i) (a n i + 2 * c₁)))} := by
      ext y
      simp only [mem_locCubes, Set.mem_iUnion, Set.mem_pi, Set.mem_univ, true_implies,
        Set.mem_Icc, Set.mem_setOf_eq]
    rw [hset]
    exact lintegral_set_euclidean_eq_pi
      (MeasurableSet.iUnion fun n => MeasurableSet.univ_pi fun i => measurableSet_Icc)
      hmeasψ
  calc ∫⁻ x : ℝᵈ, ENNReal.ofReal (‖F (fun i => (x i : ℂ))‖ ^ 2)
      = ∫⁻ x : Fin d → ℝ, ENNReal.ofReal (‖F (fun i => (x i : ℂ))‖ ^ 2) := h1
    _ ≤ ENNReal.ofReal (cellZConst q ε δ H η c₁ d)
        * (ENNReal.ofReal ((η * phiLens q ε 1 + r + 1) ^ d * ((Real.pi * r ^ 2) ^ d)⁻¹)
          * ∫⁻ z in {z : Fin d → ℂ | ∀ i, |(z i).im| ≤ η * q + r}, ENNReal.ofReal (‖F z‖ ^ 2))
          ^ (1 - zpKappa δ H d)
        * (∫⁻ x in (⋃ n : Fin d → ℤ,
              Set.pi Set.univ (fun i : Fin d => Set.Icc (a n i) (a n i + 2 * c₁))),
            ENNReal.ofReal (‖F (fun i => (x i : ℂ))‖ ^ 2)) ^ (zpKappa δ H d) := hmain
    _ = ENNReal.ofReal (cellZConst q ε δ H η c₁ d)
        * (ENNReal.ofReal ((η * phiLens q ε 1 + r + 1) ^ d * ((Real.pi * r ^ 2) ^ d)⁻¹)
          * ∫⁻ z in {z : Fin d → ℂ | ∀ i, |(z i).im| ≤ η * q + r}, ENNReal.ofReal (‖F z‖ ^ 2))
          ^ (1 - zpKappa δ H d)
        * (∫⁻ x in locCubes c₁ a, ENNReal.ofReal (‖F (fun i => (x i : ℂ))‖ ^ 2))
            ^ (zpKappa δ H d) := by
        rw [h2]


/-! ## The localisation bound: `‖1_{S'} (k * φ)‖ ≤ ‖1_S k‖_{H^{-d}}` -/

/-- **The localisation bound of Han–Schlag's Lemma 4.3.**  If `φ` is supported in the cube of
radius `c₁/2` and `‖𝓕φ ξ‖ ≤ ⟨ξ⟩^{-d}`, then the `L²` mass of `k * φ` on the concentric
sub-cubes `S'` is bounded by the squared `H^{-d}` norm of `1_S k`. -/
theorem localisation_bound {c₁ : ℝ} (hc₁ : 0 < c₁) {φ : ℝᵈ → ℂ} (hφ1 : MemLp φ 1 (volume : Measure ℝᵈ))
    (hφ2 : MemLp φ 2 (volume : Measure ℝᵈ))
    (hφsupp : ∀ᵐ z ∂(volume : Measure ℝᵈ), (∃ i : Fin d, c₁ / 2 < |z i|) → φ z = 0)
    (hφb : ∀ ξ, ‖𝓕 φ ξ‖ ≤ 1)
    (hφw : ∀ᵐ ξ ∂(volume : Measure ℝᵈ), ‖𝓕 φ ξ‖ ≤ (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ) / 2))
    (a : (Fin d → ℤ) → Fin d → ℝ) (k : Lp ℂ 2 (volume : Measure ℝᵈ)) :
    ∫⁻ x in locCubesSmall c₁ a,
        ENNReal.ofReal (‖Commons.Analysis.Fourier.convFun (k : ℝᵈ → ℂ) φ x‖ ^ 2)
      ≤ ENNReal.ofReal (hsq (subLp (locCubes c₁ a) k (measurableSet_locCubes c₁ a))) := by
  classical
  set kS : Lp ℂ 2 (volume : Measure ℝᵈ) :=
    subLp (locCubes c₁ a) k (measurableSet_locCubes c₁ a) with hkS
  have hkScoe : (kS : ℝᵈ → ℂ) =ᵐ[volume] (locCubes c₁ a).indicator (k : ℝᵈ → ℂ) :=
    subLp_coe _ _ _
  have hconv_eq : Commons.Analysis.Fourier.convFun (kS : ℝᵈ → ℂ) φ
      = Commons.Analysis.Fourier.convFun ((locCubes c₁ a).indicator (k : ℝᵈ → ℂ)) φ :=
    Commons.Analysis.Fourier.convFun_congr_ae hkScoe
  set gLp : Lp ℂ 2 (volume : Measure ℝᵈ) :=
    (Commons.Analysis.Fourier.memLp_convFun_two (Lp.memLp kS)
      (integrable_of_memLp_one hφ1)).toLp
      (Commons.Analysis.Fourier.convFun (kS : ℝᵈ → ℂ) φ) with hgLp
  have hgcoe : (gLp : ℝᵈ → ℂ) =ᵐ[volume]
      Commons.Analysis.Fourier.convFun (kS : ℝᵈ → ℂ) φ := MemLp.coeFn_toLp _
  have hbound : ‖gLp‖ ^ 2 ≤ hsq kS :=
    norm_convFun_le_hsq kS φ hφ1 hφ2 hφb hφw
  have hIntLp : Integrable (fun x : ℝᵈ => ‖(gLp : ℝᵈ → ℂ) x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp gLp).aestronglyMeasurable).mp (Lp.memLp gLp)
  have hInt : Integrable (fun x : ℝᵈ =>
      ‖Commons.Analysis.Fourier.convFun (kS : ℝᵈ → ℂ) φ x‖ ^ 2) volume :=
    hIntLp.congr (by
      filter_upwards [hgcoe] with x hx
      rw [hx])
  calc ∫⁻ x in locCubesSmall c₁ a,
        ENNReal.ofReal (‖Commons.Analysis.Fourier.convFun (k : ℝᵈ → ℂ) φ x‖ ^ 2)
      = ∫⁻ x in locCubesSmall c₁ a,
          ENNReal.ofReal (‖Commons.Analysis.Fourier.convFun
            ((locCubes c₁ a).indicator (k : ℝᵈ → ℂ)) φ x‖ ^ 2) := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_restrict_mem (measurableSet_locCubesSmall c₁ a)] with x hx
        rw [convFun_indicator_eq hc₁ φ hφsupp a (k : ℝᵈ → ℂ) x hx]
    _ = ∫⁻ x in locCubesSmall c₁ a,
          ENNReal.ofReal (‖Commons.Analysis.Fourier.convFun (kS : ℝᵈ → ℂ) φ x‖ ^ 2) := by
        rw [hconv_eq]
    _ ≤ ∫⁻ x in (Set.univ : Set ℝᵈ), ENNReal.ofReal
          (‖Commons.Analysis.Fourier.convFun (kS : ℝᵈ → ℂ) φ x‖ ^ 2) :=
        lintegral_mono_set (subset_univ _)
    _ = ENNReal.ofReal (∫ x : ℝᵈ,
          ‖Commons.Analysis.Fourier.convFun (kS : ℝᵈ → ℂ) φ x‖ ^ 2) := by
        rw [Measure.restrict_univ]
        exact (ofReal_integral_eq_lintegral_ofReal hInt (ae_of_all _ (fun x => by positivity))).symm
    _ = ENNReal.ofReal (∫ x : ℝᵈ, ‖(gLp : ℝᵈ → ℂ) x‖ ^ 2) := by
        congr 1
        refine integral_congr_ae ?_
        filter_upwards [hgcoe] with x hx
        rw [hx]
    _ = ENNReal.ofReal (‖gLp‖ ^ 2) := by
        rw [Commons.Analysis.Fourier.lp_integral_norm_sq gLp]
    _ ≤ ENNReal.ofReal (hsq kS) := ENNReal.ofReal_le_ofReal hbound

end Submission.FUP
