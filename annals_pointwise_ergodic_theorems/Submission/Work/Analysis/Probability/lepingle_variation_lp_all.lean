import Mathlib
import Submission.Commons.Analysis.Probability.lepingle_variation_ls_all_s
import Submission.Commons.Analysis.Probability.lepingle_variation_sigma_finite_ls
import Submission.Port.Aesm

open MeasureTheory Filter
open scoped ENNReal BigOperators Topology

namespace Commons.Analysis.Probability

namespace LepLp

set_option maxHeartbeats 1600000 in
/-- Decoupled `Ztr` bound: the variation exponent `r` only enters the geometric weights,
while the square-function estimate is used at the martingale exponent `p > 2`. -/
lemma eLpNorm_Ztr_le_decoup {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SigmaFinite μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) [SigmaFiniteFiltration μ ℱ] (f : Ω → ℝ) {r p : ℝ}
    (hr0 : 0 < r) (hr2 : 2 < r) (hp0 : 0 < p) (hp2 : 2 < p)
    (hf : MemLp f (ENNReal.ofReal p) μ) (hfi : Integrable f μ) (N : ℕ) :
    eLpNorm (SFTest.Ztr (fun n => condExp (ℱ n) μ f) r N) (ENNReal.ofReal (p/2)) μ
      ≤ ENNReal.ofReal (lepG r) * ENNReal.ofReal (SFTest.bdgZZ p)
          * (eLpNorm f (ENNReal.ofReal p) μ)^2 := by
  haveI : SigmaFiniteFiltration μ ℱ := ⟨fun _ => inferInstance⟩
  have hgm : ∀ n, Measurable[ℱ n] (condExp (ℱ n) μ f) :=
    fun n => (stronglyMeasurable_condExp (m := ℱ n)).measurable
  have hq0 : ENNReal.ofReal (p/2) ≠ 0 := by rw [ENNReal.ofReal_ne_zero_iff]; linarith
  have hqT : ENNReal.ofReal (p/2) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmono : Monotone (fun M : ℕ => fun ω =>
      ENNReal.ofReal (SFTest.Zterm (fun n => condExp (ℱ n) μ f) r N M ω)) := by
    intro a b hab ω
    exact ENNReal.ofReal_le_ofReal (SFTest.Zterm_mono (fun n => condExp (ℱ n) μ f) r N hab ω)
  have hkey : eLpNorm (fun ω => ⨆ M : ℕ,
        ENNReal.ofReal (SFTest.Zterm (fun n => condExp (ℱ n) μ f) r N M ω))
        (ENNReal.ofReal (p/2)) μ
      = ⨆ M : ℕ, eLpNorm (fun ω => ENNReal.ofReal
          (SFTest.Zterm (fun n => condExp (ℱ n) μ f) r N M ω)) (ENNReal.ofReal (p/2)) μ :=
    Commons.Analysis.MeasureTheory.eLpNorm_iSup_of_monotone hq0 hqT
      (fun M => (SFTest.measurable_Zterm ℱ _ hgm r N M).ennreal_ofReal) hmono
  rw [show SFTest.Ztr (fun n => condExp (ℱ n) μ f) r N = fun ω => ⨆ M : ℕ,
      ENNReal.ofReal (SFTest.Zterm (fun n => condExp (ℱ n) μ f) r N M ω) from rfl, hkey]
  refine iSup_le (fun M => ?_)
  have hsum : ∀ m ∈ Finset.Icc 2 M, AEMeasurable (fun ω =>
      ENNReal.ofReal ((1/2:ℝ)^((m-2)*(r-2))) * SFTest.Ssq (SFTest.sm (fun n => condExp (ℱ n) μ f) N m) ω) μ := by
    intro m hm
    exact ((SFTest.measurable_Ssq_sm ℱ _ hgm N m).const_mul
      (ENNReal.ofReal ((1/2:ℝ)^((m-2)*(r-2))))).aemeasurable
  have h1p : (1:ℝ≥0∞) ≤ ENNReal.ofReal (p/2) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith : (1:ℝ) ≤ p/2)
  have hp1 : (1:ℝ) < p := by linarith
  have hpq : ENNReal.ofReal p ≠ 0 := by rw [ENNReal.ofReal_ne_zero_iff]; linarith
  have hpTq : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hqq : ENNReal.ofReal (p/2) ≠ 0 := hq0
  have hqqT : ENNReal.ofReal (p/2) ≠ ⊤ := hqT
  refine le_trans (le_of_eq ?_) (le_trans
    (Commons.MeasureTheory.Lp.eLpNorm_finset_sum_le_ennreal h1p hsum) ?_)
  · refine eLpNorm_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
    exact SFTest.ofReal_Zterm_eq _ r N M ω
  · calc ∑ m ∈ Finset.Icc 2 M, eLpNorm (fun ω =>
          ENNReal.ofReal ((1/2:ℝ)^((m-2)*(r-2))) * SFTest.Ssq (SFTest.sm (fun n => condExp (ℱ n) μ f) N m) ω)
          (ENNReal.ofReal (p/2)) μ
        ≤ ∑ m ∈ Finset.Icc 2 M, ENNReal.ofReal ((1/2:ℝ)^((m-2)*(r-2))) *
            (ENNReal.ofReal (SFTest.bdgZZ p) * (eLpNorm f (ENNReal.ofReal p) μ)^2) := by
          refine Finset.sum_le_sum (fun m hm => ?_)
          rw [Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal
            (c := ENNReal.ofReal ((1/2:ℝ)^((m-2)*(r-2))))
            (V := SFTest.Ssq (SFTest.sm (fun n => condExp (ℱ n) μ f) N m)) ENNReal.ofReal_ne_top hq0 hqT]
          exact mul_le_mul_of_nonneg_left (SFTest.bdg_sm_sq ℱ f hp0 hp1 hp2 hf hfi N m) zero_le
      _ = (∑ m ∈ Finset.Icc 2 M, ENNReal.ofReal ((1/2:ℝ)^((m-2)*(r-2)))) *
            (ENNReal.ofReal (SFTest.bdgZZ p) * (eLpNorm f (ENNReal.ofReal p) μ)^2) := by
          rw [Finset.sum_mul]
      _ = ENNReal.ofReal (∑ m ∈ Finset.Icc 2 M, (1/2:ℝ)^((m-2)*(r-2))) *
            (ENNReal.ofReal (SFTest.bdgZZ p) * (eLpNorm f (ENNReal.ofReal p) μ)^2) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun m _ => Real.rpow_nonneg (by norm_num) _)]
      _ ≤ ENNReal.ofReal (lepG r) *
            (ENNReal.ofReal (SFTest.bdgZZ p) * (eLpNorm f (ENNReal.ofReal p) μ)^2) := by
          refine mul_le_mul_of_nonneg_right ?_ zero_le
          exact ENNReal.ofReal_le_ofReal (geom_bound_gen hr2 M)
      _ = ENNReal.ofReal (lepG r) * ENNReal.ofReal (SFTest.bdgZZ p)
            * (eLpNorm f (ENNReal.ofReal p) μ)^2 := by ring

set_option maxHeartbeats 1600000 in
lemma eLpNorm_Vtr_le_decoup {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SigmaFinite μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) [SigmaFiniteFiltration μ ℱ] (f : Ω → ℝ) {r p : ℝ}
    (hr0 : 0 < r) (hr2 : 2 < r) (hp0 : 0 < p) (hp2 : 2 < p)
    (hf : MemLp f (ENNReal.ofReal p) μ) (hfi : Integrable f μ) (N : ℕ) :
    eLpNorm (SFTest.Vtr (fun n => condExp (ℱ n) μ f) r N) (ENNReal.ofReal p) μ
      ≤ 8 * ((ENNReal.ofReal (lepG r) * ENNReal.ofReal (SFTest.bdgZZ p))^(1/2 : ℝ)
          * eLpNorm f (ENNReal.ofReal p) μ) := by
  have hsa : (0:ℝ) < p/2 := by linarith
  have hgm : ∀ n, Measurable[ℱ n] (condExp (ℱ n) μ f) :=
    fun n => (stronglyMeasurable_condExp (m := ℱ n)).measurable
  have hle : ∀ ω, ((SFTest.Vtr (fun n => condExp (ℱ n) μ f) r N ω)^(2:ℝ))^(p/2)
      ≤ (64 * SFTest.Ztr (fun n => condExp (ℱ n) μ f) r N ω)^(p/2) :=
    fun ω => ENNReal.rpow_le_rpow
      (SFTest.Vtr_sq_le (fun n => condExp (ℱ n) μ f) hr0 hr2 N ω) hsa.le
  have hpow : ∀ ω, ((SFTest.Vtr (fun n => condExp (ℱ n) μ f) r N ω)^(2:ℝ))^(p/2)
      = (SFTest.Vtr (fun n => condExp (ℱ n) μ f) r N ω)^p := by
    intro ω
    rw [← ENNReal.rpow_mul]
    congr 1; ring
  have hInt : ∫⁻ ω, (SFTest.Vtr (fun n => condExp (ℱ n) μ f) r N ω)^p ∂μ
      ≤ (64:ℝ≥0∞)^(p/2) * ∫⁻ ω,
          (SFTest.Ztr (fun n => condExp (ℱ n) μ f) r N ω)^(p/2) ∂μ := by
    calc ∫⁻ ω, (SFTest.Vtr (fun n => condExp (ℱ n) μ f) r N ω)^p ∂μ
        = ∫⁻ ω, ((SFTest.Vtr (fun n => condExp (ℱ n) μ f) r N ω)^(2:ℝ))^(p/2) ∂μ :=
          lintegral_congr (fun ω => (hpow ω).symm)
      _ ≤ ∫⁻ ω, (64 * SFTest.Ztr (fun n => condExp (ℱ n) μ f) r N ω)^(p/2) ∂μ :=
          lintegral_mono hle
      _ = ∫⁻ ω, (64:ℝ≥0∞)^(p/2) * (SFTest.Ztr (fun n => condExp (ℱ n) μ f) r N ω)^(p/2) ∂μ := by
          refine lintegral_congr (fun ω => ?_)
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0:ℝ) ≤ p/2)]
      _ = (64:ℝ≥0∞)^(p/2) * ∫⁻ ω, (SFTest.Ztr (fun n => condExp (ℱ n) μ f) r N ω)^(p/2) ∂μ := by
          rw [lintegral_const_mul'' _
            ((SFTest.measurable_Ztr ℱ _ hgm r N).pow_const _).aemeasurable]
  have hp0e : ENNReal.ofReal p ≠ 0 := by rw [ENNReal.ofReal_ne_zero_iff]; linarith
  have hpTe : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hA : eLpNorm (SFTest.Vtr (fun n => condExp (ℱ n) μ f) r N) (ENNReal.ofReal p) μ
      = (∫⁻ ω, (SFTest.Vtr (fun n => condExp (ℱ n) μ f) r N ω)^p ∂μ) ^ (1/p) := by
    have key := Commons.Analysis.MeasureTheory.eLpNorm_rpow_toReal (μ := μ)
      (p := ENNReal.ofReal p) (f := SFTest.Vtr (fun n => condExp (ℱ n) μ f) r N) hp0e hpTe
      (SFTest.measurable_Vtr ℱ _ hgm r N).aestronglyMeasurable
    rw [show (eLpNorm (SFTest.Vtr (fun n => condExp (ℱ n) μ f) r N) (ENNReal.ofReal p) μ)
        = ((eLpNorm (SFTest.Vtr (fun n => condExp (ℱ n) μ f) r N) (ENNReal.ofReal p) μ)^(p))^(1/p)
        from by rw [← ENNReal.rpow_mul, mul_one_div, div_self (ne_of_gt hp0), ENNReal.rpow_one]]
    congr 1
    rw [ENNReal.toReal_ofReal hp0.le] at key
    exact key
  rw [hA]
  have hpz0 : ENNReal.ofReal (p/2) ≠ 0 := by rw [ENNReal.ofReal_ne_zero_iff]; linarith
  have hpzT : ENNReal.ofReal (p/2) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hZ2 : eLpNorm (SFTest.Ztr (fun n => condExp (ℱ n) μ f) r N) (ENNReal.ofReal (p/2)) μ
      = (∫⁻ ω, (SFTest.Ztr (fun n => condExp (ℱ n) μ f) r N ω)^(p/2) ∂μ)^(2/p) := by
    have key := Commons.Analysis.MeasureTheory.eLpNorm_rpow_toReal (μ := μ)
      (p := ENNReal.ofReal (p/2)) (f := SFTest.Ztr (fun n => condExp (ℱ n) μ f) r N) hpz0 hpzT
      (SFTest.measurable_Ztr ℱ _ hgm r N).aestronglyMeasurable
    rw [ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ p/2)] at key
    simp only [enorm_eq_self] at key
    rw [show eLpNorm (SFTest.Ztr (fun n => condExp (ℱ n) μ f) r N) (ENNReal.ofReal (p/2)) μ
        = ((eLpNorm (SFTest.Ztr (fun n => condExp (ℱ n) μ f) r N) (ENNReal.ofReal (p/2)) μ)^(p/2))^(2/p)
        from by rw [← ENNReal.rpow_mul, show (p/2) * (2/p) = 1 by field_simp, ENNReal.rpow_one]]
    rw [key]
  have hB2 := eLpNorm_Ztr_le_decoup ℱ f hr0 hr2 hp0 hp2 hf hfi N
  calc (∫⁻ ω, (SFTest.Vtr (fun n => condExp (ℱ n) μ f) r N ω)^p ∂μ)^(1/p)
      ≤ ((64:ℝ≥0∞)^(p/2) * ∫⁻ ω, (SFTest.Ztr (fun n => condExp (ℱ n) μ f) r N ω)^(p/2) ∂μ)^(1/p) :=
        ENNReal.rpow_le_rpow hInt (by positivity)
    _ = 8 * (∫⁻ ω, (SFTest.Ztr (fun n => condExp (ℱ n) μ f) r N ω)^(p/2) ∂μ)^(1/p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1/p)]
        congr 1
        have h64 : (64:ℝ≥0∞) = ((8:ℝ≥0∞))^(2:ℝ) := by
          rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]; norm_num
        rw [h64, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
          show (2:ℝ) * (p/2 * (1/p)) = 1 by field_simp, ENNReal.rpow_one]
    _ = 8 * (eLpNorm (SFTest.Ztr (fun n => condExp (ℱ n) μ f) r N) (ENNReal.ofReal (p/2)) μ)^(1/2 : ℝ) := by
        congr 1
        rw [hZ2]
        have he : ((∫⁻ ω, (SFTest.Ztr (fun n => condExp (ℱ n) μ f) r N ω)^(p/2) ∂μ)^(2/p))^(1/2 : ℝ)
            = (∫⁻ ω, (SFTest.Ztr (fun n => condExp (ℱ n) μ f) r N ω)^(p/2) ∂μ)^(1/p) := by
          rw [(ENNReal.rpow_mul _ (2/p) (1/2 : ℝ)).symm]
          congr 1
          field_simp
        exact he.symm
    _ ≤ 8 * ((ENNReal.ofReal (lepG r) * ENNReal.ofReal (SFTest.bdgZZ p))
          * (eLpNorm f (ENNReal.ofReal p) μ)^2)^(1/2 : ℝ) :=
        mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow hB2 (by norm_num)) (by norm_num)
    _ = 8 * ((ENNReal.ofReal (lepG r) * ENNReal.ofReal (SFTest.bdgZZ p))^(1/2 : ℝ)
          * eLpNorm f (ENNReal.ofReal p) μ) := by
        congr 1
        have h2 : (eLpNorm f (ENNReal.ofReal p) μ)^2
            = (eLpNorm f (ENNReal.ofReal p) μ)^(2:ℝ) := by
          rw [ENNReal.rpow_ofNat]
        rw [h2]
        have he : ((ENNReal.ofReal (lepG r) * ENNReal.ofReal (SFTest.bdgZZ p))
              * (eLpNorm f (ENNReal.ofReal p) μ)^(2:ℝ))^(1/2 : ℝ)
            = (ENNReal.ofReal (lepG r) * ENNReal.ofReal (SFTest.bdgZZ p))^(1/2 : ℝ)
              * eLpNorm f (ENNReal.ofReal p) μ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2)]
          rw [(ENNReal.rpow_mul _ (2:ℝ) (1/2 : ℝ)).symm]
          norm_num
        exact he

set_option maxHeartbeats 800000 in
lemma eLpNorm_Vinf_le_decoup {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SigmaFinite μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) [SigmaFiniteFiltration μ ℱ] (f : Ω → ℝ) {r p : ℝ}
    (hr0 : 0 < r) (hr2 : 2 < r) (hp0 : 0 < p) (hp2 : 2 < p)
    (hf : MemLp f (ENNReal.ofReal p) μ) (hfi : Integrable f μ) :
    eLpNorm (fun ω => ⨆ N, SFTest.Vtr (fun n => condExp (ℱ n) μ f) r N ω)
        (ENNReal.ofReal p) μ
      ≤ 8 * ((ENNReal.ofReal (lepG r) * ENNReal.ofReal (SFTest.bdgZZ p))^(1/2 : ℝ)
          * eLpNorm f (ENNReal.ofReal p) μ) := by
  have hgm : ∀ n, Measurable[ℱ n] (condExp (ℱ n) μ f) :=
    fun n => (stronglyMeasurable_condExp (m := ℱ n)).measurable
  have hp0e : ENNReal.ofReal p ≠ 0 := by rw [ENNReal.ofReal_ne_zero_iff]; linarith
  have hpTe : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [Commons.Analysis.MeasureTheory.eLpNorm_iSup_of_monotone hp0e hpTe
    (fun N => SFTest.measurable_Vtr ℱ _ hgm r N) (SFTest.Vtr_mono _ r)]
  refine iSup_le (fun N => ?_)
  exact eLpNorm_Vtr_le_decoup ℱ f hr0 hr2 hp0 hp2 hf hfi N

/-- Reduction of the full `r`-variation to `⨆ N, Vtr …` at a *different* `L^p` exponent. -/
lemma statement_le_decoup {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SigmaFinite μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (f : Ω → ℝ) {r p : ℝ} (hr0 : 0 < r) (hp0 : 0 < p) :
    eLpNorm (fun ω => ⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
        (∑ j ∈ Finset.range J,
          |(condExp (ℱ (u.1 (j+1))) μ f) ω - (condExp (ℱ (u.1 j)) μ f) ω| ^ r) ^ (1/r))
      (ENNReal.ofReal p) μ
      ≤ eLpNorm (fun ω => ⨆ N, SFTest.Vtr (fun n => condExp (ℱ n) μ f) r N ω)
          (ENNReal.ofReal p) μ := by
  have hVm := (SFTest.measurable_iSup_variation (fun n => condExp (ℱ n) μ f) hr0
    (fun N => SFTest.measurable_Vtr ℱ _
      (fun n => (stronglyMeasurable_condExp (m := ℱ n)).measurable) r N)).aestronglyMeasurable (μ := μ)
  have h := Commons.Analysis.Probability.eLpNorm_le_of_le (μ := μ) (s := p) hp0
    (fun ω => SFTest.pointwise_bound (μ := μ) ℱ f r ω) hVm.enorm.aestronglyMeasurable
  rwa [eLpNorm_enorm (hf := hVm)] at h

end LepLp

open Classical in
set_option maxHeartbeats 1600000 in
/-- Lépingle's inequality for `2 < p`. -/
theorem lepingle_lp_gt_two {p r : ℝ} (hp : 2 < p) (hr : 2 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
      [MeasureTheory.SigmaFinite μ] (F : MeasureTheory.Filtration ℕ ‹MeasurableSpace Ω›)
      (g : Ω → ℝ), MeasureTheory.MemLp g (ENNReal.ofReal p) μ →
      MeasureTheory.eLpNorm (fun ω => ⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
        (Finset.sum (Finset.range J) (fun j =>
          |(MeasureTheory.condExp (F (u.1 (j + 1))) μ g) ω
            - (MeasureTheory.condExp (F (u.1 j)) μ g) ω| ^ r)) ^ (1/r))
        (ENNReal.ofReal p) μ
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm g (ENNReal.ofReal p) μ := by
  have hp0 : (0:ℝ) < p := by linarith
  have hp1 : (1:ℝ) < p := by linarith
  have hr0 : (0:ℝ) < r := by linarith
  have hKG : 0 < lepG r := lepG_pos hr
  have hZZ : 0 < SFTest.bdgZZ p := bdgZZ_pos hp
  set K : ℝ := 8 * Real.sqrt (lepG r * SFTest.bdgZZ p) with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]
    exact mul_pos (by norm_num) (Real.sqrt_pos.mpr (mul_pos hKG hZZ))
  have hB1 : (ENNReal.ofReal (lepG r) * ENNReal.ofReal (SFTest.bdgZZ p))^(1/2 : ℝ)
      ≤ ENNReal.ofReal (Real.sqrt (lepG r * SFTest.bdgZZ p)) := by
    rw [← ENNReal.ofReal_mul hKG.le]
    rw [show (ENNReal.ofReal (lepG r * SFTest.bdgZZ p))^(1/2 : ℝ)
        = ENNReal.ofReal ((lepG r * SFTest.bdgZZ p)^(1/2 : ℝ)) from
      ENNReal.ofReal_rpow_of_nonneg (mul_pos hKG hZZ).le (by norm_num)]
    rw [Real.sqrt_eq_rpow]
  have hKC : (8:ℝ≥0∞) * ((ENNReal.ofReal (lepG r) * ENNReal.ofReal (SFTest.bdgZZ p))^(1/2 : ℝ))
      ≤ ENNReal.ofReal K := by
    have heq : ENNReal.ofReal K
        = (8:ℝ≥0∞) * ENNReal.ofReal (Real.sqrt (lepG r * SFTest.bdgZZ p)) := by
      rw [hKdef, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 8),
        show ENNReal.ofReal (8:ℝ) = 8 by norm_num]
    calc (8:ℝ≥0∞) * ((ENNReal.ofReal (lepG r) * ENNReal.ofReal (SFTest.bdgZZ p))^(1/2 : ℝ))
        ≤ (8:ℝ≥0∞) * ENNReal.ofReal (Real.sqrt (lepG r * SFTest.bdgZZ p)) :=
          mul_le_mul_of_nonneg_left hB1 zero_le
      _ = ENNReal.ofReal K := heq.symm
  refine ⟨1 + 2*K, by linarith, ?_⟩
  intro Ω _ μ _ ℱ f hf
  change eLpNorm (lepingleVar μ ℱ r f) (ENNReal.ofReal p) μ
    ≤ ENNReal.ofReal (1 + 2*K) * eLpNorm f (ENNReal.ofReal p) μ
  have hp0e : ENNReal.ofReal p ≠ 0 := by rw [ENNReal.ofReal_ne_zero_iff]; linarith
  have hpTe : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hp1e : (1:ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hCeq : ENNReal.ofReal (1 + 2*K) = 1 + 2 * ENNReal.ofReal K := by
    rw [ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
      show ENNReal.ofReal (2:ℝ) = 2 by norm_num, show ENNReal.ofReal (1:ℝ) = 1 by norm_num]
  have hKle : ENNReal.ofReal K ≤ ENNReal.ofReal (1 + 2*K) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  by_cases hInt : Integrable f μ
  · by_cases hSF : SigmaFiniteFiltration μ ℱ
    · haveI := hSF
      have h1 : eLpNorm (lepingleVar μ ℱ r f) (ENNReal.ofReal p) μ
          ≤ ENNReal.ofReal K * eLpNorm f (ENNReal.ofReal p) μ := by
        refine le_trans (LepLp.statement_le_decoup ℱ f hr0 hp0) ?_
        refine le_trans (LepLp.eLpNorm_Vinf_le_decoup ℱ f hr0 hr hp0 hp hf hInt) ?_
        rw [show (8:ℝ≥0∞) * ((ENNReal.ofReal (lepG r) * ENNReal.ofReal (SFTest.bdgZZ p))^(1/2 : ℝ)
              * eLpNorm f (ENNReal.ofReal p) μ)
            = ((8:ℝ≥0∞) * ((ENNReal.ofReal (lepG r) * ENNReal.ofReal (SFTest.bdgZZ p))^(1/2 : ℝ)))
              * eLpNorm f (ENNReal.ofReal p) μ from by ring]
        exact mul_le_mul_of_nonneg_right hKC zero_le
      exact le_trans h1 (mul_le_mul_of_nonneg_right hKle zero_le)
    · by_cases hex : ∃ n, SigmaFinite (μ.trim (ℱ.le' n))
      · let N := Nat.find hex
        have hN : SigmaFinite (μ.trim (ℱ.le' N)) := Nat.find_spec hex
        have hfail : ∀ k < N, ¬ SigmaFinite (μ.trim (ℱ.le' k)) := fun k hk => Nat.find_min hex hk
        have hzero : ∀ k < N, condExp (ℱ k) μ f = 0 := fun k hk =>
          condExp_of_not_sigmaFinite (ℱ.le' k) (hfail k hk)
        let ℱ' : Filtration ℕ ‹MeasurableSpace Ω› :=
          { seq := fun m => ℱ (N + m)
            mono' := fun i j hij => ℱ.mono (Nat.add_le_add_left hij N)
            le' := fun m => ℱ.le' (N + m) }
        haveI : SigmaFiniteFiltration μ ℱ' := by
          refine ⟨fun m => ?_⟩
          haveI : SigmaFinite (μ.trim (ℱ.le' N)) := hN
          exact sigmaFiniteTrim_mono (μ := μ) (ℱ.le' (N + m)) (ℱ.mono (Nat.le_add_right N m))
        have hshift : ∀ ω, lepingleVar μ ℱ r f ω
            ≤ |condExp (ℱ N) μ f ω| + 2 * lepingleVar μ ℱ' r f ω := by
          intro ω
          have hz : ∀ k < N, (fun n => condExp (ℱ n) μ f ω) k = 0 := fun k hk => by
            simp only [hzero k hk, Pi.zero_apply]
          have hv := Commons.Analysis.Series.variation_shift_le (fun n => condExp (ℱ n) μ f ω) hr N hz
          simpa only [lepingleVar] using hv
        set Q : Ω → ℝ≥0∞ := fun ω => ⨆ N', SFTest.Vtr (fun n => condExp (ℱ' n) μ f) r N' ω with hQ
        have hQmeas : Measurable Q := by
          rw [hQ]
          exact Measurable.iSup (fun N' => SFTest.measurable_Vtr ℱ'
            (fun n => condExp (ℱ' n) μ f)
            (fun n => (stronglyMeasurable_condExp (m := ℱ' n)).measurable) r N')
        have hAmeas : AEMeasurable (fun ω => ‖condExp (ℱ N) μ f ω‖ₑ) μ :=
          (((stronglyMeasurable_condExp (m := ℱ N)).measurable.mono (ℱ.le' N) le_rfl).enorm).aemeasurable
        have h2Qmeas : AEMeasurable (fun ω => 2 * Q ω) μ :=
          (measurable_const.mul hQmeas).aemeasurable
        have hpoint : ∀ ω, ‖lepingleVar μ ℱ r f ω‖ₑ ≤ ‖condExp (ℱ N) μ f ω‖ₑ + 2 * Q ω := by
          intro ω
          have hnn := lepingleVar_nonneg μ ℱ r f ω
          have hnn' := lepingleVar_nonneg μ ℱ' r f ω
          have h1 := hshift ω
          have hQp : ENNReal.ofReal (lepingleVar μ ℱ' r f ω) ≤ Q ω := by
            rw [hQ, ← Real.enorm_eq_ofReal hnn']
            simpa only [lepingleVar] using SFTest.pointwise_bound (μ := μ) ℱ' f r ω
          calc ‖lepingleVar μ ℱ r f ω‖ₑ
              = ENNReal.ofReal (lepingleVar μ ℱ r f ω) := Real.enorm_eq_ofReal hnn
            _ ≤ ENNReal.ofReal (|condExp (ℱ N) μ f ω| + 2 * lepingleVar μ ℱ' r f ω) :=
                ENNReal.ofReal_le_ofReal h1
            _ = ENNReal.ofReal |condExp (ℱ N) μ f ω|
                  + 2 * ENNReal.ofReal (lepingleVar μ ℱ' r f ω) := by
                rw [ENNReal.ofReal_add (abs_nonneg _) (by positivity),
                  ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
                  show ENNReal.ofReal (2:ℝ) = 2 by norm_num]
            _ = ‖condExp (ℱ N) μ f ω‖ₑ + 2 * ENNReal.ofReal (lepingleVar μ ℱ' r f ω) := by
                rw [Real.enorm_eq_ofReal_abs]
            _ ≤ ‖condExp (ℱ N) μ f ω‖ₑ + 2 * Q ω := by
                exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hQp (by norm_num))
        have hQbound : eLpNorm Q (ENNReal.ofReal p) μ
            ≤ ENNReal.ofReal K * eLpNorm f (ENNReal.ofReal p) μ := by
          rw [hQ]
          refine le_trans (LepLp.eLpNorm_Vinf_le_decoup ℱ' f hr0 hr hp0 hp hf hInt) ?_
          rw [show (8:ℝ≥0∞) * ((ENNReal.ofReal (lepG r) * ENNReal.ofReal (SFTest.bdgZZ p))^(1/2 : ℝ)
                * eLpNorm f (ENNReal.ofReal p) μ)
              = ((8:ℝ≥0∞) * ((ENNReal.ofReal (lepG r) * ENNReal.ofReal (SFTest.bdgZZ p))^(1/2 : ℝ)))
                * eLpNorm f (ENNReal.ofReal p) μ from by ring]
          exact mul_le_mul_of_nonneg_right hKC zero_le
        have hLm := Commons.Analysis.Probability.measurable_lepingleVar μ ℱ hr0 f
        have hmain : eLpNorm (lepingleVar μ ℱ r f) (ENNReal.ofReal p) μ
            ≤ eLpNorm f (ENNReal.ofReal p) μ
              + 2 * (ENNReal.ofReal K * eLpNorm f (ENNReal.ofReal p) μ) := by
          have hMink := ENNReal.lintegral_Lp_add_le (p := p) hAmeas h2Qmeas (by linarith : (1:ℝ) ≤ p)
          calc eLpNorm (lepingleVar μ ℱ r f) (ENNReal.ofReal p) μ
              = eLpNorm (fun ω => ‖lepingleVar μ ℱ r f ω‖ₑ) (ENNReal.ofReal p) μ :=
                (eLpNorm_enorm (hf := by pw_aesm) _).symm
            _ ≤ eLpNorm (fun ω => ‖condExp (ℱ N) μ f ω‖ₑ + 2 * Q ω) (ENNReal.ofReal p) μ :=
                Commons.Analysis.Probability.eLpNorm_le_of_le hp0 hpoint
            _ = (∫⁻ ω, (‖condExp (ℱ N) μ f ω‖ₑ + 2 * Q ω) ^ p ∂μ) ^ (1 / p) :=
                Commons.Analysis.Probability.eLpNorm_ennreal_eq _ hp0
            _ ≤ (∫⁻ ω, ‖condExp (ℱ N) μ f ω‖ₑ ^ p ∂μ) ^ (1 / p)
                  + (∫⁻ ω, (2 * Q ω) ^ p ∂μ) ^ (1 / p) := hMink
            _ = eLpNorm (fun ω => ‖condExp (ℱ N) μ f ω‖ₑ) (ENNReal.ofReal p) μ
                  + eLpNorm (fun ω => 2 * Q ω) (ENNReal.ofReal p) μ := by
                rw [Commons.Analysis.Probability.eLpNorm_ennreal_eq _ hp0,
                  Commons.Analysis.Probability.eLpNorm_ennreal_eq _ hp0]
            _ = eLpNorm (condExp (ℱ N) μ f) (ENNReal.ofReal p) μ
                  + 2 * eLpNorm Q (ENNReal.ofReal p) μ := by
                rw [eLpNorm_enorm (hf := by pw_aesm),
                  Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal (c := 2) (by norm_num) hp0e hpTe]
            _ ≤ eLpNorm f (ENNReal.ofReal p) μ
                  + 2 * (ENNReal.ofReal K * eLpNorm f (ENNReal.ofReal p) μ) := by
                refine add_le_add ?_ (mul_le_mul_of_nonneg_left ?_ (by norm_num))
                · exact eLpNorm_condExp_le_eLpNorm (m := ℱ N) f hp1e
                · exact hQbound
        exact le_trans hmain (le_of_eq (by
          rw [hCeq]
          rw [show eLpNorm f (ENNReal.ofReal p) μ
                + 2 * (ENNReal.ofReal K * eLpNorm f (ENNReal.ofReal p) μ)
              = (1 + 2 * ENNReal.ofReal K) * eLpNorm f (ENNReal.ofReal p) μ from by ring]))
      · have h0 : ∀ n, condExp (ℱ n) μ f = 0 := fun n =>
          condExp_of_not_sigmaFinite (ℱ.le' n) (fun hsf => hex ⟨n, hsf⟩)
        rw [lepingleVar_eq_zero μ ℱ hr0 f h0, eLpNorm_zero]
        exact zero_le
  · have h0 : ∀ n, condExp (ℱ n) μ f = 0 := fun n => condExp_of_not_integrable hInt
    rw [lepingleVar_eq_zero μ ℱ hr0 f h0, eLpNorm_zero]
    exact zero_le

end Commons.Analysis.Probability
