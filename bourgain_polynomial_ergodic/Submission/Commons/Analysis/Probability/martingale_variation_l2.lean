import Mathlib
import Submission.Commons.Analysis.Probability.lepingle_variation_ls
import Submission.Commons.Analysis.Series.variation_shift_le

open MeasureTheory
open scoped BigOperators ENNReal

namespace Commons.Analysis.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}





variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

set_option maxHeartbeats 4000000 in
/-- The `filt` filtration of a stopped martingale is a σ-finite filtration when the base one is. -/
lemma mv_sff_filt (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) [SigmaFiniteFiltration μ ℱ]
    (g : ℕ → Ω → ℝ) (hg : ∀ n, Measurable[ℱ n] (g n)) (N mm : ℕ) :
    SigmaFiniteFiltration μ (filt ℱ g hg N mm) := by
  refine ⟨fun j => ?_⟩
  exact @MeasureTheory.IsStoppingTime.sigmaFinite_stopping_time Ω _ ℕ _ _ μ ℱ
    (fun ω => (tauR g N mm j ω : ℕ∞)) _ (isStoppingTime_tauR ‹MeasurableSpace Ω› ℱ g hg N mm j)

/-- Orthogonality of martingale increments against `𝒢 k`-measurable sets (σ-finite version). -/
lemma mv_orthogonal (𝒢 : Filtration ℕ ‹MeasurableSpace Ω›) [SigmaFiniteFiltration μ 𝒢]
    (h : ℕ → Ω → ℝ) (hmart : Martingale h 𝒢 μ) (hI : ∀ n, Integrable (h n) μ)
    (h2 : ∀ n, MemLp (h n) 2 μ) (s : Set Ω) (k : ℕ) (hs : MeasurableSet[𝒢 k] s) :
    ∫ ω in s, h k ω * dinc h k ω ∂μ = 0 := by
  have hik1 : Integrable (h (k+1)) μ := hI (k+1)
  have hikmul : Integrable (h k * h (k+1)) μ := MemLp.integrable_mul (h2 k) (h2 (k+1))
  have hkk : Integrable (h k * h k) μ := MemLp.integrable_mul (h2 k) (h2 k)
  have hpull : condExp (𝒢 k) μ (h k * h (k+1)) =ᵐ[μ] h k * h k := by
    have h1 := condExp_mul_of_stronglyMeasurable_left (μ := μ) (m := 𝒢 k)
      (f := h k) (g := h (k+1)) (hmart.1 k) hikmul hik1
    have h2' := hmart.condExp_ae_eq (Nat.le_succ k)
    filter_upwards [h1, h2'] with ω h1ω h2ω
    have : condExp (𝒢 k) μ (h k * h (k+1)) ω
        = h k ω * condExp (𝒢 k) μ (h (k+1)) ω := h1ω
    rw [this, h2ω]
    simp only [Pi.mul_apply]
  have hA : ∫ ω in s, (h k * h (k+1)) ω ∂μ = ∫ ω in s, (h k * h k) ω ∂μ := by
    rw [← setIntegral_condExp (m := 𝒢 k) (𝒢.le' k) hikmul hs]
    refine setIntegral_congr_ae (𝒢.le' k s hs) ?_
    filter_upwards [hpull] with ω hω _
    exact hω
  have hsub : ∫ ω in s, ((h k * h (k+1)) - (h k * h k)) ω ∂μ
      = ∫ ω in s, (h k * h (k+1)) ω ∂μ - ∫ ω in s, (h k * h k) ω ∂μ := by
    simp only [Pi.sub_apply]
    rw [integral_sub (μ := μ.restrict s) hikmul.integrableOn hkk.integrableOn]
  have hfinal : ∫ ω in s, ((h k * h (k+1)) - (h k * h k)) ω ∂μ = 0 := by
    rw [hsub, hA, sub_self]
  rw [dinc]
  convert hfinal using 2 with ω
  simp only [Pi.sub_apply, Pi.mul_apply]
  ring_nf

/-- Integral of the prefix square function = difference of the two endpoint `L²` masses. -/
lemma mv_integral_preSq (𝒢 : Filtration ℕ ‹MeasurableSpace Ω›) [SigmaFiniteFiltration μ 𝒢]
    (h : ℕ → Ω → ℝ) (hmart : Martingale h 𝒢 μ) (hI : ∀ n, Integrable (h n) μ)
    (h2 : ∀ n, MemLp (h n) 2 μ) (L : ℕ) :
    ∫ ω, preSq h L ω ∂μ = ∫ ω, (h L ω)^2 ∂μ - ∫ ω, (h 0 ω)^2 ∂μ := by
  have hsq_int : ∀ n, Integrable (fun ω => (h n ω)^2) μ := fun n => by
    have := MemLp.integrable_mul (h2 n) (h2 n)
    convert this using 1; ext ω; simp only [Pi.mul_apply]; ring
  have hd2 : ∀ n, MemLp (dinc h n) 2 μ := fun n => by
    simp only [dinc]; exact (h2 (n+1)).sub (h2 n)
  have hdinc2_int : ∀ n, Integrable (fun ω => (dinc h n ω)^2) μ := fun n => by
    have := MemLp.integrable_mul (hd2 n) (hd2 n)
    convert this using 1; ext ω; simp only [Pi.mul_apply]; ring
  have hmul_int : ∀ k, Integrable (fun ω => h k ω * dinc h k ω) μ :=
    fun k => MemLp.integrable_mul (h2 k) (hd2 k)
  have hkey : ∀ k, ∫ ω, (h (k+1) ω)^2 ∂μ - ∫ ω, (h k ω)^2 ∂μ
      = ∫ ω, (dinc h k ω)^2 ∂μ := by
    intro k
    have e : ∀ ω, (h (k+1) ω)^2 - (h k ω)^2
        = 2*(h k ω * dinc h k ω) + (dinc h k ω)^2 := by
      intro ω; simp only [dinc, Pi.sub_apply]; ring
    rw [← integral_sub (hsq_int (k+1)) (hsq_int k)]
    rw [show (fun ω => (h (k+1) ω)^2 - (h k ω)^2)
        = fun ω => 2*(h k ω * dinc h k ω) + (dinc h k ω)^2 from funext e]
    rw [integral_add ((hmul_int k).const_mul 2) (hdinc2_int k), integral_const_mul]
    rw [show (∫ ω, h k ω * dinc h k ω ∂μ) = ∫ ω in Set.univ, h k ω * dinc h k ω ∂μ
      from (setIntegral_univ).symm]
    rw [mv_orthogonal 𝒢 h hmart hI h2 Set.univ k (by simp)]
    ring
  have htele : ∫ ω, (h L ω)^2 ∂μ - ∫ ω, (h 0 ω)^2 ∂μ
      = ∑ k ∈ Finset.range L, (∫ ω, (h (k+1) ω)^2 ∂μ - ∫ ω, (h k ω)^2 ∂μ) :=
    (Finset.sum_range_sub (fun k => ∫ ω, (h k ω)^2 ∂μ) L).symm
  rw [show preSq h L = fun ω => ∑ k ∈ Finset.range L, (dinc h k ω)^2 from rfl]
  rw [integral_finsetSum _ (fun k _ => hdinc2_int k)]
  rw [htele]
  exact Finset.sum_congr rfl (fun k _ => (hkey k).symm)




variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma ofReal_integral_sq_eq_eLpNorm_sq (h : Ω → ℝ) (hh : MemLp h 2 μ) :
    ENNReal.ofReal (∫ ω, (h ω)^2 ∂μ) = (eLpNorm h 2 μ)^2 := by
  have hint : Integrable (fun ω => (h ω)^2) μ := by
    have := MemLp.integrable_mul hh hh
    convert this using 1; ext ω; simp only [Pi.mul_apply]; ring
  have key := Commons.Analysis.MeasureTheory.eLpNorm_rpow_toReal (μ := μ) (p := (2:ℝ≥0∞)) (f := h)
    (by norm_num) (by norm_num) hh.aestronglyMeasurable
  rw [show ((2:ℝ≥0∞)).toReal = 2 by norm_num] at key
  rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num] at key
  rw [ENNReal.rpow_natCast] at key
  rw [key]
  rw [show (∫⁻ (x : Ω), ‖h x‖ₑ ^ ((2:ℕ):ℝ) ∂μ)
      = ∫⁻ (x : Ω), ENNReal.ofReal ((h x)^2) ∂μ from
    lintegral_congr (fun x => by
      rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
        Real.rpow_natCast, sq_abs])]
  exact ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall (fun ω => sq_nonneg _))

-- martingale_sm ported (sigma-finite filtration)
set_option maxHeartbeats 4000000 in
set_option backward.isDefEq.respectTransparency false in
theorem mv_martingale_sm (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) [SigmaFiniteFiltration μ ℱ]
    (g : ℕ → Ω → ℝ) (hg : ∀ n, Measurable[ℱ n] (g n))
    (hmart : Martingale g ℱ μ) (N mm : ℕ) :
    Martingale (sm g N mm) (filt ℱ g hg N mm) μ := by
  have hSA : StronglyAdapted ℱ g := fun n => (hg n).stronglyMeasurable
  have hprog : IsStronglyProgressive ℱ g := hSA.isStronglyProgressive_of_discrete
  refine ⟨fun j => ?_, fun i j hij => ?_⟩
  · rw [sm_eq_stoppedValue]
    exact (measurable_stoppedValue hprog
      (isStoppingTime_tauR ‹MeasurableSpace Ω› ℱ g hg N mm j)).stronglyMeasurable
  · rw [sm_eq_stoppedValue, sm_eq_stoppedValue]
    have hle : (fun ω => (tauR g N mm i ω : ℕ∞)) ≤ (fun ω => (tauR g N mm j ω : ℕ∞)) := by
      intro ω
      exact ENat.natCast_le_natCast.mpr (tau_mono (fun k => g k ω) N mm hij)
    have hbdd : ∀ ω, (tauR g N mm j ω : ℕ∞) ≤ ((N+1 : ℕ) : ℕ∞) := by
      intro ω
      exact ENat.natCast_le_natCast.mpr (tau_le (fun k => g k ω) N mm j)
    have h := hmart.stoppedValue_ae_eq_condExp_of_le (μ := μ)
      (isStoppingTime_tauR ‹MeasurableSpace Ω› ℱ g hg N mm j)
      (isStoppingTime_tauR ‹MeasurableSpace Ω› ℱ g hg N mm i) hle hbdd
    exact h.symm

lemma mv_memLp_sm (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (g : ℕ → Ω → ℝ)
    (hgm : ∀ n, Measurable[ℱ n] (g n))
    (hg : ∀ n, MemLp (g n) 2 μ) (N mm j : ℕ) : MemLp (sm g N mm j) 2 μ := by
  have hSA : StronglyAdapted ℱ g := fun n => (hgm n).stronglyMeasurable
  have hprog : IsStronglyProgressive ℱ g := hSA.isStronglyProgressive_of_discrete
  have hmeas : Measurable (sm g N mm j) := by
    rw [sm_eq_stoppedValue]
    exact (measurable_stoppedValue hprog
      (isStoppingTime_tauR ‹MeasurableSpace Ω› ℱ g hgm N mm j)).mono
      (isStoppingTime_tauR ‹MeasurableSpace Ω› ℱ g hgm N mm j).measurableSpace_le le_rfl
  refine MemLp.of_le (g := fun ω => ∑ n ∈ Finset.range (N+2), |g n ω|) ?_ ?_ ?_
  · exact memLp_finsetSum _ (fun n _ => (hg n).norm)
  · exact hmeas.aestronglyMeasurable
  · filter_upwards with ω
    have hmem : tau (fun k => g k ω) N mm j ∈ Finset.range (N+2) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (tau_le (fun k => g k ω) N mm j))
    have hsum : 0 ≤ ∑ n ∈ Finset.range (N+2), |g n ω| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
    have h1 : |sm g N mm j ω| = |g (tau (fun k => g k ω) N mm j) ω| := rfl
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hsum, h1]
    exact Finset.single_le_sum (f := fun n => |g n ω|) (fun i _ => abs_nonneg _) hmem

lemma mv_integrable_sm (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (g : ℕ → Ω → ℝ)
    (hgm : ∀ n, Measurable[ℱ n] (g n))
    (hgI : ∀ n, Integrable (g n) μ) (N mm j : ℕ) : Integrable (sm g N mm j) μ := by
  have hSA : StronglyAdapted ℱ g := fun n => (hgm n).stronglyMeasurable
  have hprog : IsStronglyProgressive ℱ g := hSA.isStronglyProgressive_of_discrete
  have hmeas : Measurable (sm g N mm j) := by
    rw [sm_eq_stoppedValue]
    exact (measurable_stoppedValue hprog
      (isStoppingTime_tauR ‹MeasurableSpace Ω› ℱ g hgm N mm j)).mono
      (isStoppingTime_tauR ‹MeasurableSpace Ω› ℱ g hgm N mm j).measurableSpace_le le_rfl
  refine Integrable.mono' (g := fun ω => ∑ n ∈ Finset.range (N+2), |g n ω|) ?_ ?_ ?_
  · exact integrable_finsetSum _ (fun n _ => (hgI n).norm)
  · exact hmeas.aestronglyMeasurable
  · filter_upwards with ω
    have hmem : tau (fun k => g k ω) N mm j ∈ Finset.range (N+2) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (tau_le (fun k => g k ω) N mm j))
    have hsum : 0 ≤ ∑ n ∈ Finset.range (N+2), |g n ω| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
    calc |sm g N mm j ω| = |g (tau (fun k => g k ω) N mm j) ω| := rfl
      _ ≤ ∑ n ∈ Finset.range (N+2), |g n ω| :=
          Finset.single_le_sum (f := fun n => |g n ω|) (fun i _ => abs_nonneg _) hmem




variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

set_option maxHeartbeats 4000000 in
lemma mv_eLpNorm_Ssq_sm_le (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) [SigmaFiniteFiltration μ ℱ]
    (f : Ω → ℝ) (hf : MemLp f 2 μ) (N m : ℕ) :
    eLpNorm (Ssq (sm (fun n => condExp (ℱ n) μ f) N m)) 1 μ ≤ (eLpNorm f 2 μ)^2 := by
  set g : ℕ → Ω → ℝ := fun n => condExp (ℱ n) μ f with hgdef
  have hgm : ∀ n, Measurable[ℱ n] (g n) := fun n => (stronglyMeasurable_condExp (m := ℱ n)).measurable
  have hgI : ∀ n, Integrable (g n) μ := fun n => integrable_condExp
  have hg2 : ∀ n, MemLp (g n) 2 μ := fun n => MemLp.condExp one_le_two hf
  have hmart : Martingale g ℱ μ := martingale_condExp f ℱ μ
  haveI : SigmaFiniteFiltration μ (filt ℱ g hgm N m) := mv_sff_filt ℱ g hgm N m
  have smI : ∀ j, Integrable (sm g N m j) μ := fun j => mv_integrable_sm ℱ g hgm hgI N m j
  have sm2 : ∀ j, MemLp (sm g N m j) 2 μ := fun j => mv_memLp_sm ℱ g hgm hg2 N m j
  have hmart_sm : Martingale (sm g N m) (filt ℱ g hgm N m) μ := mv_martingale_sm ℱ g hgm hmart N m
  have hpre_int : Integrable (preSq (sm g N m) (N+2)) μ := by
    rw [show preSq (sm g N m) (N+2) = fun ω => ∑ k ∈ Finset.range (N+2), (dinc (sm g N m) k ω)^2 from rfl]
    refine integrable_finsetSum _ (fun k _ => ?_)
    have hd : MemLp (dinc (sm g N m) k) 2 μ := by
      simp only [dinc]; exact (sm2 (k+1)).sub (sm2 k)
    have heq : (fun ω => (dinc (sm g N m) k ω)^2)
        = (dinc (sm g N m) k * dinc (sm g N m) k) := by
      funext ω; simp only [Pi.mul_apply]; ring
    rw [heq]
    exact MemLp.integrable_mul hd hd
  have hpre_nn : ∀ ω, 0 ≤ preSq (sm g N m) (N+2) ω := by
    intro ω; rw [show preSq (sm g N m) (N+2) = fun ω => ∑ k ∈ Finset.range (N+2), (dinc (sm g N m) k ω)^2 from rfl]
    exact Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have hsq := mv_integral_preSq (filt ℱ g hgm N m) (sm g N m) hmart_sm smI sm2 (N+2)
  have hsmval : ∀ ω, sm g N m (N+2) ω = g (N+1) ω := by
    intro ω
    rw [sm_eq_cap g (show N+1 ≤ N+2 by omega)]
    change g (tau (fun k => g k ω) N m (N+1)) ω = g (N+1) ω
    rw [tau_reaches]
  have hEq : eLpNorm (Ssq (sm g N m)) 1 μ
      = ENNReal.ofReal (∫ ω, preSq (sm g N m) (N+2) ω ∂μ) := by
    rw [show Ssq (sm g N m) = fun ω => ENNReal.ofReal (preSq (sm g N m) (N+2) ω)
      from funext (fun ω => Ssq_sm_eq g N m ω)]
    rw [eLpNorm_one_eq_lintegral_enorm
      (measurable_preSq_sm ℱ g hgm N m (N+2)).ennreal_ofReal.aestronglyMeasurable]
    rw [show (∫⁻ ω, ‖(fun ω => ENNReal.ofReal (preSq (sm g N m) (N+2) ω)) ω‖ₑ ∂μ)
        = ∫⁻ ω, ENNReal.ofReal (preSq (sm g N m) (N+2) ω) ∂μ from rfl]
    exact (ofReal_integral_eq_lintegral_ofReal hpre_int (Filter.Eventually.of_forall hpre_nn)).symm
  have hle : ∫ ω, preSq (sm g N m) (N+2) ω ∂μ ≤ ∫ ω, (g (N+1) ω)^2 ∂μ := by
    rw [hsq]
    have h1 : ∫ ω, (sm g N m (N+2) ω)^2 ∂μ = ∫ ω, (g (N+1) ω)^2 ∂μ := by
      congr 1 with ω; rw [hsmval ω]
    rw [h1]
    linarith [integral_nonneg (μ := μ) (f := fun ω => (sm g N m 0 ω)^2) (fun ω => sq_nonneg _)]
  rw [hEq]
  calc ENNReal.ofReal (∫ ω, preSq (sm g N m) (N+2) ω ∂μ)
      ≤ ENNReal.ofReal (∫ ω, (g (N+1) ω)^2 ∂μ) := ENNReal.ofReal_le_ofReal hle
    _ = (eLpNorm (g (N+1)) 2 μ)^2 := ofReal_integral_sq_eq_eLpNorm_sq (g (N+1)) (hg2 (N+1))
    _ ≤ (eLpNorm f 2 μ)^2 := by
        have hc := eLpNorm_condExp_le_eLpNorm (μ := μ) (m := ℱ (N+1)) f (show (1:ℝ≥0∞) ≤ 2 by norm_num)
        exact pow_le_pow_left' hc 2


set_option maxHeartbeats 4000000 in
lemma mv_lintegral_Ssq_sm_le (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) [SigmaFiniteFiltration μ ℱ]
    (f : Ω → ℝ) (hf : MemLp f 2 μ) (N m : ℕ) :
    ∫⁻ ω, Ssq (sm (fun n => condExp (ℱ n) μ f) N m) ω ∂μ ≤ (eLpNorm f 2 μ)^2 := by
  have h := mv_eLpNorm_Ssq_sm_le ℱ f hf N m
  rwa [show eLpNorm (Ssq (sm (fun n => condExp (ℱ n) μ f) N m)) 1 μ
      = ∫⁻ ω, Ssq (sm (fun n => condExp (ℱ n) μ f) N m) ω ∂μ from by
    rw [eLpNorm_one_eq_lintegral_enorm (measurable_Ssq_sm ℱ _
      (fun n => (stronglyMeasurable_condExp (m := ℱ n)).measurable) N m).aestronglyMeasurable]
    rfl] at h

set_option maxHeartbeats 4000000 in
lemma mv_eLpNorm_Ztr_le (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) [SigmaFiniteFiltration μ ℱ]
    (f : Ω → ℝ) (hf : MemLp f 2 μ) {s : ℝ} (hs : 2 < s) (hs3 : s ≤ 3) (N : ℕ) :
    eLpNorm (Ztr (fun n => condExp (ℱ n) μ f) s N) 1 μ
      ≤ ENNReal.ofReal (2/((s-2)*Real.log 2)) * (eLpNorm f 2 μ)^2 := by
  set g : ℕ → Ω → ℝ := fun n => condExp (ℱ n) μ f with hgdef
  have hgm : ∀ n, Measurable[ℱ n] (g n) := fun n => (stronglyMeasurable_condExp (m := ℱ n)).measurable
  have hmono : Monotone (fun M : ℕ => fun ω => ENNReal.ofReal (Zterm g s N M ω)) :=
    fun a b hab ω => ENNReal.ofReal_le_ofReal (Zterm_mono g s N hab ω)
  have hZm := measurable_Ztr ℱ g hgm s N
  rw [show Ztr g s N = fun ω => ⨆ M, ENNReal.ofReal (Zterm g s N M ω) from rfl] at hZm ⊢
  rw [eLpNorm_one_eq_lintegral_enorm hZm.aestronglyMeasurable]
  rw [show (∫⁻ ω, ‖(fun ω => ⨆ M, ENNReal.ofReal (Zterm g s N M ω)) ω‖ₑ ∂μ)
      = ∫⁻ ω, (⨆ M, ENNReal.ofReal (Zterm g s N M ω)) ∂μ from rfl]
  rw [lintegral_iSup (fun M => (measurable_Zterm ℱ g hgm s N M).ennreal_ofReal) hmono]
  refine iSup_le (fun M => ?_)
  have hterm : ∀ m ∈ Finset.Icc 2 M, Measurable
      (fun ω => ENNReal.ofReal ((1/2:ℝ)^((m-2)*(s-2))) * Ssq (sm g N m) ω) := fun m _ =>
    (measurable_Ssq_sm ℱ g hgm N m).const_mul (ENNReal.ofReal ((1/2:ℝ)^((m-2)*(s-2))))
  calc ∫⁻ ω, ENNReal.ofReal (Zterm g s N M ω) ∂μ
      = ∫⁻ ω, (∑ m ∈ Finset.Icc 2 M,
          ENNReal.ofReal ((1/2:ℝ)^((m-2)*(s-2))) * Ssq (sm g N m) ω) ∂μ :=
        lintegral_congr (fun ω => ofReal_Zterm_eq g s N M ω)
    _ = ∑ m ∈ Finset.Icc 2 M,
          ENNReal.ofReal ((1/2:ℝ)^((m-2)*(s-2))) * ∫⁻ ω, Ssq (sm g N m) ω ∂μ := by
        rw [lintegral_finsetSum _ hterm]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [lintegral_const_mul _ (measurable_Ssq_sm ℱ g hgm N m)]
    _ ≤ ∑ m ∈ Finset.Icc 2 M,
          ENNReal.ofReal ((1/2:ℝ)^((m-2)*(s-2))) * (eLpNorm f 2 μ)^2 :=
        Finset.sum_le_sum (fun m _ => mul_le_mul_of_nonneg_left (mv_lintegral_Ssq_sm_le ℱ f hf N m) zero_le)
    _ = ENNReal.ofReal (∑ m ∈ Finset.Icc 2 M, (1/2:ℝ)^((m-2)*(s-2))) * (eLpNorm f 2 μ)^2 := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun m _ => Real.rpow_nonneg (by norm_num) _), Finset.sum_mul]
    _ ≤ ENNReal.ofReal (2/((s-2)*Real.log 2)) * (eLpNorm f 2 μ)^2 :=
        mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (geom_bound hs hs3 M)) zero_le




set_option maxHeartbeats 800000 in
lemma mv_pointwise_bound (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (f : Ω → ℝ) (s : ℝ) (ω : Ω) :
    ‖(⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
        (∑ j ∈ Finset.range J,
          |(condExp (ℱ (u.1 (j+1))) μ f) ω - (condExp (ℱ (u.1 j)) μ f) ω| ^ s) ^ (1 / s))‖ₑ
      ≤ ⨆ N, Vtr (fun n => condExp (ℱ n) μ f) s N ω := by
  haveI : Nonempty {u : ℕ → ℕ // StrictMono u} := ⟨⟨fun n => n, strictMono_id⟩⟩
  set X : (ℕ → ℕ) → ℕ → ℝ := fun u J => (∑ j ∈ Finset.range J,
      |(condExp (ℱ (u (j+1))) μ f) ω - (condExp (ℱ (u j)) μ f) ω| ^ s) ^ (1 / s) with hX
  have hnn : ∀ u J, 0 ≤ X u J := fun u J =>
    Real.rpow_nonneg (Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (abs_nonneg _) s)) _
  have h1 : ∀ u : {u : ℕ → ℕ // StrictMono u},
      ‖(⨆ J : ℕ, X u.1 J)‖ₑ ≤ ⨆ N, Vtr (fun n => condExp (ℱ n) μ f) s N ω := by
    intro u
    refine (enorm_iSup_le (fun J : ℕ => X u.1 J)).trans (iSup_le (fun J => ?_))
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hnn u.1 J)]
    refine le_trans ?_ (le_iSup (fun N : ℕ => Vtr (fun n => condExp (ℱ n) μ f) s N ω) (u.1 J))
    rw [Vtr]
    refine le_trans ?_ (le_iSup (fun u' : {u : ℕ → ℕ // StrictMono u} => ⨆ J' : ℕ,
      if u'.1 J' ≤ u.1 J then ENNReal.ofReal (X u'.1 J') else 0) u)
    refine le_trans ?_ (le_iSup (fun J' : ℕ =>
      if u.1 J' ≤ u.1 J then ENNReal.ofReal (X u.1 J') else 0) J)
    rw [if_pos (le_refl (u.1 J))]
  calc ‖(⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ), X u.1 J)‖ₑ
      ≤ ⨆ u : {u : ℕ → ℕ // StrictMono u}, ‖(⨆ J : ℕ, X u.1 J)‖ₑ := enorm_iSup_le _
    _ ≤ ⨆ N, Vtr (fun n => condExp (ℱ n) μ f) s N ω := iSup_le h1

set_option maxHeartbeats 800000 in
lemma mv_statement_le (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (f : Ω → ℝ) {s : ℝ}
    (hs0 : 0 < s) :
    eLpNorm (fun ω => ⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
        (∑ j ∈ Finset.range J,
          |(condExp (ℱ (u.1 (j+1))) μ f) ω - (condExp (ℱ (u.1 j)) μ f) ω| ^ s) ^ (1 / s))
      (2:ℝ≥0∞) μ
      ≤ eLpNorm (fun ω => ⨆ N, Vtr (fun n => condExp (ℱ n) μ f) s N ω) (2:ℝ≥0∞) μ := by
  have hgm : ∀ n, Measurable[ℱ n] (condExp (ℱ n) μ f) :=
    fun n => (stronglyMeasurable_condExp (m := ℱ n)).measurable
  have hGm : Measurable (fun ω => ⨆ N, Vtr (fun n => condExp (ℱ n) μ f) s N ω) :=
    Measurable.iSup (fun N => measurable_Vtr ℱ _ hgm s N)
  have hVm := (measurable_iSup_variation (fun n => condExp (ℱ n) μ f) hs0
    (fun N => measurable_Vtr ℱ _ hgm s N)).aestronglyMeasurable (μ := μ)
  have h1 : eLpNorm (fun ω => ⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
        (∑ j ∈ Finset.range J,
          |(condExp (ℱ (u.1 (j+1))) μ f) ω - (condExp (ℱ (u.1 j)) μ f) ω| ^ s) ^ (1 / s))
      (2:ℝ≥0∞) μ
      = (∫⁻ ω, ‖(⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
          (∑ j ∈ Finset.range J,
            |(condExp (ℱ (u.1 (j+1))) μ f) ω - (condExp (ℱ (u.1 j)) μ f) ω| ^ s) ^ (1 / s))‖ₑ ^ (2:ℝ)
        ∂μ)^(1/2:ℝ) := by
    have key := Commons.Analysis.MeasureTheory.eLpNorm_rpow_toReal (μ := μ)
      (p := (2:ℝ≥0∞))
      (f := fun ω => ⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
        (∑ j ∈ Finset.range J,
          |(condExp (ℱ (u.1 (j+1))) μ f) ω - (condExp (ℱ (u.1 j)) μ f) ω| ^ s) ^ (1 / s))
      (by norm_num) (by norm_num) hVm
    rw [show ((2:ℝ≥0∞)).toReal = 2 by norm_num] at key
    rw [show eLpNorm (fun ω => ⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
        (∑ j ∈ Finset.range J,
          |(condExp (ℱ (u.1 (j+1))) μ f) ω - (condExp (ℱ (u.1 j)) μ f) ω| ^ s) ^ (1 / s))
        (2:ℝ≥0∞) μ
        = ((eLpNorm (fun ω => ⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
          (∑ j ∈ Finset.range J,
            |(condExp (ℱ (u.1 (j+1))) μ f) ω - (condExp (ℱ (u.1 j)) μ f) ω| ^ s) ^ (1 / s))
          (2:ℝ≥0∞) μ)^(2:ℝ))^(1/2:ℝ) from by
      rw [← ENNReal.rpow_mul]; norm_num]
    rw [key]
  have h2 : eLpNorm (fun ω => ⨆ N, Vtr (fun n => condExp (ℱ n) μ f) s N ω) (2:ℝ≥0∞) μ
      = (∫⁻ ω, (⨆ N, Vtr (fun n => condExp (ℱ n) μ f) s N ω) ^ (2:ℝ) ∂μ)^(1/2:ℝ) := by
    have key := Commons.Analysis.MeasureTheory.eLpNorm_rpow_toReal (μ := μ)
      (p := (2:ℝ≥0∞))
      (f := fun ω => ⨆ N, Vtr (fun n => condExp (ℱ n) μ f) s N ω) (by norm_num) (by norm_num)
      hGm.aestronglyMeasurable
    rw [show ((2:ℝ≥0∞)).toReal = 2 by norm_num] at key
    rw [show eLpNorm (fun ω => ⨆ N, Vtr (fun n => condExp (ℱ n) μ f) s N ω) (2:ℝ≥0∞) μ
        = ((eLpNorm (fun ω => ⨆ N, Vtr (fun n => condExp (ℱ n) μ f) s N ω)
          (2:ℝ≥0∞) μ)^(2:ℝ))^(1/2:ℝ) from by
      rw [← ENNReal.rpow_mul]; norm_num]
    rw [key]
    simp only [enorm_eq_self]
  rw [h1, h2]
  refine ENNReal.rpow_le_rpow (lintegral_mono (fun ω =>
    ENNReal.rpow_le_rpow (mv_pointwise_bound ℱ f s ω) (by norm_num))) (by norm_num)

set_option maxHeartbeats 4000000 in
lemma mv_eLpNorm_Vtr_le (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) [SigmaFiniteFiltration μ ℱ]
    (f : Ω → ℝ) (hf : MemLp f 2 μ) {s : ℝ} (hs : 2 < s) (hs3 : s ≤ 3) (N : ℕ) :
    eLpNorm (Vtr (fun n => condExp (ℱ n) μ f) s N) (2:ℝ≥0∞) μ
      ≤ 8 * ((ENNReal.ofReal (2/((s-2)*Real.log 2)))^(1/2:ℝ) * eLpNorm f 2 μ) := by
  set g : ℕ → Ω → ℝ := fun n => condExp (ℱ n) μ f with hgdef
  have hgm : ∀ n, Measurable[ℱ n] (g n) := fun n => (stronglyMeasurable_condExp (m := ℱ n)).measurable
  have heq : (eLpNorm (Vtr g s N) (2:ℝ≥0∞) μ)^(2:ℝ) = ∫⁻ ω, (Vtr g s N ω)^(2:ℝ) ∂μ := by
    have key := Commons.Analysis.MeasureTheory.eLpNorm_rpow_toReal (μ := μ)
      (p := (2:ℝ≥0∞)) (f := Vtr g s N) (by norm_num) (by norm_num)
      (measurable_Vtr ℱ g hgm s N).aestronglyMeasurable
    rw [show ((2:ℝ≥0∞)).toReal = 2 by norm_num] at key
    exact key.trans (lintegral_congr (fun ω => by rw [enorm_eq_self]))
  have hsq : (eLpNorm (Vtr g s N) (2:ℝ≥0∞) μ)^(2:ℝ) ≤ 64 * ∫⁻ ω, Ztr g s N ω ∂μ := by
    rw [heq]
    calc ∫⁻ ω, (Vtr g s N ω)^(2:ℝ) ∂μ ≤ ∫⁻ ω, 64 * Ztr g s N ω ∂μ :=
          lintegral_mono (fun ω => Vtr_sq_le g (by linarith) hs N ω)
      _ = 64 * ∫⁻ ω, Ztr g s N ω ∂μ :=
          lintegral_const_mul _ (measurable_Ztr ℱ g hgm s N)
  have hZ : ∫⁻ ω, Ztr g s N ω ∂μ
      ≤ ENNReal.ofReal (2/((s-2)*Real.log 2)) * (eLpNorm f 2 μ)^2 := by
    have h := mv_eLpNorm_Ztr_le ℱ f hf hs hs3 N
    rwa [show eLpNorm (Ztr (fun n => condExp (ℱ n) μ f) s N) 1 μ
        = ∫⁻ ω, Ztr (fun n => condExp (ℱ n) μ f) s N ω ∂μ from by
      rw [eLpNorm_one_eq_lintegral_enorm (measurable_Ztr ℱ g hgm s N).aestronglyMeasurable]
      rfl] at h
  have hfin : eLpNorm (Vtr g s N) (2:ℝ≥0∞) μ
      = ((eLpNorm (Vtr g s N) (2:ℝ≥0∞) μ)^(2:ℝ))^(1/2:ℝ) := by
    rw [← ENNReal.rpow_mul]; norm_num
  rw [hfin]
  have h64 : (64:ℝ≥0∞) = (8:ℝ≥0∞)^(2:ℝ) := by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]; norm_num
  calc ((eLpNorm (Vtr g s N) (2:ℝ≥0∞) μ)^(2:ℝ))^(1/2:ℝ)
      ≤ (64 * ∫⁻ ω, Ztr g s N ω ∂μ)^(1/2:ℝ) := ENNReal.rpow_le_rpow hsq (by norm_num)
    _ = 8 * (∫⁻ ω, Ztr g s N ω ∂μ)^(1/2:ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), h64, ← ENNReal.rpow_mul]
        norm_num
    _ ≤ 8 * (ENNReal.ofReal (2/((s-2)*Real.log 2)) * (eLpNorm f 2 μ)^2)^(1/2:ℝ) :=
        mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow hZ (by norm_num)) (by norm_num)
    _ = 8 * ((ENNReal.ofReal (2/((s-2)*Real.log 2)))^(1/2:ℝ) * eLpNorm f 2 μ) := by
        congr 1
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          show ((eLpNorm f 2 μ)^2) = (eLpNorm f 2 μ)^(2:ℝ) from (ENNReal.rpow_natCast _ 2).symm,
          ← ENNReal.rpow_mul]
        norm_num

set_option maxHeartbeats 4000000 in
lemma mv_eLpNorm_Vinf_le (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) [SigmaFiniteFiltration μ ℱ]
    (f : Ω → ℝ) (hf : MemLp f 2 μ) {s : ℝ} (hs : 2 < s) (hs3 : s ≤ 3) :
    eLpNorm (fun ω => ⨆ N, Vtr (fun n => condExp (ℱ n) μ f) s N ω) (2:ℝ≥0∞) μ
      ≤ 8 * ((ENNReal.ofReal (2/((s-2)*Real.log 2)))^(1/2:ℝ) * eLpNorm f 2 μ) := by
  have hgm : ∀ n, Measurable[ℱ n] (condExp (ℱ n) μ f) :=
    fun n => (stronglyMeasurable_condExp (m := ℱ n)).measurable
  rw [Commons.Analysis.MeasureTheory.eLpNorm_iSup_of_monotone (by norm_num) (by norm_num)
    (fun N => measurable_Vtr ℱ _ hgm s N) (Vtr_mono _ s)]
  exact iSup_le (fun N => mv_eLpNorm_Vtr_le ℱ f hf hs hs3 N)

lemma mv_const_bound {s : ℝ} (hs : 2 < s) (hs3 : s ≤ 3) :
    8 * (2/((s-2)*Real.log 2))^(1/2:ℝ) ≤ 10^6/(s-2) := by
  have hpos : 0 < s - 2 := by linarith
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have key : (s - 2) ≤ 2 * Real.log 2 := by
    nlinarith [Real.log_two_gt_d9, hpos]
  have key2 : 2/((s-2)*Real.log 2) ≤ (2/(s-2))^2 := by
    rw [show (2/(s-2))^2 = 4/(s-2)^2 by rw [div_pow]; norm_num,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [key, hpos, hlog]
  have hb : (2/((s-2)*Real.log 2))^(1/2:ℝ) ≤ 2/(s-2) := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_le_iff]
    exact ⟨by positivity, key2⟩
  calc 8 * (2/((s-2)*Real.log 2))^(1/2:ℝ) ≤ 8 * (2/(s-2)) :=
        mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = 16/(s-2) := by ring
    _ ≤ 10^6/(s-2) := by
        rw [div_le_div_iff₀ hpos hpos]; nlinarith

set_option maxHeartbeats 4000000 in
theorem mv_main_sf (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) [SigmaFiniteFiltration μ ℱ]
    (f : Ω → ℝ) (hf : MemLp f 2 μ) {s : ℝ} (hs : 2 < s) (hs3 : s ≤ 3) :
    eLpNorm (fun ω => ⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
        (∑ j ∈ Finset.range J,
          |(condExp (ℱ (u.1 (j+1))) μ f) ω - (condExp (ℱ (u.1 j)) μ f) ω| ^ s) ^ (1 / s))
      (2:ℝ≥0∞) μ
      ≤ ENNReal.ofReal (10^6/(s-2)) * eLpNorm f 2 μ := by
  have hs0 : 0 < s := by linarith
  refine le_trans (mv_statement_le ℱ f hs0) ?_
  refine le_trans (mv_eLpNorm_Vinf_le ℱ f hf hs hs3) ?_
  have hmain : 8 * (ENNReal.ofReal (2/((s-2)*Real.log 2)))^(1/2:ℝ)
      ≤ ENNReal.ofReal (10^6/(s-2)) := by
    rw [show (8:ℝ≥0∞) * (ENNReal.ofReal (2/((s-2)*Real.log 2)))^(1/2:ℝ)
        = ENNReal.ofReal (8 * (2/((s-2)*Real.log 2))^(1/2:ℝ)) from by
      rw [show (8:ℝ≥0∞) = ENNReal.ofReal 8 by norm_num,
        ENNReal.ofReal_rpow_of_nonneg (by positivity : (0:ℝ) ≤ 2/((s-2)*Real.log 2)) (by norm_num),
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 8)]]
    exact ENNReal.ofReal_le_ofReal (mv_const_bound hs hs3)
  calc 8 * ((ENNReal.ofReal (2/((s-2)*Real.log 2)))^(1/2:ℝ) * eLpNorm f 2 μ)
      = (8 * (ENNReal.ofReal (2/((s-2)*Real.log 2)))^(1/2:ℝ)) * eLpNorm f 2 μ := by rw [mul_assoc]
    _ ≤ ENNReal.ofReal (10^6/(s-2)) * eLpNorm f 2 μ :=
        mul_le_mul_of_nonneg_right hmain zero_le


set_option maxHeartbeats 4000000 in
lemma mv_eLpNorm_Vinf_le' (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) [SigmaFiniteFiltration μ ℱ]
    (f : Ω → ℝ) (hf : MemLp f 2 μ) {s : ℝ} (hs : 2 < s) (hs3 : s ≤ 3) :
    eLpNorm (fun ω => ⨆ N, Vtr (fun n => condExp (ℱ n) μ f) s N ω) (2:ℝ≥0∞) μ
      ≤ ENNReal.ofReal (10^6/(s-2)) * eLpNorm f 2 μ := by
  refine le_trans (mv_eLpNorm_Vinf_le ℱ f hf hs hs3) ?_
  have hmain : 8 * (ENNReal.ofReal (2/((s-2)*Real.log 2)))^(1/2:ℝ)
      ≤ ENNReal.ofReal (10^6/(s-2)) := by
    rw [show (8:ℝ≥0∞) * (ENNReal.ofReal (2/((s-2)*Real.log 2)))^(1/2:ℝ)
        = ENNReal.ofReal (8 * (2/((s-2)*Real.log 2))^(1/2:ℝ)) from by
      rw [show (8:ℝ≥0∞) = ENNReal.ofReal 8 by norm_num,
        ENNReal.ofReal_rpow_of_nonneg (by positivity : (0:ℝ) ≤ 2/((s-2)*Real.log 2)) (by norm_num),
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 8)]]
    exact ENNReal.ofReal_le_ofReal (mv_const_bound hs hs3)
  calc 8 * ((ENNReal.ofReal (2/((s-2)*Real.log 2)))^(1/2:ℝ) * eLpNorm f 2 μ)
      = (8 * (ENNReal.ofReal (2/((s-2)*Real.log 2)))^(1/2:ℝ)) * eLpNorm f 2 μ := by rw [mul_assoc]
    _ ≤ ENNReal.ofReal (10^6/(s-2)) * eLpNorm f 2 μ := mul_le_mul_of_nonneg_right hmain zero_le

set_option maxHeartbeats 2000000 in
lemma mv_trim_mono (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) {n k : ℕ} (hnk : n ≤ k)
    (h : SigmaFinite (μ.trim (ℱ.le' n))) : SigmaFinite (μ.trim (ℱ.le' k)) := by
  haveI := h
  exact sigmaFiniteTrim_mono (ℱ.le' k) (ℱ.mono hnk)

set_option maxHeartbeats 8000000 in
theorem martingale_variation_l2 :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} {m : MeasurableSpace Ω} (μ : MeasureTheory.Measure Ω)
      [MeasureTheory.SigmaFinite μ] (ℱ : MeasureTheory.Filtration ℕ m) (s : ℝ) (hs : 2 < s)
      (hs3 : s ≤ 3) (f : Ω → ℝ), MeasureTheory.MemLp f 2 μ →
      MeasureTheory.eLpNorm (fun ω => ⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
        (Finset.sum (Finset.range J) (fun j =>
          ‖(MeasureTheory.condExp (ℱ (u.1 (j + 1))) μ f) ω
            - (MeasureTheory.condExp (ℱ (u.1 j)) μ f) ω‖ ^ s)) ^ (1 / s)) 2 μ
      ≤ ENNReal.ofReal (C / (s - 2)) * MeasureTheory.eLpNorm f 2 μ := by
  refine ⟨10^7, by norm_num, ?_⟩
  intro Ω m μ hσ ℱ s hs hs3 f hf
  classical
  have hs0 : 0 < s := by linarith
  have h1s0 : (0:ℝ) < 1/s := by positivity
  set Vf : Ω → ℝ := fun ω => ⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
      (∑ j ∈ Finset.range J,
        ‖(condExp (ℱ (u.1 (j+1))) μ f) ω - (condExp (ℱ (u.1 j)) μ f) ω‖ ^ s) ^ (1/s) with hVf
  change eLpNorm Vf (2:ℝ≥0∞) μ ≤ ENNReal.ofReal (10^7/(s-2)) * eLpNorm f 2 μ
  have key : ∀ (𝒢 : Filtration ℕ m) [SigmaFiniteFiltration μ 𝒢],
      eLpNorm (fun ω => ⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
        (∑ j ∈ Finset.range J,
          ‖(condExp (𝒢 (u.1 (j+1))) μ f) ω - (condExp (𝒢 (u.1 j)) μ f) ω‖ ^ s) ^ (1/s))
        (2:ℝ≥0∞) μ ≤ ENNReal.ofReal (10^6/(s-2)) * eLpNorm f 2 μ := by
    intro 𝒢 _
    simpa only [Real.norm_eq_abs] using mv_main_sf 𝒢 f hf hs hs3
  have hVfnn : ∀ ω, 0 ≤ Vf ω := by
    intro ω
    refine Real.iSup_nonneg (fun u => ?_)
    refine Real.iSup_nonneg (fun J => ?_)
    exact Real.rpow_nonneg (Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (norm_nonneg _) s)) _
  by_cases hfi : Integrable f μ
  · by_cases hSFF : SigmaFiniteFiltration μ ℱ
    · haveI : SigmaFiniteFiltration μ ℱ := hSFF
      have h1 : ENNReal.ofReal (10^6/(s-2)) ≤ ENNReal.ofReal (10^7/(s-2)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
      exact le_trans (key ℱ) (mul_le_mul_of_nonneg_right h1 zero_le)
    · by_cases hex : ∃ n : ℕ, SigmaFinite (μ.trim (ℱ.le' n))
      · let n₀ := Nat.find hex
        have hn₀ : SigmaFinite (μ.trim (ℱ.le' n₀)) := Nat.find_spec hex
        have hge : ∀ n, n₀ ≤ n → SigmaFinite (μ.trim (ℱ.le' n)) :=
          fun n hn => mv_trim_mono ℱ hn hn₀
        let ℱₛ : Filtration ℕ m :=
          { seq := fun k => ℱ (n₀ + k)
            mono' := fun i j hij => ℱ.mono (by omega)
            le' := fun k => ℱ.le' (n₀ + k) }
        haveI : SigmaFiniteFiltration μ ℱₛ := ⟨fun k => hge (n₀ + k) (by omega)⟩
        let VSp : Ω → ℝ≥0∞ := fun ω => ⨆ N, Vtr (fun n => condExp (ℱₛ n) μ f) s N ω
        have hVSpb : eLpNorm VSp (2:ℝ≥0∞) μ ≤ ENNReal.ofReal (10^6/(s-2)) * eLpNorm f 2 μ :=
          mv_eLpNorm_Vinf_le' (μ := μ) ℱₛ f hf hs hs3
        let Vp : Ω → ℝ := fun ω => ⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
            (∑ j ∈ Finset.range J,
              ‖(condExp (ℱₛ (u.1 (j+1))) μ f) ω - (condExp (ℱₛ (u.1 j)) μ f) ω‖ ^ s) ^ (1/s)
        have hVpnn : ∀ ω, 0 ≤ Vp ω := by
          intro ω
          refine Real.iSup_nonneg (fun u => ?_)
          refine Real.iSup_nonneg (fun J => ?_)
          exact Real.rpow_nonneg (Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (norm_nonneg _) s)) _
        have hVp_le : ∀ ω, ENNReal.ofReal (Vp ω) ≤ VSp ω := by
          intro ω
          have hsn : 0 ≤ (⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
              (∑ j ∈ Finset.range J,
                |(condExp (ℱₛ (u.1 (j+1))) μ f) ω - (condExp (ℱₛ (u.1 j)) μ f) ω| ^ s) ^ (1/s)) := by
            refine Real.iSup_nonneg (fun u => ?_); refine Real.iSup_nonneg (fun J => ?_)
            exact Real.rpow_nonneg (Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (abs_nonneg _) s)) _
          have hp := mv_pointwise_bound (μ := μ) ℱₛ f s ω
          rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hsn] at hp
          have hEq : Vp ω = (⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
              (∑ j ∈ Finset.range J,
                |(condExp (ℱₛ (u.1 (j+1))) μ f) ω - (condExp (ℱₛ (u.1 j)) μ f) ω| ^ s) ^ (1/s)) := by
            simp only [Vp, Real.norm_eq_abs]
          rw [hEq]
          exact hp
        have hpt : ∀ ω, Vf ω ≤ |(condExp (ℱ n₀) μ f) ω| + 2 * Vp ω := by
          intro ω
          have hz : ∀ k < n₀, (fun k => (condExp (ℱ k) μ f) ω) k = 0 := by
            intro k hk
            have hns : ¬ SigmaFinite (μ.trim (ℱ.le' k)) :=
              fun hc => Nat.find_min hex (show k < Nat.find hex from hk) hc
            simp only [condExp_of_not_sigmaFinite (ℱ.le' k) hns, Pi.zero_apply]
          have hb := Commons.Analysis.Series.variation_shift_le
            (fun k => (condExp (ℱ k) μ f) ω) hs n₀ hz
          have hL : Vf ω = (⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
              (∑ j ∈ Finset.range J,
                |(condExp (ℱ (u.1 (j+1))) μ f) ω - (condExp (ℱ (u.1 j)) μ f) ω| ^ s) ^ (1/s)) := by
            simp only [hVf, Real.norm_eq_abs]
          have hR : Vp ω = (⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
              (∑ j ∈ Finset.range J,
                |(fun k => (condExp (ℱ k) μ f) ω) (n₀ + u.1 (j+1))
                  - (fun k => (condExp (ℱ k) μ f) ω) (n₀ + u.1 j)| ^ s) ^ (1/s)) := by
            simp only [Vp, ℱₛ, Real.norm_eq_abs]
          rw [hL, hR]
          exact hb
        have hmem1 : AEStronglyMeasurable
            (fun ω => ENNReal.ofReal |(condExp (ℱ n₀) μ f) ω|) μ :=
          (((stronglyMeasurable_condExp (m := ℱ n₀)).measurable.mono (ℱ.le' n₀) le_rfl).abs.ennreal_ofReal).aestronglyMeasurable
        have hmem2 : AEStronglyMeasurable (fun ω => (2:ℝ≥0∞) * VSp ω) μ :=
          ((Measurable.const_mul (Measurable.iSup (fun N => measurable_Vtr ℱₛ _
              (fun n => (stronglyMeasurable_condExp (m := ℱₛ n)).measurable) s N)) 2)).aestronglyMeasurable
        have hpt_enorm : ∀ ω, ‖Vf ω‖ₑ ≤ ENNReal.ofReal |(condExp (ℱ n₀) μ f) ω|
            + (2:ℝ≥0∞) * VSp ω := by
          intro ω
          rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hVfnn ω)]
          calc ENNReal.ofReal (Vf ω)
              ≤ ENNReal.ofReal (|(condExp (ℱ n₀) μ f) ω| + 2 * Vp ω) :=
                ENNReal.ofReal_le_ofReal (hpt ω)
            _ ≤ ENNReal.ofReal |(condExp (ℱ n₀) μ f) ω| + ENNReal.ofReal (2 * Vp ω) :=
                ENNReal.ofReal_add_le
            _ = ENNReal.ofReal |(condExp (ℱ n₀) μ f) ω| + 2 * ENNReal.ofReal (Vp ω) := by
                rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
                  show ENNReal.ofReal (2:ℝ) = 2 by norm_num]
            _ ≤ ENNReal.ofReal |(condExp (ℱ n₀) μ f) ω| + (2:ℝ≥0∞) * VSp ω := by
                refine add_le_add_right ?_ _
                exact mul_le_mul_of_nonneg_left (hVp_le ω) (by norm_num)
        calc eLpNorm Vf (2:ℝ≥0∞) μ
            ≤ eLpNorm (fun ω => ENNReal.ofReal |(condExp (ℱ n₀) μ f) ω|
                + (2:ℝ≥0∞) * VSp ω) (2:ℝ≥0∞) μ := by
              have hVfm : AEStronglyMeasurable Vf μ := by
                have hm := measurable_iSup_variation (fun n => condExp (ℱ n) μ f) hs0
                  (fun N => measurable_Vtr ℱ _
                    (fun n => (stronglyMeasurable_condExp (m := ℱ n)).measurable) s N)
                refine hm.aestronglyMeasurable.congr (Filter.Eventually.of_forall fun ω => ?_)
                simp only [hVf, Real.norm_eq_abs]
              exact eLpNorm_mono_enorm hVfm hpt_enorm
          _ ≤ eLpNorm (fun ω => ENNReal.ofReal |(condExp (ℱ n₀) μ f) ω|) (2:ℝ≥0∞) μ
              + eLpNorm (fun ω => (2:ℝ≥0∞) * VSp ω) (2:ℝ≥0∞) μ := by
              rw [show (fun ω => ENNReal.ofReal |(condExp (ℱ n₀) μ f) ω| + (2:ℝ≥0∞) * VSp ω)
                  = (fun ω => ENNReal.ofReal |(condExp (ℱ n₀) μ f) ω|)
                    + (fun ω => (2:ℝ≥0∞) * VSp ω) from rfl]
              exact eLpNorm_add_le (by norm_num)
          _ = eLpNorm (condExp (ℱ n₀) μ f) (2:ℝ≥0∞) μ + (2:ℝ≥0∞) * eLpNorm VSp (2:ℝ≥0∞) μ := by
              have hB : eLpNorm (fun ω => (2:ℝ≥0∞) * VSp ω) (2:ℝ≥0∞) μ
                  = (2:ℝ≥0∞) * eLpNorm VSp (2:ℝ≥0∞) μ :=
                Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal (c := (2:ℝ≥0∞)) (V := VSp)
                  (p := (2:ℝ≥0∞)) (by norm_num) (by norm_num) (by norm_num)
              have hA : eLpNorm (fun ω => ENNReal.ofReal |(condExp (ℱ n₀) μ f) ω|) (2:ℝ≥0∞) μ
                  = eLpNorm (condExp (ℱ n₀) μ f) (2:ℝ≥0∞) μ := by
                rw [show (fun ω => ENNReal.ofReal |(condExp (ℱ n₀) μ f) ω|)
                    = ENNReal.ofReal ∘ (fun ω => |(condExp (ℱ n₀) μ f) ω|) from rfl]
                rw [eLpNorm_ofReal (fun ω => |(condExp (ℱ n₀) μ f) ω|)
                  (Filter.Eventually.of_forall (fun ω => abs_nonneg _))]
                simpa only [Real.norm_eq_abs] using eLpNorm_norm (p := 2) (condExp (ℱ n₀) μ f)
                  (integrable_condExp (m := ℱ n₀) (μ := μ) (f := f)).aestronglyMeasurable
              rw [hA, hB]
          _ ≤ eLpNorm f 2 μ + (2:ℝ≥0∞) * (ENNReal.ofReal (10^6/(s-2)) * eLpNorm f 2 μ) := by
              refine add_le_add ?_ (mul_le_mul_of_nonneg_left hVSpb (by norm_num))
              exact eLpNorm_condExp_le_eLpNorm (μ := μ) (m := ℱ n₀) f (by norm_num)
          _ ≤ ENNReal.ofReal (10^7/(s-2)) * eLpNorm f 2 μ := by
              have h3 : (3:ℝ≥0∞) * ENNReal.ofReal (10^6/(s-2))
                  ≤ ENNReal.ofReal (10^7/(s-2)) := by
                rw [show (3:ℝ≥0∞) * ENNReal.ofReal (10^6/(s-2))
                    = ENNReal.ofReal (3 * (10^6/(s-2))) from by
                  rw [show (3:ℝ≥0∞) = ENNReal.ofReal 3 by norm_num,
                    ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)]]
                refine ENNReal.ofReal_le_ofReal ?_
                rw [show (3:ℝ) * (10^6/(s-2)) = 3*10^6/(s-2) by ring,
                  div_le_div_iff₀ (by linarith) (by linarith)]
                nlinarith
              calc eLpNorm f 2 μ + (2:ℝ≥0∞) * (ENNReal.ofReal (10^6/(s-2)) * eLpNorm f 2 μ)
                  = ((1:ℝ≥0∞) + 2 * ENNReal.ofReal (10^6/(s-2))) * eLpNorm f 2 μ := by ring
                _ ≤ ENNReal.ofReal (10^7/(s-2)) * eLpNorm f 2 μ := by
                  refine mul_le_mul_of_nonneg_right ?_ zero_le
                  have h1 : (1:ℝ≥0∞) ≤ ENNReal.ofReal (10^6/(s-2)) := by
                    rw [← ENNReal.ofReal_one]
                    refine ENNReal.ofReal_le_ofReal ?_
                    rw [le_div_iff₀ (by linarith)]; nlinarith
                  calc (1:ℝ≥0∞) + 2 * ENNReal.ofReal (10^6/(s-2))
                      ≤ ENNReal.ofReal (10^6/(s-2)) + 2 * ENNReal.ofReal (10^6/(s-2)) :=
                        add_le_add_left h1 _
                    _ = (3:ℝ≥0∞) * ENNReal.ofReal (10^6/(s-2)) := by ring
                    _ ≤ ENNReal.ofReal (10^7/(s-2)) := h3
      · have hcond : ∀ n, condExp (ℱ n) μ f = 0 := fun n => by
          have hns : ¬ SigmaFinite (μ.trim (ℱ.le' n)) := fun hc => hex ⟨n, hc⟩
          exact condExp_of_not_sigmaFinite (ℱ.le' n) hns
        have hV0 : Vf = 0 := by
          funext ω
          simp only [hVf, hcond, Pi.zero_apply, sub_self, norm_zero]
          simp only [Real.zero_rpow hs0.ne', Finset.sum_const_zero, Real.zero_rpow h1s0.ne']
          simp
        rw [hV0, eLpNorm_zero]
        exact zero_le
  · have hcond : ∀ n, condExp (ℱ n) μ f = 0 := fun n => condExp_of_not_integrable hfi
    have hV0 : Vf = 0 := by
      funext ω
      simp only [hVf, hcond, Pi.zero_apply, sub_self, norm_zero]
      simp only [Real.zero_rpow hs0.ne', Finset.sum_const_zero, Real.zero_rpow h1s0.ne']
      simp
    rw [hV0, eLpNorm_zero]
    exact zero_le

end Commons.Analysis.Probability
