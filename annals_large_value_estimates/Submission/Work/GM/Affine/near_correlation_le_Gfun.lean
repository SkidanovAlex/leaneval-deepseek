import Mathlib
import Submission.Work.GM.Affine.nearcorr_defs
import Submission.Work.GM.Affine.nearcorr_fejerK_nonneg
import Submission.Work.GM.Affine.nearcorr_fejerK_pairing
import Submission.Work.GM.Affine.nearcorr_Afun_fhat
import Submission.Work.GM.Affine.nearcorr_Afun_eq_sum_gm
import Submission.Work.GM.Affine.nearcorr_gm_le_smoothed
import Submission.Work.GM.Affine.nearcorr_Afun_eq_zero_of_notMem
import Submission.Work.GM.Affine.nearcorr_Afun_continuous
import Submission.Work.GM.Affine.WinMass_fejer_defs
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.WinMass_basic
import Submission.Work.GM.Affine.rho_kernel_domination
import Submission.Work.GM.Affine.psiSmooth_fhat_lower_bound
import Submission.Work.GM.Affine.smoothed_L2_le
import Submission.Work.GM.Affine.autocorr_eq_spectral

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.GM.Affine

noncomputable section

/-! ## Elementary helpers -/

/-- `fejerK M₃` is continuous. -/
lemma nearcorr_continuous_fejerK (M₃ : ℝ) : Continuous (fejerK M₃) := by
  unfold fejerK
  refine continuous_const.add (continuous_const.mul ?_)
  refine continuous_finsetSum _ (fun k _ => ?_)
  exact continuous_const.mul (Real.continuous_cos.comp (by fun_prop))

/-- Uniform bound for the Fejér kernel. -/
lemma nearcorr_abs_fejerK_le (M₃ x : ℝ) : |fejerK M₃ x| ≤ 1 + 2 * (fejerN M₃ : ℝ) := by
  have hNpos : (0 : ℝ) < (fejerN M₃ : ℝ) :=
    lt_of_lt_of_le zero_lt_one (one_le_fejerN M₃)
  have hcast : (((fejerN M₃ - 1 : ℕ)) : ℝ) = (fejerN M₃ : ℝ) - 1 := by
    rw [Nat.cast_sub (fejerN_pos M₃)]
    norm_num
  set Tf : ℕ → ℝ := fun k => (1 - ((k : ℕ) : ℝ) / (fejerN M₃)) *
    Real.cos (2 * Real.pi * ((k : ℕ) : ℝ) * x) with hTf
  have hterm : ∀ k ∈ Finset.Icc 1 (fejerN M₃ - 1), |Tf k| ≤ 1 := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hkR : ((k : ℕ) : ℝ) ≤ (fejerN M₃ : ℝ) - 1 := by
      have h1 : ((k : ℕ) : ℝ) ≤ (((fejerN M₃ - 1 : ℕ)) : ℝ) := by exact_mod_cast hk.2
      rw [hcast] at h1
      exact h1
    have hnonneg : 0 ≤ ((k : ℕ) : ℝ) / (fejerN M₃) := div_nonneg (Nat.cast_nonneg k) hNpos.le
    have hquot : ((k : ℕ) : ℝ) / (fejerN M₃) ≤ 1 := by
      rw [div_le_one hNpos]
      linarith
    have hnn : 0 ≤ 1 - ((k : ℕ) : ℝ) / (fejerN M₃) := by linarith
    rw [hTf]
    simp only
    rw [abs_mul, abs_of_nonneg hnn]
    calc (1 - ((k : ℕ) : ℝ) / (fejerN M₃)) *
          |Real.cos (2 * Real.pi * ((k : ℕ) : ℝ) * x)|
        ≤ 1 * 1 := mul_le_mul (by linarith) (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one
      _ = 1 := by norm_num
  have hsub : Finset.Icc 1 (fejerN M₃ - 1) ⊆ Finset.range (fejerN M₃) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_range]
    omega
  have hsum : (∑ k ∈ Finset.Icc 1 (fejerN M₃ - 1), |Tf k|) ≤ (fejerN M₃ : ℝ) := by
    calc (∑ k ∈ Finset.Icc 1 (fejerN M₃ - 1), |Tf k|)
        ≤ ∑ k ∈ Finset.Icc 1 (fejerN M₃ - 1), ((1:ℝ)) := Finset.sum_le_sum hterm
      _ ≤ ∑ k ∈ Finset.range (fejerN M₃), ((1:ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => zero_le_one)
      _ = (fejerN M₃ : ℝ) := by simp
  have hsumabs : |∑ k ∈ Finset.Icc 1 (fejerN M₃ - 1), Tf k| ≤ (fejerN M₃ : ℝ) :=
    le_trans (abs_sum_le_sum_abs Tf (Finset.Icc 1 (fejerN M₃ - 1))) hsum
  have hfej : fejerK M₃ x = 1 + 2 * ∑ k ∈ Finset.Icc 1 (fejerN M₃ - 1), Tf k := rfl
  rw [hfej]
  calc |1 + 2 * ∑ k ∈ Finset.Icc 1 (fejerN M₃ - 1), Tf k|
      ≤ 1 + |2 * ∑ k ∈ Finset.Icc 1 (fejerN M₃ - 1), Tf k| := by
        simpa using abs_add_le (1:ℝ) (2 * ∑ k ∈ Finset.Icc 1 (fejerN M₃ - 1), Tf k)
    _ = 1 + 2 * |∑ k ∈ Finset.Icc 1 (fejerN M₃ - 1), Tf k| := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    _ ≤ 1 + 2 * (fejerN M₃ : ℝ) := by linarith [hsumabs]

/-- `SuppHyp` gives compact support. -/
lemma nearcorr_suppHyp_hcs {C₀ : ℝ} (_hC₀ : 1 ≤ C₀) {f : ℝ → ℝ} (hsup : SuppHyp C₀ f) :
    HasCompactSupport f := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (1 / C₀) C₀) isCompact_Icc ?_
  intro u hu
  rw [Function.mem_support] at hu
  exact hsup u hu

/-- The smoothed test function is nonnegative. -/
lemma nearcorr_smoothed_nonneg {T : ℝ} (hT : 0 < T) {f : ℝ → ℝ} (hnn : ∀ u, 0 ≤ f u)
    (u : ℝ) : 0 ≤ smoothed psiSmooth T f u := by
  rw [smoothed]
  exact mul_nonneg hT.le (integral_nonneg fun u' => mul_nonneg (psiSmooth_nonneg _) (hnn u'))

/-- Compact support of `v ↦ g (v / c)`, `c ≠ 0`. -/
lemma nearcorr_hcs_div {g : ℝ → ℝ} (hg : HasCompactSupport g) {c : ℝ} (hc : c ≠ 0) :
    HasCompactSupport (fun v : ℝ => g (v / c)) := by
  have h := hg.comp_smul (c := c⁻¹) (inv_ne_zero hc)
  have hfun : (fun x : ℝ => g (c⁻¹ • x)) = fun v : ℝ => g (v / c) := by
    funext v
    rw [smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [hfun] at h
  exact h

/-- Integrability of `u ↦ f̃ (u/m) f̃ ((u+k)/m')`. -/
lemma nearcorr_integrable_smoothed_mul {C₀ T : ℝ} (hC₀ : 1 ≤ C₀) (hT : 0 < T) {f : ℝ → ℝ}
    (hf : Continuous f) (hsup : SuppHyp C₀ f) (m m' : ℤ) (hm : m ≠ 0) (k : ℝ) :
    Integrable (fun u : ℝ => smoothed psiSmooth T f (u / (m:ℝ)) *
      smoothed psiSmooth T f ((u + k) / (m':ℝ))) := by
  have hfcs : HasCompactSupport f := nearcorr_suppHyp_hcs hC₀ hsup
  have hft_cont : Continuous (smoothed psiSmooth T f) := continuous_smoothed hf hfcs
  have hft_cs : HasCompactSupport (smoothed psiSmooth T f) := hasCompactSupport_smoothed hT hfcs
  have hcont : Continuous (fun u : ℝ => smoothed psiSmooth T f (u / (m:ℝ)) *
      smoothed psiSmooth T f ((u + k) / (m':ℝ))) :=
    (hft_cont.comp (continuous_id.div_const _)).mul
      (hft_cont.comp ((continuous_id.add continuous_const).div_const _))
  have hcs1 : HasCompactSupport (fun u : ℝ => smoothed psiSmooth T f (u / (m:ℝ))) :=
    nearcorr_hcs_div hft_cs (Int.cast_ne_zero.mpr hm)
  exact hcont.integrable_of_hasCompactSupport
    (hcs1.mul_right (f' := fun u : ℝ => smoothed psiSmooth T f ((u + k) / (m':ℝ))))

/-- Integrability of `u ↦ f̃ u · f̃ ((m u + k)/m')`. -/
lemma nearcorr_integrable_smoothed_mul' {C₀ T : ℝ} (hC₀ : 1 ≤ C₀) (hT : 0 < T) {f : ℝ → ℝ}
    (hf : Continuous f) (hsup : SuppHyp C₀ f) (m m' : ℤ) (k : ℝ) :
    Integrable (fun u : ℝ => smoothed psiSmooth T f u *
      smoothed psiSmooth T f (((m:ℝ) * u + k) / (m':ℝ))) := by
  have hfcs : HasCompactSupport f := nearcorr_suppHyp_hcs hC₀ hsup
  have hft_cont : Continuous (smoothed psiSmooth T f) := continuous_smoothed hf hfcs
  have hft_cs : HasCompactSupport (smoothed psiSmooth T f) := hasCompactSupport_smoothed hT hfcs
  have hcont : Continuous (fun u : ℝ => smoothed psiSmooth T f u *
      smoothed psiSmooth T f (((m:ℝ)*u + k) / (m':ℝ))) :=
    hft_cont.mul (hft_cont.comp (((continuous_const.mul continuous_id).add continuous_const).div_const _))
  exact hcont.integrable_of_hasCompactSupport
    (hft_cs.mul_right (f' := fun u : ℝ => smoothed psiSmooth T f (((m:ℝ)*u + k) / (m':ℝ))))

/-- Change of variables `v = m u` in the shifted product of smoothed test functions. -/
lemma nearcorr_integral_div_shift {C₀ T : ℝ} (hC₀ : 1 ≤ C₀) (hT : 0 < T) {f : ℝ → ℝ}
    (hf : Continuous f) (hsup : SuppHyp C₀ f) {m : ℤ} (hm : 0 < m) (m' : ℤ) (k : ℝ) :
    (∫ v : ℝ, smoothed psiSmooth T f (v / (m:ℝ)) *
        smoothed psiSmooth T f ((v + k) / (m':ℝ)))
      = (m:ℝ) * NTerm T f m m' k := by
  unfold NTerm
  set φ : ℝ → ℝ := fun u => smoothed psiSmooth T f u *
    smoothed psiSmooth T f (((m:ℝ) * u + k) / (m':ℝ)) with hφ
  have h1 : (∫ v : ℝ, smoothed psiSmooth T f (v / (m:ℝ)) *
        smoothed psiSmooth T f ((v + k) / (m':ℝ)))
      = ∫ v : ℝ, φ (v / (m:ℝ)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
    rw [hφ]
    simp only
    have harg : (m:ℝ) * (v / (m:ℝ)) + k = v + k := by
      rw [mul_comm, div_mul_cancel₀ v (Int.cast_ne_zero.mpr (ne_of_gt hm))]
    rw [harg]
  rw [h1, Measure.integral_comp_div φ (m:ℝ), abs_of_pos (Int.cast_pos.mpr hm), smul_eq_mul]

/-! ## The correlation bound for a single shift -/

lemma nearcorr_single_corr {C₀ K T M₂ : ℝ} (hC₀ : 1 ≤ C₀) (hT : 1 ≤ T) (hK : 8 ≤ K)
    (hM₂ : 1 ≤ M₂) {f : ℝ → ℝ} (hf : Continuous f) (hfnn : ∀ u, 0 ≤ f u)
    (hsup : SuppHyp C₀ f) (k : ℝ) :
    (∫ v : ℝ, Afun f M₂ K T v * Afun f M₂ K T (v + k))
      ≤ ∑ m ∈ R2 M₂, ∑ m' ∈ R2 M₂, (16 * K ^ 2) * (m : ℝ) * NTerm T f m m' k := by
  have hTpos : 0 < T := by linarith
  have hKpos : 0 < K := by linarith
  have hM₂pos : 0 < M₂ := by linarith
  have hfcs : HasCompactSupport f := nearcorr_suppHyp_hcs hC₀ hsup
  have hfint : Integrable f := hf.integrable_of_hasCompactSupport hfcs
  have hft_nn : ∀ u : ℝ, 0 ≤ smoothed psiSmooth T f u :=
    fun u => nearcorr_smoothed_nonneg hTpos hfnn u
  have hAcont : Continuous (Afun f M₂ K T) := nearcorr_Afun_continuous hf M₂ K T
  have hAsupp : ∀ v : ℝ, v ∉ Set.Icc (M₂ / C₀ - smScale K T M₂ / 4)
      (2 * C₀ * M₂ + smScale K T M₂ / 4) → Afun f M₂ K T v = 0 :=
    fun v hv => nearcorr_Afun_eq_zero_of_notMem hC₀ hsup hM₂pos hKpos hTpos hv
  have hAcs : HasCompactSupport (Afun f M₂ K T) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := Set.Icc (M₂ / C₀ - smScale K T M₂ / 4)
        (2 * C₀ * M₂ + smScale K T M₂ / 4)) isCompact_Icc ?_
    intro v hv
    rw [Function.mem_support] at hv
    by_contra hmem
    exact hv (hAsupp v hmem)
  have hAle : ∀ v : ℝ, Afun f M₂ K T v ≤
      ∑ m ∈ R2 M₂, 4 * K * smoothed psiSmooth T f (v / (m : ℝ)) := by
    intro v
    rw [nearcorr_Afun_eq_sum_gm hC₀ hf hsup hM₂pos hKpos hTpos v]
    exact Finset.sum_le_sum
      (fun m hm => nearcorr_gm_le_smoothed hT hK hM₂ hfnn hfint hm (v / (m : ℝ)))
  have hPnn : ∀ v : ℝ, 0 ≤ ∑ m ∈ R2 M₂, 4 * K * smoothed psiSmooth T f (v / (m : ℝ)) :=
    fun v => Finset.sum_nonneg (fun m _ => mul_nonneg (by positivity) (hft_nn _))
  have hAprod : ∀ v : ℝ, Afun f M₂ K T v * Afun f M₂ K T (v + k) ≤
      ∑ m ∈ R2 M₂, ∑ m' ∈ R2 M₂, (16 * K^2) *
        (smoothed psiSmooth T f (v/(m:ℝ)) *
          smoothed psiSmooth T f ((v+k)/(m':ℝ))) := by
    intro v
    calc Afun f M₂ K T v * Afun f M₂ K T (v + k)
        ≤ (∑ m ∈ R2 M₂, 4*K*smoothed psiSmooth T f (v/(m:ℝ))) *
            (∑ m' ∈ R2 M₂, 4*K*smoothed psiSmooth T f ((v+k)/(m':ℝ))) :=
          mul_le_mul (hAle v) (hAle (v+k)) (Afun_nonneg hfnn M₂ K T (v+k)) (hPnn v)
      _ = ∑ m ∈ R2 M₂, ∑ m' ∈ R2 M₂,
            (4*K*smoothed psiSmooth T f (v/(m:ℝ))) *
              (4*K*smoothed psiSmooth T f ((v+k)/(m':ℝ))) := by
          rw [Finset.sum_mul_sum]
      _ = ∑ m ∈ R2 M₂, ∑ m' ∈ R2 M₂, (16 * K^2) *
            (smoothed psiSmooth T f (v/(m:ℝ)) *
              smoothed psiSmooth T f ((v+k)/(m':ℝ))) := by
          refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun m' _ => ?_))
          ring
  have hIA : Integrable (fun v : ℝ => Afun f M₂ K T v * Afun f M₂ K T (v + k)) :=
    (hAcont.mul (hAcont.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      (hAcs.mul_right (f' := fun v : ℝ => Afun f M₂ K T (v + k)))
  have hterm : ∀ m ∈ R2 M₂, ∀ m' ∈ R2 M₂,
      Integrable (fun v : ℝ => (16 * K^2) * (smoothed psiSmooth T f (v/(m:ℝ)) *
        smoothed psiSmooth T f ((v+k)/(m':ℝ)))) :=
    fun m hm m' _ => (nearcorr_integrable_smoothed_mul hC₀ hTpos hf hsup m m'
      (Int.cast_ne_zero.mpr (ne_of_gt (Int.cast_pos.mp (R2_pos' hm)))) k).const_mul _
  have hsumint : Integrable (fun v : ℝ => ∑ m ∈ R2 M₂, ∑ m' ∈ R2 M₂, (16 * K^2) *
      (smoothed psiSmooth T f (v/(m:ℝ)) * smoothed psiSmooth T f ((v+k)/(m':ℝ)))) :=
    integrable_finsetSum _ (fun m hm => integrable_finsetSum _ (fun m' hm' => hterm m hm m' hm'))
  calc (∫ v : ℝ, Afun f M₂ K T v * Afun f M₂ K T (v + k))
      ≤ ∫ v : ℝ, ∑ m ∈ R2 M₂, ∑ m' ∈ R2 M₂, (16 * K^2) *
          (smoothed psiSmooth T f (v/(m:ℝ)) *
            smoothed psiSmooth T f ((v+k)/(m':ℝ))) :=
        integral_mono hIA hsumint (fun v => hAprod v)
    _ = ∑ m ∈ R2 M₂, ∑ m' ∈ R2 M₂, ∫ v : ℝ, (16 * K^2) *
          (smoothed psiSmooth T f (v/(m:ℝ)) *
            smoothed psiSmooth T f ((v+k)/(m':ℝ))) := by
        rw [integral_finsetSum]
        · refine Finset.sum_congr rfl (fun m hm => ?_)
          rw [integral_finsetSum]
          intro m' hm'
          exact hterm m hm m' hm'
        · intro m hm
          exact integrable_finsetSum _ (fun m' hm' => hterm m hm m' hm')
    _ = ∑ m ∈ R2 M₂, ∑ m' ∈ R2 M₂, (16 * K^2) * ∫ v : ℝ,
          (smoothed psiSmooth T f (v/(m:ℝ)) *
            smoothed psiSmooth T f ((v+k)/(m':ℝ))) := by
        refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun m' _ => ?_))
        rw [integral_const_mul]
    _ = ∑ m ∈ R2 M₂, ∑ m' ∈ R2 M₂, (16 * K^2) * (m:ℝ) * NTerm T f m m' k := by
        refine Finset.sum_congr rfl (fun m hm => Finset.sum_congr rfl (fun m' _ => ?_))
        rw [nearcorr_integral_div_shift hC₀ hTpos hf hsup (Int.cast_pos.mp (R2_pos' hm)) m' k]
        ring

/-! ## The `Gfun` sum -/

lemma nearcorr_sum_gfun_eq {C₀ T M₂ : ℝ} (hC₀ : 1 ≤ C₀) (hT : 0 < T) {f : ℝ → ℝ}
    (hf : Continuous f) (hsup : SuppHyp C₀ f) :
    (∑ m ∈ R2 M₂, ∑ m' ∈ R2 M₂, ∑ k ∈ Finset.Icc (-(⌊2 * C₀ * M₂⌋)) ⌊2 * C₀ * M₂⌋,
        NTerm T f m m' (k : ℝ))
      = ∫ u : ℝ, smoothed psiSmooth T f u * Gfun C₀ T M₂ f u := by
  have hper : ∀ m ∈ R2 M₂, ∀ m' ∈ R2 M₂, ∀ k ∈ Finset.Icc (-(⌊2 * C₀ * M₂⌋)) ⌊2 * C₀ * M₂⌋,
      Integrable (fun u : ℝ => smoothed psiSmooth T f u *
        smoothed psiSmooth T f (((m:ℝ) * u + (k:ℝ)) / (m':ℝ))) :=
    fun m _ m' _ k _ => nearcorr_integrable_smoothed_mul' hC₀ hT hf hsup m m' (k:ℝ)
  unfold NTerm
  unfold Gfun
  rw [show (∫ u : ℝ, smoothed psiSmooth T f u *
        (∑ m ∈ R2 M₂, ∑ m' ∈ R2 M₂, ∑ j ∈ Finset.Icc (-⌊2 * C₀ * M₂⌋) ⌊2 * C₀ * M₂⌋,
          smoothed psiSmooth T f (((m:ℝ) * u + (j:ℝ)) / (m':ℝ))))
      = ∫ u : ℝ, ∑ m ∈ R2 M₂, ∑ m' ∈ R2 M₂, ∑ j ∈ Finset.Icc (-⌊2 * C₀ * M₂⌋) ⌊2 * C₀ * M₂⌋,
          (smoothed psiSmooth T f u * smoothed psiSmooth T f (((m:ℝ) * u + (j:ℝ)) / (m':ℝ)))
      from by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
        simp only [Finset.mul_sum]]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl (fun m' hm' => ?_)
      rw [integral_finsetSum]
      intro k hk
      exact hper m hm m' hm' k hk
    · intro m' hm'
      exact integrable_finsetSum _ (fun k hk => hper m hm m' hm' k hk)
  · intro m hm
    exact integrable_finsetSum _
      (fun m' hm' => integrable_finsetSum _ (fun k hk => hper m hm m' hm' k hk))

/-! ## The `k`-truncated Fejér sum -/

lemma nearcorr_fejer_sum_bound {C₀ K T M₂ M₃ : ℝ} (hC₀ : 1 ≤ C₀) (hT : 1 ≤ T) (hK : 8 ≤ K)
    (hM₂ : 2 * C₀ ≤ M₂) (hT2 : 2 * C₀ ≤ T) {f : ℝ → ℝ} (hf : Continuous f)
    (hfnn : ∀ u, 0 ≤ f u) (hsup : SuppHyp C₀ f) :
    (∫ x : ℝ, ‖Fhat (Afun f M₂ K T) x‖ ^ 2 * fejerK M₃ x)
      ≤ ∑ k ∈ Finset.Icc (-(⌊2 * C₀ * M₂⌋)) ⌊2 * C₀ * M₂⌋,
          ∫ v : ℝ, Afun f M₂ K T v * Afun f M₂ K T (v + (k : ℝ)) := by
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have hTpos : 0 < T := by linarith
  have hKpos : 0 < K := by linarith
  have hM₂pos : 0 < M₂ := by linarith
  have hAcont : Continuous (Afun f M₂ K T) := nearcorr_Afun_continuous hf M₂ K T
  have hAsupp : ∀ v : ℝ, v ∉ Set.Icc (M₂ / C₀ - smScale K T M₂ / 4)
      (2 * C₀ * M₂ + smScale K T M₂ / 4) → Afun f M₂ K T v = 0 :=
    fun v hv => nearcorr_Afun_eq_zero_of_notMem hC₀ hsup hM₂pos hKpos hTpos hv
  have hAcs : HasCompactSupport (Afun f M₂ K T) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := Set.Icc (M₂ / C₀ - smScale K T M₂ / 4) (2 * C₀ * M₂ + smScale K T M₂ / 4))
      isCompact_Icc ?_
    intro v hv
    rw [Function.mem_support] at hv
    by_contra hmem
    exact hv (hAsupp v hmem)
  have hwidth : (2 * C₀ * M₂ + smScale K T M₂ / 4) - (M₂ / C₀ - smScale K T M₂ / 4)
      ≤ 2 * C₀ * M₂ := by
    have hC₀4KT : C₀ ≤ 4 * K * T := by nlinarith [hK, hT2, hC₀pos, hTpos]
    have h1 : smScale K T M₂ / 2 ≤ M₂ / C₀ := by
      rw [smScale, div_div, div_le_div_iff₀ (by positivity) hC₀pos]
      nlinarith [hC₀4KT, hM₂pos]
    linarith
  have hAknneg : ∀ k : ℤ, 0 ≤ ∫ v : ℝ, Afun f M₂ K T v * Afun f M₂ K T (v + (k:ℝ)) :=
    fun k => integral_nonneg (fun v => mul_nonneg (Afun_nonneg hfnn M₂ K T v)
      (Afun_nonneg hfnn M₂ K T (v + (k:ℝ))))
  have hterm_le : ∀ k ∈ Finset.Icc (-((fejerN M₃ : ℤ) - 1)) ((fejerN M₃ : ℤ) - 1),
      (1 - |(k:ℝ)| / (fejerN M₃ : ℝ)) *
          (∫ v : ℝ, Afun f M₂ K T v * Afun f M₂ K T (v + (k:ℝ)))
        ≤ ∫ v : ℝ, Afun f M₂ K T v * Afun f M₂ K T (v + (k:ℝ)) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hNpos : (0:ℝ) < (fejerN M₃ : ℝ) := lt_of_lt_of_le zero_lt_one (one_le_fejerN M₃)
    have h1 : -(((((fejerN M₃ : ℤ) - 1 : ℤ))) : ℝ) ≤ (k:ℝ) := by exact_mod_cast hk.1
    have h2 : (k:ℝ) ≤ ((((fejerN M₃ : ℤ) - 1 : ℤ)) : ℝ) := by exact_mod_cast hk.2
    have h3 : (((((fejerN M₃ : ℤ) - 1 : ℤ))) : ℝ) = (fejerN M₃ : ℝ) - 1 := by push_cast; ring
    rw [h3] at h1 h2
    have hle1 : 1 - |(k:ℝ)| / (fejerN M₃ : ℝ) ≤ 1 := by
      have := div_nonneg (abs_nonneg (k:ℝ)) hNpos.le
      linarith
    calc (1 - |(k:ℝ)| / (fejerN M₃ : ℝ)) *
            (∫ v : ℝ, Afun f M₂ K T v * Afun f M₂ K T (v + (k:ℝ)))
        ≤ 1 * (∫ v : ℝ, Afun f M₂ K T v * Afun f M₂ K T (v + (k:ℝ))) :=
          mul_le_mul_of_nonneg_right hle1 (hAknneg k)
      _ = (∫ v : ℝ, Afun f M₂ K T v * Afun f M₂ K T (v + (k:ℝ))) := one_mul _
  have hzero : ∀ k ∈ Finset.Icc (-((fejerN M₃ : ℤ) - 1)) ((fejerN M₃ : ℤ) - 1),
      k ∉ Finset.Icc (-(⌊2 * C₀ * M₂⌋)) ⌊2 * C₀ * M₂⌋ →
      (∫ v : ℝ, Afun f M₂ K T v * Afun f M₂ K T (v + (k:ℝ))) = 0 := by
    intro k _ hk
    have hpt : ∀ v : ℝ, Afun f M₂ K T v * Afun f M₂ K T (v + (k:ℝ)) = 0 := by
      intro v
      by_contra hne
      have h1 : Afun f M₂ K T v ≠ 0 := fun h => hne (by rw [h, zero_mul])
      have h2 : Afun f M₂ K T (v + (k:ℝ)) ≠ 0 := fun h => hne (by rw [h, mul_zero])
      have hv1 : v ∈ Set.Icc (M₂ / C₀ - smScale K T M₂ / 4)
          (2 * C₀ * M₂ + smScale K T M₂ / 4) := by
        by_contra hmem; exact h1 (hAsupp v hmem)
      have hv2 : v + (k:ℝ) ∈ Set.Icc (M₂ / C₀ - smScale K T M₂ / 4)
          (2 * C₀ * M₂ + smScale K T M₂ / 4) := by
        by_contra hmem; exact h2 (hAsupp (v + (k:ℝ)) hmem)
      rw [Set.mem_Icc] at hv1 hv2
      have hkup : (k:ℝ) ≤ 2 * C₀ * M₂ := by linarith [hv1.1, hv1.2, hv2.1, hv2.2, hwidth]
      have hkdown : -((k:ℝ)) ≤ 2 * C₀ * M₂ := by linarith [hv1.1, hv1.2, hv2.1, hv2.2, hwidth]
      have hkabs : |(k:ℝ)| ≤ 2 * C₀ * M₂ := by rw [abs_le]; exact ⟨by linarith, hkup⟩
      have hmem : k ∈ Finset.Icc (-(⌊2 * C₀ * M₂⌋)) ⌊2 * C₀ * M₂⌋ := by
        rw [Finset.mem_Icc]
        refine ⟨?_, ?_⟩
        · have h : (-k : ℤ) ≤ ⌊2 * C₀ * M₂⌋ :=
            Int.le_floor.mpr (show (((-k : ℤ)) : ℝ) ≤ 2 * C₀ * M₂ from by
              push_cast
              linarith [hkdown])
          omega
        · exact Int.le_floor.mpr (le_trans (le_abs_self (k:ℝ)) hkabs)
      exact hk hmem
    rw [show (fun v : ℝ => Afun f M₂ K T v * Afun f M₂ K T (v + (k:ℝ))) = fun _ => (0:ℝ) from
      funext hpt, integral_zero]
  rw [nearcorr_fejerK_pairing hAcont hAcs M₃]
  calc (∑ k ∈ Finset.Icc (-((fejerN M₃ : ℤ) - 1)) ((fejerN M₃ : ℤ) - 1),
        (1 - |(k:ℝ)| / (fejerN M₃ : ℝ)) *
          (∫ v : ℝ, Afun f M₂ K T v * Afun f M₂ K T (v + (k:ℝ))))
      ≤ ∑ k ∈ Finset.Icc (-((fejerN M₃ : ℤ) - 1)) ((fejerN M₃ : ℤ) - 1),
          (∫ v : ℝ, Afun f M₂ K T v * Afun f M₂ K T (v + (k:ℝ))) := Finset.sum_le_sum hterm_le
    _ = ∑ k ∈ (Finset.Icc (-((fejerN M₃ : ℤ) - 1)) ((fejerN M₃ : ℤ) - 1)).filter
            (fun k => k ∈ Finset.Icc (-(⌊2 * C₀ * M₂⌋)) ⌊2 * C₀ * M₂⌋),
          (∫ v : ℝ, Afun f M₂ K T v * Afun f M₂ K T (v + (k:ℝ))) :=
        (Finset.sum_subset
          (Finset.filter_subset (p := fun k : ℤ => k ∈ Finset.Icc (-(⌊2 * C₀ * M₂⌋)) ⌊2 * C₀ * M₂⌋)
            (Finset.Icc (-((fejerN M₃ : ℤ) - 1)) ((fejerN M₃ : ℤ) - 1)))
          (fun k hk hnk => hzero k hk (fun h => hnk (Finset.mem_filter.mpr ⟨hk, h⟩)))).symm
    _ ≤ ∑ k ∈ Finset.Icc (-(⌊2 * C₀ * M₂⌋)) ⌊2 * C₀ * M₂⌋,
          (∫ v : ℝ, Afun f M₂ K T v * Afun f M₂ K T (v + (k:ℝ))) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun k hk => (Finset.mem_filter.mp hk).2)
          (fun k _ _ => hAknneg k)

/-- **The near-correlation bound.** -/
theorem near_correlation_le_Gfun {C₀ : ℝ} (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ K T M₂ : ℝ, 1 ≤ T → 8 ≤ K → 2 * C₀ ≤ M₂ → 2 * C₀ ≤ T →
        ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
          ∀ M₃ : ℝ, 1 ≤ M₃ →
            (∫ x in Set.Icc (-(K * T / M₂)) (K * T / M₂),
                ‖Bsum f M₂ x‖ ^ 2 * fejerK M₃ x)
              ≤ C * K ^ 2 * M₂ *
                  ∫ u : ℝ, smoothed psiSmooth T f u * Gfun C₀ T M₂ f u := by
  refine ⟨64, by norm_num, ?_⟩
  intro K T M₂ hT hK hM₂ hT2 f hf hfnn hsup M₃ hM₃
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hKpos : 0 < K := by linarith
  have hM₂pos : 0 < M₂ := by linarith
  have hM₂1 : (1:ℝ) ≤ M₂ := by linarith
  have hspos : 0 < smScale K T M₂ := smScale_pos hKpos hTpos hM₂pos
  have hfejnn : ∀ x : ℝ, 0 ≤ fejerK M₃ x := fun x => nearcorr_fejerK_nonneg M₃ x
  have hfcs : HasCompactSupport f := nearcorr_suppHyp_hcs hC₀ hsup
  have hHcs : HasCompactSupport (Hprof f M₂) := Hprof_hasCompactSupport hsup hC₀ hM₂pos.le
  have hHcont : Continuous (Hprof f M₂) := Hprof_continuous hf M₂
  have hFHsq : Integrable (fun x : ℝ => ‖Fhat (Hprof f M₂) x‖ ^ 2) :=
    integrable_Fhat_sq hHcont hHcs
  have hAcont : Continuous (Afun f M₂ K T) := nearcorr_Afun_continuous hf M₂ K T
  have hAsupp : ∀ v : ℝ, v ∉ Set.Icc (M₂ / C₀ - smScale K T M₂ / 4)
      (2 * C₀ * M₂ + smScale K T M₂ / 4) → Afun f M₂ K T v = 0 :=
    fun v hv => nearcorr_Afun_eq_zero_of_notMem hC₀ hsup hM₂pos hKpos hTpos hv
  have hAcs : HasCompactSupport (Afun f M₂ K T) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := Set.Icc (M₂ / C₀ - smScale K T M₂ / 4) (2 * C₀ * M₂ + smScale K T M₂ / 4))
      isCompact_Icc ?_
    intro v hv
    rw [Function.mem_support] at hv
    by_contra hmem
    exact hv (hAsupp v hmem)
  -- pointwise smoothing bound on the relevant interval
  have hpoint : ∀ x ∈ Set.Icc (-(K * T / M₂)) (K * T / M₂),
      ‖Bsum f M₂ x‖ ^ 2 * fejerK M₃ x ≤
        2 * (‖Fhat (Afun f M₂ K T) x‖ ^ 2 * fejerK M₃ x) := by
    intro x hx
    rw [Set.mem_Icc] at hx
    have hxabs : |x| ≤ K * T / M₂ := by
      rw [abs_le]; exact ⟨hx.1, hx.2⟩
    have hsx : |smScale K T M₂ * x| ≤ 1 / 2 := by
      rw [abs_mul, abs_of_pos hspos]
      have h1 : smScale K T M₂ * |x| ≤ smScale K T M₂ * (K * T / M₂) :=
        mul_le_mul_of_nonneg_left hxabs hspos.le
      have h2 : smScale K T M₂ * (K * T / M₂) = 1 / 2 := by
        rw [smScale]
        field_simp
      linarith [h1, h2.le]
    have hψ : 1 / 2 ≤ ‖Fhat psiSmooth (smScale K T M₂ * x)‖ ^ 2 :=
      psiSmooth_fhat_lower_bound hsx
    have hB : Bsum f M₂ x = Fhat (Hprof f M₂) x := Bsum_eq_Fhat_Hprof hf hsup hC₀ hM₂pos x
    have hAsq : ‖Fhat (Afun f M₂ K T) x‖ ^ 2 =
        ‖Fhat (Hprof f M₂) x‖ ^ 2 * ‖Fhat psiSmooth (smScale K T M₂ * x)‖ ^ 2 := by
      rw [nearcorr_Afun_fhat hC₀ hf hsup hM₂pos hKpos hTpos x, norm_mul, mul_pow]
    have hkey : ‖Fhat (Hprof f M₂) x‖ ^ 2 ≤ 2 * ‖Fhat (Afun f M₂ K T) x‖ ^ 2 := by
      rw [hAsq]
      nlinarith [sq_nonneg ‖Fhat (Hprof f M₂) x‖, hψ]
    rw [hB]
    calc ‖Fhat (Hprof f M₂) x‖ ^ 2 * fejerK M₃ x
        ≤ (2 * ‖Fhat (Afun f M₂ K T) x‖ ^ 2) * fejerK M₃ x :=
          mul_le_mul_of_nonneg_right hkey (hfejnn x)
      _ = 2 * (‖Fhat (Afun f M₂ K T) x‖ ^ 2 * fejerK M₃ x) := by ring
  have hIB : Integrable (fun x : ℝ => ‖Bsum f M₂ x‖ ^ 2 * fejerK M₃ x) := by
    have h1 : Integrable (fun x : ℝ => ‖Fhat (Hprof f M₂) x‖ ^ 2 * fejerK M₃ x) :=
      hFHsq.mul_bdd (nearcorr_continuous_fejerK M₃).aestronglyMeasurable
        (c := 1 + 2 * (fejerN M₃ : ℝ))
        (Filter.Eventually.of_forall (fun x => by
          rw [Real.norm_eq_abs]; exact nearcorr_abs_fejerK_le M₃ x))
    exact h1.congr (Filter.Eventually.of_forall (fun x => by
      simp only [Bsum_eq_Fhat_Hprof hf hsup hC₀ hM₂pos x]))
  have hIA : Integrable (fun x : ℝ => ‖Fhat (Afun f M₂ K T) x‖ ^ 2 * fejerK M₃ x) :=
    (integrable_Fhat_sq hAcont hAcs).mul_bdd
      (nearcorr_continuous_fejerK M₃).aestronglyMeasurable
      (c := 1 + 2 * (fejerN M₃ : ℝ))
      (Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs]; exact nearcorr_abs_fejerK_le M₃ x))
  have hstep1 : (∫ x in Set.Icc (-(K * T / M₂)) (K * T / M₂),
        ‖Bsum f M₂ x‖ ^ 2 * fejerK M₃ x)
      ≤ ∫ x in Set.Icc (-(K * T / M₂)) (K * T / M₂),
          2 * (‖Fhat (Afun f M₂ K T) x‖ ^ 2 * fejerK M₃ x) :=
    setIntegral_mono_on hIB.integrableOn (hIA.const_mul 2).integrableOn measurableSet_Icc hpoint
  have hstep2 : (∫ x in Set.Icc (-(K * T / M₂)) (K * T / M₂),
        2 * (‖Fhat (Afun f M₂ K T) x‖ ^ 2 * fejerK M₃ x))
      ≤ ∫ x : ℝ, 2 * (‖Fhat (Afun f M₂ K T) x‖ ^ 2 * fejerK M₃ x) :=
    setIntegral_le_integral (hIA.const_mul 2)
      (Filter.Eventually.of_forall (fun x => mul_nonneg (by norm_num)
        (mul_nonneg (sq_nonneg _) (hfejnn x))))
  -- the correlation sum
  have hcorr_sum : (∑ k ∈ Finset.Icc (-(⌊2 * C₀ * M₂⌋)) ⌊2 * C₀ * M₂⌋,
        ∫ v : ℝ, Afun f M₂ K T v * Afun f M₂ K T (v + (k:ℝ)))
      ≤ 32 * K ^ 2 * M₂ * ∫ u : ℝ, smoothed psiSmooth T f u * Gfun C₀ T M₂ f u := by
    have hft_nn : ∀ u : ℝ, 0 ≤ smoothed psiSmooth T f u :=
      fun u => nearcorr_smoothed_nonneg hTpos hfnn u
    have hsingle : ∀ k : ℤ, (∫ v : ℝ, Afun f M₂ K T v * Afun f M₂ K T (v + (k:ℝ)))
        ≤ ∑ m ∈ R2 M₂, ∑ m' ∈ R2 M₂, (16 * K^2) * (m:ℝ) * NTerm T f m m' (k:ℝ) :=
      fun k => nearcorr_single_corr hC₀ hT hK hM₂1 hf hfnn hsup (k:ℝ)
    have hstep_a : (∑ k ∈ Finset.Icc (-(⌊2 * C₀ * M₂⌋)) ⌊2 * C₀ * M₂⌋,
          ∫ v : ℝ, Afun f M₂ K T v * Afun f M₂ K T (v + (k:ℝ)))
        ≤ ∑ k ∈ Finset.Icc (-(⌊2 * C₀ * M₂⌋)) ⌊2 * C₀ * M₂⌋, ∑ m ∈ R2 M₂, ∑ m' ∈ R2 M₂,
            (16 * K^2) * (m:ℝ) * NTerm T f m m' (k:ℝ) :=
      Finset.sum_le_sum (fun k _ => hsingle k)
    have hstep_b : (∑ k ∈ Finset.Icc (-(⌊2 * C₀ * M₂⌋)) ⌊2 * C₀ * M₂⌋, ∑ m ∈ R2 M₂,
          ∑ m' ∈ R2 M₂, (16 * K^2) * (m:ℝ) * NTerm T f m m' (k:ℝ))
        = ∑ m ∈ R2 M₂, ∑ m' ∈ R2 M₂, ∑ k ∈ Finset.Icc (-(⌊2 * C₀ * M₂⌋)) ⌊2 * C₀ * M₂⌋,
            (16 * K^2) * (m:ℝ) * NTerm T f m m' (k:ℝ) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [Finset.sum_comm]
    have hstep_c : (∑ m ∈ R2 M₂, ∑ m' ∈ R2 M₂, ∑ k ∈ Finset.Icc (-(⌊2 * C₀ * M₂⌋)) ⌊2 * C₀ * M₂⌋,
          (16 * K^2) * (m:ℝ) * NTerm T f m m' (k:ℝ))
        ≤ ∑ m ∈ R2 M₂, ∑ m' ∈ R2 M₂, ∑ k ∈ Finset.Icc (-(⌊2 * C₀ * M₂⌋)) ⌊2 * C₀ * M₂⌋,
            (16 * K^2) * (2 * M₂) * NTerm T f m m' (k:ℝ) := by
      refine Finset.sum_le_sum (fun m hm => Finset.sum_le_sum (fun m' _ =>
        Finset.sum_le_sum (fun k _ => ?_)))
      have hmle : (m:ℝ) ≤ 2 * M₂ := R2_le' hm
      have hInn : 0 ≤ NTerm T f m m' (k:ℝ) := by
        unfold NTerm
        exact integral_nonneg (fun u => mul_nonneg (hft_nn u) (hft_nn _))
      have h1 : (m:ℝ) * NTerm T f m m' (k:ℝ) ≤ (2*M₂) * NTerm T f m m' (k:ℝ) :=
        mul_le_mul_of_nonneg_right hmle hInn
      have hK2 : 0 ≤ 16 * K^2 := by positivity
      calc (16 * K^2) * (m:ℝ) * NTerm T f m m' (k:ℝ)
          = (16 * K^2) * ((m:ℝ) * NTerm T f m m' (k:ℝ)) := by ring
        _ ≤ (16 * K^2) * ((2*M₂) * NTerm T f m m' (k:ℝ)) :=
            mul_le_mul_of_nonneg_left h1 hK2
        _ = (16 * K^2) * (2 * M₂) * NTerm T f m m' (k:ℝ) := by ring
    have hstep_d : (∑ m ∈ R2 M₂, ∑ m' ∈ R2 M₂, ∑ k ∈ Finset.Icc (-(⌊2 * C₀ * M₂⌋)) ⌊2 * C₀ * M₂⌋,
          (16 * K^2) * (2 * M₂) * NTerm T f m m' (k:ℝ))
        = (16 * K^2) * (2 * M₂) * (∑ m ∈ R2 M₂, ∑ m' ∈ R2 M₂,
            ∑ k ∈ Finset.Icc (-(⌊2 * C₀ * M₂⌋)) ⌊2 * C₀ * M₂⌋, NTerm T f m m' (k:ℝ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun m' _ => ?_)
      rw [Finset.mul_sum]
    have hstep_e : (∑ m ∈ R2 M₂, ∑ m' ∈ R2 M₂, ∑ k ∈ Finset.Icc (-(⌊2 * C₀ * M₂⌋)) ⌊2 * C₀ * M₂⌋,
          NTerm T f m m' (k:ℝ))
        = ∫ u : ℝ, smoothed psiSmooth T f u * Gfun C₀ T M₂ f u :=
      nearcorr_sum_gfun_eq hC₀ hTpos hf hsup
    calc (∑ k ∈ Finset.Icc (-(⌊2 * C₀ * M₂⌋)) ⌊2 * C₀ * M₂⌋,
          ∫ v : ℝ, Afun f M₂ K T v * Afun f M₂ K T (v + (k:ℝ)))
        ≤ _ := hstep_a
      _ = _ := hstep_b
      _ ≤ _ := hstep_c
      _ = (16 * K^2) * (2 * M₂) * (∑ m ∈ R2 M₂, ∑ m' ∈ R2 M₂,
            ∑ k ∈ Finset.Icc (-(⌊2 * C₀ * M₂⌋)) ⌊2 * C₀ * M₂⌋, NTerm T f m m' (k:ℝ)) := hstep_d
      _ = (16 * K^2) * (2 * M₂) * (∫ u : ℝ, smoothed psiSmooth T f u * Gfun C₀ T M₂ f u) := by
          rw [hstep_e]
      _ = 32 * K ^ 2 * M₂ * ∫ u : ℝ, smoothed psiSmooth T f u * Gfun C₀ T M₂ f u := by ring
  have hpairbound := nearcorr_fejer_sum_bound hC₀ hT hK hM₂ hT2 hf hfnn hsup (M₃ := M₃)
  calc (∫ x in Set.Icc (-(K * T / M₂)) (K * T / M₂), ‖Bsum f M₂ x‖ ^ 2 * fejerK M₃ x)
      ≤ ∫ x in Set.Icc (-(K * T / M₂)) (K * T / M₂),
          2 * (‖Fhat (Afun f M₂ K T) x‖ ^ 2 * fejerK M₃ x) := hstep1
    _ ≤ ∫ x : ℝ, 2 * (‖Fhat (Afun f M₂ K T) x‖ ^ 2 * fejerK M₃ x) := hstep2
    _ = 2 * (∫ x : ℝ, ‖Fhat (Afun f M₂ K T) x‖ ^ 2 * fejerK M₃ x) := integral_const_mul 2 _
    _ ≤ 2 * (∑ k ∈ Finset.Icc (-(⌊2 * C₀ * M₂⌋)) ⌊2 * C₀ * M₂⌋,
          ∫ v : ℝ, Afun f M₂ K T v * Afun f M₂ K T (v + (k:ℝ))) :=
        mul_le_mul_of_nonneg_left hpairbound (by norm_num)
    _ ≤ 2 * (32 * K ^ 2 * M₂ * ∫ u : ℝ, smoothed psiSmooth T f u * Gfun C₀ T M₂ f u) :=
        mul_le_mul_of_nonneg_left hcorr_sum (by norm_num)
    _ = 64 * K ^ 2 * M₂ * ∫ u : ℝ, smoothed psiSmooth T f u * Gfun C₀ T M₂ f u := by ring

end

end Work.GM.Affine
