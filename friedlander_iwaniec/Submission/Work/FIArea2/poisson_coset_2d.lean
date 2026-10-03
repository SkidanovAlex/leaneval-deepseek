import Mathlib
import Submission.Work.FIArea2.Poisson2dDefs
import Submission.Commons.Analysis.Fourier.fourier_isBigO_rpow_neg_two
import Submission.Commons.Analysis.Fourier.summable_of_isBigO_cocompact_rpow
import Submission.Commons.Analysis.Fourier.fourier_eq_integral_exp_real
import Mathlib.Analysis.Fourier.FourierTransformDeriv

namespace Work.FIArea2
open scoped BigOperators FourierTransform
open MeasureTheory Filter Asymptotics

noncomputable section

lemma norm_two_pi_I_mul' (x : ℝ) :
    ‖(2 * Real.pi * Complex.I * (x:ℂ))‖ = 2 * Real.pi * |x| := by
  have h : (2 * Real.pi * Complex.I * (x:ℂ)) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, norm_mul, Complex.norm_I, mul_one]
  have h2 : ‖((2 * Real.pi * x : ℝ) : ℂ)‖ = |2 * Real.pi * x| := by simp
  rw [h2, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]

lemma hcs_iteratedDeriv {F : ℝ → ℂ} (hc : HasCompactSupport F) (n : ℕ) :
    HasCompactSupport (iteratedDeriv n F) := by
  rw [iteratedDeriv_eq_equiv_comp]
  exact (hc.iteratedFDeriv (𝕜 := ℝ) n).comp_left (map_zero _)

lemma fourier_fourier_iteratedDeriv_le {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F)
    (hc : HasCompactSupport F) (k : ℕ) (hk : k ≤ 2) (ξ : ℝ) :
    ‖𝓕 F ξ‖ * (2 * Real.pi * |ξ|) ^ k ≤ ∫ y, ‖iteratedDeriv k F y‖ := by
  have hcont : ∀ n : ℕ, (n:ℕ∞) ≤ (2:ℕ∞) → Integrable (iteratedDeriv n F) := by
    intro n hn
    refine ((hF.of_le (WithTop.coe_le_coe.mpr hn)).continuous_iteratedDeriv' n)
      |>.integrable_of_hasCompactSupport (hcs_iteratedDeriv hc n)
  have hfour := Real.fourier_iteratedDeriv (f := F) (N := (2:ℕ∞)) (n := k) hF hcont
    (by exact_mod_cast hk)
  have hpt := congrFun hfour ξ
  have hnorm : ‖𝓕 (iteratedDeriv k F) ξ‖ ≤ ∫ y, ‖iteratedDeriv k F y‖ := by
    rw [Real.fourier_eq]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    simp only [Circle.norm_smul]
  rw [hpt, norm_smul, norm_pow, norm_two_pi_I_mul'] at hnorm
  calc ‖𝓕 F ξ‖ * (2 * Real.pi * |ξ|) ^ k = (2 * Real.pi * |ξ|) ^ k * ‖𝓕 F ξ‖ := by ring
    _ ≤ ∫ y, ‖iteratedDeriv k F y‖ := hnorm

lemma fourier_decay_explicit {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F) (hc : HasCompactSupport F)
    (k : ℕ) (hk : k ≤ 2) (ξ : ℝ) (hξ : ξ ≠ 0) :
    ‖𝓕 F ξ‖ ≤ (∫ y, ‖iteratedDeriv k F y‖) / (2 * Real.pi * |ξ|) ^ k := by
  have hpos : 0 < (2 * Real.pi * |ξ|) ^ k := by
    apply pow_pos; positivity
  exact (le_div_iff₀ hpos).mpr (fourier_fourier_iteratedDeriv_le hF hc k hk ξ)

lemma isBigO_of_hasCompactSupport {f : ℝ → ℂ} (hcs : HasCompactSupport f) (b : ℝ) :
    f =O[Filter.cocompact ℝ] (fun x : ℝ => |x| ^ (-b)) := by
  refine IsBigO.of_bound 1 ?_
  have hev : f =ᶠ[Filter.cocompact ℝ] 0 := by
    rw [← Filter.coclosedCompact_eq_cocompact, ← hasCompactSupport_iff_eventuallyEq]
    exact hcs
  filter_upwards [hev] with x hx
  rw [hx, Pi.zero_apply, norm_zero]
  positivity

lemma exists_box_support {φ : ℝ × ℝ → ℂ} (hcs : HasCompactSupport φ) :
    ∃ R : ℝ, 0 ≤ R ∧ (∀ x₁ x₂, R < |x₁| → φ (x₁,x₂) = 0) ∧
               (∀ x₁ x₂, R < |x₂| → φ (x₁,x₂) = 0) := by
  have hev : φ =ᶠ[Filter.coclosedCompact (ℝ×ℝ)] 0 := hasCompactSupport_iff_eventuallyEq.mp hcs
  rw [Filter.coclosedCompact_eq_cocompact] at hev
  have hm : {x : ℝ×ℝ | φ x = 0} ∈ Filter.cocompact (ℝ×ℝ) := hev
  rw [Metric.mem_cocompact_iff_closedBall_compl_subset (0:ℝ×ℝ)] at hm
  obtain ⟨r, hr⟩ := hm
  refine ⟨max r 0, le_max_right _ _, ?_, ?_⟩
  · intro x₁ x₂ hx
    apply hr
    simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right]
    intro hmem
    have hnorm : ‖x₁‖ ≤ ‖(x₁,x₂)‖ := norm_fst_le (x := (x₁,x₂))
    rw [Real.norm_eq_abs] at hnorm
    linarith [le_max_left r (0:ℝ)]
  · intro x₁ x₂ hx
    apply hr
    simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right]
    intro hmem
    have hnorm : ‖x₂‖ ≤ ‖(x₁,x₂)‖ := norm_snd_le (x := (x₁,x₂))
    rw [Real.norm_eq_abs] at hnorm
    linarith [le_max_left r (0:ℝ)]

lemma contDiff_slice_fst {φ : ℝ × ℝ → ℂ} (hφ : ContDiff ℝ 3 φ) (x : ℝ) :
    ContDiff ℝ 3 (fun t => φ (t,x)) := hφ.comp (by fun_prop)

lemma contDiff_slice_snd {φ : ℝ × ℝ → ℂ} (hφ : ContDiff ℝ 3 φ) (x : ℝ) :
    ContDiff ℝ 3 (fun t => φ (x,t)) := hφ.comp (by fun_prop)

lemma hasCompactSupport_slice_fst {φ : ℝ × ℝ → ℂ} (hcs : HasCompactSupport φ) (x : ℝ) :
    HasCompactSupport (fun t => φ (t,x)) := by
  obtain ⟨R, hR0, hRR, _⟩ := exists_box_support hcs
  rw [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact]
  have hm : {t : ℝ | φ (t,x) = 0} ∈ Filter.cocompact ℝ := by
    rw [Metric.mem_cocompact_iff_closedBall_compl_subset (0:ℝ)]
    refine ⟨R, fun t ht => ?_⟩
    rw [Set.mem_ofPred_eq]
    apply hRR t x
    simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at ht
    linarith
  exact hm

lemma hasCompactSupport_slice_snd {φ : ℝ × ℝ → ℂ} (hcs : HasCompactSupport φ) (x : ℝ) :
    HasCompactSupport (fun t => φ (x,t)) := by
  obtain ⟨R, hR0, _, hLL⟩ := exists_box_support hcs
  rw [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact]
  have hm : {t : ℝ | φ (x,t) = 0} ∈ Filter.cocompact ℝ := by
    rw [Metric.mem_cocompact_iff_closedBall_compl_subset (0:ℝ)]
    refine ⟨R, fun t ht => ?_⟩
    rw [Set.mem_ofPred_eq]
    apply hLL x t
    simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at ht
    linarith
  exact hm

lemma poisson_unit_one (f : ℝ → ℂ) (hc : Continuous f) (hcs : HasCompactSupport f)
    (hFf : Summable fun n : ℤ => 𝓕 f n) :
    (∑' n : ℤ, f n) = ∑' n : ℤ, 𝓕 f n := by
  have hb : (1:ℝ) < 2 := by norm_num
  have hf : f =O[Filter.cocompact ℝ] (fun x : ℝ => |x| ^ (-(2:ℝ))) :=
    isBigO_of_hasCompactSupport hcs 2
  have h := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hc hb hf hFf 0
  have h1 : (∑' n : ℤ, f (0 + (n:ℝ))) = ∑' n : ℤ, f (n:ℝ) := by
    apply tsum_congr; intro n; rw [zero_add]
  rw [h1] at h
  have h2 : (∑' n : ℤ, 𝓕 f n * fourier n ((0:ℝ) : UnitAddCircle)) = ∑' n : ℤ, 𝓕 f n := by
    apply tsum_congr; intro n
    rw [show ((0:ℝ) : UnitAddCircle) = 0 by rfl, fourier_eval_zero, mul_one]
  rw [h2] at h
  exact h

lemma summable_fourier_of_contDiff {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hcs : HasCompactSupport f) :
    Summable fun n : ℤ => 𝓕 f n := by
  simpa using Commons.Analysis.Fourier.summable_of_isBigO_cocompact_rpow
    (show (1:ℝ) < 2 by norm_num)
    (Commons.Analysis.Fourier.fourier_isBigO_rpow_neg_two hf hcs) (d := 1) one_pos

def kern (x : ℝ) : ℂ := Complex.exp (-(2*Real.pi*Complex.I) * (x:ℂ))

lemma kern_add (a b : ℝ) : kern (a+b) = kern a * kern b := by
  rw [kern, kern, kern, Complex.ofReal_add, ← Complex.exp_add]
  congr 1; ring

lemma kern_norm (a : ℝ) : ‖kern a‖ = 1 := by
  simp only [kern]
  rw [Complex.norm_exp]
  have hre : (-(2*Real.pi*Complex.I) * (a:ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, Real.exp_zero]

lemma continuous_kern (c : ℝ) : Continuous (fun x : ℝ => kern (c*x)) := by
  unfold kern
  exact Complex.continuous_exp.comp (continuous_const.mul
    (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)))

lemma fourier_slice (F : ℝ → ℂ) (p : ℝ) : 𝓕 F p = ∫ t, F t * kern (p*t) := by
  rw [Commons.Analysis.Fourier.fourier_eq_integral_exp_real]
  apply integral_congr_ae
  filter_upwards with t
  congr 1
  simp only [kern]
  congr 1
  push_cast; ring

lemma ft2_eq_kern (φ : ℝ×ℝ→ℂ) (h : ℤ×ℤ) :
    ft2 φ h = ∫ t : ℝ×ℝ, φ t * kern ((h.1:ℝ)*t.1 + (h.2:ℝ)*t.2) := by
  rw [ft2]
  apply integral_congr_ae
  filter_upwards with t
  congr 1
  congr 1
  push_cast; ring

lemma integrable_ft2_integrand {φ : ℝ×ℝ→ℂ} (hc : Continuous φ) (hcs : HasCompactSupport φ)
    (h : ℤ×ℤ) :
    Integrable (fun t : ℝ×ℝ => φ t * kern ((h.1:ℝ)*t.1 + (h.2:ℝ)*t.2)) := by
  have hcont : Continuous (fun t : ℝ×ℝ => φ t * kern ((h.1:ℝ)*t.1 + (h.2:ℝ)*t.2)) := by
    refine hc.mul ?_
    refine Complex.continuous_exp.comp ?_
    refine continuous_const.mul ?_
    exact Complex.continuous_ofReal.comp (by fun_prop)
  exact hcont.integrable_of_hasCompactSupport (hcs.mul_right)

lemma integrable_kern_prod {φ : ℝ×ℝ→ℂ} (hc : Continuous φ) (hcs : HasCompactSupport φ)
    (a b : ℤ) :
    Integrable (fun z : ℝ×ℝ => φ z * (kern ((a:ℝ)*z.1) * kern ((b:ℝ)*z.2))) := by
  have hcont : Continuous (fun z : ℝ×ℝ => φ z * (kern ((a:ℝ)*z.1) * kern ((b:ℝ)*z.2))) :=
    hc.mul ((continuous_kern _ |>.comp continuous_fst).mul
      (continuous_kern _ |>.comp continuous_snd))
  exact hcont.integrable_of_hasCompactSupport (hcs.mul_right)

lemma ft2_eq_iter_snd (φ : ℝ×ℝ→ℂ) (hc : Continuous φ) (hcs : HasCompactSupport φ) (h : ℤ×ℤ) :
    ft2 φ h = ∫ t₂, (∫ t₁, φ (t₁,t₂) * kern ((h.1:ℝ)*t₁)) * kern ((h.2:ℝ)*t₂) := by
  rw [ft2_eq_kern]
  rw [MeasureTheory.Measure.volume_eq_prod,
    MeasureTheory.integral_prod_symm _ (integrable_ft2_integrand hc hcs h)]
  apply integral_congr_ae
  filter_upwards with t₂
  rw [show (∫ t₁, φ (t₁,t₂) * kern ((h.1:ℝ)*t₁ + (h.2:ℝ)*t₂))
        = ∫ t₁, (φ (t₁,t₂) * kern ((h.1:ℝ)*t₁)) * kern ((h.2:ℝ)*t₂) from by
      apply integral_congr_ae; filter_upwards with t₁
      rw [kern_add]; ring]
  rw [MeasureTheory.integral_mul_const]

lemma ft2_eq_fourier_slice (φ : ℝ×ℝ→ℂ) (hc : Continuous φ) (hcs : HasCompactSupport φ)
    (h : ℤ×ℤ) :
    ft2 φ h = ∫ t₂, (𝓕 (fun t₁ => φ (t₁,t₂)) (h.1)) * kern ((h.2:ℝ)*t₂) := by
  rw [ft2_eq_iter_snd φ hc hcs h]
  apply integral_congr_ae
  filter_upwards with t₂
  rw [fourier_slice]

lemma fourier_spectral_slice (φ : ℝ×ℝ→ℂ) (hc : Continuous φ) (hcs : HasCompactSupport φ)
    (h : ℤ×ℤ) :
    𝓕 (fun x₁ => ∫ t₂, φ (x₁,t₂) * kern ((h.2:ℝ)*t₂)) (h.1) = ft2 φ h := by
  have hfin' : Integrable (fun z : ℝ×ℝ =>
      (φ (z.1,z.2) * kern ((h.2:ℝ)*z.2)) * kern ((h.1:ℝ)*z.1)) := by
    refine (integrable_kern_prod hc hcs h.1 h.2).congr ?_
    filter_upwards with z
    simp only [Prod.mk.eta]
    ring
  have hfin : Integrable (Function.uncurry (fun x₁ t₂ =>
      (φ (x₁,t₂) * kern ((h.2:ℝ)*t₂)) * kern ((h.1:ℝ)*x₁))) := hfin'
  rw [fourier_slice, ft2_eq_kern]
  rw [show (∫ x₁, (∫ t₂, φ (x₁,t₂) * kern ((h.2:ℝ)*t₂)) * kern ((h.1:ℝ)*x₁))
        = ∫ x₁, ∫ t₂, (φ (x₁,t₂) * kern ((h.2:ℝ)*t₂)) * kern ((h.1:ℝ)*x₁) from by
      apply integral_congr_ae; filter_upwards with x₁
      rw [MeasureTheory.integral_mul_const]]
  rw [MeasureTheory.integral_integral hfin]
  apply integral_congr_ae
  filter_upwards with z
  simp only [Prod.mk.eta]
  rw [mul_assoc, mul_comm (kern ((h.2:ℝ)*z.2)) (kern ((h.1:ℝ)*z.1)), ← kern_add]

def blin : (ℝ×ℝ) →L[ℝ] (ℝ×ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun v w : ℝ×ℝ => v.1*w.1 + v.2*w.2)
      (by intro m₁ m₂ n; simp only [Prod.fst_add, Prod.snd_add]; ring)
      (by intro c m n; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)
      (by intro m n₁ n₂; simp only [Prod.fst_add, Prod.snd_add]; ring)
      (by intro c m n; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring))
    2
    (by
      intro v w
      simp only [LinearMap.mk₂_apply]
      have h1 : ‖v.1‖ ≤ ‖v‖ := norm_fst_le (x := v)
      have h2 : ‖v.2‖ ≤ ‖v‖ := norm_snd_le (x := v)
      have h3 : ‖w.1‖ ≤ ‖w‖ := norm_fst_le (x := w)
      have h4 : ‖w.2‖ ≤ ‖w‖ := norm_snd_le (x := w)
      have e1 : ‖v.1‖ * ‖w.1‖ ≤ ‖v‖ * ‖w‖ := mul_le_mul h1 h3 (norm_nonneg _) (norm_nonneg _)
      have e2 : ‖v.2‖ * ‖w.2‖ ≤ ‖v‖ * ‖w‖ := mul_le_mul h2 h4 (norm_nonneg _) (norm_nonneg _)
      calc ‖v.1 * w.1 + v.2 * w.2‖ ≤ ‖v.1 * w.1‖ + ‖v.2 * w.2‖ := norm_add_le _ _
        _ = ‖v.1‖ * ‖w.1‖ + ‖v.2‖ * ‖w.2‖ := by rw [norm_mul, norm_mul]
        _ ≤ ‖v‖ * ‖w‖ + ‖v‖ * ‖w‖ := add_le_add e1 e2
        _ = 2 * ‖v‖ * ‖w‖ := by ring)

lemma blin_apply (v w : ℝ×ℝ) : blin v w = v.1*w.1 + v.2*w.2 := rfl


example (φ : ℝ×ℝ→ℂ) (hφ : ContDiff ℝ 3 φ) (hcs : HasCompactSupport φ) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℝ×ℝ,
      ‖VectorFourier.fourierIntegral Real.fourierChar volume blin.toLinearMap₁₂ φ w‖
        ≤ C / (1 + ‖w‖)^3 := by
  have hinteg : ∀ n : ℕ, n ≤ 3 → Integrable (fun v : ℝ×ℝ => ‖iteratedFDeriv ℝ n φ v‖) := by
    intro n hn
    have hcd : ContDiff ℝ n φ := hφ.of_le (by exact_mod_cast hn)
    exact ((hcd.continuous_iteratedFDeriv le_rfl).integrable_of_hasCompactSupport
      (hcs.iteratedFDeriv (𝕜 := ℝ) n)).norm
  set S : ℝ := ∑ p ∈ Finset.range 1 ×ˢ Finset.range 4,
      ∫ v : ℝ×ℝ, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 φ v‖ with hS
  have hSnonneg : 0 ≤ S := by rw [hS]; positivity
  set A : ℝ := ∫ v : ℝ×ℝ, ‖φ v‖ with hA
  have hAnonneg : 0 ≤ A := by rw [hA]; exact integral_nonneg (fun v => norm_nonneg (φ v))
  have hsum_eq : (∑ p ∈ Finset.range (0+1) ×ˢ Finset.range (3+1),
      ∫ v : ℝ×ℝ, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 φ v‖) = S := by
    rw [hS]
  have hmain : ∀ w : ℝ×ℝ,
      ‖w‖^3 * ‖VectorFourier.fourierIntegral Real.fourierChar volume blin.toLinearMap₁₂ φ w‖
        ≤ 8 * S := by
    intro w
    have hle := VectorFourier.pow_mul_norm_iteratedFDeriv_fourierIntegral_le
      (L := blin) (μ := volume) (K := (0:ℕ∞)) (N := (3:ℕ∞)) (f := φ) hφ
      (by
        intro k n hk hn
        have hk0 : k = 0 := by simpa using hk
        subst hk0
        simpa using hinteg n (by simpa using hn))
      (k := 0) (n := 3) le_rfl le_rfl w w
    simp only [blin_apply, norm_iteratedFDeriv_zero, pow_zero, mul_one, Nat.cast_zero] at hle
    rw [hsum_eq,
        show |w.1 * w.1 + w.2 * w.2| = w.1^2 + w.2^2 by
          rw [← sq, ← sq, abs_of_nonneg (by positivity)]] at hle
    norm_num at hle
    have hw2 : ‖w‖^2 ≤ w.1^2 + w.2^2 := by
      rw [Prod.norm_def]
      have h1 : ‖w.1‖^2 = w.1^2 := by rw [Real.norm_eq_abs, sq_abs]
      have h2 : ‖w.2‖^2 = w.2^2 := by rw [Real.norm_eq_abs, sq_abs]
      rcases max_cases (‖w.1‖) (‖w.2‖) with ⟨hm, _⟩ | ⟨hm, _⟩
      · rw [hm, h1]; nlinarith [sq_nonneg w.2]
      · rw [hm, h2]; nlinarith [sq_nonneg w.1]
    have hcube : ‖w‖^6 ≤ (w.1^2+w.2^2)^3 := by
      calc ‖w‖^6 = (‖w‖^2)^3 := by ring
        _ ≤ (w.1^2+w.2^2)^3 := by gcongr
    rcases eq_or_ne w 0 with rfl | hw
    · rw [norm_zero, zero_pow (by norm_num : (3:ℕ) ≠ 0), zero_mul]
      positivity
    · have hwn : (0:ℝ) < ‖w‖ := norm_pos_iff.mpr hw
      have key : ‖w‖^3 * (‖w‖^3 * ‖VectorFourier.fourierIntegral Real.fourierChar volume blin.toLinearMap₁₂ φ w‖) ≤ ‖w‖^3 * (8 * S) := by
        calc ‖w‖^3 * (‖w‖^3 * ‖VectorFourier.fourierIntegral Real.fourierChar volume blin.toLinearMap₁₂ φ w‖)
            = ‖w‖^6 * ‖VectorFourier.fourierIntegral Real.fourierChar volume blin.toLinearMap₁₂ φ w‖ := by ring
          _ ≤ (w.1^2+w.2^2)^3 * ‖VectorFourier.fourierIntegral Real.fourierChar volume blin.toLinearMap₁₂ φ w‖ :=
                mul_le_mul_of_nonneg_right hcube (norm_nonneg _)
          _ ≤ ‖w‖^3 * 8 * S := hle
          _ = ‖w‖^3 * (8*S) := by ring
      exact le_of_mul_le_mul_left key (pow_pos hwn 3)
  refine ⟨8 * max A (8*S) + 1, by positivity, ?_⟩
  intro w
  have htriv : ‖VectorFourier.fourierIntegral Real.fourierChar volume blin.toLinearMap₁₂ φ w‖ ≤ A := by
    rw [hA]; exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  by_cases hw : ‖w‖ ≤ 1
  · have h8 : (1 + ‖w‖)^3 ≤ 8 := by
      have : 1 + ‖w‖ ≤ 2 := by linarith [norm_nonneg w]
      calc (1 + ‖w‖)^3 ≤ 2^3 := by gcongr
        _ = 8 := by norm_num
    have hC : 8 * A ≤ 8 * max A (8*S) + 1 := by
      nlinarith [le_max_left A (8*S), hAnonneg, hSnonneg]
    calc ‖VectorFourier.fourierIntegral Real.fourierChar volume blin.toLinearMap₁₂ φ w‖
        ≤ A := htriv
      _ ≤ (8 * max A (8*S) + 1) / (1 + ‖w‖)^3 := by
          rw [le_div_iff₀ (by positivity)]
          nlinarith [h8, hC, hAnonneg]
  · have h3 : 1 ≤ ‖w‖ := le_of_lt (not_le.mp hw)
    have hcube2 : (1 + ‖w‖)^3 ≤ 8 * ‖w‖^3 := by
      have h2 : 1 + ‖w‖ ≤ 2 * ‖w‖ := by linarith
      calc (1 + ‖w‖)^3 ≤ (2*‖w‖)^3 := by gcongr
        _ = 8 * ‖w‖^3 := by ring
    have hC : 64 * S ≤ 8 * max A (8*S) + 1 := by
      nlinarith [le_max_right A (8*S), hAnonneg, hSnonneg]
    calc ‖VectorFourier.fourierIntegral Real.fourierChar volume blin.toLinearMap₁₂ φ w‖
        ≤ 8 * S / ‖w‖^3 := by
          rw [le_div_iff₀ (pow_pos (lt_of_lt_of_le zero_lt_one h3) 3)]
          nlinarith [hmain w]
      _ ≤ (8 * max A (8*S) + 1) / (1 + ‖w‖)^3 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          calc 8 * S * (1 + ‖w‖)^3 ≤ 8 * S * (8 * ‖w‖^3) :=
                mul_le_mul_of_nonneg_left hcube2 (by positivity)
            _ = 64 * S * ‖w‖^3 := by ring
            _ ≤ (8 * max A (8*S) + 1) * ‖w‖^3 :=
                mul_le_mul_of_nonneg_right hC (by positivity)


lemma ft2_decay_aux (φ : ℝ×ℝ→ℂ) (hφ : ContDiff ℝ 3 φ) (hcs : HasCompactSupport φ) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℝ×ℝ,
      ‖VectorFourier.fourierIntegral Real.fourierChar volume blin.toLinearMap₁₂ φ w‖
        ≤ C / (1 + ‖w‖)^3 := by
  have hinteg : ∀ n : ℕ, n ≤ 3 → Integrable (fun v : ℝ×ℝ => ‖iteratedFDeriv ℝ n φ v‖) := by
    intro n hn
    have hcd : ContDiff ℝ n φ := hφ.of_le (by exact_mod_cast hn)
    exact ((hcd.continuous_iteratedFDeriv le_rfl).integrable_of_hasCompactSupport
      (hcs.iteratedFDeriv (𝕜 := ℝ) n)).norm
  set S : ℝ := ∑ p ∈ Finset.range 1 ×ˢ Finset.range 4,
      ∫ v : ℝ×ℝ, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 φ v‖ with hS
  have hSnonneg : 0 ≤ S := by rw [hS]; positivity
  set A : ℝ := ∫ v : ℝ×ℝ, ‖φ v‖ with hA
  have hAnonneg : 0 ≤ A := by rw [hA]; exact integral_nonneg (fun v => norm_nonneg (φ v))
  have hsum_eq : (∑ p ∈ Finset.range (0+1) ×ˢ Finset.range (3+1),
      ∫ v : ℝ×ℝ, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 φ v‖) = S := by
    rw [hS]
  have hmain : ∀ w : ℝ×ℝ,
      ‖w‖^3 * ‖VectorFourier.fourierIntegral Real.fourierChar volume blin.toLinearMap₁₂ φ w‖
        ≤ 8 * S := by
    intro w
    have hle := VectorFourier.pow_mul_norm_iteratedFDeriv_fourierIntegral_le
      (L := blin) (μ := volume) (K := (0:ℕ∞)) (N := (3:ℕ∞)) (f := φ) hφ
      (by
        intro k n hk hn
        have hk0 : k = 0 := by simpa using hk
        subst hk0
        simpa using hinteg n (by simpa using hn))
      (k := 0) (n := 3) le_rfl le_rfl w w
    simp only [blin_apply, norm_iteratedFDeriv_zero, pow_zero, mul_one, Nat.cast_zero] at hle
    rw [hsum_eq,
        show |w.1 * w.1 + w.2 * w.2| = w.1^2 + w.2^2 by
          rw [← sq, ← sq, abs_of_nonneg (by positivity)]] at hle
    norm_num at hle
    have hw2 : ‖w‖^2 ≤ w.1^2 + w.2^2 := by
      rw [Prod.norm_def]
      have h1 : ‖w.1‖^2 = w.1^2 := by rw [Real.norm_eq_abs, sq_abs]
      have h2 : ‖w.2‖^2 = w.2^2 := by rw [Real.norm_eq_abs, sq_abs]
      rcases max_cases (‖w.1‖) (‖w.2‖) with ⟨hm, _⟩ | ⟨hm, _⟩
      · rw [hm, h1]; nlinarith [sq_nonneg w.2]
      · rw [hm, h2]; nlinarith [sq_nonneg w.1]
    have hcube : ‖w‖^6 ≤ (w.1^2+w.2^2)^3 := by
      calc ‖w‖^6 = (‖w‖^2)^3 := by ring
        _ ≤ (w.1^2+w.2^2)^3 := by gcongr
    rcases eq_or_ne w 0 with rfl | hw
    · rw [norm_zero, zero_pow (by norm_num : (3:ℕ) ≠ 0), zero_mul]
      positivity
    · have hwn : (0:ℝ) < ‖w‖ := norm_pos_iff.mpr hw
      have key : ‖w‖^3 * (‖w‖^3 * ‖VectorFourier.fourierIntegral Real.fourierChar volume blin.toLinearMap₁₂ φ w‖) ≤ ‖w‖^3 * (8 * S) := by
        calc ‖w‖^3 * (‖w‖^3 * ‖VectorFourier.fourierIntegral Real.fourierChar volume blin.toLinearMap₁₂ φ w‖)
            = ‖w‖^6 * ‖VectorFourier.fourierIntegral Real.fourierChar volume blin.toLinearMap₁₂ φ w‖ := by ring
          _ ≤ (w.1^2+w.2^2)^3 * ‖VectorFourier.fourierIntegral Real.fourierChar volume blin.toLinearMap₁₂ φ w‖ :=
                mul_le_mul_of_nonneg_right hcube (norm_nonneg _)
          _ ≤ ‖w‖^3 * 8 * S := hle
          _ = ‖w‖^3 * (8*S) := by ring
      exact le_of_mul_le_mul_left key (pow_pos hwn 3)
  refine ⟨8 * max A (8*S) + 1, by positivity, ?_⟩
  intro w
  have htriv : ‖VectorFourier.fourierIntegral Real.fourierChar volume blin.toLinearMap₁₂ φ w‖ ≤ A := by
    rw [hA]; exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  by_cases hw : ‖w‖ ≤ 1
  · have h8 : (1 + ‖w‖)^3 ≤ 8 := by
      have : 1 + ‖w‖ ≤ 2 := by linarith [norm_nonneg w]
      calc (1 + ‖w‖)^3 ≤ 2^3 := by gcongr
        _ = 8 := by norm_num
    have hC : 8 * A ≤ 8 * max A (8*S) + 1 := by
      nlinarith [le_max_left A (8*S), hAnonneg, hSnonneg]
    calc ‖VectorFourier.fourierIntegral Real.fourierChar volume blin.toLinearMap₁₂ φ w‖
        ≤ A := htriv
      _ ≤ (8 * max A (8*S) + 1) / (1 + ‖w‖)^3 := by
          rw [le_div_iff₀ (by positivity)]
          nlinarith [h8, hC, hAnonneg]
  · have h3 : 1 ≤ ‖w‖ := le_of_lt (not_le.mp hw)
    have hcube2 : (1 + ‖w‖)^3 ≤ 8 * ‖w‖^3 := by
      have h2 : 1 + ‖w‖ ≤ 2 * ‖w‖ := by linarith
      calc (1 + ‖w‖)^3 ≤ (2*‖w‖)^3 := by gcongr
        _ = 8 * ‖w‖^3 := by ring
    have hC : 64 * S ≤ 8 * max A (8*S) + 1 := by
      nlinarith [le_max_right A (8*S), hAnonneg, hSnonneg]
    calc ‖VectorFourier.fourierIntegral Real.fourierChar volume blin.toLinearMap₁₂ φ w‖
        ≤ 8 * S / ‖w‖^3 := by
          rw [le_div_iff₀ (pow_pos (lt_of_lt_of_le zero_lt_one h3) 3)]
          nlinarith [hmain w]
      _ ≤ (8 * max A (8*S) + 1) / (1 + ‖w‖)^3 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          calc 8 * S * (1 + ‖w‖)^3 ≤ 8 * S * (8 * ‖w‖^3) :=
                mul_le_mul_of_nonneg_left hcube2 (by positivity)
            _ = 64 * S * ‖w‖^3 := by ring
            _ ≤ (8 * max A (8*S) + 1) * ‖w‖^3 :=
                mul_le_mul_of_nonneg_right hC (by positivity)


/-- `ft2` is the Fourier integral of `φ` at the frequency `(h₁,h₂)`. -/
lemma blin_apply' (v w : ℝ×ℝ) :
    ((ContinuousLinearMap.toLinearMap₁₂ blin) v) w = v.1*w.1 + v.2*w.2 := rfl

lemma ft2_eq_fourierIntegral (φ : ℝ×ℝ→ℂ) (h : ℤ×ℤ) :
    ft2 φ h = VectorFourier.fourierIntegral Real.fourierChar volume blin.toLinearMap₁₂ φ
      ((h.1:ℝ),(h.2:ℝ)) := by
  rw [ft2]
  simp only [VectorFourier.fourierIntegral]
  apply integral_congr_ae
  filter_upwards with v
  have hpt : 𝐞 (-((ContinuousLinearMap.toLinearMap₁₂ blin) v) (↑h.1, ↑h.2)) • φ v
      = φ v * Complex.exp (-(2 * Real.pi * Complex.I) * (↑↑h.1 * ↑v.1 + ↑↑h.2 * ↑v.2)) := by
    rw [Circle.smul_def, Real.fourierChar_apply]
    rw [show (↑(2 * Real.pi * -((ContinuousLinearMap.toLinearMap₁₂ blin) v) (↑h.1, ↑h.2)) * Complex.I)
        = -(2 * Real.pi * Complex.I) * (↑↑h.1 * ↑v.1 + ↑↑h.2 * ↑v.2) by
      rw [blin_apply']; push_cast; ring]
    ring
  rw [hpt]
  simp

/-- **The two-dimensional decay of `ft2`.** -/
lemma ft2_decay (φ : ℝ×ℝ→ℂ) (hφ : ContDiff ℝ 3 φ) (hcs : HasCompactSupport φ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℤ×ℤ,
      ‖ft2 φ h‖ ≤ C / (1 + (max |(h.1:ℝ)| |(h.2:ℝ)|))^3 := by
  obtain ⟨C, hC, hbound⟩ := ft2_decay_aux φ hφ hcs
  refine ⟨C, hC, fun h => ?_⟩
  rw [ft2_eq_fourierIntegral]
  have hnorm : ‖(((h.1:ℝ)),((h.2:ℝ)))‖ = max |(h.1:ℝ)| |(h.2:ℝ)| := by
    rw [Prod.norm_def]; norm_num
  have := hbound ((h.1:ℝ),(h.2:ℝ))
  rwa [hnorm] at this


lemma norm_le_indicator {φ : ℝ×ℝ→ℂ} (hc : Continuous φ) (hcs : HasCompactSupport φ) :
    ∃ (M R : ℝ), 0 ≤ M ∧ ∀ x t₂, ‖φ (x,t₂)‖
      ≤ M * Set.indicator (Set.Icc (-R) R) (fun _ => (1:ℝ)) t₂ := by
  obtain ⟨R, hR0, hRR, hLL⟩ := exists_box_support hcs
  have hcpt : IsCompact (Set.Icc (-R) R ×ˢ Set.Icc (-R) R) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨M, hM⟩ := hcpt.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max M 0, R, le_max_right _ _, fun x t₂ => ?_⟩
  by_cases h2 : t₂ ∈ Set.Icc (-R) R
  · rw [Set.indicator_of_mem h2, mul_one]
    by_cases h1 : x ∈ Set.Icc (-R) R
    · exact (hM (x,t₂) ⟨h1, h2⟩).trans (le_max_left _ _)
    · have hz : φ (x,t₂) = 0 := by
        apply hRR x t₂
        simp only [Set.mem_Icc, not_and_or, not_le] at h1
        rcases h1 with h1 | h1
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      rw [hz, norm_zero]; exact le_max_right M 0
  · rw [Set.indicator_of_notMem h2, mul_zero]
    have hz : φ (x,t₂) = 0 := by
      apply hLL x t₂
      simp only [Set.mem_Icc, not_and_or, not_le] at h2
      rcases h2 with h2 | h2
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    rw [hz, norm_zero]

lemma cont_F {φ : ℝ×ℝ→ℂ} (hc : Continuous φ) (hcs : HasCompactSupport φ) (h₂ : ℤ) :
    Continuous (fun x : ℝ => ∫ t₂, φ (x,t₂) * kern ((h₂:ℝ)*t₂)) := by
  obtain ⟨M, R, hM0, hM⟩ := norm_le_indicator hc hcs
  refine continuous_of_dominated
    (F := fun x t₂ => φ (x,t₂) * kern ((h₂:ℝ)*t₂))
    (bound := fun t₂ => M * Set.indicator (Set.Icc (-R) R) (fun _ => (1:ℝ)) t₂) ?_ ?_ ?_ ?_
  · intro x
    exact (((hc.comp (by fun_prop : Continuous fun t₂ : ℝ => (x,t₂))).mul
      (continuous_kern _))).aestronglyMeasurable
  · intro x
    filter_upwards with t₂
    rw [norm_mul, kern_norm, mul_one]
    exact hM x t₂
  · exact ((integrableOn_const (isCompact_Icc.measure_lt_top.ne) (C := (1:ℝ))).integrable_indicator
      measurableSet_Icc).const_mul M
  · exact Filter.Eventually.of_forall (fun t₂ =>
      (hc.comp (by fun_prop : Continuous fun x : ℝ => (x,t₂))).mul continuous_const)

lemma hasCompactSupport_F {φ : ℝ×ℝ→ℂ} (hcs : HasCompactSupport φ) (h₂ : ℤ) :
    HasCompactSupport (fun x : ℝ => ∫ t₂, φ (x,t₂) * kern ((h₂:ℝ)*t₂)) := by
  obtain ⟨R, hR0, hRR, _⟩ := exists_box_support hcs
  rw [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact]
  have hm : {x : ℝ | (∫ t₂, φ (x,t₂) * kern ((h₂:ℝ)*t₂)) = 0} ∈ Filter.cocompact ℝ := by
    rw [Metric.mem_cocompact_iff_closedBall_compl_subset (0:ℝ)]
    refine ⟨R, fun x hx => ?_⟩
    rw [Set.mem_ofPred_eq]
    simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hx
    have hz : (fun t₂ => φ (x,t₂) * kern ((h₂:ℝ)*t₂)) = 0 := by
      funext t₂; rw [Pi.zero_apply, hRR x t₂ (by linarith), zero_mul]
    rw [hz]; simp
  exact hm

lemma summable_fourier_F (φ : ℝ×ℝ→ℂ) (hφ : ContDiff ℝ 3 φ) (hcs : HasCompactSupport φ)
    (h₂ : ℤ) :
    Summable (fun h₁ : ℤ => 𝓕 (fun x : ℝ => ∫ t₂, φ (x,t₂) * kern ((h₂:ℝ)*t₂)) h₁) := by
  obtain ⟨C, hC, hbound⟩ := ft2_decay φ hφ hcs
  have heq : ∀ h₁ : ℤ, 𝓕 (fun x : ℝ => ∫ t₂, φ (x,t₂)*kern ((h₂:ℝ)*t₂)) h₁ = ft2 φ (h₁,h₂) :=
    fun h₁ => fourier_spectral_slice φ hφ.continuous hcs (h₁,h₂)
  have hmaj : Summable (fun h₁ : ℤ => C * |(h₁:ℝ)| ^ (-(3:ℝ))) :=
    (Real.summable_abs_int_rpow (by norm_num : (1:ℝ) < 3)).mul_left C
  refine Summable.of_norm_bounded_eventually hmaj ?_
  rw [Filter.eventually_cofinite]
  refine Set.Finite.subset (Set.finite_Icc (-1:ℤ) 1) (fun h₁ hh => ?_)
  simp only [Set.mem_setOf_eq] at hh
  rw [Set.mem_Icc]
  by_contra hcon
  rw [not_and_or] at hcon
  have hge : (1:ℝ) ≤ |(h₁:ℝ)| := by
    rcases hcon with h|h
    · have : (h₁:ℝ) < -1 := by exact_mod_cast (not_le.mp h)
      rw [abs_of_neg (by linarith)]; linarith
    · have : (1:ℝ) < (h₁:ℝ) := by exact_mod_cast (not_le.mp h)
      rw [abs_of_pos (by linarith)]; linarith
  have hb : ‖𝓕 (fun x : ℝ => ∫ t₂, φ (x,t₂)*kern ((h₂:ℝ)*t₂)) h₁‖ ≤ C * |(h₁:ℝ)|^(-(3:ℝ)) := by
    rw [heq h₁]
    calc ‖ft2 φ (h₁,h₂)‖ ≤ C / (1 + max |(h₁:ℝ)| |(h₂:ℝ)|)^3 := hbound (h₁,h₂)
      _ ≤ C / (1 + |(h₁:ℝ)|)^3 := by
          apply div_le_div_of_nonneg_left hC.le (by positivity)
          gcongr; exact le_max_left _ _
      _ = C * (1 + |(h₁:ℝ)|)^(-(3:ℝ)) := by
          rw [Real.rpow_neg (by positivity), div_eq_mul_inv]
          norm_num
      _ ≤ C * |(h₁:ℝ)|^(-(3:ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hC.le
          exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)
  linarith [not_le.mp hh, hb]

lemma fourier_zero_real : 𝓕 (0 : ℝ → ℂ) = 0 := by
  funext p
  rw [Real.fourier_eq']
  simp

lemma summable_ft2 (φ : ℝ×ℝ→ℂ) (hφ : ContDiff ℝ 3 φ) (hcs : HasCompactSupport φ) :
    Summable (fun p : ℤ×ℤ => ft2 φ p) := by
  obtain ⟨C, hC, hbound⟩ := ft2_decay φ hφ hcs
  set f : ℤ → ℝ := fun i => (1 + |(i:ℝ)|) ^ (-(3/2:ℝ)) with hf
  have hf_nn : ∀ i, 0 ≤ f i := fun i => Real.rpow_nonneg (by positivity) _
  have hfsumm : Summable f := by
    refine Summable.of_norm_bounded_eventually
      (Real.summable_abs_int_rpow (by norm_num : (1:ℝ) < 3/2)) ?_
    rw [Filter.eventually_cofinite]
    refine Set.Finite.subset (Set.finite_singleton (0:ℤ)) (fun i hi => ?_)
    simp only [Set.mem_setOf_eq] at hi
    rw [Set.mem_singleton_iff]
    by_contra hne
    have hge : (1:ℝ) ≤ |(i:ℝ)| := by
      have : (1:ℤ) ≤ |i| := Int.one_le_abs hne
      rw [← Int.cast_abs]; exact_mod_cast this
    have hb : ‖f i‖ ≤ |(i:ℝ)| ^ (-(3/2:ℝ)) := by
      rw [Real.norm_of_nonneg (hf_nn i)]
      rw [hf]; simp only
      exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)
    exact absurd hb hi
  have hg : Summable (fun p : ℤ×ℤ => C * f p.1 * f p.2) := by
    rw [summable_prod_of_nonneg (fun p => by positivity)]
    constructor
    · intro x
      exact (hfsumm.mul_left (C * f x))
    · have : (fun x : ℤ => ∑' y : ℤ, C * f x * f y)
          = (fun x : ℤ => (C * f x) * (∑' y, f y)) := by
        funext x; rw [tsum_mul_left]
      rw [this]
      exact ((hfsumm.mul_left C).mul_right _)
  refine Summable.of_norm_bounded hg (fun p => ?_)
  have hM0 : 0 < 1 + max |(p.1:ℝ)| |(p.2:ℝ)| := by positivity
  have h1 : (1 + max |(p.1:ℝ)| |(p.2:ℝ)|)^(-(3/2:ℝ)) ≤ f p.1 := by
    rw [hf]; simp only
    exact Real.rpow_le_rpow_of_nonpos (by positivity)
      (by linarith [le_max_left |(p.1:ℝ)| |(p.2:ℝ)|]) (by norm_num)
  have h2 : (1 + max |(p.1:ℝ)| |(p.2:ℝ)|)^(-(3/2:ℝ)) ≤ f p.2 := by
    rw [hf]; simp only
    exact Real.rpow_le_rpow_of_nonpos (by positivity)
      (by linarith [le_max_right |(p.1:ℝ)| |(p.2:ℝ)|]) (by norm_num)
  calc ‖ft2 φ p‖ ≤ C / (1 + max |(p.1:ℝ)| |(p.2:ℝ)|)^3 := hbound p
    _ = C * (1 + max |(p.1:ℝ)| |(p.2:ℝ)|)^(-(3:ℝ)) := by
        rw [Real.rpow_neg (by positivity), div_eq_mul_inv]; norm_num
    _ ≤ C * (f p.1 * f p.2) := by
        apply mul_le_mul_of_nonneg_left _ hC.le
        calc (1 + max |(p.1:ℝ)| |(p.2:ℝ)|)^(-(3:ℝ))
            = (1 + max |(p.1:ℝ)| |(p.2:ℝ)|)^(-(3/2:ℝ))
              * (1 + max |(p.1:ℝ)| |(p.2:ℝ)|)^(-(3/2:ℝ)) := by
                rw [← Real.rpow_add hM0]; norm_num
          _ ≤ f p.1 * f p.2 := mul_le_mul h1 h2 (Real.rpow_nonneg (by positivity) _) (hf_nn p.1)
    _ = C * f p.1 * f p.2 := by ring

/-- **Two-dimensional Poisson summation** on the unit lattice, for `C³` compactly supported `φ`. -/
theorem poisson_2d_unit (φ : ℝ×ℝ→ℂ) (hφ : ContDiff ℝ 3 φ) (hcs : HasCompactSupport φ) :
    (∑' n : ℤ×ℤ, φ ((n.1:ℝ),(n.2:ℝ))) = ∑' h : ℤ×ℤ, ft2 φ h := by
  obtain ⟨R, hR0, hRR, hLL⟩ := exists_box_support hcs
  set N : ℤ := ((⌈R⌉₊ : ℕ) : ℤ) with hNdef
  have hNR : R ≤ (N:ℝ) := by rw [hNdef]; exact Nat.le_ceil R
  have hslice_zero : ∀ n₁ : ℤ, N < |n₁| → (fun t : ℝ => φ ((n₁:ℝ),t)) = 0 := by
    intro n₁ hn
    funext t
    simp only [Pi.zero_apply]
    apply hRR n₁ t
    have h1 : (N:ℝ) < |(n₁:ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hn
    linarith
  have hN0 : (0:ℤ) ≤ N := by rw [hNdef]; positivity
  have hnotmem : ∀ n₁ : ℤ, n₁ ∉ Finset.Icc (-N) N → N < |n₁| := by
    intro n₁ hn₁
    rw [Finset.mem_Icc, not_and_or] at hn₁
    rcases hn₁ with h|h
    · have h' : n₁ < -N := not_le.mp h
      rw [abs_of_neg (by omega : n₁ < 0)]; omega
    · have h' : N < n₁ := not_le.mp h
      rw [abs_of_pos (by omega : 0 < n₁)]; exact h'
  have hf_summ : Summable (fun n : ℤ×ℤ => φ ((n.1:ℝ),(n.2:ℝ))) := by
    apply summable_of_ne_finset_zero (s := Finset.Icc (-N) N ×ˢ Finset.Icc (-N) N)
    intro n hn
    rw [Finset.mem_product, not_and_or] at hn
    rcases hn with h|h
    · apply hRR n.1 n.2
      have h1 : (N:ℝ) < |(n.1:ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast (hnotmem n.1 h)
      linarith
    · apply hLL n.1 n.2
      have h1 : (N:ℝ) < |(n.2:ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast (hnotmem n.2 h)
      linarith
  rw [hf_summ.tsum_prod]
  have hslice_summ : ∀ n₁ : ℤ,
      Summable (fun h₂ : ℤ => 𝓕 (fun t => φ ((n₁:ℝ),t)) h₂) := fun n₁ =>
    summable_fourier_of_contDiff ((contDiff_slice_snd hφ n₁).of_le (by norm_num))
      (hasCompactSupport_slice_snd hcs n₁)
  have step1 : (∑' n₁ : ℤ, ∑' n₂ : ℤ, φ ((n₁:ℝ),(n₂:ℝ)))
      = ∑' n₁ : ℤ, ∑' h₂ : ℤ, 𝓕 (fun t => φ ((n₁:ℝ),t)) h₂ := by
    apply tsum_congr; intro n₁
    exact poisson_unit_one (fun t => φ ((n₁:ℝ),t)) (contDiff_slice_snd hφ n₁).continuous
      (hasCompactSupport_slice_snd hcs n₁) (hslice_summ n₁)
  rw [step1]
  have hg0 : ∀ n₁ ∉ Finset.Icc (-N) N,
      (∑' h₂ : ℤ, 𝓕 (fun t => φ ((n₁:ℝ),t)) h₂) = 0 := by
    intro n₁ hn₁
    rw [hslice_zero n₁ (hnotmem n₁ hn₁), fourier_zero_real]
    simp
  rw [tsum_eq_sum hg0]
  rw [← Summable.tsum_finsetSum (s := Finset.Icc (-N) N) (fun i _ => hslice_summ i)]
  have stepC : ∀ h₂ : ℤ, (∑ n₁ ∈ Finset.Icc (-N) N, 𝓕 (fun t => φ ((n₁:ℝ),t)) h₂)
      = ∑' h₁ : ℤ, ft2 φ (h₁,h₂) := by
    intro h₂
    have hte : (∑' n₁ : ℤ, 𝓕 (fun t => φ ((n₁:ℝ),t)) h₂)
        = ∑ n₁ ∈ Finset.Icc (-N) N, 𝓕 (fun t => φ ((n₁:ℝ),t)) h₂ :=
      tsum_eq_sum (fun n₁ hn₁ => by
        rw [hslice_zero n₁ (hnotmem n₁ hn₁)]
        simpa using congrFun fourier_zero_real h₂)
    rw [← hte]
    rw [show (∑' n₁ : ℤ, 𝓕 (fun t => φ ((n₁:ℝ),t)) h₂)
          = ∑' n₁ : ℤ, (∫ t₂, φ ((n₁:ℝ),t₂) * kern ((h₂:ℝ)*t₂)) from
        tsum_congr (fun n₁ => fourier_slice (fun t => φ ((n₁:ℝ),t)) (h₂:ℝ))]
    rw [poisson_unit_one (fun x : ℝ => ∫ t₂, φ (x,t₂) * kern ((h₂:ℝ)*t₂))
        (cont_F hφ.continuous hcs h₂) (hasCompactSupport_F hcs h₂) (summable_fourier_F φ hφ hcs h₂)]
    apply tsum_congr
    intro h₁
    exact fourier_spectral_slice φ hφ.continuous hcs (h₁,h₂)
  rw [show (∑' h₂ : ℤ, ∑ n₁ ∈ Finset.Icc (-N) N, 𝓕 (fun t => φ ((n₁:ℝ),t)) h₂)
        = ∑' h₂ : ℤ, ∑' h₁ : ℤ, ft2 φ (h₁,h₂) from tsum_congr stepC]
  rw [Summable.tsum_comm (f := fun h₁ h₂ : ℤ => ft2 φ (h₁,h₂)) (summable_ft2 φ hφ hcs)]
  rw [← (summable_ft2 φ hφ hcs).tsum_prod]

/-- The real-point version of `cosetPt`: the affine map `x ↦ γ + m·x` on `ℝ²`. -/
def cosetPtR (m : ℕ) (γ : ℤ × ℤ) (x : ℝ × ℝ) : ℝ × ℝ :=
  ((γ.1 : ℝ) + (m:ℝ) * x.1, (γ.2 : ℝ) + (m:ℝ) * x.2)

/-- `cosetPt` on lattice points is `cosetPtR` on their real images. -/
lemma cosetPt_eq (m : ℕ) (γ c : ℤ × ℤ) :
    cosetPt m γ c = cosetPtR m γ ((c.1 : ℝ), (c.2 : ℝ)) := by
  simp [cosetPt, cosetPtR]

/-- The affine map `x ↦ γ + m·x` (`m ≥ 1`) is a homeomorphism of `ℝ²`. -/
lemma exists_homeomorph_cosetPtR (m : ℕ) (hm : 1 ≤ m) (γ : ℤ × ℤ) :
    ∃ e : ℝ × ℝ ≃ₜ ℝ × ℝ, ⇑e = cosetPtR m γ := by
  have hmpos : (0:ℝ) < (m:ℝ) := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hm)
  let e : ℝ × ℝ ≃ₜ ℝ × ℝ :=
  { toFun := fun x => ((γ.1:ℝ) + (m:ℝ)*x.1, (γ.2:ℝ)+(m:ℝ)*x.2)
    invFun := fun y => ((y.1 - (γ.1:ℝ))/(m:ℝ), (y.2-(γ.2:ℝ))/(m:ℝ))
    left_inv := by intro x; ext <;> field_simp <;> ring
    right_inv := by intro y; ext <;> field_simp <;> ring
    continuous_toFun := by continuity
    continuous_invFun := by continuity }
  exact ⟨e, rfl⟩

/-- **The change of variables in the Fourier integral.**  For `φ : ℝ² → ℂ`, `m ≥ 1`, `γ ∈ ℤ²`
and `h ∈ ℤ²`,
  `∫_{ℝ²} φ(γ + m x) e(−h·x) dx = m^{-2} ∫_{ℝ²} φ(t) e(−h·(t−γ)/m) dt`. -/
lemma ft2_comp_affine (φ : ℝ × ℝ → ℂ) (m : ℕ) (hm : 1 ≤ m) (γ : ℤ × ℤ) (h : ℤ × ℤ) :
    ft2 (fun x : ℝ × ℝ => φ (cosetPtR m γ x)) h
      = ((m:ℝ)^2)⁻¹ * ft2coset φ m γ h := by
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have ha : (0:ℝ) < (m:ℝ) := lt_of_lt_of_le zero_lt_one hm1
  have hane : ((m:ℝ)) ≠ 0 := ha.ne'
  have hcane' : ((m:ℂ)) ≠ 0 := by exact_mod_cast hane
  simp only [ft2, ft2coset]
  set g : ℝ×ℝ → ℂ := fun u => φ ((γ.1:ℝ)+u.1, (γ.2:ℝ)+u.2) *
      Complex.exp (-(2*Real.pi*Complex.I) * (((h.1:ℝ)*((m:ℝ)⁻¹*u.1) + (h.2:ℝ)*((m:ℝ)⁻¹*u.2)) : ℂ)) with hg_def
  have hstep1 : (∫ t : ℝ×ℝ, φ (cosetPtR m γ t) * Complex.exp (-(2*Real.pi*Complex.I) * (((h.1:ℝ)*t.1 + (h.2:ℝ)*t.2) : ℂ)))
      = ∫ t : ℝ×ℝ, g ((m:ℝ) • t) := by
    apply integral_congr_ae
    filter_upwards with t
    simp only [hg_def, cosetPtR, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    congr 1
    congr 1
    congr 1
    push_cast
    field_simp
  rw [hstep1]
  rw [Measure.integral_comp_smul_of_nonneg (volume : Measure (ℝ×ℝ)) g (m:ℝ) (hR := ha.le)]
  have hfin : Module.finrank ℝ (ℝ×ℝ) = 2 := by simp [Module.finrank_prod]
  rw [hfin, Complex.real_smul]
  set H : ℝ×ℝ → ℂ := fun s => φ s * Complex.exp (-(2*Real.pi*Complex.I) * ((((h.1:ℝ)*(s.1-(γ.1:ℝ)) + (h.2:ℝ)*(s.2-(γ.2:ℝ)))/(m:ℝ)) : ℂ)) with hH_def
  have hstep2 : (∫ u : ℝ×ℝ, g u) = ∫ s : ℝ×ℝ, H s := by
    have h1 : (∫ u : ℝ×ℝ, g u) = ∫ u : ℝ×ℝ, H (((γ.1:ℝ),(γ.2:ℝ)) + u) := by
      apply integral_congr_ae
      filter_upwards with u
      simp only [hg_def, hH_def, Prod.fst_add, Prod.snd_add]
      congr 1
      congr 1
      congr 1
      push_cast
      field_simp <;> ring_nf
    rw [h1, MeasureTheory.integral_add_left_eq_self H ((γ.1:ℝ),(γ.2:ℝ))]
  rw [hstep2]

/-- **Two-dimensional Poisson summation on a lattice coset** `γ + mℤ²`: for `φ : ℝ² → ℂ` of
class `C³` with compact support, `m ≥ 1` and `γ ∈ ℤ²`,

  `∑_{c ∈ ℤ²} φ(γ₁ + m c₁, γ₂ + m c₂) = m^{-2} ∑_{h ∈ ℤ²} ∫_{ℝ²} φ(t) e(−h·(t−γ)/m) dt`.

This is `poisson_2d` applied to `x ↦ φ(γ + m x)` together with the scaling
`∫_{ℝ²} φ(γ+mx) e(−h·x) dx = m^{-2} ∫_{ℝ²} φ(t) e(−h·(t−γ)/m) dt`; it is the form in which FI §6
sums each residue class modulo `|Δ|` of the lattice count (6.7).  (`Work.FIArea2.cosetPt` and
`Work.FIArea2.ft2coset` in `Submission.Work.FIArea2.Poisson2dDefs` are the two sides'
ingredients.) -/
theorem poisson_coset_2d (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ 3 φ) (hcs : HasCompactSupport φ)
    (m : ℕ) (hm : 1 ≤ m) (γ : ℤ × ℤ) :
    (∑' c : ℤ × ℤ, φ (Work.FIArea2.cosetPt m γ c))
      = ((m : ℝ) ^ 2)⁻¹ * ∑' h : ℤ × ℤ, Work.FIArea2.ft2coset φ m γ h := by
  obtain ⟨e, he⟩ := exists_homeomorph_cosetPtR m hm γ
  have hcd : ContDiff ℝ 3 (fun x : ℝ × ℝ => φ (cosetPtR m γ x)) := by
    refine hφ.comp ?_
    unfold cosetPtR
    fun_prop
  have hcs' : HasCompactSupport (fun x : ℝ × ℝ => φ (cosetPtR m γ x)) := by
    simpa only [he, Function.comp_def] using hcs.comp_homeomorph e
  have hL : (∑' c : ℤ × ℤ, φ (cosetPt m γ c))
      = ∑' n : ℤ × ℤ, (fun x : ℝ × ℝ => φ (cosetPtR m γ x)) ((n.1 : ℝ), (n.2 : ℝ)) :=
    tsum_congr (fun c => by rw [cosetPt_eq])
  rw [hL, poisson_2d_unit (fun x : ℝ × ℝ => φ (cosetPtR m γ x)) hcd hcs']
  rw [show (∑' h : ℤ × ℤ, ft2 (fun x : ℝ × ℝ => φ (cosetPtR m γ x)) h)
        = ∑' h : ℤ × ℤ, ((m:ℝ)^2)⁻¹ * ft2coset φ m γ h from
      tsum_congr (fun h => ft2_comp_affine φ m hm γ h)]
  rw [tsum_mul_left]

end

end Work.FIArea2
