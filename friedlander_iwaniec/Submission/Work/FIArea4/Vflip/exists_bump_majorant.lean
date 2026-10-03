import Mathlib
import Submission.Commons.Analysis.Fourier.scaled_bump_fourier_decay
import Submission.Commons.Analysis.Fourier.fourier_scaled_translate
import Submission.Commons.Analysis.Fourier.fourier_eq_integral_exp_real

open MeasureTheory
open scoped FourierTransform

namespace Work.FIArea4.Vflip

/-- A fixed smooth bump function: equal to `1` on `[1,2]` and supported in `(1/2, 5/2)`. -/
noncomputable def bumpF (x : ℝ) : ℝ :=
  Real.smoothTransition (2 * x - 1) * Real.smoothTransition (5 - 2 * x)

/-- The same bump, viewed as a complex valued function. -/
noncomputable def bumpFc (x : ℝ) : ℂ := (bumpF x : ℂ)

lemma bumpF_nonneg (x : ℝ) : 0 ≤ bumpF x :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma bumpF_eq_one {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 2) : bumpF x = 1 := by
  simp only [bumpF]
  rw [Real.smoothTransition.one_of_one_le (x := 2 * x - 1) (by linarith),
    Real.smoothTransition.one_of_one_le (x := 5 - 2 * x) (by linarith), mul_one]

lemma bumpF_support {x : ℝ} (h : bumpF x ≠ 0) : 1 / 2 < x ∧ x < 5 / 2 := by
  have h1 : Real.smoothTransition (2 * x - 1) ≠ 0 := fun hz => h (by rw [bumpF, hz, zero_mul])
  have h2 : Real.smoothTransition (5 - 2 * x) ≠ 0 := fun hz => h (by rw [bumpF, hz, mul_zero])
  have h1' : 0 < 2 * x - 1 := by
    by_contra hc
    exact h1 (Real.smoothTransition.zero_of_nonpos (not_lt.mp hc))
  have h2' : 0 < 5 - 2 * x := by
    by_contra hc
    exact h2 (Real.smoothTransition.zero_of_nonpos (not_lt.mp hc))
  constructor <;> linarith

lemma bumpF_contDiff : ContDiff ℝ (⊤ : ℕ∞) bumpF := by
  unfold bumpF
  fun_prop

lemma bumpF_continuous : Continuous bumpF := bumpF_contDiff.continuous

lemma bumpF_hasCompactSupport : HasCompactSupport bumpF := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (1/2:ℝ) (5/2))
    isCompact_Icc (fun x hx => ?_)
  obtain ⟨h1, h2⟩ := bumpF_support (Function.mem_support.mp hx)
  exact ⟨le_of_lt h1, le_of_lt h2⟩

lemma bumpFc_contDiff : ContDiff ℝ (⊤ : ℕ∞) bumpFc := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => (bumpF x : ℂ))
  simpa [Function.comp_def] using
    (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := (⊤ : ℕ∞)) Complex.ofRealCLM).comp
      bumpF_contDiff

lemma bumpFc_hasCompactSupport : HasCompactSupport bumpFc := by
  change HasCompactSupport (fun x : ℝ => (bumpF x : ℂ))
  simpa [Function.comp_def] using
    bumpF_hasCompactSupport.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)

/-- The fixed bump `bumpFc` has Fourier transform decaying like `(1 + |t|) ^ (-2)`. -/
lemma bumpFc_fourier_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖FourierTransform.fourier bumpFc t‖ ≤ C * (1 + |t|) ^ (-(2:ℝ)) := by
  obtain ⟨C₀, hC₀, hdecay⟩ :=
    Commons.Analysis.Fourier.scaled_bump_fourier_decay bumpFc bumpFc_contDiff
      bumpFc_hasCompactSupport 2
  refine ⟨C₀, hC₀, fun t => ?_⟩
  have h := hdecay 1 one_pos (2 * Real.pi * t)
  simp only [div_one, Complex.ofReal_one] at h
  have hEq : ‖FourierTransform.fourier bumpFc t‖
      = ‖∫ u : ℝ, bumpFc u * Complex.exp
          (-(Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) * (u : ℂ)))‖ := by
    rw [Commons.Analysis.Fourier.fourier_eq_integral_exp_real]
  have hmono : (1 + 1 * |2 * Real.pi * t|) ^ (-(2:ℝ)) ≤ (1 + |t|) ^ (-(2:ℝ)) := by
    refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by norm_num)
    rw [one_mul, abs_mul, abs_mul, abs_of_pos Real.pi_pos,
      abs_of_pos (by norm_num : (0:ℝ) < 2)]
    nlinarith [abs_nonneg t, Real.pi_gt_three]
  calc ‖FourierTransform.fourier bumpFc t‖
      = _ := hEq
    _ ≤ C₀ * (1 + 1 * |2 * Real.pi * t|) ^ (-(2:ℝ)) := h
    _ ≤ C₀ * (1 + |t|) ^ (-(2:ℝ)) := mul_le_mul_of_nonneg_left hmono hC₀

theorem exists_bump_majorant (S : ℕ) (hS : 1 ≤ S) :
    ∃ (f : ℝ → ℝ) (C : ℝ), 0 < C ∧
      (∀ x, 0 ≤ f x) ∧
      (∀ x, (S : ℝ) < x → x ≤ 2 * (S : ℝ) → 1 ≤ f x) ∧
      (∀ x, f x ≠ 0 → (S:ℝ)/2 ≤ x ∧ x ≤ 5 * (S:ℝ)/2) ∧
      Continuous f ∧
      (∀ ξ : ℝ, ‖FourierTransform.fourier (fun x : ℝ => (f x : ℂ)) ξ‖
          ≤ C * (S:ℝ) * (1 + (S:ℝ) * |ξ|) ^ (-(2:ℝ))) := by
  set s : ℝ := (S : ℝ) with hsdef
  have hs : 0 < s := by
    rw [hsdef]
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hS)
  obtain ⟨C₀, hC₀, hbnd⟩ := bumpFc_fourier_bound
  refine ⟨fun x => bumpF (x / s), C₀ + 1, by linarith, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact bumpF_nonneg _
  · intro x hx1 hx2
    have h1 : 1 ≤ x / s := by
      rw [one_le_div₀ hs]
      linarith
    have h2 : x / s ≤ 2 := by
      rw [div_le_iff₀ hs]
      linarith
    show (1:ℝ) ≤ bumpF (x / s)
    rw [bumpF_eq_one h1 h2]
  · intro x hx
    obtain ⟨h1, h2⟩ := bumpF_support hx
    rw [lt_div_iff₀ hs] at h1
    rw [div_lt_iff₀ hs] at h2
    constructor <;> linarith
  · exact bumpF_continuous.comp (continuous_id.div_const s)
  · intro ξ
    have hfun : (fun x : ℝ => (bumpF (x / s) : ℂ)) = fun x : ℝ => bumpFc (s⁻¹ • x) := by
      funext x
      simp only [bumpFc]
      congr 1
      congr 1
      rw [smul_eq_mul, div_eq_mul_inv, mul_comm]
    have hscale := Commons.Analysis.Fourier.fourier_comp_inv_smul (V := ℝ) (f := bumpFc) hs ξ
    have hnorm : ‖FourierTransform.fourier (fun x : ℝ => (bumpF (x / s) : ℂ)) ξ‖
        = s * ‖FourierTransform.fourier bumpFc (s * ξ)‖ := by
      rw [hfun, hscale, Module.finrank_self, pow_one, norm_smul, Real.norm_eq_abs,
        abs_of_pos hs, smul_eq_mul]
    have hb := hbnd (s * ξ)
    have hP : 0 < (1 + s * |ξ|) ^ (-(2:ℝ)) := Real.rpow_pos_of_pos (by positivity) _
    have hle : C₀ * (1 + s * |ξ|) ^ (-(2:ℝ))
        ≤ (C₀ + 1) * (1 + s * |ξ|) ^ (-(2:ℝ)) := by
      nlinarith [hP]
    calc ‖FourierTransform.fourier (fun x : ℝ => (bumpF (x / s) : ℂ)) ξ‖
        = s * ‖FourierTransform.fourier bumpFc (s * ξ)‖ := hnorm
      _ ≤ s * (C₀ * (1 + |s * ξ|) ^ (-(2:ℝ))) :=
            mul_le_mul_of_nonneg_left hb hs.le
      _ = s * (C₀ * (1 + s * |ξ|) ^ (-(2:ℝ))) := by
            rw [abs_mul, abs_of_pos hs]
      _ ≤ (C₀ + 1) * s * (1 + s * |ξ|) ^ (-(2:ℝ)) := by
            calc s * (C₀ * (1 + s * |ξ|) ^ (-(2:ℝ)))
                ≤ s * ((C₀ + 1) * (1 + s * |ξ|) ^ (-(2:ℝ))) :=
                  mul_le_mul_of_nonneg_left hle hs.le
              _ = (C₀ + 1) * s * (1 + s * |ξ|) ^ (-(2:ℝ)) := by ring

end Work.FIArea4.Vflip
