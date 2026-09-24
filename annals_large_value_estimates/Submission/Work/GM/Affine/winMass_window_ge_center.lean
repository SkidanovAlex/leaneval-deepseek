import Mathlib
import Submission.Work.GM.Affine.region_II_defs
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.f_sq_le_const_sq_smallT

/-!
# `Work.GM.Affine.winMass_window_ge_center`

A cheap *lower* bound for the window mass `∫_{|τ| ≤ 2} ‖Hfun f M₂ M₃ 0 τ‖²` in terms of the
"center" value `Σ_{m₂ ∈ R2 M₂} m₂ · ∫ f`.

Writing `H(τ) = Hfun f M₂ M₃ 0 τ = Σ_{m₂ ∈ R2 M₂} m₂ Fhat f (m₂ τ / M₃)`, the Fourier inversion
formula gives

`Re H(τ) = Σ_{m₂ ∈ R2 M₂} m₂ ∫ f(u) cos (2π u m₂ τ / M₃) du`.

For `f ≥ 0` supported in `[1/C₀, C₀]` and `|τ| ≤ δ := 1/(8πC₀)` every phase
`2π u m₂ τ / M₃` is bounded by `1/2` in modulus (using `m₂ ≤ 2M₂ ≤ 2M₃` and `u ≤ C₀`), hence
`cos ≥ 1/2` there (Lipschitz continuity of `cos`) and

`Re H(τ) ≥ (1/2) (Σ_{m₂ ∈ R2 M₂} m₂) ∫ f` for `|τ| ≤ δ`.

Integrating the (non-negative) pointwise bound over `τ ∈ [-δ, δ]` and using `[-δ,δ] ⊆ [-2,2]`
gives the claim with `c = 1/(16 π C₀) = δ/2`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.GM.Affine

noncomputable section

/-! ### Elementary facts about `efun`, `Fhat` and `R2` -/

lemma efun_re_l (t : ℝ) : (efun t).re = Real.cos (2 * Real.pi * t) := by
  rw [efun]
  rw [show (2 : ℂ) * ↑Real.pi * I * ↑t = ↑(2 * Real.pi * t) * I by push_cast; ring]
  exact Complex.exp_ofReal_mul_I_re _

lemma efun_cont_l : Continuous efun := by unfold efun; fun_prop

/-- `Fhat f ξ = ∫ u, f u · e^{-2πi u ξ}`. -/
lemma Fhat_eq_integral_l (f : ℝ → ℝ) (ξ : ℝ) :
    Fhat f ξ = ∫ u : ℝ, (f u : ℂ) * efun (-(u * ξ)) := by
  rw [Fhat, Real.fourier_real_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
  have hchar : (Real.fourierChar (-(v * ξ)) : ℂ) = efun (-(v * ξ)) := by
    rw [efun, Real.fourierChar_apply]; congr 1; push_cast; ring
  simp only [Circle.smul_def, smul_eq_mul]
  rw [hchar, mul_comm]

lemma integrable_f_mul_efun_neg_l {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f)
    (x : ℝ) : Integrable (fun u : ℝ => (f u : ℂ) * efun (-(u * x))) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (Complex.continuous_ofReal.comp hf).mul
      (efun_cont_l.comp ((continuous_id.mul continuous_const).neg))
  · exact (hcs.comp_left (g := Complex.ofReal) (by simp)).mul_right

/-- The real part of `Fhat f` as a cosine integral. -/
lemma re_Fhat_eq_integral_l {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f)
    (ξ : ℝ) : (Fhat f ξ).re = ∫ u : ℝ, f u * Real.cos (2 * Real.pi * u * ξ) := by
  rw [Fhat_eq_integral_l]
  have hg : Integrable (fun u : ℝ => (f u : ℂ) * efun (-(u * ξ))) :=
    integrable_f_mul_efun_neg_l hf hcs ξ
  have hre2 : (∫ u : ℝ, (f u : ℂ) * efun (-(u * ξ))).re
      = ∫ u : ℝ, ((f u : ℂ) * efun (-(u * ξ))).re := (integral_re hg).symm
  rw [hre2]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  simp only
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, efun_re_l]
  congr 1
  rw [show 2 * Real.pi * -(u * ξ) = -(2 * Real.pi * u * ξ) by ring, Real.cos_neg]

/-- `cos (2π u ξ) ≥ 1/2` for `u ∈ [1/C₀, C₀]` and `|ξ| ≤ 1/(4πC₀)`. -/
lemma cos_ge_half_of_small_l {C₀ : ℝ} (hC₀ : 1 ≤ C₀) {ξ : ℝ}
    (hξ : |ξ| ≤ 1 / (4 * Real.pi * C₀)) :
    ∀ u ∈ Set.Icc (1/C₀) C₀, 1/2 ≤ Real.cos (2 * Real.pi * u * ξ) := by
  intro u hu
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have hpi : 0 < Real.pi := Real.pi_pos
  have hu1 : 1/C₀ ≤ u := hu.1
  have hu2 : u ≤ C₀ := hu.2
  have hu0 : 0 ≤ u := le_trans (by positivity) hu1
  have harg : |2 * Real.pi * u * ξ| ≤ 1/2 := by
    have huabs : |u| ≤ C₀ := abs_le.mpr ⟨by linarith, hu2⟩
    have h1 : |u * ξ| ≤ C₀ * (1 / (4 * Real.pi * C₀)) := by
      rw [abs_mul]
      exact mul_le_mul huabs hξ (abs_nonneg ξ) (le_of_lt hC₀pos)
    have h3 : C₀ * (1 / (4 * Real.pi * C₀)) = 1/(4 * Real.pi) := by field_simp
    rw [h3] at h1
    have h2 : |2 * Real.pi * u * ξ| = 2 * Real.pi * |u * ξ| := by
      rw [show 2 * Real.pi * u * ξ = 2 * Real.pi * (u * ξ) by ring]
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
    rw [h2]
    have h4 : 2 * Real.pi * (1/(4*Real.pi)) = 1/2 := by field_simp; norm_num
    nlinarith [h1, h4]
  have hmain : 1 - |2 * Real.pi * u * ξ| ≤ Real.cos (2 * Real.pi * u * ξ) := by
    have h := Real.lipschitzWith_cos.dist_le_mul (2 * Real.pi * u * ξ) 0
    rw [Real.dist_eq, Real.dist_eq, Real.cos_zero, sub_zero, NNReal.coe_one, one_mul] at h
    rcases abs_le.mp h with ⟨ha, hb⟩
    linarith
  linarith

/-- For `f ≥ 0` supported in `[1/C₀, C₀]` and `|ξ| ≤ 1/(4πC₀)`: `Re Fhat f ξ ≥ (1/2) ∫ f`. -/
lemma re_Fhat_ge_half_l {C₀ : ℝ} (hC₀ : 1 ≤ C₀) {f : ℝ → ℝ} (hf : Continuous f)
    (hcs : HasCompactSupport f) (hfnn : ∀ u, 0 ≤ f u) (hsupp : SuppHyp C₀ f) {ξ : ℝ}
    (hξ : |ξ| ≤ 1 / (4 * Real.pi * C₀)) :
    (1/2) * (∫ u, f u) ≤ (Fhat f ξ).re := by
  rw [re_Fhat_eq_integral_l hf hcs ξ, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_mono ?_ ?_ ?_
  · exact (hf.integrable_of_hasCompactSupport hcs).const_mul (1/2)
  · apply Continuous.integrable_of_hasCompactSupport
    · exact hf.mul (Real.continuous_cos.comp (by fun_prop))
    · exact hcs.mul_right
  · intro u
    rcases eq_or_ne (f u) 0 with h | h
    · simp only; rw [h]; ring_nf; positivity
    · simp only
      have hu := hsupp u h
      have hc := cos_ge_half_of_small_l hC₀ hξ u hu
      have hf0 : 0 ≤ f u := hfnn u
      have : 0 < f u := lt_of_le_of_ne hf0 (Ne.symm h)
      nlinarith [hc, hf0]

lemma R2_pos_l {M₂ : ℝ} {m : ℤ} (hm : m ∈ R2 M₂) : (0:ℝ) < (m:ℝ) := by
  have h1 : (1:ℤ) ≤ m := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
  exact_mod_cast (by omega : (0:ℤ) < m)

lemma R2_le_l {M₂ : ℝ} {m : ℤ} (hm : m ∈ R2 M₂) : (m:ℝ) ≤ 2 * M₂ := by
  have h1 : m ≤ ⌊2 * M₂⌋ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).2
  have h2 : ((⌊2 * M₂⌋ : ℤ) : ℝ) ≤ 2 * M₂ := Int.floor_le _
  have h3 : (m:ℝ) ≤ ((⌊2 * M₂⌋ : ℤ) : ℝ) := by exact_mod_cast h1
  linarith

/-- `Re Hfun f M₂ M₃ 0 τ` as a sum of real parts. -/
lemma re_Hfun_zero_l (f : ℝ → ℝ) (M₂ M₃ τ : ℝ) :
    (Hfun f M₂ M₃ 0 τ).re
      = ∑ m₂ ∈ R2 M₂, (m₂ : ℝ) * (Fhat f ((m₂ : ℝ) * (τ / M₃))).re := by
  rw [Hfun, Complex.re_sum]
  refine Finset.sum_congr rfl (fun m₂ hm₂ => ?_)
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  congr 1
  simp

/-- **The center bound.**  For `|τ| ≤ 1/(8πC₀)`, `Re Hfun f M₂ M₃ 0 τ ≥ (1/2)(Σ m₂)(∫ f)`. -/
lemma re_Hfun_ge_l {C₀ : ℝ} (hC₀ : 1 ≤ C₀) {f : ℝ → ℝ} (hf : Continuous f)
    (hcs : HasCompactSupport f) (hfnn : ∀ u, 0 ≤ f u) (hsupp : SuppHyp C₀ f)
    {M₂ M₃ τ : ℝ} (hM₂ : 0 < M₂) (hM₂M₃ : M₂ ≤ M₃)
    (hτ : |τ| ≤ 1 / (8 * Real.pi * C₀)) :
    (∑ m ∈ R2 M₂, (m : ℝ)) * (∫ u, f u) / 2 ≤ (Hfun f M₂ M₃ 0 τ).re := by
  have hM₃pos : 0 < M₃ := lt_of_lt_of_le hM₂ hM₂M₃
  set S : ℝ := ∑ m ∈ R2 M₂, (m:ℝ) with hS
  set A : ℝ := ∫ u, f u with hA
  have hterm : ∀ m₂ ∈ R2 M₂,
      (m₂:ℝ) * (A/2) ≤ (m₂:ℝ) * (Fhat f ((m₂:ℝ)*(τ/M₃))).re := by
    intro m₂ hm₂
    have hm2pos : (0:ℝ) < (m₂:ℝ) := R2_pos_l hm₂
    have hle : (m₂:ℝ) ≤ 2*M₂ := R2_le_l hm₂
    have hmratio : (m₂:ℝ)/M₃ ≤ 2 := by
      rw [div_le_iff₀ hM₃pos]; nlinarith
    have hξ : |(m₂:ℝ)*(τ/M₃)| ≤ 1/(4*Real.pi*C₀) := by
      rw [show (m₂:ℝ)*(τ/M₃) = ((m₂:ℝ)/M₃) * τ by ring, abs_mul]
      have h1 : |(m₂:ℝ)/M₃| ≤ 2 := by
        rw [abs_of_nonneg (by positivity)]; exact hmratio
      have h2 : |(m₂:ℝ)/M₃| * |τ| ≤ 2 * (1/(8*Real.pi*C₀)) :=
        mul_le_mul h1 hτ (abs_nonneg _) (by norm_num)
      have h3 : 2 * (1/(8*Real.pi*C₀)) = 1/(4*Real.pi*C₀) := by field_simp; ring
      linarith [h2, h3]
    have hFhat : (1/2)*A ≤ (Fhat f ((m₂:ℝ)*(τ/M₃))).re := by
      rw [hA]; exact re_Fhat_ge_half_l hC₀ hf hcs hfnn hsupp hξ
    have h2 := mul_le_mul_of_nonneg_left hFhat hm2pos.le
    linarith [h2]
  have heq : S * A / 2 = ∑ m₂ ∈ R2 M₂, (m₂:ℝ) * (A/2) := by
    rw [hS, ← Finset.sum_mul]; ring_nf
  calc S * A / 2 = ∑ m₂ ∈ R2 M₂, (m₂:ℝ) * (A/2) := heq
    _ ≤ ∑ m₂ ∈ R2 M₂, (m₂:ℝ) * (Fhat f ((m₂:ℝ) * (τ/M₃))).re := Finset.sum_le_sum hterm
    _ = (Hfun f M₂ M₃ 0 τ).re := (re_Hfun_zero_l f M₂ M₃ τ).symm

/-! ### The main statement -/

-- `C₀` is a parameter appearing BEFORE `c`: the witness `c` may depend on `C₀`
-- (concretely `c = 1/(8*Real.pi*C₀)` works).  The statement is uniform only in `M₂, M₃, f`.
theorem winMass_window_ge_center (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {M₂ M₃ : ℝ}, 0 < M₂ → M₂ ≤ M₃ →
        ∀ {f : ℝ → ℝ}, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
          c * (∑ m ∈ R2 M₂, (m : ℝ)) ^ 2 * (∫ u, f u) ^ 2
            ≤ ∫ τ in Set.Icc (-2 : ℝ) 2, ‖Hfun f M₂ M₃ 0 τ‖ ^ 2 := by
  refine ⟨1 / (16 * Real.pi * C₀), by positivity, ?_⟩
  intro M₂ M₃ hM₂ hM₂M₃ f hf hfnn hsupp
  have hM₃pos : 0 < M₃ := lt_of_lt_of_le hM₂ hM₂M₃
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have hcs : HasCompactSupport f := hasCompactSupport_of_SuppHyp' hsupp
  set δ : ℝ := 1 / (8 * Real.pi * C₀) with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hδle2 : δ ≤ 2 := by
    rw [hδ, div_le_iff₀ (by positivity : (0:ℝ) < 8 * Real.pi * C₀)]
    nlinarith [Real.pi_gt_three, hC₀]
  set S : ℝ := ∑ m ∈ R2 M₂, (m:ℝ) with hS
  set A : ℝ := ∫ u, f u with hA
  have hA0 : 0 ≤ A := by rw [hA]; exact integral_nonneg hfnn
  have hS0 : 0 ≤ S := by
    rw [hS]; exact Finset.sum_nonneg (fun m hm => (R2_pos_l hm).le)
  have hHcont : Continuous (fun τ : ℝ => ‖Hfun f M₂ M₃ 0 τ‖ ^ 2) := by
    have hcont : Continuous (fun τ : ℝ => Hfun f M₂ M₃ 0 τ) := by
      unfold Hfun
      refine continuous_finsetSum _ (fun m₂ hm₂ => ?_)
      exact continuous_const.mul ((continuous_Fhat_aux hf hcs).comp
        (continuous_const.mul (continuous_const.add (continuous_id.div_const M₃))))
    exact hcont.norm.pow 2
  -- the pointwise lower bound on `[-δ, δ]`
  have hpoint : ∀ τ ∈ Set.Icc (-δ) δ, ((S*A)/2) ≤ ‖Hfun f M₂ M₃ 0 τ‖ := by
    intro τ hτ
    rw [Set.mem_Icc] at hτ
    have hτabs : |τ| ≤ δ := abs_le.mpr ⟨by linarith [hτ.1], hτ.2⟩
    have hτ' : |τ| ≤ 1/(8*Real.pi*C₀) := by rw [hδ] at hτabs; exact hτabs
    exact le_trans (re_Hfun_ge_l hC₀ hf hcs hfnn hsupp hM₂ hM₂M₃ hτ')
      (Complex.re_le_norm _)
  have hpt0 : 0 ≤ (S*A)/2 := div_nonneg (mul_nonneg hS0 hA0) (by norm_num)
  have hInt1 : ∫ τ in Set.Icc (-δ) δ, ((S*A)/2)^2
      ≤ ∫ τ in Set.Icc (-δ) δ, ‖Hfun f M₂ M₃ 0 τ‖^2 := by
    refine MeasureTheory.setIntegral_mono_on ?_ ?_ measurableSet_Icc ?_
    · exact (continuous_const : Continuous (fun _ : ℝ => ((S*A)/2)^2)).integrableOn_Icc
    · exact hHcont.integrableOn_Icc
    · intro τ hτ
      exact pow_le_pow_left₀ hpt0 (hpoint τ hτ) 2
  have hval : ∫ τ in Set.Icc (-δ) δ, ((S*A)/2)^2 = 2*δ*((S*A)/2)^2 := by
    rw [MeasureTheory.setIntegral_const, Real.volume_real_Icc_of_le (by linarith [hδpos] : -δ ≤ δ)]
    simp only [smul_eq_mul]
    ring
  have hsub : Set.Icc (-δ) δ ⊆ Set.Icc (-2:ℝ) 2 := by
    intro x hx
    rw [Set.mem_Icc] at hx ⊢
    exact ⟨by linarith [hx.1, hδle2], by linarith [hx.2]⟩
  have hInt2 : ∫ τ in Set.Icc (-δ) δ, ‖Hfun f M₂ M₃ 0 τ‖^2
      ≤ ∫ τ in Set.Icc (-2:ℝ) 2, ‖Hfun f M₂ M₃ 0 τ‖^2 :=
    MeasureTheory.setIntegral_mono_set hHcont.integrableOn_Icc
      (Filter.Eventually.of_forall (fun x => sq_nonneg _))
      (Filter.Eventually.of_forall hsub)
  have harith : (1/(16*Real.pi*C₀)) * S^2 * A^2 = 2*δ*((S*A)/2)^2 := by
    rw [hδ]; field_simp; ring
  rw [harith]
  calc 2*δ*((S*A)/2)^2 = ∫ τ in Set.Icc (-δ) δ, ((S*A)/2)^2 := hval.symm
    _ ≤ ∫ τ in Set.Icc (-δ) δ, ‖Hfun f M₂ M₃ 0 τ‖^2 := hInt1
    _ ≤ ∫ τ in Set.Icc (-2:ℝ) 2, ‖Hfun f M₂ M₃ 0 τ‖^2 := hInt2

end

end Work.GM.Affine
