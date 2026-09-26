import Mathlib
import Submission.Work.Asymptotics.HalfFunnel.lowBadDefs
import Submission.Work.Asymptotics.DomainD
import Submission.Work.HFN.Kaxis_local_tail

noncomputable section

open MeasureTheory Filter Topology UpperHalfPlane
open scoped Topology ContDiff

namespace Work.HFN.HalfFunnel
open Work.Asymptotics Work.Asymptotics.HalfFunnel  -- ck-hfn-fix: fork moved out of Work.Asymptotics

open Work.Kernels

/-!
# Elementary facts about the bad-line region

These are the small geometric / analytic facts about `lowBadSet`, its scale, the translate pole
`tpole` and the cusp expansion `Aexp`, shared between the main file `lowRegion_badLine` and the
lemmas about the explicit layer `lowF2`.  Everything here depends only on `lowBadDefs` and
`Kaxis_local_tail` (and Mathlib).
-/

/-! ## The scale is bounded on the bad-line region -/

lemma lowBadSet_scale_le {τ : ℍ} (hτ : lowBadSet τ) : scale τ ≤ 6 := by
  obtain ⟨hD, h1, h2, _⟩ := hτ
  obtain ⟨hre1, hre2⟩ := hD.1, hD.2.1
  have him1 : (0:ℝ) < τ.im := τ.im_pos
  have hinv : (τ.im)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ him1 (by norm_num : (0:ℝ) < 2)]
    linarith
  have hnorm : ‖(τ : ℂ)‖ ≤ 3 := by
    have hsq : ‖(τ : ℂ)‖^2 = τ.re^2 + τ.im^2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      ring
    have : τ.re^2 + τ.im^2 ≤ 1 + 4 := by
      have h3 : τ.re^2 < 1 := by nlinarith
      have h4 : τ.im^2 ≤ 4 := by nlinarith
      linarith
    nlinarith [norm_nonneg (τ : ℂ)]
  rw [Work.Kernels.scale]
  linarith

/-! ## The translate pole -/

lemma lowBadSet_re_lt_one {τ : ℍ} (hτ : lowBadSet τ) : |τ.re| < 1 := by
  obtain ⟨hD, -, -, -⟩ := hτ
  rw [abs_lt]
  exact ⟨hD.1, hD.2.1⟩

lemma lowBadSet_eps_ne {τ : ℍ} (hτ : lowBadSet τ) : τ.re - tsign τ ≠ 0 := by
  have hlt := lowBadSet_re_lt_one hτ
  rw [abs_lt] at hlt
  intro h
  unfold tsign at h
  rcases lt_or_ge 0 τ.re with hpos | hneg
  · rw [if_pos hpos] at h; linarith [hlt.2]
  · rw [if_neg (not_lt.mpr hneg)] at h; linarith [hlt.1]

lemma norm_tpole_le {τ : ℍ} (hτ : lowBadSet τ) (t : ℝ) :
    ‖tpole τ t‖ ≤ 1 / (2 * Real.pi * |τ.re - tsign τ|) := by
  have heps := lowBadSet_eps_ne hτ
  have hnum : ‖(tsign τ : ℂ)‖ = 1 := by
    unfold tsign; split <;> norm_num
  have hpi : ‖(2:ℂ) * (Real.pi:ℂ)‖ = 2 * Real.pi := by
    rw [norm_mul, Complex.norm_ofNat, Complex.norm_of_nonneg Real.pi_pos.le]
  have hge : |τ.re - tsign τ| ≤ ‖((t:ℂ) * Complex.I - ((τ:ℂ) - (tsign τ : ℂ)))‖ := by
    have hre : (((t:ℂ) * Complex.I - ((τ:ℂ) - (tsign τ : ℂ)))).re = tsign τ - τ.re := by
      simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, mul_one,
        mul_zero, zero_sub, sub_zero, Complex.ofReal_re, Complex.intCast_re, Complex.ofReal_im,
        Complex.intCast_im, UpperHalfPlane.coe_re]
      ring
    have h1 := Complex.abs_re_le_norm ((t:ℂ) * Complex.I - ((τ:ℂ) - (tsign τ : ℂ)))
    rw [hre, abs_sub_comm] at h1
    exact h1
  have hpos : 0 < |τ.re - tsign τ| := abs_pos.mpr heps
  rw [tpole, norm_div, norm_div, hnum, hpi]
  have hDpos : 0 < ‖((t:ℂ) * Complex.I - ((τ:ℂ) - (tsign τ : ℂ)))‖ :=
    lt_of_lt_of_le hpos hge
  have h2 : (1 / (2 * Real.pi)) / ‖((t:ℂ) * Complex.I - ((τ:ℂ) - (tsign τ : ℂ)))‖
      ≤ (1 / (2 * Real.pi)) / |τ.re - tsign τ| :=
    div_le_div_of_nonneg_left (by positivity) hpos hge
  have h3 : (1 / (2 * Real.pi)) / |τ.re - tsign τ| = 1 / (2 * Real.pi * |τ.re - tsign τ|) := by
    rw [div_div, mul_comm]
  linarith [h2, h3.le, h3.ge]

lemma continuous_tpole {τ : ℍ} (hτ : lowBadSet τ) : Continuous (fun t : ℝ => tpole τ t) := by
  have h1 : Continuous (fun t : ℝ => (t:ℂ) * Complex.I - ((τ:ℂ) - (tsign τ : ℂ))) :=
    (Complex.continuous_ofReal.mul continuous_const).sub continuous_const
  have hne : ∀ t : ℝ, (t:ℂ) * Complex.I - ((τ:ℂ) - (tsign τ : ℂ)) ≠ 0 := by
    intro t h
    have h2 : ((t:ℂ) * Complex.I - ((τ:ℂ) - (tsign τ : ℂ))).re = 0 := by rw [h]; simp
    rw [show ((t:ℂ) * Complex.I - ((τ:ℂ) - (tsign τ : ℂ))).re = tsign τ - τ.re from by
      simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, mul_one, mul_zero,
        zero_sub, sub_zero, Complex.ofReal_re, Complex.intCast_re, Complex.ofReal_im,
        Complex.intCast_im, UpperHalfPlane.coe_re]
      ring] at h2
    exact lowBadSet_eps_ne hτ (by linarith [h2])
  exact continuous_const.div h1 hne

/-! ## Smoothness of the spike piece -/

/-! ## Boundedness of `Aexp` on the region -/

lemma lowBadSet_Gcusp_le (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (i j : Fin 2) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ τ : ℍ, lowBadSet τ → ‖Gcusp ℓ d i j τ‖ ≤ B := by
  obtain ⟨α, β, γ, hα, hβ, hγ, hb⟩ := Gcusp_moderate ℓ d i j
  refine ⟨α * (2 ^ β + 3 ^ γ), ?_, ?_⟩
  · have h1 : (0:ℝ) ≤ 2 ^ β := Real.rpow_nonneg (by norm_num) _
    have h2 : (0:ℝ) ≤ 3 ^ γ := Real.rpow_nonneg (by norm_num) _
    positivity
  · intro τ hτ
    have h1 : τ.im⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ τ.im_pos (by norm_num : (0:ℝ) < 2)]
      linarith [hτ.2.1]
    have h2 : ‖(τ : ℂ)‖ ≤ 3 := by
      have hsq : ‖(τ : ℂ)‖^2 = τ.re^2 + τ.im^2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
        ring
      have h3 : τ.re^2 ≤ 1 := by
        have h := lowBadSet_re_lt_one hτ
        rw [abs_lt] at h
        nlinarith [h.1, h.2]
      have h4 : τ.im^2 ≤ 4 := by
        nlinarith [hτ.2.2.1, τ.im_pos]
      have : τ.re^2 + τ.im^2 ≤ 1 + 4 := by linarith
      nlinarith [norm_nonneg (τ : ℂ)]
    have h5 : (τ.im⁻¹) ^ β ≤ (2:ℝ) ^ β := Real.rpow_le_rpow (by positivity) h1 hβ
    have h6 : ‖(τ : ℂ)‖ ^ γ ≤ (3:ℝ) ^ γ := Real.rpow_le_rpow (norm_nonneg _) h2 hγ
    calc ‖Gcusp ℓ d i j τ‖ ≤ α * ((τ.im⁻¹) ^ β + ‖(τ : ℂ)‖ ^ γ) := hb τ hτ.1
      _ ≤ α * ((2:ℝ) ^ β + (3:ℝ) ^ γ) := by
          apply mul_le_mul_of_nonneg_left _ hα
          linarith

lemma norm_mul_I_mul {t : ℝ} (ht : 0 ≤ t) (c : ℂ) : ‖((t:ℂ) * Complex.I * c)‖ = t * ‖c‖ := by
  rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ht]

lemma lowBadSet_Aexp_le (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ CB : ℝ, 0 ≤ CB ∧ ∀ (τ : ℍ), lowBadSet τ → ∀ t : ℝ, 1 ≤ t → t ≤ lowT →
      ‖Aexp (Gcusp ℓ d) τ t‖ ≤ CB := by
  obtain ⟨B00, hB00, hb00⟩ := lowBadSet_Gcusp_le ℓ d hd 0 0
  obtain ⟨B01, hB01, hb01⟩ := lowBadSet_Gcusp_le ℓ d hd 0 1
  obtain ⟨B10, hB10, hb10⟩ := lowBadSet_Gcusp_le ℓ d hd 1 0
  obtain ⟨B11, hB11, hb11⟩ := lowBadSet_Gcusp_le ℓ d hd 1 1
  refine ⟨B00 + lowT * B01 + Real.exp (2 * Real.pi * lowT) * (B10 + lowT * B11), ?_, ?_⟩
  · have hLT : (0:ℝ) ≤ lowT := by rw [lowT]; norm_num
    have h1 : (0:ℝ) ≤ Real.exp (2 * Real.pi * lowT) := Real.exp_nonneg _
    have h2 : (0:ℝ) ≤ B00 + lowT * B01 := by positivity
    have h3 : 0 ≤ B10 + lowT * B11 := by positivity
    linarith [mul_nonneg h1 h3]
  · intro τ hτ t ht1 htT
    have ht0 : (0:ℝ) ≤ t := le_trans zero_le_one ht1
    have hexp : Real.exp (2 * Real.pi * t) ≤ Real.exp (2 * Real.pi * lowT) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, htT])
    have e2 : ‖((t:ℂ) * Complex.I * Gcusp ℓ d 0 1 τ)‖ ≤ t * B01 := by
      rw [norm_mul_I_mul ht0]; exact mul_le_mul_of_nonneg_left (hb01 τ hτ) ht0
    have e2' : ‖((t:ℂ) * Complex.I * Gcusp ℓ d 1 1 τ)‖ ≤ t * B11 := by
      rw [norm_mul_I_mul ht0]; exact mul_le_mul_of_nonneg_left (hb11 τ hτ) ht0
    have e3 : ‖Gcusp ℓ d 1 0 τ + (t:ℂ) * Complex.I * Gcusp ℓ d 1 1 τ‖ ≤ B10 + t * B11 := by
      linarith [norm_add_le (Gcusp ℓ d 1 0 τ) ((t:ℂ) * Complex.I * Gcusp ℓ d 1 1 τ),
        hb10 τ hτ, e2']
    have e4 : ‖Complex.exp (2 * Real.pi * t)‖ = Real.exp (2 * Real.pi * t) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.ofReal_re, Complex.mul_re]
    rw [Aexp]
    have hsplit := norm_add_le (Gcusp ℓ d 0 0 τ + (t:ℂ) * Complex.I * Gcusp ℓ d 0 1 τ)
      (Complex.exp (2 * Real.pi * t) * (Gcusp ℓ d 1 0 τ + (t:ℂ) * Complex.I * Gcusp ℓ d 1 1 τ))
    have hsplit2 := norm_add_le (Gcusp ℓ d 0 0 τ) ((t:ℂ) * Complex.I * Gcusp ℓ d 0 1 τ)
    have e5 : ‖Complex.exp (2 * Real.pi * t) * (Gcusp ℓ d 1 0 τ + (t:ℂ) * Complex.I * Gcusp ℓ d 1 1 τ)‖
        = Real.exp (2 * Real.pi * t) * ‖Gcusp ℓ d 1 0 τ + (t:ℂ) * Complex.I * Gcusp ℓ d 1 1 τ‖ := by
      rw [norm_mul, e4]
    have h1 : ‖Gcusp ℓ d 0 0 τ + (t:ℂ) * Complex.I * Gcusp ℓ d 0 1 τ‖ ≤ B00 + t * B01 := by
      linarith [hsplit2, hb00 τ hτ, e2]
    have h2 : Real.exp (2 * Real.pi * t) * ‖Gcusp ℓ d 1 0 τ + (t:ℂ) * Complex.I * Gcusp ℓ d 1 1 τ‖
        ≤ Real.exp (2 * Real.pi * lowT) * (B10 + lowT * B11) := by
      have h8 : ‖Gcusp ℓ d 1 0 τ + (t:ℂ) * Complex.I * Gcusp ℓ d 1 1 τ‖ ≤ B10 + lowT * B11 := by
        have h9 : t * B11 ≤ lowT * B11 := mul_le_mul_of_nonneg_right htT hB11
        linarith [e3, h9]
      exact mul_le_mul hexp h8 (norm_nonneg _) (Real.exp_nonneg _)
    have h10 : t * B01 ≤ lowT * B01 := mul_le_mul_of_nonneg_right htT hB01
    rw [e5] at hsplit
    linarith [hsplit, h1, h2, h10]


/-! ## Smoothness of the low and tail pieces -/

lemma lowRho_pos : (0:ℝ) < lowRho := by rw [lowRho]; norm_num

lemma off_win_gives_sep {τ : ℍ} {t : ℝ} (ht : t ∉ lowWin τ) : lowRho ≤ |t - τ.im| := by
  have hρ := lowRho_pos
  rw [lowWin, Set.mem_Ioo, not_and_or, not_lt, not_lt] at ht
  rcases ht with h | h
  · have h1 : t ≤ τ.im := by linarith
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · have h1 : τ.im ≤ t := by linarith
    rw [abs_of_nonneg (by linarith)]
    linarith

/-! ## The spike window sits in `(3/8, 17/8)` and hence in `(0,∞)` -/

lemma win_bound {τ : ℍ} (hτ : lowBadSet τ) {t : ℝ} (ht : t ∈ lowWin τ) :
    3 / 8 < t ∧ t < 17 / 8 := by
  rw [lowWin, Set.mem_Ioo] at ht
  have hρ : lowRho = 1 / 8 := rfl
  constructor
  · have h1 : τ.im - lowRho < t := ht.1
    rw [hρ] at h1
    linarith [hτ.2.1]
  · have h2 : t < τ.im + lowRho := ht.2
    rw [hρ] at h2
    linarith [hτ.2.2.1]

lemma lowWin_subset_Ioi {τ : ℍ} (hτ : lowBadSet τ) : lowWin τ ⊆ Set.Ioi (0 : ℝ) :=
  fun t ht => lt_trans (by norm_num) (win_bound hτ ht).1

end Work.HFN.HalfFunnel
