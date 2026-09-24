import Mathlib
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.window_integral_Bsum
import Submission.Work.GM.Affine.finset_sum_window_le_WinMass
import Submission.Work.GM.Affine.region_I_bound
import Submission.Work.GM.Affine.psi1hat_decay
import Submission.Work.GM.Affine.tsum_resonance_eq_finsum
import Submission.Work.GM.Affine.supf_le_of_decay
import Submission.Work.GM.Affine.region_II_resonant_low

/-!
# GM §9, region II, the resonant *low* part, third scale relaxed to `C₃ Mbig`

This file proves `Work.GM.Affine.region_II_resonant_low_C3`: the region-II low-part bound of
GM Lemma 9.2 with the third scale hypothesis relaxed from `M₃ ≤ Mbig` to `M₃ ≤ C₃ Mbig`
(`C₃ ≥ 1`).  The argument is exactly the one of `region_II_resonant_low` (whose
development is reproduced below, since the auxiliary lemmas there are file-local `private`):
Cauchy–Schwarz over `m₁ ∈ R1 M₁` with weights `1/|m₁|`, the resonance sum reducing to at most
`15` terms on the low region, and `window_integral_Bsum` to compute the `ξ`-integral of the
resulting majorant.

The only place where the hypothesis `M₃ ≤ Mbig` is used is the bound `M₃ ≤ D := 4^{4/η}`,
valid because the low region is non-empty only for `T^η < 4`, i.e. `T⁴ ≤ D`, and then
`Mbig ≤ T⁴ ≤ D`.  With the relaxed hypothesis one gets
`M₃ ≤ C₃ Mbig ≤ C₃ D` and the constant is multiplied by
`((4 C₃ D + 1)/(4 D + 1))²` accordingly.
-/


open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.GM.Affine

noncomputable section

/-! ## The resonance windows and the majorant -/

/-- The resonance window of the pair `(m₁,ℓ)`: `|ξ - m₁ℓ| ≤ 2|m₁|/M₃`. -/
private def resWin (M₃ : ℝ) (m₁ ℓ : ℤ) : Set ℝ :=
  Set.Icc ((m₁ : ℝ) * (ℓ : ℝ) - 2 * |(m₁ : ℝ)| / M₃)
    ((m₁ : ℝ) * (ℓ : ℝ) + 2 * |(m₁ : ℝ)| / M₃)

/-- The window mass `W_ℓ = ∫_{[-2,2]} ‖Hfun f M₂ M₃ ℓ τ‖² dτ`. -/
private def Wwin (f : ℝ → ℝ) (M₂ M₃ : ℝ) (ℓ : ℤ) : ℝ :=
  ∫ τ in Set.Icc (-2 : ℝ) 2, ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2

/-- The Cauchy–Schwarz majorant of `‖ghatRes ξ‖²` in the low region. -/
private def resMaj (M₁ M₂ M₃ V : ℝ) (f : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  ∑ m₁ ∈ R1 M₁, ∑ ℓ ∈ Finset.Icc (-7 : ℤ) 7,
    (1 / |(m₁ : ℝ)|) * M₃ ^ 2 * V ^ 2 *
      ((resWin M₃ m₁ ℓ).indicator (fun ξ => ‖Bsum f M₂ (ξ / (m₁ : ℝ))‖ ^ 2) ξ)

/-! ## Elementary bounds -/

/-- `Bsum f M₂` is continuous for continuous `f` with compact support. -/
private lemma continuous_Bsum_low {M₂ : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    (hcs : HasCompactSupport f) : Continuous (fun u => Bsum f M₂ u) := by
  unfold Bsum
  refine continuous_finsetSum _ (fun m₂ _ => ?_)
  exact Continuous.mul continuous_const
    ((continuous_fhat hf hcs).comp (continuous_const.mul continuous_id))

/-- The trivial `L¹` bound for the Fourier transform. -/
private lemma norm_Fhat_le_integral_low (f : ℝ → ℝ) (y : ℝ) :
    ‖Fhat f y‖ ≤ ∫ u, ‖f u‖ := by
  rw [Fhat, Real.fourier_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
  simp

/-- A uniform bound for `‖Bsum f M₂‖`. -/
private lemma norm_Bsum_le_sum_low (M₂ u : ℝ) (f : ℝ → ℝ) :
    ‖Bsum f M₂ u‖ ≤ (∑ m₂ ∈ R2 M₂, (m₂ : ℝ)) * (∫ v, ‖f v‖) := by
  rw [Bsum]
  calc ‖∑ m₂ ∈ R2 M₂, ((m₂ : ℝ) : ℂ) * Fhat f ((m₂ : ℝ) * u)‖
      ≤ ∑ m₂ ∈ R2 M₂, ‖((m₂ : ℝ) : ℂ) * Fhat f ((m₂ : ℝ) * u)‖ := norm_sum_le _ _
    _ = ∑ m₂ ∈ R2 M₂, (m₂ : ℝ) * ‖Fhat f ((m₂ : ℝ) * u)‖ := by
        refine Finset.sum_congr rfl (fun m₂ hm₂ => ?_)
        have hm1 : (1 : ℤ) ≤ m₂ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm₂).1).1
        have hm1R : (1 : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast hm1
        rw [norm_mul, show ‖((m₂ : ℝ) : ℂ)‖ = |(m₂ : ℝ)| from by simp,
          abs_of_nonneg (by linarith)]
    _ ≤ ∑ m₂ ∈ R2 M₂, (m₂ : ℝ) * (∫ v, ‖f v‖) :=
        Finset.sum_le_sum (fun m₂ hm₂ => by
          have hm1 : (1 : ℤ) ≤ m₂ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm₂).1).1
          have hm1R : (1 : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast hm1
          exact mul_le_mul_of_nonneg_left (norm_Fhat_le_integral_low f _) (by linarith))
    _ = (∑ m₂ ∈ R2 M₂, (m₂ : ℝ)) * (∫ v, ‖f v‖) := by rw [Finset.sum_mul]

/-- Membership in a resonance window. -/
private lemma mem_resWin_iff_low {M₃ : ℝ} (hM₃ : 0 < M₃) {m₁ : ℤ} (hm : (m₁ : ℝ) ≠ 0)
    (ℓ : ℤ) (ξ : ℝ) :
    ξ ∈ resWin M₃ m₁ ℓ ↔ |(ℓ : ℝ) - ξ / (m₁ : ℝ)| ≤ 2 / M₃ := by
  have hmpos : 0 < |(m₁ : ℝ)| := abs_pos.mpr hm
  have h0 : (m₁ : ℝ) * (ξ / (m₁ : ℝ)) = ξ := by
    field_simp
  have h1 : (m₁ : ℝ) * ((ℓ : ℝ) - ξ / (m₁ : ℝ)) = (m₁ : ℝ) * (ℓ : ℝ) - ξ := by
    rw [mul_sub, h0]
  have hiff : ((m₁ : ℝ) * (ℓ : ℝ) - 2 * |(m₁ : ℝ)| / M₃ ≤ ξ ∧
        ξ ≤ (m₁ : ℝ) * (ℓ : ℝ) + 2 * |(m₁ : ℝ)| / M₃) ↔
      |ξ - (m₁ : ℝ) * (ℓ : ℝ)| ≤ 2 * |(m₁ : ℝ)| / M₃ := by
    rw [abs_le]
    constructor
    · intro h; exact ⟨by linarith [h.2], by linarith [h.1]⟩
    · intro h; exact ⟨by linarith [h.2], by linarith [h.1]⟩
  have habs : |ξ - (m₁ : ℝ) * (ℓ : ℝ)| = |(m₁ : ℝ)| * |(ℓ : ℝ) - ξ / (m₁ : ℝ)| := by
    rw [abs_sub_comm ξ ((m₁ : ℝ) * (ℓ : ℝ)), ← abs_mul, h1, abs_sub_comm]
  have h2 : 2 * |(m₁ : ℝ)| / M₃ = |(m₁ : ℝ)| * (2 / M₃) := by ring
  rw [resWin, Set.mem_Icc, hiff, habs, h2, mul_le_mul_iff_of_pos_left hmpos]

/-- The resWin-indicator of `g` equals `g` times the "abs" indicator. -/
private lemma indicator_eq_abs {M₃ : ℝ} (hM₃ : 0 < M₃) {m₁ : ℤ} (hm : (m₁ : ℝ) ≠ 0)
    (g : ℝ → ℝ) (ℓ : ℤ) (ξ : ℝ) :
    (resWin M₃ m₁ ℓ).indicator g ξ
      = g ξ * (if |(ℓ : ℝ) - ξ / (m₁ : ℝ)| ≤ 2 / M₃ then (1 : ℝ) else 0) := by
  by_cases h : ξ ∈ resWin M₃ m₁ ℓ
  · rw [Set.indicator_of_mem h, if_pos ((mem_resWin_iff_low hM₃ hm ℓ ξ).mp h), mul_one]
  · rw [Set.indicator_of_notMem h,
      if_neg (fun hh => h ((mem_resWin_iff_low hM₃ hm ℓ ξ).mpr hh)), mul_zero]

/-- Weighted Cauchy–Schwarz for finite sums. -/
private lemma weighted_cauchy_schwarz {ι : Type*} (s : Finset ι) (w q : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * q i) ^ 2 ≤ (∑ i ∈ s, w i) * (∑ i ∈ s, w i * q i ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => Real.sqrt (w i))
    (fun i => Real.sqrt (w i) * q i)
  have e1 : ∑ i ∈ s, Real.sqrt (w i) * (Real.sqrt (w i) * q i) = ∑ i ∈ s, w i * q i := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [← mul_assoc, Real.mul_self_sqrt (hw i hi)]
  have e2 : ∑ i ∈ s, (Real.sqrt (w i)) ^ 2 = ∑ i ∈ s, w i :=
    Finset.sum_congr rfl (fun i hi => Real.sq_sqrt (hw i hi))
  have e3 : ∑ i ∈ s, (Real.sqrt (w i) * q i) ^ 2 = ∑ i ∈ s, w i * q i ^ 2 := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [mul_pow, Real.sq_sqrt (hw i hi)]
  rwa [e1, e2, e3] at h

/-- The number of indices `ℓ ∈ [-7,7]` with `|ℓ - x| ≤ 2/M₃` is at most `15`. -/
private lemma sum_window_indicator_le (x : ℝ) {M₃ : ℝ} :
    (∑ ℓ ∈ Finset.Icc (-7 : ℤ) 7,
        (if |(ℓ : ℝ) - x| ≤ 2 / M₃ then (1 : ℝ) else 0)) ≤ 15 := by
  have hcard : (Finset.Icc (-7 : ℤ) 7).card = 15 := by
    rw [Int.card_Icc]; norm_num; try decide
  calc (∑ ℓ ∈ Finset.Icc (-7 : ℤ) 7,
        (if |(ℓ : ℝ) - x| ≤ 2 / M₃ then (1 : ℝ) else 0))
      ≤ ∑ _ℓ ∈ Finset.Icc (-7 : ℤ) 7, (1 : ℝ) :=
        Finset.sum_le_sum (fun ℓ _ => by split_ifs <;> norm_num)
    _ = 15 := by rw [Finset.sum_const, hcard]; norm_num

/-- With `|x| ≤ 5`, the resonance sum has all its non-zero terms in `[-7,7]`, so it is bounded
by `V` times the number of those terms. -/
private lemma norm_resonance_tsum_low {K M₃ V : ℝ} (hM₃ : 1 ≤ M₃)
    (hV : ∀ y : ℝ, ‖psi1hat K y‖ ≤ V) {x : ℝ} (hx : |x| ≤ 5) :
    ‖∑' ℓ : ℤ,
        (if |(ℓ : ℝ) - x| ≤ 2 / M₃ then psi1hat K (M₃ * ((ℓ : ℝ) - x)) else 0)‖
      ≤ V * (∑ ℓ ∈ Finset.Icc (-7 : ℤ) 7,
          (if |(ℓ : ℝ) - x| ≤ 2 / M₃ then (1 : ℝ) else 0)) := by
  have hVnn : 0 ≤ V := le_trans (norm_nonneg _) (hV 0)
  have hx' : |x| ≤ ((7 : ℤ) : ℝ) - 2 := by
    have h7 : ((7 : ℤ) : ℝ) - 2 = 5 := by norm_num
    rw [h7]; exact hx
  rw [tsum_resonance_eq_finsum (K := K) (M₃ := M₃) (x := x) (L := 7) hM₃ hx']
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun ℓ _ => ?_)
  by_cases h : |(ℓ : ℝ) - x| ≤ 2 / M₃
  · rw [if_pos h, if_pos h, mul_one]
    exact hV _
  · rw [if_neg h, if_neg h, norm_zero, mul_zero]

/-! ## The pointwise estimate -/

/-- **Pointwise Cauchy–Schwarz bound in the low region.**  For `|ξ| ≤ 4M₁/M₃`,
`‖ghatRes ξ‖² ≤ 120 · resMaj ξ`.  The factor `120 = 8 · 15` is
`Σ_{m₁∈R1}1/|m₁| ≤ 8` (`sum_inv_abs_R1_le`) times the maximal number `15` of resonance windows. -/
private lemma ghatRes_sq_le_resMaj {K M₁ M₂ M₃ V : ℝ} (hM₃ : 1 ≤ M₃) (hM₁ : 0 < M₁)
    (hV : ∀ y : ℝ, ‖psi1hat K y‖ ≤ V) {f : ℝ → ℝ} {ξ : ℝ}
    (hξ : |ξ| ≤ 4 * M₁ / M₃) :
    ‖ghatRes K M₁ M₂ M₃ f ξ‖ ^ 2 ≤ 120 * resMaj M₁ M₂ M₃ V f ξ := by
  have hM₃pos : 0 < M₃ := lt_of_lt_of_le zero_lt_one hM₃
  have hVnn : 0 ≤ V := le_trans (norm_nonneg _) (hV 0)
  set Nf : ℤ → ℝ := fun m₁ => ∑ ℓ ∈ Finset.Icc (-7 : ℤ) 7,
      (if |(ℓ : ℝ) - ξ / (m₁ : ℝ)| ≤ 2 / M₃ then (1 : ℝ) else 0) with hNf
  set w : ℤ → ℝ := fun m₁ => (1 / |(m₁ : ℝ)|) * Nf m₁ with hw
  set q : ℤ → ℝ := fun m₁ => ‖Bsum f M₂ (ξ / (m₁ : ℝ))‖ * M₃ * V with hq
  have hw_nn : ∀ m₁ ∈ R1 M₁, 0 ≤ w m₁ := by
    intro m₁ _
    simp only [hw, hNf]
    refine mul_nonneg (by positivity) ?_
    exact Finset.sum_nonneg (fun ℓ _ => by split_ifs <;> norm_num)
  -- (a) the raw norm bound
  have hraw : ‖ghatRes K M₁ M₂ M₃ f ξ‖ ≤ ∑ m₁ ∈ R1 M₁, w m₁ * q m₁ := by
    rw [ghatRes]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun m₁ hm₁ => ?_))
    have hlt : M₁ < |(m₁ : ℝ)| := (Finset.mem_filter.mp hm₁).2
    have hm₁ne : (m₁ : ℝ) ≠ 0 := by
      intro h0; rw [h0] at hlt; simp at hlt; linarith
    have hm₁pos : 0 < |(m₁ : ℝ)| := abs_pos.mpr hm₁ne
    have hx5 : |ξ / (m₁ : ℝ)| ≤ 5 := by
      rw [abs_div]
      have h1 : |ξ| / |(m₁ : ℝ)| ≤ 4 / M₃ := by
        rw [div_le_iff₀ hm₁pos]
        rw [show 4 / M₃ * |(m₁ : ℝ)| = 4 * |(m₁ : ℝ)| / M₃ from by ring]
        exact le_trans hξ (div_le_div_of_nonneg_right (by linarith) hM₃pos.le)
      have h2 : (4 : ℝ) / M₃ ≤ 5 := by
        rw [div_le_iff₀ hM₃pos]; linarith
      linarith
    have hinner := norm_resonance_tsum_low hM₃ hV hx5
    have hnorm1 : ‖((( |(m₁ : ℝ)| : ℝ) : ℂ))⁻¹‖ = 1 / |(m₁ : ℝ)| := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _),
        inv_eq_one_div]
    have hnorm2 : ‖(((M₃ : ℝ)) : ℂ)‖ = M₃ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM₃pos]
    have hterm : ‖((( |(m₁ : ℝ)| : ℝ) : ℂ))⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
        ((M₃ : ℂ) * ∑' ℓ : ℤ,
          (if |(ℓ : ℝ) - ξ / (m₁ : ℝ)| ≤ 2 / M₃ then
            psi1hat K (M₃ * ((ℓ : ℝ) - ξ / (m₁ : ℝ))) else 0))‖
        ≤ (1 / |(m₁ : ℝ)|) * ‖Bsum f M₂ (ξ / (m₁ : ℝ))‖ * (M₃ * (V * Nf m₁)) := by
      simp only [norm_mul, hnorm1, hnorm2]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinner hM₃pos.le)
        (by positivity)
    calc ‖(((|(m₁ : ℝ)| : ℝ) : ℂ))⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
          ((M₃ : ℂ) * ∑' ℓ : ℤ,
            (if |(ℓ : ℝ) - ξ / (m₁ : ℝ)| ≤ 2 / M₃ then
              psi1hat K (M₃ * ((ℓ : ℝ) - ξ / (m₁ : ℝ))) else 0))‖
        ≤ (1 / |(m₁ : ℝ)|) * ‖Bsum f M₂ (ξ / (m₁ : ℝ))‖ * (M₃ * (V * Nf m₁)) := hterm
      _ = w m₁ * q m₁ := by
          simp only [hw, hq]
          ring
  -- (b) Cauchy–Schwarz and the two sums
  have hCS : (∑ m₁ ∈ R1 M₁, w m₁ * q m₁) ^ 2 ≤
      (∑ m₁ ∈ R1 M₁, w m₁) * (∑ m₁ ∈ R1 M₁, w m₁ * q m₁ ^ 2) :=
    weighted_cauchy_schwarz _ _ _ hw_nn
  have hwsum : ∑ m₁ ∈ R1 M₁, w m₁ ≤ 120 := by
    have h1 : ∀ m₁ ∈ R1 M₁, w m₁ ≤ (1 / |(m₁ : ℝ)|) * 15 := by
      intro m₁ _
      simp only [hw, hNf]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact sum_window_indicator_le _ (M₃ := M₃)
    calc ∑ m₁ ∈ R1 M₁, w m₁ ≤ ∑ m₁ ∈ R1 M₁, (1 / |(m₁ : ℝ)|) * 15 := Finset.sum_le_sum h1
      _ = (∑ m₁ ∈ R1 M₁, (1 / |(m₁ : ℝ)|)) * 15 := by rw [Finset.sum_mul]
      _ ≤ 8 * 15 := mul_le_mul_of_nonneg_right (sum_inv_abs_R1_le M₁ hM₁) (by norm_num)
      _ = 120 := by norm_num
  have hqsum : ∑ m₁ ∈ R1 M₁, w m₁ * q m₁ ^ 2 = resMaj M₁ M₂ M₃ V f ξ := by
    have hterm : ∀ m₁ ∈ R1 M₁, w m₁ * q m₁ ^ 2
        = ∑ ℓ ∈ Finset.Icc (-7 : ℤ) 7, (1 / |(m₁ : ℝ)|) * M₃ ^ 2 * V ^ 2 *
            ((resWin M₃ m₁ ℓ).indicator (fun ξ => ‖Bsum f M₂ (ξ / (m₁ : ℝ))‖ ^ 2) ξ) := by
      intro m₁ hm₁
      have hlt : M₁ < |(m₁ : ℝ)| := (Finset.mem_filter.mp hm₁).2
      have hm₁ne : (m₁ : ℝ) ≠ 0 := by
        intro h0; rw [h0] at hlt; simp at hlt; linarith
      have hNfm : Nf m₁ = ∑ ℓ ∈ Finset.Icc (-7 : ℤ) 7,
          (if |(ℓ : ℝ) - ξ / (m₁ : ℝ)| ≤ 2 / M₃ then (1 : ℝ) else 0) := by simp only [hNf]
      have hwm : w m₁ = (1 / |(m₁ : ℝ)|) * Nf m₁ := by simp only [hw]
      have hqm : q m₁ = ‖Bsum f M₂ (ξ / (m₁ : ℝ))‖ * M₃ * V := by simp only [hq]
      have hsum_eq : (∑ ℓ ∈ Finset.Icc (-7 : ℤ) 7,
            (resWin M₃ m₁ ℓ).indicator (fun ξ => ‖Bsum f M₂ (ξ / (m₁ : ℝ))‖ ^ 2) ξ)
          = ‖Bsum f M₂ (ξ / (m₁ : ℝ))‖ ^ 2 * Nf m₁ := by
        rw [hNfm, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun ℓ _ => indicator_eq_abs hM₃pos hm₁ne
          (fun ξ => ‖Bsum f M₂ (ξ / (m₁ : ℝ))‖ ^ 2) ℓ ξ)
      rw [hwm, hqm, hNfm, ← Finset.mul_sum, hsum_eq]
      ring
    rw [Finset.sum_congr rfl hterm]
    simp only [resMaj]
  calc ‖ghatRes K M₁ M₂ M₃ f ξ‖ ^ 2
      ≤ (∑ m₁ ∈ R1 M₁, w m₁ * q m₁) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hraw 2
    _ ≤ (∑ m₁ ∈ R1 M₁, w m₁) * (∑ m₁ ∈ R1 M₁, w m₁ * q m₁ ^ 2) := hCS
    _ ≤ 120 * (∑ m₁ ∈ R1 M₁, w m₁ * q m₁ ^ 2) := by
        refine mul_le_mul_of_nonneg_right hwsum ?_
        exact Finset.sum_nonneg (fun m₁ hm₁ => mul_nonneg (hw_nn m₁ hm₁) (sq_nonneg _))
    _ = 120 * resMaj M₁ M₂ M₃ V f ξ := by rw [hqsum]

/-! ## Integrability of the majorant -/

private lemma integrableOn_resMaj {M₁ M₂ M₃ V : ℝ} (hVnn : 0 ≤ V) {f : ℝ → ℝ}
    (hf : Continuous f) (hcs : HasCompactSupport f) (S : Set ℝ) (hS : volume S < ⊤) :
    IntegrableOn (fun ξ => resMaj M₁ M₂ M₃ V f ξ) S := by
  set Bb : ℝ := (∑ m₂ ∈ R2 M₂, (m₂ : ℝ)) * (∫ v, ‖f v‖) with hBb
  have hBbnn : 0 ≤ Bb := by
    rw [hBb]
    refine mul_nonneg (Finset.sum_nonneg (fun m₂ hm₂ => ?_)) (by positivity)
    have h1 : (1 : ℤ) ≤ m₂ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm₂).1).1
    have := (by exact_mod_cast h1 : (1 : ℝ) ≤ (m₂ : ℝ))
    linarith
  have hmeas : Measurable (fun ξ => resMaj M₁ M₂ M₃ V f ξ) := by
    simp only [resMaj]
    refine measurable_sum _ (fun m₁ _ => measurable_sum _ (fun ℓ _ => ?_))
    refine Measurable.const_mul ?_ ((1 / |(m₁ : ℝ)|) * M₃ ^ 2 * V ^ 2)
    refine Measurable.indicator ?_ measurableSet_Icc
    exact (((continuous_Bsum_low hf hcs).comp
      (continuous_id.div_const (m₁ : ℝ))).norm.pow 2).measurable
  have hbound : ∀ ξ : ℝ, ‖resMaj M₁ M₂ M₃ V f ξ‖
      ≤ ∑ m₁ ∈ R1 M₁, ∑ _ℓ ∈ Finset.Icc (-7 : ℤ) 7,
          (1 / |(m₁ : ℝ)|) * M₃ ^ 2 * V ^ 2 * Bb ^ 2 := by
    intro ξ
    have hnn : 0 ≤ resMaj M₁ M₂ M₃ V f ξ := by
      simp only [resMaj]
      refine Finset.sum_nonneg (fun m₁ _ => Finset.sum_nonneg (fun ℓ _ => ?_))
      refine mul_nonneg (by positivity) ?_
      by_cases hc : ξ ∈ resWin M₃ m₁ ℓ
      · rw [Set.indicator_of_mem hc]; exact sq_nonneg _
      · rw [Set.indicator_of_notMem hc]
    rw [Real.norm_of_nonneg hnn]
    simp only [resMaj]
    refine Finset.sum_le_sum (fun m₁ _ => Finset.sum_le_sum (fun ℓ _ => ?_))
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    by_cases hc : ξ ∈ resWin M₃ m₁ ℓ
    · rw [Set.indicator_of_mem hc]
      simpa only [hBb] using
        pow_le_pow_left₀ (norm_nonneg _) (norm_Bsum_le_sum_low M₂ (ξ / (m₁ : ℝ)) f) 2
    · rw [Set.indicator_of_notMem hc]
      positivity
  exact MeasureTheory.IntegrableOn.of_bound hS hmeas.aestronglyMeasurable _
    (Filter.Eventually.of_forall hbound)

/-! ## The integral of the majorant -/

/-- **The window-by-window estimate for the majorant.** -/
private lemma setIntegral_resMaj_le {T Λ : ℝ} (hT : 1 ≤ T) {M₁ M₂ M₃ V : ℝ} (hM₁ : 0 < M₁)
    (hM₂ : 0 < M₂) (hM₃ : 1 ≤ M₃) {c : ℕ → ℝ → ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    (hcs : HasCompactSupport f)
    (hdec : ∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
        ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ)
    (S : Set ℝ) (hSfin : volume S < ⊤) :
    ∫ ξ in S, resMaj M₁ M₂ M₃ V f ξ ≤ (R1 M₁).card * M₃ * V ^ 2 * WinMass f M₂ M₃ := by
  have hM₃pos : 0 < M₃ := lt_of_lt_of_le zero_lt_one hM₃
  set Bb : ℝ := (∑ m₂ ∈ R2 M₂, (m₂ : ℝ)) * (∫ v, ‖f v‖) with hBb
  have hBbnn : 0 ≤ Bb := by
    rw [hBb]
    refine mul_nonneg (Finset.sum_nonneg (fun m₂ hm₂ => ?_)) (by positivity)
    have h1 : (1 : ℤ) ≤ m₂ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm₂).1).1
    have := (by exact_mod_cast h1 : (1 : ℝ) ≤ (m₂ : ℝ))
    linarith
  have hInt : ∀ m₁ ∈ R1 M₁, ∀ ℓ ∈ Finset.Icc (-7 : ℤ) 7,
      IntegrableOn (fun ξ : ℝ => ((1 / |(m₁ : ℝ)|) * M₃ ^ 2 * V ^ 2) *
        ((resWin M₃ m₁ ℓ).indicator (fun ξ => ‖Bsum f M₂ (ξ / (m₁ : ℝ))‖ ^ 2) ξ)) S := by
    intro m₁ _ ℓ _
    have hcont : Continuous (fun ξ : ℝ => ‖Bsum f M₂ (ξ / (m₁ : ℝ))‖ ^ 2) :=
      (((continuous_Bsum_low hf hcs).comp (continuous_id.div_const (m₁ : ℝ))).norm.pow 2)
    have hbase : IntegrableOn
        ((resWin M₃ m₁ ℓ).indicator (fun ξ => ‖Bsum f M₂ (ξ / (m₁ : ℝ))‖ ^ 2)) S := by
      refine MeasureTheory.IntegrableOn.of_bound hSfin ?_ (Bb ^ 2) ?_
      · exact (hcont.measurable.indicator measurableSet_Icc).aestronglyMeasurable
      · refine Filter.Eventually.of_forall (fun ξ => ?_)
        by_cases hc : ξ ∈ resWin M₃ m₁ ℓ
        · rw [Set.indicator_of_mem hc, Real.norm_of_nonneg (sq_nonneg _)]
          simpa only [hBb] using
            pow_le_pow_left₀ (norm_nonneg _) (norm_Bsum_le_sum_low M₂ (ξ / (m₁ : ℝ)) f) 2
        · rw [Set.indicator_of_notMem hc, norm_zero]; positivity
    exact MeasureTheory.Integrable.const_mul hbase _
  have h1 : ∫ ξ in S, resMaj M₁ M₂ M₃ V f ξ
      = ∑ m₁ ∈ R1 M₁, ∑ ℓ ∈ Finset.Icc (-7 : ℤ) 7,
          ∫ ξ in S, ((1 / |(m₁ : ℝ)|) * M₃ ^ 2 * V ^ 2) *
            ((resWin M₃ m₁ ℓ).indicator (fun ξ => ‖Bsum f M₂ (ξ / (m₁ : ℝ))‖ ^ 2) ξ) := by
    simp only [resMaj]
    rw [MeasureTheory.integral_finsetSum (R1 M₁) (fun m₁ hm₁ =>
      MeasureTheory.integrable_finsetSum _ (fun ℓ hℓ => hInt m₁ hm₁ ℓ hℓ))]
    refine Finset.sum_congr rfl (fun m₁ hm₁ => ?_)
    rw [MeasureTheory.integral_finsetSum (Finset.Icc (-7 : ℤ) 7)
      (fun ℓ hℓ => hInt m₁ hm₁ ℓ hℓ)]
  have h2 : ∀ m₁ ∈ R1 M₁, ∀ ℓ ∈ Finset.Icc (-7 : ℤ) 7,
      ∫ ξ in S, ((1 / |(m₁ : ℝ)|) * M₃ ^ 2 * V ^ 2) *
            ((resWin M₃ m₁ ℓ).indicator (fun ξ => ‖Bsum f M₂ (ξ / (m₁ : ℝ))‖ ^ 2) ξ)
        ≤ M₃ * V ^ 2 * Wwin f M₂ M₃ ℓ := by
    intro m₁ hm₁ ℓ _
    have hlt : M₁ < |(m₁ : ℝ)| := (Finset.mem_filter.mp hm₁).2
    have hm₁ne : (m₁ : ℝ) ≠ 0 := by
      intro h0; rw [h0] at hlt; simp at hlt; linarith
    have hm₁ℤ : m₁ ≠ 0 := fun h0 => hm₁ne (by rw [h0]; norm_num)
    have hmono : ∫ ξ in S ∩ resWin M₃ m₁ ℓ, ‖Bsum f M₂ (ξ / (m₁ : ℝ))‖ ^ 2
        ≤ ∫ ξ in resWin M₃ m₁ ℓ, ‖Bsum f M₂ (ξ / (m₁ : ℝ))‖ ^ 2 := by
      refine MeasureTheory.setIntegral_mono_set ?_ ?_ ?_
      · exact ((((continuous_Bsum_low hf hcs).comp
          (continuous_id.div_const (m₁ : ℝ))).norm.pow 2)).integrableOn_Icc
      · exact Filter.Eventually.of_forall (fun x => sq_nonneg _)
      · rw [MeasureTheory.ae_le_set, Set.diff_eq_empty.mpr Set.inter_subset_right,
          measure_empty]
    have hwin : ∫ ξ in resWin M₃ m₁ ℓ, ‖Bsum f M₂ (ξ / (m₁ : ℝ))‖ ^ 2
        = (|(m₁ : ℝ)| / M₃) * Wwin f M₂ M₃ ℓ :=
      window_integral_Bsum hM₃pos f ℓ hm₁ℤ
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.setIntegral_indicator (t := resWin M₃ m₁ ℓ) measurableSet_Icc]
    calc ((1 / |(m₁ : ℝ)|) * M₃ ^ 2 * V ^ 2) *
          (∫ ξ in S ∩ resWin M₃ m₁ ℓ, ‖Bsum f M₂ (ξ / (m₁ : ℝ))‖ ^ 2)
        ≤ ((1 / |(m₁ : ℝ)|) * M₃ ^ 2 * V ^ 2) *
          (∫ ξ in resWin M₃ m₁ ℓ, ‖Bsum f M₂ (ξ / (m₁ : ℝ))‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = ((1 / |(m₁ : ℝ)|) * M₃ ^ 2 * V ^ 2) * ((|(m₁ : ℝ)| / M₃) * Wwin f M₂ M₃ ℓ) := by
          rw [hwin]
      _ = M₃ * V ^ 2 * Wwin f M₂ M₃ ℓ := by
          field_simp
  have h3 : ∑ m₁ ∈ R1 M₁, ∑ ℓ ∈ Finset.Icc (-7 : ℤ) 7, M₃ * V ^ 2 * Wwin f M₂ M₃ ℓ
      = (R1 M₁).card * (M₃ * V ^ 2 * ∑ ℓ ∈ Finset.Icc (-7 : ℤ) 7, Wwin f M₂ M₃ ℓ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    congr 1
    rw [Finset.mul_sum]
  have h4 : ∑ ℓ ∈ Finset.Icc (-7 : ℤ) 7, Wwin f M₂ M₃ ℓ ≤ WinMass f M₂ M₃ := by
    have := finset_sum_window_le_WinMass (c := c) (T := T) (Λ := Λ) hT hM₂ hM₃ hf hdec
      (Finset.Icc (-7 : ℤ) 7)
    simpa only [Wwin, WinMass] using this
  calc ∫ ξ in S, resMaj M₁ M₂ M₃ V f ξ
      = ∑ m₁ ∈ R1 M₁, ∑ ℓ ∈ Finset.Icc (-7 : ℤ) 7,
          ∫ ξ in S, ((1 / |(m₁ : ℝ)|) * M₃ ^ 2 * V ^ 2) *
            ((resWin M₃ m₁ ℓ).indicator (fun ξ => ‖Bsum f M₂ (ξ / (m₁ : ℝ))‖ ^ 2) ξ) := h1
    _ ≤ ∑ m₁ ∈ R1 M₁, ∑ ℓ ∈ Finset.Icc (-7 : ℤ) 7, M₃ * V ^ 2 * Wwin f M₂ M₃ ℓ :=
        Finset.sum_le_sum (fun m₁ hm₁ => Finset.sum_le_sum (fun ℓ hℓ => h2 m₁ hm₁ ℓ hℓ))
    _ = (R1 M₁).card * (M₃ * V ^ 2 * ∑ ℓ ∈ Finset.Icc (-7 : ℤ) 7, Wwin f M₂ M₃ ℓ) := h3
    _ ≤ (R1 M₁).card * (M₃ * V ^ 2 * WinMass f M₂ M₃) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = (R1 M₁).card * M₃ * V ^ 2 * WinMass f M₂ M₃ := by ring

/-! ## Arithmetic -/

/-- `T⁴ ≤ 4^{4/η}` when `T^{η} < 4` and `T ≥ 1`. -/
private lemma pow_four_le_of_rpow_lt {η : ℝ} (hη : 0 < η) {T : ℝ} (hT : 1 ≤ T)
    (h : T ^ η < 4) : T ^ 4 ≤ (4 : ℝ) ^ (4 / η) := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  calc T ^ 4 = T ^ (4 : ℝ) := (Real.rpow_natCast T 4).symm
    _ = (T ^ η) ^ (4 / η) := by
        rw [← Real.rpow_mul hTpos.le η (4 / η)]
        congr 1
        field_simp
    _ ≤ (4 : ℝ) ^ (4 / η) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hTpos.le η) h.le (by positivity)

/-- The factor `|R1 M₁| · M₃` is bounded by `120(4D+1)²(M₁+M₃)` when `M₁, M₃ ≤ D` and `M₃ ≥ 1`. -/
private lemma card_mul_M₃_le {M₁ M₃ D : ℝ} (hM₁ : 0 < M₁) (hM₃ : 1 ≤ M₃)
    (hM₁D : M₁ ≤ D) (hM₃D : M₃ ≤ D) :
    ((R1 M₁).card : ℝ) * M₃ ≤ 120 * (4 * D + 1) ^ 2 * (M₁ + M₃) := by
  have hD0 : 0 ≤ D := le_trans hM₁.le hM₁D
  have hcard := card_R1_le M₁ hM₁
  have h1 : ((R1 M₁).card : ℝ) * M₃ ≤ (4 * M₁ + 1) * M₃ :=
    mul_le_mul_of_nonneg_right hcard (by linarith)
  have h2 : (4 * M₁ + 1) * M₃ ≤ (4 * D + 1) * D :=
    mul_le_mul (by linarith) hM₃D (by linarith) (by linarith)
  have h3 : (4 * D + 1) * D ≤ (4 * D + 1) ^ 2 := by nlinarith [hD0]
  have h4 : (4 * D + 1) ^ 2 ≤ 120 * (4 * D + 1) ^ 2 * (M₁ + M₃) := by
    have h5 : (1 : ℝ) ≤ M₁ + M₃ := by linarith
    nlinarith [sq_nonneg (4 * D + 1)]
  linarith

/-! ## The theorem -/

/-- **Region II of GM Lemma 9.2, the low part (`T^η M₁/M₃ < |ξ| ≤ min(4M₁/M₃, T⁶)`, `η = min δ 1/2`),
with the third scale relaxed to `M₃ ≤ C₃ Mbig`.**

Same proof as `Work.GM.Affine.region_II_resonant_low`: Cauchy–Schwarz over `m₁ ∈ R1 M₁` with
weights `1/|m₁|`, the resonance sum having at most `15` terms on the low region
(`norm_resonance_tsum_low`), and `window_integral_Bsum` to integrate the majorant.  The only
change is that the scale bound `M₃ ≤ D := 4^{4/η}` becomes `M₃ ≤ C₃ D`, which multiplies the
constant by `(4 C₃ D + 1)²/(4 D + 1)²`. -/
theorem region_II_resonant_low_C3 {K : ℝ} (hK : 0 < K) (δ : ℝ) (hδ : 0 < δ) (C₃ : ℝ)
    (hC₃ : 1 ≤ C₃) (c : ℕ → ℝ → ℝ) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ (T Λ : ℝ), 1 ≤ T → 0 < Λ → ∀ (Mbig M₁ M₂ M₃ : ℝ),
        1 ≤ Mbig → 1 ≤ M₃ → 0 < M₁ → M₁ ≤ Mbig → 0 < M₂ → M₂ ≤ Mbig → M₃ ≤ C₃ * Mbig →
        Mbig ≤ T ^ 4 →
        ∀ (f : ℝ → ℝ), Continuous f → HasCompactSupport f →
        (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
          ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
        (∫ ξ in ((Set.Icc (-(T ^ 6)) (T ^ 6)) ∩ (Set.Icc (-(4 * M₁ / M₃)) (4 * M₁ / M₃)))
            \ (Set.Icc (-(T ^ (min δ 1 / 2) * M₁ / M₃)) (T ^ (min δ 1 / 2) * M₁ / M₃)),
            ‖ghatRes K M₁ M₂ M₃ f ξ‖ ^ 2) ≤
          C' * (M₁ + M₃) * WinMass f M₂ M₃ := by
  obtain ⟨V, hVpos, hV⟩ : ∃ V : ℝ, 0 < V ∧ ∀ y : ℝ, ‖psi1hat K y‖ ≤ V := by
    obtain ⟨V, hVpos, hV⟩ := psi1hat_decay K hK 0
    exact ⟨V, hVpos, fun y => by simpa using hV y⟩
  have hVnn : 0 ≤ V := le_of_lt hVpos
  set η : ℝ := (min δ 1) / 2 with hηdef
  have hηpos : 0 < η := by
    rw [hηdef]
    exact div_pos (lt_min hδ zero_lt_one) (by norm_num)
  set D : ℝ := (4 : ℝ) ^ (4 / η) with hDdef
  have hDpos : 0 < D := by
    rw [hDdef]
    exact Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨14400 * V ^ 2 * (4 * (C₃ * D) + 1) ^ 2, by positivity, ?_⟩
  intro T Λ hT hΛ Mbig M₁ M₂ M₃ hMbig hM₃ hM₁ hM₁b hM₂ hM₂b hM₃b hMb f hf hcs hdec
  set S : Set ℝ :=
    ((Set.Icc (-(T ^ 6)) (T ^ 6)) ∩ (Set.Icc (-(4 * M₁ / M₃)) (4 * M₁ / M₃)))
      \ (Set.Icc (-(T ^ (min δ 1 / 2) * M₁ / M₃)) (T ^ (min δ 1 / 2) * M₁ / M₃)) with hSdef
  have hWnn : 0 ≤ WinMass f M₂ M₃ :=
    tsum_nonneg (fun ℓ => integral_nonneg (fun x => sq_nonneg _))
  have hmain : ∫ ξ in S, ‖ghatRes K M₁ M₂ M₃ f ξ‖ ^ 2
      ≤ 14400 * V ^ 2 * (4 * (C₃ * D) + 1) ^ 2 * (M₁ + M₃) * WinMass f M₂ M₃ := by
    by_cases hcase : 4 ≤ T ^ η
    · have hSe : S = ∅ := by
        rw [hSdef, Set.eq_empty_iff_forall_notMem]
        intro ξ hξ
        obtain ⟨⟨-, hmem⟩, hout⟩ := hξ
        rw [Set.mem_Icc] at hmem hout
        apply hout
        have hM₃pos : 0 < M₃ := lt_of_lt_of_le zero_lt_one hM₃
        have ha : 4 * M₁ / M₃ ≤ T ^ η * M₁ / M₃ := by
          rw [div_le_div_iff_of_pos_right hM₃pos]
          exact mul_le_mul_of_nonneg_right hcase hM₁.le
        exact ⟨by linarith [hmem.1, ha], by linarith [hmem.2, ha]⟩
      rw [hSe, setIntegral_empty]
      exact mul_nonneg (mul_nonneg (by positivity) (by linarith)) hWnn
    · push Not at hcase
      have hT4D : T ^ 4 ≤ D := by
        rw [hDdef]
        exact pow_four_le_of_rpow_lt hηpos hT hcase
      have hMbigD : Mbig ≤ D := le_trans hMb hT4D
      have hM₁D : M₁ ≤ C₃ * D :=
        le_trans (le_trans hM₁b hMbigD) (le_mul_of_one_le_left hDpos.le hC₃)
      have hM₃D : M₃ ≤ C₃ * D :=
        le_trans hM₃b (mul_le_mul_of_nonneg_left hMbigD (by linarith))
      have hSsub : S ⊆ Set.Icc (-(T ^ 6)) (T ^ 6) := fun x hx => hx.1.1
      have hSfin : volume S < ⊤ :=
        lt_of_le_of_lt (measure_mono hSsub) isCompact_Icc.measure_lt_top
      have hpt : ∀ ξ ∈ S, ‖ghatRes K M₁ M₂ M₃ f ξ‖ ^ 2
          ≤ 120 * resMaj M₁ M₂ M₃ V f ξ := by
        intro ξ hξ
        have hξb : |ξ| ≤ 4 * M₁ / M₃ := by
          have h1 : ξ ∈ Set.Icc (-(4 * M₁ / M₃)) (4 * M₁ / M₃) := hξ.1.2
          rw [Set.mem_Icc] at h1
          exact abs_le.mpr ⟨h1.1, h1.2⟩
        exact ghatRes_sq_le_resMaj hM₃ hM₁ hV hξb
      have hInt : IntegrableOn (fun ξ => resMaj M₁ M₂ M₃ V f ξ) S :=
        integrableOn_resMaj hVnn hf hcs S hSfin
      have hstep1 : ∫ ξ in S, ‖ghatRes K M₁ M₂ M₃ f ξ‖ ^ 2
          ≤ ∫ ξ in S, 120 * resMaj M₁ M₂ M₃ V f ξ :=
        MeasureTheory.setIntegral_mono_of_nonneg (fun ξ _ => sq_nonneg _) hpt
          (MeasureTheory.Integrable.const_mul hInt 120)
      have hstep1b : ∫ ξ in S, 120 * resMaj M₁ M₂ M₃ V f ξ
          = 120 * ∫ ξ in S, resMaj M₁ M₂ M₃ V f ξ :=
        MeasureTheory.integral_const_mul 120 _
      have hstep2 : ∫ ξ in S, resMaj M₁ M₂ M₃ V f ξ
          ≤ (R1 M₁).card * M₃ * V ^ 2 * WinMass f M₂ M₃ :=
        setIntegral_resMaj_le hT hM₁ hM₂ hM₃ hf hcs hdec S hSfin
      have harith : ((R1 M₁).card : ℝ) * M₃ ≤ 120 * (4 * (C₃ * D) + 1) ^ 2 * (M₁ + M₃) :=
        card_mul_M₃_le hM₁ hM₃ hM₁D hM₃D
      calc ∫ ξ in S, ‖ghatRes K M₁ M₂ M₃ f ξ‖ ^ 2
          ≤ ∫ ξ in S, 120 * resMaj M₁ M₂ M₃ V f ξ := hstep1
        _ = 120 * ∫ ξ in S, resMaj M₁ M₂ M₃ V f ξ := hstep1b
        _ ≤ 120 * ((R1 M₁).card * M₃ * V ^ 2 * WinMass f M₂ M₃) :=
            mul_le_mul_of_nonneg_left hstep2 (by norm_num)
        _ ≤ 120 * ((120 * (4 * (C₃ * D) + 1) ^ 2 * (M₁ + M₃)) * V ^ 2
              * WinMass f M₂ M₃) := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right harith (sq_nonneg V)) hWnn
        _ = 14400 * V ^ 2 * (4 * (C₃ * D) + 1) ^ 2 * (M₁ + M₃) * WinMass f M₂ M₃ := by ring
  exact hmain

end

end Work.GM.Affine
