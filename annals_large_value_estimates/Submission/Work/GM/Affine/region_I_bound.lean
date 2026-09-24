import Mathlib
import Submission.Work.GM.Affine.fine_setup

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-!
# GM §9, region I of the fine case

This file proves `Work.GM.Affine.region_I_bound`: the (elementary) region-I estimate occurring
in the proof of GM Proposition 9.1 / Lemma 9.2.  The function `ghat` is the Fourier transform of
the "smoothed majorant" `gSum` of the affine sum.  We use the trivial pointwise estimate
`‖ghat ξ‖ ≤ ∫ gSum`, then bound `∫ gSum` by a multiple of `M₂² M₃ ∫f`; multiplying by the length
`2 T^η M₁/M₃` of the region gives the claim, the `M₁` factor cancelling against `M₃` because
`Σ_{m₁ ∈ R1} 1/|m₁|` is bounded by the absolute constant `8`.
-/

/-- `gSum` is non-negative for a non-negative test function. -/
lemma gSum_nonneg {K M₁ M₂ M₃ : ℝ} {f : ℝ → ℝ} (hf : ∀ u, 0 ≤ f u) (u : ℝ) :
    0 ≤ gSum K M₁ M₂ M₃ f u := by
  unfold gSum
  apply Finset.sum_nonneg
  intro m₁ _
  apply Finset.sum_nonneg
  intro m₂ _
  apply Finset.sum_nonneg
  intro m₃ _
  exact mul_nonneg (psi1_nonneg _ _) (hf _)

/-- The Fourier transform of the majorant `gSum` is bounded by the integral of `gSum`. -/
lemma norm_ghat_le_integral_gSum {K M₁ M₂ M₃ : ℝ} {f : ℝ → ℝ} (hfnn : ∀ u, 0 ≤ f u) (ξ : ℝ) :
    ‖ghat K M₁ M₂ M₃ f ξ‖ ≤ ∫ u, gSum K M₁ M₂ M₃ f u := by
  have h1 : ‖ghat K M₁ M₂ M₃ f ξ‖ ≤ ∫ u, ‖((gSum K M₁ M₂ M₃ f u : ℝ) : ℂ)‖ := by
    unfold ghat
    rw [Real.fourier_eq (fun u : ℝ => ((gSum K M₁ M₂ M₃ f u : ℝ) : ℂ)) ξ]
    exact VectorFourier.norm_fourierIntegral_le_integral_norm (e := 𝐞) (μ := volume)
      (L := innerₗ ℝ) (f := fun u : ℝ => ((gSum K M₁ M₂ M₃ f u : ℝ) : ℂ)) (w := ξ)
  refine h1.trans (le_of_eq ?_)
  apply integral_congr_ae
  filter_upwards with u
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (gSum_nonneg hfnn u)]

/-! ### Cardinality bounds for the summation ranges -/

lemma card_R1_le (M₁ : ℝ) (hM₁ : 0 < M₁) : ((R1 M₁).card : ℝ) ≤ 4*M₁ + 1 := by
  have h2 : (Finset.Icc (-⌊2*M₁⌋) ⌊2*M₁⌋).card = (2*⌊2*M₁⌋+1).toNat := by
    rw [Int.card_Icc]; congr 1; ring_nf
  have h1 : (R1 M₁).card ≤ (2*⌊(2:ℝ)*M₁⌋+1).toNat :=
    le_trans (Finset.card_filter_le _ _) (le_of_eq h2)
  have hb : (((2*⌊(2:ℝ)*M₁⌋+1).toNat : ℕ) : ℝ) ≤ 4*M₁+1 := by
    by_cases h : (0:ℤ) ≤ 2*⌊(2:ℝ)*M₁⌋+1
    · have hz := Int.toNat_of_nonneg h
      have hcast : (((2*⌊(2:ℝ)*M₁⌋+1).toNat : ℕ) : ℝ) = ((2*⌊(2:ℝ)*M₁⌋+1 : ℤ) : ℝ) := by
        exact_mod_cast hz
      rw [hcast]; push_cast
      linarith [Int.floor_le ((2:ℝ)*M₁)]
    · have hz := Int.toNat_of_nonpos (by omega : (2*⌊(2:ℝ)*M₁⌋+1 : ℤ) ≤ 0)
      have hcast : (((2*⌊(2:ℝ)*M₁⌋+1).toNat : ℕ) : ℝ) = ((0:ℤ):ℝ) := by exact_mod_cast hz
      rw [hcast]; push_cast; linarith
  exact le_trans (by exact_mod_cast h1) hb

lemma card_R2_le (M₂ : ℝ) (hM₂ : 0 < M₂) : ((R2 M₂).card : ℝ) ≤ 2*M₂ := by
  have h2 : (Finset.Icc (1:ℤ) ⌊2*M₂⌋).card = (⌊2*M₂⌋).toNat := by
    rw [Int.card_Icc]; congr 1; ring_nf
  have h1 : (R2 M₂).card ≤ (⌊(2:ℝ)*M₂⌋).toNat :=
    le_trans (Finset.card_filter_le _ _) (le_of_eq h2)
  have hb : (((⌊(2:ℝ)*M₂⌋).toNat : ℕ) : ℝ) ≤ 2*M₂ := by
    have hfl : (0:ℤ) ≤ ⌊(2:ℝ)*M₂⌋ := Int.floor_nonneg.mpr (by linarith)
    have hz := Int.toNat_of_nonneg hfl
    have hcast : (((⌊(2:ℝ)*M₂⌋).toNat : ℕ) : ℝ) = ((⌊(2:ℝ)*M₂⌋ : ℤ) : ℝ) := by
      exact_mod_cast hz
    rw [hcast]; linarith [Int.floor_le ((2:ℝ)*M₂)]
  exact le_trans (by exact_mod_cast h1) hb

lemma card_R3ext_le (K M₃ : ℝ) (hM₃ : 1 ≤ M₃) :
    ((R3ext K M₃).card : ℝ) ≤ (2*|K|+10)*M₃ := by
  have hM₃pos : 0 < M₃ := by linarith
  have h2 : (R3ext K M₃).card = (2*⌈(K+1)*M₃⌉+1).toNat := by
    rw [R3ext, Int.card_Icc]; congr 1; ring_nf
  rw [h2]
  by_cases h : (0:ℤ) ≤ 2*⌈(K+1)*M₃⌉+1
  · have hz := Int.toNat_of_nonneg h
    have hcast : (((2*⌈(K+1)*M₃⌉+1).toNat : ℕ) : ℝ) = ((2*⌈(K+1)*M₃⌉+1 : ℤ) : ℝ) := by
      exact_mod_cast hz
    rw [hcast]; push_cast
    have hceil : ((⌈(K+1)*M₃⌉ : ℤ) : ℝ) < (K+1)*M₃ + 1 := Int.ceil_lt_add_one _
    have hA : 2*((K+1)*M₃) ≤ 2 * (|K| * M₃) + 2*M₃ := by
      have hKK : K ≤ |K| := le_abs_self K
      nlinarith [hM₃pos]
    nlinarith [hceil, hA, hM₃, abs_nonneg K]
  · have hz := Int.toNat_of_nonpos (by omega : (2*⌈(K+1)*M₃⌉+1 : ℤ) ≤ 0)
    have hcast : (((2*⌈(K+1)*M₃⌉+1).toNat : ℕ) : ℝ) = ((0:ℤ):ℝ) := by exact_mod_cast hz
    rw [hcast]; push_cast
    nlinarith [abs_nonneg K, hM₃]

/-- `Σ_{m₁ ∈ R1 M₁} 1/|m₁|` is bounded by an absolute constant. -/
lemma sum_inv_abs_R1_le (M₁ : ℝ) (hM₁ : 0 < M₁) :
    ∑ m ∈ R1 M₁, (1:ℝ)/|(m:ℝ)| ≤ 8 := by
  by_cases h : M₁ < 1/2
  · have hf : ⌊(2:ℝ)*M₁⌋ = 0 := by
      rw [Int.floor_eq_zero_iff]; constructor <;> linarith
    have hempty : R1 M₁ = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro m hm
      rw [R1, Finset.mem_filter, Finset.mem_Icc] at hm
      obtain ⟨⟨h1,h2⟩, h3⟩ := hm
      rw [hf] at h1 h2
      simp only [neg_zero] at h1 h2
      have hm0 : m = 0 := by omega
      rw [hm0] at h3
      simp only [Int.cast_zero, abs_zero] at h3
      linarith
    rw [hempty]; simp
  · push Not at h
    calc ∑ m ∈ R1 M₁, (1:ℝ)/|(m:ℝ)|
        ≤ ∑ m ∈ R1 M₁, (1/M₁) := by
          apply Finset.sum_le_sum
          intro m hm
          rw [R1, Finset.mem_filter] at hm
          exact one_div_le_one_div_of_le hM₁ (le_of_lt hm.2)
      _ = (R1 M₁).card * (1/M₁) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (4*M₁+1) * (1/M₁) := by
          apply mul_le_mul_of_nonneg_right (card_R1_le M₁ hM₁)
          positivity
      _ ≤ 8 := by
          rw [mul_one_div, div_le_iff₀ hM₁]; linarith

lemma sum_R2_le (M₂ : ℝ) (hM₂ : 0 < M₂) : ∑ m ∈ R2 M₂, (m:ℝ) ≤ 4*M₂^2 := by
  have hterm : ∀ m ∈ R2 M₂, (m:ℝ) ≤ 2*M₂ := by
    intro m hm
    rw [R2, Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨h1,h2⟩, h3⟩ := hm
    have hh : (m:ℝ) ≤ (⌊(2:ℝ)*M₂⌋ : ℤ) := by exact_mod_cast h2
    linarith [Int.floor_le ((2:ℝ)*M₂)]
  calc ∑ m ∈ R2 M₂, (m:ℝ) ≤ ∑ m ∈ R2 M₂, (2*M₂) := Finset.sum_le_sum hterm
    _ = ((R2 M₂).card : ℝ) * (2*M₂) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2*M₂) * (2*M₂) := by
          apply mul_le_mul_of_nonneg_right (card_R2_le M₂ hM₂); linarith
    _ = 4*M₂^2 := by ring

lemma sum_psi1_le (K M₃ : ℝ) (hM₃ : 1 ≤ M₃) :
    ∑ m ∈ R3ext K M₃, psi1 K ((m:ℝ)/M₃) ≤ (2*|K|+10)*M₃ := by
  calc ∑ m ∈ R3ext K M₃, psi1 K ((m:ℝ)/M₃) ≤ ∑ m ∈ R3ext K M₃, (1:ℝ) :=
        Finset.sum_le_sum (fun m _ => psi1_le_one K _)
    _ = ((R3ext K M₃).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ (2*|K|+10)*M₃ := card_R3ext_le K M₃ hM₃

/-- Factorization of a triple sum of products. -/
lemma sum3_factor (s₁ : Finset ℤ) (s₂ : Finset ℤ) (s₃ : Finset ℤ) (A B C : ℤ → ℝ) (D : ℝ) :
    ∑ i ∈ s₁, ∑ j ∈ s₂, ∑ k ∈ s₃, A i * B j * C k * D
      = (∑ i ∈ s₁, A i) * (∑ j ∈ s₂, B j) * (∑ k ∈ s₃, C k) * D := by
  have haux : (∑ i ∈ s₁, A i) * (∑ j ∈ s₂, B j) * (∑ k ∈ s₃, C k)
      = ∑ i ∈ s₁, ∑ j ∈ s₂, ∑ k ∈ s₃, A i * B j * C k := by
    rw [Finset.sum_mul_sum]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro j _
    rw [Finset.mul_sum]
  rw [haux]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro j _
  rw [Finset.sum_mul]

/-! ### The integral of `gSum` -/

/-- A continuous compactly supported function composed with an invertible affine map is
integrable. -/
lemma integrable_const_mul_affine {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f)
    (c m₁ m₂ m₃ : ℝ) (h₁ : m₁ ≠ 0) (h₂ : 0 < m₂) :
    Integrable (fun u : ℝ => c * f ((m₁*u + m₃)/m₂)) volume := by
  have hcont : Continuous (fun u : ℝ => f ((m₁*u + m₃)/m₂)) := by fun_prop
  have hcomp : HasCompactSupport (fun u : ℝ => f ((m₁*u + m₃)/m₂)) := by
    have ha : m₁/m₂ ≠ 0 := div_ne_zero h₁ (ne_of_gt h₂)
    let φ : ℝ ≃ₜ ℝ := (Homeomorph.smulOfNeZero (m₁/m₂) ha).trans (Homeomorph.addRight (m₃/m₂))
    have h1 : HasCompactSupport (f ∘ ⇑φ) := hcs.comp_homeomorph φ
    have h2 : (f ∘ ⇑φ) = fun u => f ((m₁*u + m₃)/m₂) := by
      funext u
      simp only [Function.comp_apply, φ, Homeomorph.trans_apply, Homeomorph.smulOfNeZero_apply,
        Homeomorph.coe_addRight, smul_eq_mul]
      rw [div_eq_mul_inv]; ring_nf
    rwa [h2] at h1
  exact (hcont.integrable_of_hasCompactSupport hcomp).const_mul c

/-- The change of variables `u ↦ (m₁u+m₃)/m₂`. -/
lemma integral_comp_affine (f : ℝ → ℝ) {m₁ m₂ m₃ : ℝ} (hm₂ : 0 < m₂) :
    ∫ u, f ((m₁ * u + m₃) / m₂) = (m₂ / |m₁|) * ∫ u, f u := by
  have hfun : ∀ u, (m₁ * u + m₃) / m₂ = (m₁/m₂) * u + m₃/m₂ := by
    intro u; rw [div_eq_mul_inv]; ring
  simp_rw [hfun]
  rw [Measure.integral_comp_mul_left (fun w => f (w + m₃/m₂)) (m₁/m₂)]
  rw [MeasureTheory.integral_add_right_eq_self f (m₃/m₂)]
  rw [abs_inv, abs_div, abs_of_pos hm₂]
  simp only [smul_eq_mul]
  rw [inv_div]

/-- The integral of the majorant `gSum`, bounded by `32 (2|K|+10) M₂² M₃ ∫f`. -/
lemma integral_gSum_le {K M₁ M₂ M₃ : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 1 ≤ M₃)
    {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f) (hfnn : ∀ u, 0 ≤ f u) :
    ∫ u, gSum K M₁ M₂ M₃ f u ≤ 32 * (2*|K|+10) * M₂^2 * M₃ * ∫ u, f u := by
  have hIf : 0 ≤ ∫ u, f u := integral_nonneg hfnn
  have hIntTerm : ∀ (m₁ m₂ m₃ : ℤ), (m₁:ℝ) ≠ 0 → 0 < (m₂:ℝ) →
      Integrable (fun u : ℝ => psi1 K ((m₃:ℝ)/M₃) * f (((m₁:ℝ)*u + (m₃:ℝ))/(m₂:ℝ))) volume :=
    fun m₁ m₂ m₃ h₁ h₂ => integrable_const_mul_affine hf hcs _ _ _ _ h₁ h₂
  have hm₂pos_of : ∀ {m₂ : ℤ}, m₂ ∈ R2 M₂ → 0 < (m₂:ℝ) := by
    intro m₂ hm₂
    rw [R2, Finset.mem_filter, Finset.mem_Icc] at hm₂
    have hh : (1:ℝ) ≤ (m₂:ℝ) := by exact_mod_cast hm₂.1.1
    linarith
  have hm₁ne_of : ∀ {m₁ : ℤ}, m₁ ∈ R1 M₁ → (m₁:ℝ) ≠ 0 := by
    intro m₁ hm₁
    rw [R1, Finset.mem_filter] at hm₁
    intro h; rw [h] at hm₁; simp at hm₁; linarith [hm₁.2, hM₁]
  have hIntIn : ∀ (m₁ : ℤ), (m₁:ℝ) ≠ 0 → Integrable (fun u : ℝ =>
      ∑ m₂ ∈ R2 M₂, ∑ m₃ ∈ R3ext K M₃,
        psi1 K ((m₃:ℝ)/M₃) * f (((m₁:ℝ)*u + (m₃:ℝ))/(m₂:ℝ))) volume := by
    intro m₁ h₁
    refine MeasureTheory.integrable_finsetSum _ (fun m₂ hm₂ =>
      MeasureTheory.integrable_finsetSum _ (fun m₃ _ => hIntTerm m₁ m₂ m₃ h₁ (hm₂pos_of hm₂)))
  have hIntOut : ∀ m₁ ∈ R1 M₁, Integrable (fun u : ℝ =>
      ∑ m₂ ∈ R2 M₂, ∑ m₃ ∈ R3ext K M₃,
        psi1 K ((m₃:ℝ)/M₃) * f (((m₁:ℝ)*u + (m₃:ℝ))/(m₂:ℝ))) volume :=
    fun m₁ hm₁ => hIntIn m₁ (hm₁ne_of hm₁)
  have hEq : ∫ u, gSum K M₁ M₂ M₃ f u
      = ∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, ∑ m₃ ∈ R3ext K M₃,
          (1/|(m₁:ℝ)|) * (m₂:ℝ) * psi1 K ((m₃:ℝ)/M₃) * ∫ u, f u := by
    simp only [gSum]
    rw [MeasureTheory.integral_finsetSum (R1 M₁) hIntOut]
    apply Finset.sum_congr rfl; intro m₁ hm₁
    rw [MeasureTheory.integral_finsetSum (R2 M₂) (fun m₂ hm₂ =>
      MeasureTheory.integrable_finsetSum _ (fun m₃ _ =>
        hIntTerm m₁ m₂ m₃ (hm₁ne_of hm₁) (hm₂pos_of hm₂)))]
    apply Finset.sum_congr rfl; intro m₂ hm₂
    rw [MeasureTheory.integral_finsetSum (R3ext K M₃) (fun m₃ _ =>
      hIntTerm m₁ m₂ m₃ (hm₁ne_of hm₁) (hm₂pos_of hm₂))]
    apply Finset.sum_congr rfl; intro m₃ hm₃
    rw [MeasureTheory.integral_const_mul]
    rw [integral_comp_affine f (hm₂pos_of hm₂)]
    ring_nf
  have hA0 : 0 ≤ ∑ m ∈ R1 M₁, (1:ℝ)/|(m:ℝ)| :=
    Finset.sum_nonneg (fun m _ => by positivity)
  have hB0 : 0 ≤ ∑ m ∈ R2 M₂, (m:ℝ) :=
    Finset.sum_nonneg (fun m hm => by
      rw [R2, Finset.mem_filter, Finset.mem_Icc] at hm
      have : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm.1.1
      linarith)
  have hC0 : 0 ≤ ∑ m ∈ R3ext K M₃, psi1 K ((m:ℝ)/M₃) :=
    Finset.sum_nonneg (fun m _ => psi1_nonneg _ _)
  calc ∫ u, gSum K M₁ M₂ M₃ f u
      = _ := hEq
    _ = (∑ m₁ ∈ R1 M₁, (1/|(m₁:ℝ)|)) * (∑ m₂ ∈ R2 M₂, (m₂:ℝ)) *
          (∑ m₃ ∈ R3ext K M₃, psi1 K ((m₃:ℝ)/M₃)) * ∫ u, f u :=
        sum3_factor _ _ _ _ _ _ _
    _ ≤ 8 * (4*M₂^2) * ((2*|K|+10)*M₃) * (∫ u, f u) := by
        have hAB : (∑ m₁ ∈ R1 M₁, (1/|(m₁:ℝ)|)) * (∑ m₂ ∈ R2 M₂, (m₂:ℝ))
            ≤ 8 * (4*M₂^2) :=
          mul_le_mul (sum_inv_abs_R1_le M₁ hM₁) (sum_R2_le M₂ hM₂) hB0 (by norm_num)
        have hABC : _ * (∑ m₃ ∈ R3ext K M₃, psi1 K ((m₃:ℝ)/M₃))
            ≤ (8 * (4*M₂^2)) * ((2*|K|+10)*M₃) :=
          mul_le_mul hAB (sum_psi1_le K M₃ hM₃) hC0 (by positivity)
        exact mul_le_mul_of_nonneg_right hABC hIf
    _ = 32 * (2*|K|+10) * M₂^2 * M₃ * ∫ u, f u := by ring

/-! ### The region-I bound -/

theorem region_I_bound (K : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Mbig M₁ M₂ M₃ T η : ℝ), 0 < M₁ → M₁ ≤ Mbig → 0 < M₂ → M₂ ≤ Mbig →
      1 ≤ M₃ → M₃ ≤ Mbig → 1 ≤ T → 0 ≤ η → ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f →
      (∀ u, 0 ≤ f u) →
      ∫ ξ in Set.Icc (-(T ^ η * M₁ / M₃)) (T ^ η * M₁ / M₃), ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2 ≤
        C * T ^ η * Mbig ^ 6 * (∫ u, f u) ^ 2 := by
  refine ⟨2048 * (2*|K|+10)^2, by positivity, ?_⟩
  intro Mbig M₁ M₂ M₃ T η hM₁ hM₁M hM₂ hM₂M hM₃ hM₃M hT hη f hf hcs hfnn
  have hMbig : 0 < Mbig := lt_of_lt_of_le hM₁ hM₁M
  have hM₃pos : 0 < M₃ := by linarith
  have hIf : 0 ≤ ∫ u, f u := integral_nonneg hfnn
  set a : ℝ := T ^ η * M₁ / M₃ with ha
  have hT0 : (0:ℝ) < T := by linarith
  have hTpow : 0 < T ^ η := Real.rpow_pos_of_pos hT0 η
  have ha_pos : 0 < a := by rw [ha]; positivity
  have ha_nn : 0 ≤ a := ha_pos.le
  set B : ℝ := 32 * (2*|K|+10) * M₂^2 * M₃ * ∫ u, f u with hB
  have hBnn : 0 ≤ B := by rw [hB]; positivity
  have hbnd : ∀ ξ, ‖ghat K M₁ M₂ M₃ f ξ‖ ≤ B := by
    intro ξ
    rw [hB]
    exact le_trans (norm_ghat_le_integral_gSum hfnn ξ)
      (integral_gSum_le hM₁ hM₂ hM₃ hf hcs hfnn)
  have hint : ∫ ξ in Set.Icc (-a) a, ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2 ≤ B^2 * (2*a) := by
    have h1 : ‖∫ ξ in Set.Icc (-a) a, ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2‖
        ≤ B^2 * volume.real (Set.Icc (-a) a) :=
      MeasureTheory.norm_setIntegral_le_of_norm_le_const (measure_Icc_lt_top) (fun ξ _ => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hbnd ξ) 2)
    rw [Real.norm_of_nonneg (MeasureTheory.setIntegral_nonneg measurableSet_Icc
          (fun ξ _ => by positivity)),
        Real.volume_real_Icc, sub_neg_eq_add, ← two_mul, max_eq_left (by linarith [ha_nn])] at h1
    exact h1
  have hprod : M₁ * M₂^4 * M₃ ≤ Mbig^6 := by
    have h2 : M₂^4 ≤ Mbig^4 := pow_le_pow_left₀ hM₂.le hM₂M 4
    calc M₁ * M₂^4 * M₃ ≤ Mbig * Mbig^4 * Mbig := by
          apply mul_le_mul
          · exact mul_le_mul hM₁M h2 (by positivity) hMbig.le
          · exact hM₃M
          · exact hM₃pos.le
          · positivity
      _ = Mbig^6 := by ring
  calc ∫ ξ in Set.Icc (-(T ^ η * M₁ / M₃)) (T ^ η * M₁ / M₃), ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2
      = ∫ ξ in Set.Icc (-a) a, ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2 := by rw [ha]
    _ ≤ B^2 * (2*a) := hint
    _ = 2048 * (2*|K|+10)^2 * T ^ η * M₁ * M₂^4 * M₃ * (∫ u, f u)^2 := by
        rw [hB, ha]; field_simp; ring
    _ ≤ 2048 * (2*|K|+10)^2 * T ^ η * Mbig^6 * (∫ u, f u)^2 := by
        rw [show 2048 * (2*|K|+10)^2 * T ^ η * M₁ * M₂^4 * M₃ * (∫ u, f u)^2
              = (2048 * (2*|K|+10)^2 * T ^ η * (∫ u, f u)^2) * (M₁ * M₂^4 * M₃) from by ring,
            show 2048 * (2*|K|+10)^2 * T ^ η * Mbig^6 * (∫ u, f u)^2
              = (2048 * (2*|K|+10)^2 * T ^ η * (∫ u, f u)^2) * Mbig^6 from by ring]
        exact mul_le_mul_of_nonneg_left hprod (by positivity)

end

end Work.GM.Affine
