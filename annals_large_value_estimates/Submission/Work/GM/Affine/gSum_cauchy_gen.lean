import Mathlib
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.cauchy_base

/-!
# GM §9: `L²` bound for the majorant `gSum`, uniform constant and general `Mbig`

The elementary Cauchy–Schwarz bound for `gSum` proved in `Submission.Work.GM.Affine.gSum_cauchy`
is

`∫ u, (gSum K M₁ M₂ M₃ f u)^2 ≤ C * (K + 1)^2 * Mbig^6 * ∫ u, (f u)^2`

for parameters with `1 ≤ Mbig`, but with the constant `C` hidden inside an existential, i.e. not
usable as a single constant valid for all parameter tuples.  Here we

* expose the constant (`10368`) as the *uniform* version `gSum_cauchy_uniform`, with the same
  proof, and
* deduce the general form in which `Mbig` is only assumed positive and the right side carries
  `Mbig^6 + 1` instead of `Mbig^6` (the `+ 1` covers `Mbig < 1`, where all the summation ranges
  are small and the bound is trivially true).  Concretely we apply the uniform version with
  `Mbig` replaced by `max Mbig 1` and use `(max Mbig 1)^6 ≤ Mbig^6 + 1`.

This is the interface `Work.GM.Affine.gSum_cauchy_gen` used for the base case `ε = 100` of the
downward induction in GM §9.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-! ### Cardinality bounds for the summation ranges -/

private lemma cardR1_le_four_add_one {M₁ : ℝ} (hM₁ : 0 ≤ M₁) :
    ((R1 M₁).card : ℝ) ≤ 4 * M₁ + 1 := by
  have hfloor : (0 : ℤ) ≤ ⌊2 * M₁⌋ := Int.floor_nonneg.mpr (by linarith)
  have hnat : (R1 M₁).card ≤ (2 * ⌊2 * M₁⌋ + 1).toNat := by
    calc (R1 M₁).card
        ≤ (Finset.Icc (-⌊2 * M₁⌋) ⌊2 * M₁⌋).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
      _ = (2 * ⌊2 * M₁⌋ + 1).toNat := by rw [Int.card_Icc]; congr 1; ring
  have hreal : ((2 * ⌊2 * M₁⌋ + 1).toNat : ℝ) ≤ 4 * M₁ + 1 := by
    have hnn : (0 : ℤ) ≤ 2 * ⌊2 * M₁⌋ + 1 := by linarith
    have hcast : ((2 * ⌊2 * M₁⌋ + 1).toNat : ℝ) = 2 * (⌊2 * M₁⌋ : ℝ) + 1 := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]; push_cast; ring
    rw [hcast]
    have := Int.floor_le (2 * M₁)
    linarith
  exact le_trans (by exact_mod_cast hnat) hreal

/-- If `M₁ < 1/2` the range `R1 M₁` is empty; otherwise `|R1| ≤ 6 M₁`. -/
private lemma cardR1_le_six {M₁ : ℝ} (hM₁ : 0 < M₁) : ((R1 M₁).card : ℝ) ≤ 6 * M₁ := by
  by_cases h : M₁ < 1 / 2
  · have hf : ⌊(2 : ℝ) * M₁⌋ = 0 := by
      rw [Int.floor_eq_zero_iff]; constructor <;> linarith
    have hempty : R1 M₁ = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro m hm
      rw [R1, Finset.mem_filter, Finset.mem_Icc] at hm
      obtain ⟨⟨h1, h2⟩, h3⟩ := hm
      rw [hf] at h1 h2
      simp only [neg_zero] at h1 h2
      have hm0 : m = 0 := by omega
      rw [hm0] at h3
      simp only [Int.cast_zero, abs_zero] at h3
      linarith
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    linarith
  · push Not at h
    have := cardR1_le_four_add_one hM₁.le
    linarith

private lemma cardR2_le_two {M₂ : ℝ} (hM₂ : 0 < M₂) : ((R2 M₂).card : ℝ) ≤ 2 * M₂ := by
  have hfloor : (0 : ℤ) ≤ ⌊2 * M₂⌋ := Int.floor_nonneg.mpr (by linarith)
  have hnat : (R2 M₂).card ≤ (⌊2 * M₂⌋).toNat := by
    calc (R2 M₂).card
        ≤ (Finset.Icc (1 : ℤ) ⌊2 * M₂⌋).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
      _ = (⌊2 * M₂⌋).toNat := by rw [Int.card_Icc]; congr 1; ring
  have hreal : ((⌊2 * M₂⌋).toNat : ℝ) ≤ 2 * M₂ := by
    have hcast : ((⌊2 * M₂⌋).toNat : ℝ) = (⌊2 * M₂⌋ : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hfloor]
    rw [hcast]
    exact Int.floor_le (2 * M₂)
  exact le_trans (by exact_mod_cast hnat) hreal

private lemma cardR3ext_le_three {K M₃ : ℝ} (hK : 0 ≤ K) (hM₃ : 0 < M₃) :
    ((R3ext K M₃).card : ℝ) ≤ 3 * (K + 1) * (M₃ + 1) := by
  have hx : 0 < (K + 1) * M₃ := by nlinarith
  have hceil : (0 : ℤ) < ⌈(K + 1) * M₃⌉ := Int.ceil_pos.mpr hx
  have h2 : (R3ext K M₃).card = (2 * ⌈(K + 1) * M₃⌉ + 1).toNat := by
    rw [R3ext, Int.card_Icc]; congr 1; ring
  rw [h2]
  have hpos : (0 : ℤ) ≤ 2 * ⌈(K + 1) * M₃⌉ + 1 := by omega
  have hcast : (((2 * ⌈(K + 1) * M₃⌉ + 1).toNat : ℕ) : ℝ)
      = ((2 * ⌈(K + 1) * M₃⌉ + 1 : ℤ) : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg hpos)
  rw [hcast]
  push_cast
  have hc := Int.ceil_lt_add_one ((K + 1) * M₃)
  have hK1 : (1 : ℝ) ≤ K + 1 := by linarith
  have hM31 : (3 : ℝ) ≤ M₃ + 3 := by linarith
  have hprod : (3 : ℝ) ≤ (K + 1) * (M₃ + 3) := by
    have := mul_le_mul hK1 hM31 (by norm_num) (by linarith)
    simpa using this
  nlinarith [hc, hprod]

/-- **Uniform-constant version of `gSum_cauchy`.**  The constant `10368` is valid for *all*
parameter tuples with `1 ≤ Mbig` (this is exactly the proof of `gSum_cauchy`, which produces that
constant before hiding it in an existential). -/
theorem gSum_cauchy_uniform {K Mbig M₁ M₂ M₃ : ℝ} (hK : 0 ≤ K) (hMb : 1 ≤ Mbig) (hM₁ : 0 < M₁)
    (hM₁b : M₁ ≤ Mbig) (hM₂ : 0 < M₂) (hM₂b : M₂ ≤ Mbig) (hM₃ : 0 < M₃) (hM₃b : M₃ ≤ Mbig)
    {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f) (hfnn : ∀ u, 0 ≤ f u) :
    ∫ u, (gSum K M₁ M₂ M₃ f u) ^ 2 ≤ 10368 * (K + 1) ^ 2 * Mbig ^ 6 * ∫ u, (f u) ^ 2 := by
  set A : ℝ := ((R1 M₁).card : ℝ) with hA
  set B : ℝ := ((R2 M₂).card : ℝ) with hB
  set C3 : ℝ := ((R3ext K M₃).card : ℝ) with hC3
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hC30 : 0 ≤ C3 := by rw [hC3]; positivity
  have hIf : 0 ≤ ∫ u, (f u) ^ 2 := integral_nonneg fun u => sq_nonneg _
  -- Integrability and evaluation of the elementary affine squares.
  have hint_affine : ∀ m₁ ∈ R1 M₁, ∀ m₂ ∈ R2 M₂, ∀ m₃ ∈ R3ext K M₃,
      Integrable (fun u : ℝ => f (((m₁ : ℝ) * u + m₃) / m₂) ^ 2) := by
    intro m₁ hm₁ m₂ hm₂ m₃ _
    exact integrable_affine_sq hf hcs (R1_ne_zero hM₁ hm₁) (ne_of_gt (R2_pos hM₂ hm₂))
  have hInt_eval : ∀ m₁ ∈ R1 M₁, ∀ m₂ ∈ R2 M₂, ∀ m₃ ∈ R3ext K M₃,
      ∫ u, f (((m₁ : ℝ) * u + m₃) / m₂) ^ 2 = ((m₂ : ℝ) / |(m₁ : ℝ)|) * ∫ u, f u ^ 2 := by
    intro m₁ hm₁ m₂ hm₂ m₃ _
    exact integral_affine_sq (c := (m₁ : ℝ)) (d := (m₂ : ℝ)) (e := (m₃ : ℝ))
      (R1_ne_zero hM₁ hm₁) (R2_pos hM₂ hm₂)
  set G : ℝ → ℝ := fun u => A * B * C3 *
    ∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, ∑ m₃ ∈ R3ext K M₃, f (((m₁ : ℝ) * u + m₃) / m₂) ^ 2 with hG
  -- The pointwise Cauchy–Schwarz bound.
  have hpt : ∀ u, (gSum K M₁ M₂ M₃ f u) ^ 2 ≤ G u := by
    intro u
    rw [hG]
    have h1 : (gSum K M₁ M₂ M₃ f u) ^ 2 ≤ (A * B * C3) *
        ∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, ∑ m₃ ∈ R3ext K M₃,
          (psi1 K ((m₃ : ℝ) / M₃) * f (((m₁ : ℝ) * u + m₃) / m₂)) ^ 2 := by
      have := sq_sum_sum_le (R1 M₁) (R2 M₂) (R3ext K M₃)
        (fun m₁ m₂ m₃ => psi1 K ((m₃ : ℝ) / M₃) * f (((m₁ : ℝ) * u + m₃) / m₂))
      simpa [gSum, hA, hB, hC3] using this
    have h2 : ∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, ∑ m₃ ∈ R3ext K M₃,
          (psi1 K ((m₃ : ℝ) / M₃) * f (((m₁ : ℝ) * u + m₃) / m₂)) ^ 2
        ≤ ∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, ∑ m₃ ∈ R3ext K M₃,
          f (((m₁ : ℝ) * u + m₃) / m₂) ^ 2 := by
      apply Finset.sum_le_sum; intro m₁ _
      apply Finset.sum_le_sum; intro m₂ _
      apply Finset.sum_le_sum; intro m₃ _
      have hw0 : 0 ≤ psi1 K ((m₃ : ℝ) / M₃) := psi1_nonneg _ _
      have hw1 : psi1 K ((m₃ : ℝ) / M₃) ≤ 1 := psi1_le_one _ _
      have hfv : 0 ≤ f (((m₁ : ℝ) * u + m₃) / m₂) := hfnn _
      have hle : psi1 K ((m₃ : ℝ) / M₃) * f (((m₁ : ℝ) * u + m₃) / m₂)
          ≤ f (((m₁ : ℝ) * u + m₃) / m₂) := by
        calc psi1 K ((m₃ : ℝ) / M₃) * f (((m₁ : ℝ) * u + m₃) / m₂)
            ≤ 1 * f (((m₁ : ℝ) * u + m₃) / m₂) := mul_le_mul_of_nonneg_right hw1 hfv
          _ = f (((m₁ : ℝ) * u + m₃) / m₂) := one_mul _
      exact pow_le_pow_left₀ (mul_nonneg hw0 hfv) hle 2
    calc (gSum K M₁ M₂ M₃ f u) ^ 2
        ≤ (A * B * C3) * ∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, ∑ m₃ ∈ R3ext K M₃,
            (psi1 K ((m₃ : ℝ) / M₃) * f (((m₁ : ℝ) * u + m₃) / m₂)) ^ 2 := h1
      _ ≤ (A * B * C3) * ∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, ∑ m₃ ∈ R3ext K M₃,
            f (((m₁ : ℝ) * u + m₃) / m₂) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
  have hIntG : Integrable G := by
    rw [hG]
    refine Integrable.const_mul ?_ (A * B * C3)
    refine integrable_finsetSum _ fun m₁ hm₁ => ?_
    refine integrable_finsetSum _ fun m₂ hm₂ => ?_
    exact integrable_finsetSum _ fun m₃ hm₃ => hint_affine m₁ hm₁ m₂ hm₂ m₃ hm₃
  have hsumfac :
      (∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, ∑ m₃ ∈ R3ext K M₃, ((m₂ : ℝ) / |(m₁ : ℝ)|) * ∫ u, f u ^ 2)
        = (∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, ∑ m₃ ∈ R3ext K M₃, ((m₂ : ℝ) / |(m₁ : ℝ)|))
          * ∫ u, f u ^ 2 := by
    simp only [Finset.sum_mul]
  have hGint : ∫ u, G u = A * B * C3 *
      ((∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, ∑ m₃ ∈ R3ext K M₃, ((m₂ : ℝ) / |(m₁ : ℝ)|))
        * ∫ u, f u ^ 2) := by
    rw [hG, MeasureTheory.integral_const_mul]
    congr 1
    rw [← hsumfac]
    rw [MeasureTheory.integral_finsetSum _ fun m₁ hm₁ =>
      integrable_finsetSum _ fun m₂ hm₂ =>
        integrable_finsetSum _ fun m₃ hm₃ => hint_affine m₁ hm₁ m₂ hm₂ m₃ hm₃]
    apply Finset.sum_congr rfl; intro m₁ hm₁
    rw [MeasureTheory.integral_finsetSum _ fun m₂ hm₂ =>
      integrable_finsetSum _ fun m₃ hm₃ => hint_affine m₁ hm₁ m₂ hm₂ m₃ hm₃]
    apply Finset.sum_congr rfl; intro m₂ hm₂
    rw [MeasureTheory.integral_finsetSum _ fun m₃ hm₃ => hint_affine m₁ hm₁ m₂ hm₂ m₃ hm₃]
    apply Finset.sum_congr rfl; intro m₃ hm₃
    exact hInt_eval m₁ hm₁ m₂ hm₂ m₃ hm₃
  -- Bound the sum of scale factors.
  have hsum_bound :
      (∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, ∑ m₃ ∈ R3ext K M₃, ((m₂ : ℝ) / |(m₁ : ℝ)|))
        ≤ A * B * C3 * (2 * M₂ / M₁) := by
    have hterm : ∀ m₁ ∈ R1 M₁, ∀ m₂ ∈ R2 M₂, ∀ m₃ ∈ R3ext K M₃,
        ((m₂ : ℝ) / |(m₁ : ℝ)|) ≤ 2 * M₂ / M₁ := by
      intro m₁ hm₁ m₂ hm₂ m₃ _
      have hb : (m₂ : ℝ) ≤ 2 * M₂ := R2_le hm₂
      have ha : M₁ ≤ |(m₁ : ℝ)| := abs_of_mem_R1 hM₁ hm₁
      have h1 : 1 / |(m₁ : ℝ)| ≤ 1 / M₁ := one_div_le_one_div_of_le hM₁ ha
      calc ((m₂ : ℝ) / |(m₁ : ℝ)|) = (m₂ : ℝ) * (1 / |(m₁ : ℝ)|) := by ring
        _ ≤ (2 * M₂) * (1 / M₁) := by
            exact mul_le_mul hb h1 (by positivity) (by positivity)
        _ = 2 * M₂ / M₁ := by ring
    calc (∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, ∑ m₃ ∈ R3ext K M₃, ((m₂ : ℝ) / |(m₁ : ℝ)|))
        ≤ ∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, ∑ m₃ ∈ R3ext K M₃, (2 * M₂ / M₁) :=
          Finset.sum_le_sum fun m₁ hm₁ => Finset.sum_le_sum fun m₂ hm₂ =>
            Finset.sum_le_sum fun m₃ hm₃ => hterm m₁ hm₁ m₂ hm₂ m₃ hm₃
      _ = A * B * C3 * (2 * M₂ / M₁) := by
          simp only [Finset.sum_const, nsmul_eq_mul, hA, hB, hC3]
          ring
  -- Arithmetic: the counting coefficient.
  have hK1nn : (0 : ℝ) ≤ K + 1 := by linarith
  have hM31nn : (0 : ℝ) ≤ M₃ + 1 := by linarith
  have hMbnn : 0 ≤ Mbig := by linarith
  have hCoef : (A * B * C3) ^ 2 * (2 * M₂ / M₁) ≤ 10368 * (K + 1) ^ 2 * Mbig ^ 6 := by
    have hA6 : A ≤ 6 * M₁ := by rw [hA]; exact cardR1_le_six hM₁
    have hB2 : B ≤ 2 * M₂ := by rw [hB]; exact cardR2_le_two hM₂
    have hC3b : C3 ≤ 3 * (K + 1) * (M₃ + 1) := by rw [hC3]; exact cardR3ext_le_three hK hM₃
    have hAsq : A ^ 2 * (2 * M₂ / M₁) ≤ 72 * (M₁ * M₂) := by
      have hsq : A ^ 2 ≤ (6 * M₁) ^ 2 := pow_le_pow_left₀ hA0 hA6 2
      have hnn : (0 : ℝ) ≤ 2 * M₂ / M₁ := by positivity
      calc A ^ 2 * (2 * M₂ / M₁) ≤ (6 * M₁) ^ 2 * (2 * M₂ / M₁) :=
            mul_le_mul_of_nonneg_right hsq hnn
        _ = 72 * (M₁ * M₂) := by field_simp; ring
    have hBsq : B ^ 2 ≤ (2 * M₂) ^ 2 := pow_le_pow_left₀ hB0 hB2 2
    have hC3sq : C3 ^ 2 ≤ (3 * (K + 1) * (M₃ + 1)) ^ 2 := pow_le_pow_left₀ hC30 hC3b 2
    have hBC : B ^ 2 * C3 ^ 2 ≤ (2 * M₂) ^ 2 * (3 * (K + 1) * (M₃ + 1)) ^ 2 :=
      mul_le_mul hBsq hC3sq (by positivity) (by positivity)
    have hprod : M₁ * M₂ ^ 3 * (M₃ + 1) ^ 2 ≤ 4 * Mbig ^ 6 := by
      have h2 : M₂ ^ 3 ≤ Mbig ^ 3 := pow_le_pow_left₀ hM₂.le hM₂b 3
      have h3 : (M₃ + 1) ^ 2 ≤ (2 * Mbig) ^ 2 := pow_le_pow_left₀ hM31nn (by linarith) 2
      have h4 : M₁ * M₂ ^ 3 ≤ Mbig * Mbig ^ 3 :=
        mul_le_mul hM₁b h2 (by positivity) (by linarith)
      calc M₁ * M₂ ^ 3 * (M₃ + 1) ^ 2 ≤ (Mbig * Mbig ^ 3) * (2 * Mbig) ^ 2 :=
            mul_le_mul h4 h3 (by positivity) (by positivity)
        _ = 4 * Mbig ^ 6 := by ring
    have hstep1 : (A ^ 2 * (2 * M₂ / M₁)) * (B ^ 2 * C3 ^ 2) ≤
        (72 * (M₁ * M₂)) * ((2 * M₂) ^ 2 * (3 * (K + 1) * (M₃ + 1)) ^ 2) :=
      mul_le_mul hAsq hBC (by positivity) (by positivity)
    have hstep2 : (72 * (M₁ * M₂)) * ((2 * M₂) ^ 2 * (3 * (K + 1) * (M₃ + 1)) ^ 2) ≤
        10368 * (K + 1) ^ 2 * Mbig ^ 6 := by
      have hrw : (72 * (M₁ * M₂)) * ((2 * M₂) ^ 2 * (3 * (K + 1) * (M₃ + 1)) ^ 2)
          = 2592 * (K + 1) ^ 2 * (M₁ * M₂ ^ 3 * (M₃ + 1) ^ 2) := by ring
      rw [hrw]
      calc 2592 * (K + 1) ^ 2 * (M₁ * M₂ ^ 3 * (M₃ + 1) ^ 2)
          ≤ 2592 * (K + 1) ^ 2 * (4 * Mbig ^ 6) := mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = 10368 * (K + 1) ^ 2 * Mbig ^ 6 := by ring
    have hshape : (A * B * C3) ^ 2 * (2 * M₂ / M₁) = (A ^ 2 * (2 * M₂ / M₁)) * (B ^ 2 * C3 ^ 2) := by
      ring
    rw [hshape]
    exact le_trans hstep1 hstep2
  calc ∫ u, (gSum K M₁ M₂ M₃ f u) ^ 2
      ≤ ∫ u, G u := integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => sq_nonneg _)
        hIntG (Filter.Eventually.of_forall hpt)
    _ = A * B * C3 *
        ((∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, ∑ m₃ ∈ R3ext K M₃, ((m₂ : ℝ) / |(m₁ : ℝ)|))
          * ∫ u, f u ^ 2) := hGint
    _ ≤ A * B * C3 * ((A * B * C3 * (2 * M₂ / M₁)) * ∫ u, f u ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right hsum_bound hIf
    _ = ((A * B * C3) ^ 2 * (2 * M₂ / M₁)) * ∫ u, f u ^ 2 := by ring
    _ ≤ (10368 * (K + 1) ^ 2 * Mbig ^ 6) * ∫ u, f u ^ 2 :=
        mul_le_mul_of_nonneg_right hCoef hIf
    _ = 10368 * (K + 1) ^ 2 * Mbig ^ 6 * ∫ u, (f u) ^ 2 := by ring

theorem gSum_cauchy_gen :
    ∃ C : ℝ, 0 < C ∧
      ∀ (K Mbig M₁ M₂ M₃ : ℝ), 0 ≤ K → 0 < Mbig → 0 < M₁ → M₁ ≤ Mbig → 0 < M₂ → M₂ ≤ Mbig →
        0 < M₃ → M₃ ≤ Mbig → ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f →
        (∀ u, 0 ≤ f u) →
        ∫ u, (gSum K M₁ M₂ M₃ f u) ^ 2 ≤ C * (K + 1) ^ 2 * (Mbig ^ 6 + 1) * ∫ u, (f u) ^ 2 := by
  refine ⟨10368, by norm_num, ?_⟩
  intro K Mbig M₁ M₂ M₃ hK hMb hM₁ hM₁b hM₂ hM₂b hM₃ hM₃b f hf hcs hfnn
  -- replace `Mbig` by `Mb = max Mbig 1 ≥ 1` (the ranges are unchanged: `gSum` does not depend
  -- on `Mbig`, only the side condition `M ≤ Mbig` does)
  set Mb : ℝ := max Mbig 1 with hMbdef
  have hMb1 : (1 : ℝ) ≤ Mb := le_max_right _ _
  have hM₁b' : M₁ ≤ Mb := le_trans hM₁b (le_max_left _ _)
  have hM₂b' : M₂ ≤ Mb := le_trans hM₂b (le_max_left _ _)
  have hM₃b' : M₃ ≤ Mb := le_trans hM₃b (le_max_left _ _)
  have hmain := gSum_cauchy_uniform hK hMb1 hM₁ hM₁b' hM₂ hM₂b' hM₃ hM₃b' hf hcs hfnn
  -- `(max Mbig 1)^6 ≤ Mbig^6 + 1`
  have hpow : Mb ^ 6 ≤ Mbig ^ 6 + 1 := by
    rcases le_or_gt (1 : ℝ) Mbig with h | h
    · rw [hMbdef, max_eq_left h]; linarith
    · rw [hMbdef, max_eq_right (le_of_lt h)]
      have h0 : (0 : ℝ) ≤ Mbig ^ 6 := by positivity
      norm_num
      linarith
  have hI : (0 : ℝ) ≤ ∫ u, (f u) ^ 2 := integral_nonneg fun u => sq_nonneg _
  calc ∫ u, (gSum K M₁ M₂ M₃ f u) ^ 2
      ≤ 10368 * (K + 1) ^ 2 * Mb ^ 6 * ∫ u, (f u) ^ 2 := hmain
    _ ≤ 10368 * (K + 1) ^ 2 * (Mbig ^ 6 + 1) * ∫ u, (f u) ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hI
        exact mul_le_mul_of_nonneg_left hpow (by positivity)

end

end Work.GM.Affine
