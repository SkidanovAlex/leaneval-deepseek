import Mathlib
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.card_mul_pairs_le

namespace Work.GM.Affine

/-- Membership in `R1 M₁` gives `M₁ ≤ |m|` (in fact `M₁ < |m|`). -/
lemma R1_le_abs {M₁ : ℝ} {m : ℤ} (hm : m ∈ R1 M₁) : M₁ ≤ |(m : ℝ)| :=
  le_of_lt (Finset.mem_filter.mp hm).2

/-- Membership in `R1 M₁` gives `|m| ≤ 2 M₁` (the range `R1` is contained in `[-⌊2M₁⌋, ⌊2M₁⌋]`). -/
lemma abs_le_two_mul_of_mem_R1 {M₁ : ℝ} {m : ℤ} (hm : m ∈ R1 M₁) :
    |(m : ℝ)| ≤ 2 * M₁ := by
  have hb := (Finset.mem_filter.mp hm).1
  rw [Finset.mem_Icc] at hb
  obtain ⟨h1, h2⟩ := hb
  have h1' : -(((⌊2 * M₁⌋ : ℤ)) : ℝ) ≤ (m : ℝ) := by exact_mod_cast h1
  have h2' : (m : ℝ) ≤ (((⌊2 * M₁⌋ : ℤ)) : ℝ) := by exact_mod_cast h2
  have hfl : (((⌊2 * M₁⌋ : ℤ)) : ℝ) ≤ 2 * M₁ := Int.floor_le _
  rw [abs_le]
  constructor <;> linarith

/-- **Count of resonant pairs.** With `M₁ > 0`, `M₃ ≥ 1`, `T ≥ 1`, `4M₁/M₃ < |ξ| ≤ T⁶`, the
number of pairs `(m₁, ℓ)` with `m₁ ∈ R1 M₁` and `|ℓ - ξ/m₁| ≤ 2/M₃` is
`⪅ T^{6ε} (1 + M₁/M₃)`.

This is GM §9's "count the resonant pairs" step: the second condition is exactly
`|m₁ℓ - ξ| ≤ 4M₁/M₃`, so the resonance count `card_mul_pairs_le` (divisor bound) applies with
`r = 4M₁/M₃`, `X = T⁶`. -/
theorem resonant_count_good {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M₁ M₃ T ξ : ℝ), 0 < M₁ → 1 ≤ M₃ → 1 ≤ T →
        4 * M₁ / M₃ < |ξ| → |ξ| ≤ T ^ 6 →
        ∀ P : Finset (ℤ × ℤ),
          (∀ p ∈ P, p.1 ∈ R1 M₁) →
          (∀ p ∈ P, |(p.2 : ℝ) - ξ / (p.1 : ℝ)| ≤ 2 / M₃) →
          (P.card : ℝ) ≤ C * T ^ (6 * ε) * (1 + M₁ / M₃) := by
  obtain ⟨C0, hC0pos, hC0⟩ := card_mul_pairs_le hε
  refine ⟨8 * C0 * 4 ^ ε, by positivity, ?_⟩
  intro M₁ M₃ T ξ hM₁ hM₃ hT hξlo hξhi P hP1 hP2
  have hM₃pos : 0 < M₃ := lt_of_lt_of_le zero_lt_one hM₃
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  set r : ℝ := 4 * M₁ / M₃ with hr
  have hrpos : 0 < r := by rw [hr]; positivity
  have hrlt : r < |ξ| := by rw [hr]; exact hξlo
  have hX : 1 ≤ T ^ 6 := one_le_pow₀ hT
  -- the two hypotheses of `card_mul_pairs_le`
  have hP1' : ∀ p ∈ P, M₁ ≤ |(p.1 : ℝ)| := fun p hp => R1_le_abs (hP1 p hp)
  have hP2' : ∀ p ∈ P, |((p.1 : ℝ) * (p.2 : ℝ)) - ξ| ≤ r := by
    intro p hp
    have hmem := hP1 p hp
    have hp1ne : (p.1 : ℝ) ≠ 0 := by
      have : (0 : ℝ) < |(p.1 : ℝ)| := lt_of_lt_of_le hM₁ (R1_le_abs hmem)
      exact abs_pos.mp this
    have h1abs : |(p.1 : ℝ)| ≤ 2 * M₁ := abs_le_two_mul_of_mem_R1 hmem
    have h2 := hP2 p hp
    have hmul : |((p.1 : ℝ) * (p.2 : ℝ)) - ξ|
        = |(p.1 : ℝ)| * |(p.2 : ℝ) - ξ / (p.1 : ℝ)| := by
      rw [← abs_mul]
      congr 1
      field_simp
    rw [hmul]
    calc |(p.1 : ℝ)| * |(p.2 : ℝ) - ξ / (p.1 : ℝ)|
        ≤ (2 * M₁) * (2 / M₃) :=
          mul_le_mul h1abs h2 (abs_nonneg _) (by linarith)
      _ = r := by rw [hr]; field_simp; ring
  have hmain := hC0 M₁ r (T ^ 6) hM₁ hrpos.le hX ξ hrlt hξhi P hP1' hP2'
  -- the two size estimates
  have hle : T ^ 6 + r + 2 ≤ 4 * T ^ 6 := by
    have hr6 : r < T ^ 6 := lt_of_lt_of_le hrlt hξhi
    linarith
  have h4 : (4 * T ^ 6) ^ ε = 4 ^ ε * T ^ (6 * ε) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast T 6,
      ← Real.rpow_mul hTpos.le]
    congr 1
  have hrpow : (T ^ 6 + r + 2) ^ ε ≤ 4 ^ ε * T ^ (6 * ε) := by
    rw [← h4]
    exact Real.rpow_le_rpow (by positivity) hle hε.le
  have hr2 : 2 * r + 1 ≤ 8 * (1 + M₁ / M₃) := by
    have hM₃ne : M₃ ≠ 0 := ne_of_gt hM₃pos
    rw [hr]
    field_simp
    linarith [hM₃pos]
  have hC0nn : 0 ≤ C0 := hC0pos.le
  have hrnn : 0 ≤ r := hrpos.le
  calc (P.card : ℝ)
      ≤ C0 * (T ^ 6 + r + 2) ^ ε * (2 * r + 1) := hmain
    _ ≤ C0 * (4 ^ ε * T ^ (6 * ε)) * (8 * (1 + M₁ / M₃)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hrpow hC0nn) hr2
          (by linarith) (by positivity)
    _ = 8 * C0 * 4 ^ ε * T ^ (6 * ε) * (1 + M₁ / M₃) := by ring

end Work.GM.Affine
