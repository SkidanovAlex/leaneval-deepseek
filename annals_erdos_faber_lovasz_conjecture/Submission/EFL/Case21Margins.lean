import Submission.EFL.LargeEdgeHierarchy

/-!
# The `δ`-based margins of Case 2.1 (`Case21.lean`)

These are the numeric inequalities consumed by `case2_nonExtremal'`
(`Case21.lean`): the small-parameter bounds (`3τ^{1/4}(3σ) ≤ δ/10⁷`,
`2δ² + 2σ ≤ δ/1000`, `2000σ ≤ δ`, `16/√δ ≤ n`, `4√n ≤ βn`,
`2σ + 1/n ≤ 1/12000`), the room/budget bounds for the colour sets
(`|Cmed| + n/1000 + 1 ≤ n`, `|Cmed| + 2 ≤ 2σn`, `(1−2σ)n + 2 ≤ ⌊(1−3σ/2)n⌋₊`)
and `hmarginA` in its `δ`-form.
-/

set_option autoImplicit false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- `γ^7/10⁴⁰ ≤ 1/10⁴` for `0 < γ ≤ 1` (the `δ`-threshold is tiny). -/
theorem gamma_seven_div_le {γ : ℝ} (h0 : 0 < γ) (h1 : γ ≤ 1) :
    γ ^ 7 / 10 ^ 40 ≤ 1 / 10 ^ 4 := by
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 40) (by norm_num : (0 : ℝ) < 10 ^ 4)]
  have h2 : γ ^ 7 ≤ 1 := pow_le_one₀ h0.le h1
  linarith

/-- `3τ^{1/4}(3σ) ≤ δ/10⁷` when `σ ≤ δ^{12}/10⁶` and `δ ≤ 1/10⁴`. -/
theorem margin_alphaδ {δ σ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 10 ^ 4) (hσ0 : 0 < σ)
    (hσ : σ ≤ δ ^ 12 / 10 ^ 6) : 3 * tauQuarter (3 * σ) ≤ δ / 10 ^ 7 := by
  have h1 : tauQuarter (3 * σ) ≤ δ ^ 3 / 20 :=
    tauQuarter_three_sigma_le hδ0 (by linarith) hσ0 hσ
  have h2 : 3 * (δ ^ 3 / 20) ≤ δ / 10 ^ 7 := by
    have h3 : δ ^ 2 ≤ 1 / 10 ^ 8 := by nlinarith [hδ1, hδ0]
    nlinarith [h3, hδ0]
  linarith

/-- `2δ² + 2σ ≤ δ/1000` when `σ ≤ δ^{12}/10⁶` and `δ ≤ 1/10⁴`. -/
theorem margin_k2δ {δ σ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 10 ^ 4) (hσ0 : 0 < σ)
    (hσ : σ ≤ δ ^ 12 / 10 ^ 6) : 2 * δ ^ 2 + 2 * σ ≤ δ / 1000 := by
  have h1 : 2 * δ ^ 2 ≤ δ / 2000 := by nlinarith [hδ1, hδ0]
  have h2 : 2 * σ ≤ δ / 2000 := by
    have h3 : δ ^ 12 / 10 ^ 6 ≤ δ / 4000 := by
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 6) (by norm_num : (0 : ℝ) < 4000)]
      have h4 : δ ^ 11 ≤ 1 := pow_le_one₀ hδ0.le (by linarith)
      nlinarith [h4, hδ0]
    linarith [hσ, h3]
  linarith

/-- `2000σ ≤ δ` when `σ ≤ δ^{12}/10⁶` and `δ ≤ 1`. -/
theorem margin_2σδ {δ σ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hσ0 : 0 < σ)
    (hσ : σ ≤ δ ^ 12 / 10 ^ 6) : 2000 * σ ≤ δ := by
  have h3 : δ ^ 12 / 10 ^ 6 ≤ δ / 2000 := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 6) (by norm_num : (0 : ℝ) < 2000)]
    have h4 : δ ^ 11 ≤ 1 := pow_le_one₀ hδ0.le hδ1
    nlinarith [h4, hδ0]
  linarith [hσ, h3]

/-- `4√n ≤ βn` when `16 ≤ β²n`. -/
theorem margin_sqrt4 {β : ℝ} (hβ0 : 0 < β) {m : ℕ} (h : 16 ≤ β ^ 2 * (m : ℝ)) :
    4 * Real.sqrt (m : ℝ) ≤ β * (m : ℝ) := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have h2 : 16 * (m : ℝ) ≤ (β * (m : ℝ)) ^ 2 := by
    have heq : (β * (m : ℝ)) ^ 2 = β ^ 2 * (m : ℝ) ^ 2 := by ring
    rw [heq]
    nlinarith [h, hm0]
  have h4 : (m : ℝ) ≤ (β * (m : ℝ) / 4) ^ 2 := by
    have h5 : (β * (m : ℝ) / 4) ^ 2 = β ^ 2 * (m : ℝ) ^ 2 / 16 := by ring
    rw [h5]
    nlinarith [h, hm0]
  have h5 : Real.sqrt (m : ℝ) ≤ β * (m : ℝ) / 4 :=
    Real.sqrt_le_iff.mpr ⟨by positivity, h4⟩
  linarith [h5]

/-- `16/√δ ≤ n` when `16/δ² ≤ n` and `δ ≤ 1`. -/
theorem margin_hnbig2 {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {m : ℕ}
    (h : 16 / δ ^ 2 ≤ (m : ℝ)) : 16 / Real.sqrt δ ≤ (m : ℝ) := by
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos_of_pos hδ0
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have h2 : 16 ≤ (m : ℝ) * δ ^ 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < δ ^ 2)] at h
    linarith [h]
  have h3 : δ ^ 2 ≤ Real.sqrt δ := by
    have h4 : δ ≤ Real.sqrt δ :=
      (Real.le_sqrt hδ0.le hδ0.le).mpr (by nlinarith [hδ1, hδ0])
    nlinarith [h4, hδ1, hδ0]
  rw [div_le_iff₀ hs]
  nlinarith [h2, h3, hm0]

/-- `2σ + 1/n ≤ 1/12000` when `σ ≤ 1/10⁶` and `n ≥ 24000`. -/
theorem margin_σsmall2 {σ : ℝ} (hσ0 : 0 < σ) (hσ : σ ≤ 1 / 10 ^ 6) {m : ℕ}
    (hm : 24000 ≤ m) : 2 * σ + 1 / (m : ℝ) ≤ 1 / 12000 := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by
    have h1 : (0 : ℝ) < 24000 := by norm_num
    have h2 : (24000 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have h1 : 1 / (m : ℝ) ≤ 1 / 24000 := by
    rw [div_le_div_iff₀ hm0 (by norm_num : (0 : ℝ) < 24000)]
    simp only [one_mul]
    exact_mod_cast hm
  linarith

/-- `|Cmed| + n/1000 + 1 ≤ n` for `|Cmed| ≤ γ₁n ≤ n/2000` and `n ≥ 4000`. -/
theorem margin_room1C {γ₁ : ℝ} (hγ₁0 : 0 < γ₁) (hγ₁ : γ₁ ≤ 1 / 2000) {n : ℕ}
    (Cmed : Finset (Fin n)) (hC : (Cmed.card : ℝ) ≤ γ₁ * (n : ℝ)) (hn : 4000 ≤ n) :
    (Cmed.card : ℝ) + (1 / 1000) * (n : ℝ) + 1 ≤ (n : ℝ) := by
  have hnR : (4000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by linarith
  have h2 : γ₁ * (n : ℝ) ≤ (1 / 2000) * (n : ℝ) := mul_le_mul_of_nonneg_right hγ₁ hn0
  nlinarith [hC, h2, hnR]

/-- `|Cmed| + 2 ≤ 2σn` for `|Cmed| ≤ γ₁n ≤ σn` and `2 ≤ σn`. -/
theorem margin_room2C {γ₁ σ : ℝ} (hγ₁0 : 0 < γ₁) (hσ0 : 0 < σ) (hγ₁σ : γ₁ ≤ σ) {n : ℕ}
    (Cmed : Finset (Fin n)) (hC : (Cmed.card : ℝ) ≤ γ₁ * (n : ℝ))
    (h : 2 ≤ σ * (n : ℝ)) : (Cmed.card : ℝ) + 2 ≤ 2 * σ * (n : ℝ) := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h2 : γ₁ * (n : ℝ) ≤ σ * (n : ℝ) := mul_le_mul_of_nonneg_right hγ₁σ hn0
  nlinarith [hC, h2, h]

/-- `(1−2σ)n + 2 ≤ ⌊(1−3σ/2)n⌋₊` for `12 ≤ σn`. -/
theorem margin_budgetC {σ : ℝ} (hσ0 : 0 < σ) {n : ℕ} (h : 12 ≤ σ * (n : ℝ)) :
    (1 - 2 * σ) * (n : ℝ) + 2 ≤ (⌊(1 - 3 * σ / 2) * (n : ℝ)⌋₊ : ℝ) := by
  have h1 : (1 - 3 * σ / 2) * (n : ℝ) - 1 ≤ (⌊(1 - 3 * σ / 2) * (n : ℝ)⌋₊ : ℝ) := by
    have h2 := Nat.lt_floor_add_one ((1 - 3 * σ / 2) * (n : ℝ))
    linarith
  have h2 : (1 - 2 * σ) * (n : ℝ) + 2 ≤ (1 - 3 * σ / 2) * (n : ℝ) - 1 := by nlinarith [h]
  linarith

/-- `hmarginA` in its `δ`-form: for `r₀ ≥ 3·10⁵/(β²δ)`,
`(2/((β/5)/2)+1)·(n/(((β/5)/2)r₀)) ≤ δn/1000`. -/
theorem margin_marginAδ {β δ : ℝ} (hβ0 : 0 < β) (hδ0 : 0 < δ) (hβ1 : β ≤ 1)
    {r₀ n : ℕ} (h : 3 * 10 ^ 5 / (β ^ 2 * δ) ≤ (r₀ : ℝ)) (hn0 : 0 < n) :
    ((2 : ℝ) / ((β / 5) / 2) + 1) * ((n : ℝ) / (((β / 5) / 2 : ℝ) * (r₀ : ℝ))) ≤
      δ * (n : ℝ) / 1000 := by
  have hn0' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hβ2 : (0 : ℝ) < β ^ 2 := by positivity
  have hβδ : (0 : ℝ) < β ^ 2 * δ := mul_pos hβ2 hδ0
  have hr : 3 * 10 ^ 5 ≤ β ^ 2 * δ * (r₀ : ℝ) := by
    rw [div_le_iff₀ hβδ] at h
    linarith [h]
  have hr₀ : (0 : ℝ) < (r₀ : ℝ) := by nlinarith [hr, hβδ]
  have hL : ((2 : ℝ) / ((β / 5) / 2) + 1) * ((n : ℝ) / (((β / 5) / 2 : ℝ) * (r₀ : ℝ))) =
      (200 + 10 * β) / (β ^ 2 * (r₀ : ℝ)) * (n : ℝ) := by
    field_simp
    ring
  rw [hL]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < β ^ 2 * (r₀ : ℝ))]
  have h2 : (200 + 10 * β) ≤ δ * (β ^ 2 * (r₀ : ℝ)) / 1000 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 1000)]
    nlinarith [hr, hβ1, hβ0]
  have h3 : (200 + 10 * β) * (n : ℝ) ≤ (δ * (β ^ 2 * (r₀ : ℝ)) / 1000) * (n : ℝ) :=
    mul_le_mul_of_nonneg_right h2 (le_of_lt hn0')
  have h4 : (δ * (β ^ 2 * (r₀ : ℝ)) / 1000) * (n : ℝ) = δ * (n : ℝ) / 1000 * (β ^ 2 * (r₀ : ℝ)) :=
    by ring
  linarith [h3, h4.le, h4.ge]

end

end ErdosFaberLovaszConjecture
