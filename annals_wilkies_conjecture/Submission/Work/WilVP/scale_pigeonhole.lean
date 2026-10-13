import Mathlib

namespace Work.WilVP

/-- Numeric core of the scale pigeonhole: if `0 < a, b, c` and `a / b ≤ b * (a / c)` then
`c ≤ b ^ 2`.  (Multiplying by `b * c > 0` and cancelling `a > 0`.) -/
private lemma key_num (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a / b ≤ b * (a / c)) : c ≤ b ^ 2 := by
  have h1 : a ≤ b * (a / c) * b := (div_le_iff₀ hb).mp h
  have hdc : a / c * c = a := div_mul_cancel₀ a (ne_of_gt hc)
  have h1' : a * c ≤ (b * (a / c) * b) * c := mul_le_mul_of_nonneg_right h1 (le_of_lt hc)
  have h2 : a * c ≤ b * b * a := by
    calc a * c ≤ (b * (a / c) * b) * c := h1'
      _ = b * ((a / c) * c) * b := by ring
      _ = b * a * b := by rw [hdc]
      _ = b * b * a := by ring
  have h3 : a * c ≤ a * (b ^ 2) := by nlinarith [h2]
  exact le_of_mul_le_mul_left h3 ha

/-- **Scale separation.**  For a positive `t`, a factor `lam ≥ 4N²+1` and `j₁ < j₂`, the two
"windows" `[t/lam^j/(2N), 2N·t/lam^j]` (`j = j₁, j₂`) are disjoint. -/
private lemma scale_key (N : ℕ) (hN : 0 < N) {t lam : ℝ} (ht : 0 < t)
    (hlam : 4 * (N : ℝ) ^ 2 + 1 ≤ lam) {j₁ j₂ : ℕ} (hlt : j₁ < j₂) {b : ℝ}
    (h1 : t / lam ^ j₁ / (2 * (N : ℝ)) ≤ b ∧ b ≤ 2 * (N : ℝ) * (t / lam ^ j₁))
    (h2 : t / lam ^ j₂ / (2 * (N : ℝ)) ≤ b ∧ b ≤ 2 * (N : ℝ) * (t / lam ^ j₂)) :
    False := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have h2N : (0 : ℝ) < 2 * (N : ℝ) := by linarith
  have hlam1 : 1 ≤ lam := by nlinarith [sq_nonneg (N : ℝ), hlam]
  have hlampos : 0 < lam := lt_of_lt_of_le one_pos hlam1
  have hxpos : 0 < t / lam ^ j₁ := div_pos ht (pow_pos hlampos j₁)
  -- `lam ^ j₁ * lam ≤ lam ^ j₂`
  have hle1 : lam ^ j₁ * lam ≤ lam ^ j₂ := by
    have : lam ^ (j₁ + 1) ≤ lam ^ j₂ :=
      pow_le_pow_right₀ hlam1 (Nat.succ_le_of_lt hlt)
    simpa [pow_succ] using this
  -- hence `t / lam ^ j₂ ≤ t / lam ^ j₁ / lam`
  have hstep : t / lam ^ j₂ ≤ t / lam ^ j₁ / lam := by
    have h2' : t / lam ^ j₂ ≤ t / (lam ^ j₁ * lam) := by
      rw [div_le_div_iff₀ (pow_pos hlampos j₂)
        (mul_pos (pow_pos hlampos j₁) hlampos)]
      exact mul_le_mul_of_nonneg_left hle1 (le_of_lt ht)
    rwa [div_div]
  -- chain the two windows
  have hchain : t / lam ^ j₁ / (2 * (N : ℝ)) ≤ 2 * (N : ℝ) * (t / lam ^ j₁ / lam) := by
    have hm : 2 * (N : ℝ) * (t / lam ^ j₂) ≤ 2 * (N : ℝ) * (t / lam ^ j₁ / lam) :=
      mul_le_mul_of_nonneg_left hstep (by linarith)
    linarith [h1.1, h2.2, hm]
  have hk : lam ≤ (2 * (N : ℝ)) ^ 2 :=
    key_num (t / lam ^ j₁) (2 * (N : ℝ)) lam hxpos h2N hlampos hchain
  have hk2 : lam ≤ 4 * (N : ℝ) ^ 2 := by nlinarith [hk]
  nlinarith [hk2, hlam]

theorem scale_pigeonhole (N : ℕ) (hN : 0 < N) (B : Set ℝ) (hB : B.encard ≤ N) {t : ℝ}
    (ht : 0 < t) :
    ∃ j ∈ Finset.range (N + 1), ∀ b ∈ B,
      ¬ (t / (4 * (N : ℝ) ^ 2 + 1) ^ j / (2 * N) ≤ b ∧
          b ≤ 2 * N * (t / (4 * (N : ℝ) ^ 2 + 1) ^ j)) := by
  classical
  by_contra hcon
  push Not at hcon
  -- `hcon : ∀ j, j ∈ range (N+1) → ∃ b, b ∈ B ∧ (window j b)`
  let w : ℕ → ℝ := fun j =>
    if h : j ∈ Finset.range (N + 1) then (hcon j h).choose else 0
  have hw : ∀ j (hj : j ∈ Finset.range (N + 1)),
      w j ∈ B ∧ (t / (4 * (N : ℝ) ^ 2 + 1) ^ j / (2 * N) ≤ w j ∧
                 w j ≤ 2 * N * (t / (4 * (N : ℝ) ^ 2 + 1) ^ j)) := by
    intro j hj
    simp only [w, dite_eq_left hj]
    exact (hcon j hj).choose_spec
  -- the chosen witnesses are pairwise distinct
  have hinj : Set.InjOn w (↑(Finset.range (N + 1)) : Set ℕ) := by
    intro j₁ hj₁ j₂ hj₂ heq
    simp only [Finset.mem_coe, Finset.mem_range] at hj₁ hj₂
    rcases lt_trichotomy j₁ j₂ with hlt | heq' | hgt
    · exfalso
      have h1 := (hw j₁ (Finset.mem_range.mpr hj₁)).2
      have h2 := (hw j₂ (Finset.mem_range.mpr hj₂)).2
      rw [heq] at h1
      exact scale_key N hN ht (le_refl (4 * (N : ℝ) ^ 2 + 1)) hlt h1 h2
    · exact heq'
    · exfalso
      have h1 := (hw j₁ (Finset.mem_range.mpr hj₁)).2
      have h2 := (hw j₂ (Finset.mem_range.mpr hj₂)).2
      rw [← heq] at h2
      exact scale_key N hN ht (le_refl (4 * (N : ℝ) ^ 2 + 1)) hgt h2 h1
  set T : Finset ℝ := (Finset.range (N + 1)).image w with hT
  have hcard : T.card = N + 1 := by
    rw [hT, Finset.card_image_of_injOn hinj, Finset.card_range]
  have hTB : (T : Set ℝ) ⊆ B := by
    intro x hx
    simp only [Finset.mem_coe] at hx
    rw [hT] at hx
    obtain ⟨j, hj, hxj⟩ := Finset.mem_image.mp hx
    rw [← hxj]
    exact (hw j hj).1
  have hle : ((N + 1 : ℕ) : ℕ∞) ≤ B.encard := by
    have h1 : (T : Set ℝ).encard ≤ B.encard := Set.encard_le_encard hTB
    have h2 : (T : Set ℝ).encard = (T.card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard T
    rw [h2, hcard] at h1
    exact h1
  have hnat : N + 1 ≤ N :=
    ENat.natCast_le_natCast.mp (le_trans hle hB)
  omega

end Work.WilVP
