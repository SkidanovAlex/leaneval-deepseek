import Mathlib

/-!
# `Work.HP.Q44Child.exists_chain3`

Elementary number-theoretic chain lemma used in the lattice point count `ballCount_le`:
for reals `x₁ ≥ x₂ ≥ x₃ ≥ 0` there are positive integers `m₃ ∣ m₂ ∣ m₁` with
`2xᵢ < mᵢ` and `m₁ m₂ m₃ ≤ 27 (1+x₁)(1+x₂)(1+x₃)`.

The construction is a case split on the ratio `q₂/q₃`, where `qᵢ = ⌊2xᵢ⌋ + 1`.
-/

namespace Work.HP.Q44Child

/-- `a * (q ⌈/⌉ a)` is the least multiple of `a` which is `≥ q` (for `0 < a`). -/
private lemma le_nextMul {a q : ℕ} (ha : 0 < a) : q ≤ a * (q ⌈/⌉ a) := by
  simpa using le_smul_ceilDiv (a := a) (b := q) ha

/-- `a * (q ⌈/⌉ a) < q + a` (for `0 < a`). -/
private lemma nextMul_lt_add {a q : ℕ} (ha : 0 < a) : a * (q ⌈/⌉ a) < q + a := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  have h := Nat.mul_div_le (q + a - 1) a
  omega

/-- If `1 ≤ q ≤ a` then the least multiple of `a` which is `≥ q` is `a` itself. -/
private lemma nextMul_of_le {a q : ℕ} (ha : 0 < a) (h1 : 1 ≤ q) (h2 : q ≤ a) :
    a * (q ⌈/⌉ a) = a := by
  have hc : q ⌈/⌉ a = 1 := by
    apply le_antisymm
    · rw [ceilDiv_le_iff_le_mul ha]; simpa using h2
    · rcases Nat.eq_zero_or_pos (q ⌈/⌉ a) with h | h
      · exfalso
        have hle := le_nextMul (a := a) (q := q) ha
        rw [h, mul_zero] at hle
        omega
      · exact h
  rw [hc, mul_one]

/-- Case 1 arithmetic: with `q₂ ≤ q₁`, `16 q₂ ≤ 27 q₃`, and `M₁ < q₁ + q₂`, the product
`M₁ q₂ q₂` is at most `(27/8) q₁ q₂ q₃`. -/
private lemma key1 (Q1 Q2 Q3 M1 : ℝ) (hM1 : M1 < Q1 + Q2) (hQ21 : Q2 ≤ Q1)
    (hc : 16 * Q2 ≤ 27 * Q3) (hQ1 : 0 ≤ Q1) (hQ2 : 0 ≤ Q2) (_hQ3 : 0 ≤ Q3) :
    M1 * Q2 * Q2 ≤ (27 / 8) * (Q1 * Q2 * Q3) := by
  have hr : 0 ≤ 2 * Q1 - M1 := by linarith
  have hprod1 : 0 ≤ (2 * Q1 - M1) * Q2 * Q2 := mul_nonneg (mul_nonneg hr hQ2) hQ2
  have hstep1 : M1 * Q2 * Q2 ≤ (2 * Q1) * Q2 * Q2 := by nlinarith [hprod1]
  have hr2 : 0 ≤ (27 / 8) * Q3 - 2 * Q2 := by linarith
  have hprod2 : 0 ≤ Q1 * Q2 * ((27 / 8) * Q3 - 2 * Q2) :=
    mul_nonneg (mul_nonneg hQ1 hQ2) hr2
  have hstep2 : (2 * Q1) * Q2 * Q2 ≤ (27 / 8) * (Q1 * Q2 * Q3) := by nlinarith [hprod2]
  linarith [hstep1, hstep2]

/-- Case 2, sub-case `q₁ ≤ M₂`: with `M₂ < (43/27) q₂`, `q₂ ≤ q₁`, the product `M₂ M₂ q₃`
is at most `(27/8) q₁ q₂ q₃`. -/
private lemma key2a (Q1 Q2 Q3 M2 : ℝ) (hM2 : M2 < (43 / 27) * Q2) (hQ21 : Q2 ≤ Q1)
    (hM2n : 0 ≤ M2) (hQ1 : 0 ≤ Q1) (hQ2 : 0 ≤ Q2) (hQ3 : 0 ≤ Q3) :
    M2 * M2 * Q3 ≤ (27 / 8) * (Q1 * Q2 * Q3) := by
  have hM2a : M2 ≤ (43 / 27) * Q1 := by
    have : (43 / 27) * Q2 ≤ (43 / 27) * Q1 := by nlinarith
    linarith
  have hsq : M2 * M2 ≤ ((43 / 27) * Q1) * ((43 / 27) * Q2) :=
    mul_le_mul hM2a (le_of_lt hM2) hM2n (by positivity)
  have hnum : (43 / 27 : ℝ) ^ 2 ≤ 27 / 8 := by norm_num
  have hQ12 : 0 ≤ Q1 * Q2 := mul_nonneg hQ1 hQ2
  have hsq2 : ((43 / 27 : ℝ) * Q1) * ((43 / 27) * Q2) ≤ (27 / 8) * (Q1 * Q2) := by
    have : ((43 / 27 : ℝ) * Q1) * ((43 / 27) * Q2) = (43 / 27) ^ 2 * (Q1 * Q2) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hnum hQ12
  calc M2 * M2 * Q3 = (M2 * M2) * Q3 := by ring
    _ ≤ ((27 / 8) * (Q1 * Q2)) * Q3 := mul_le_mul_of_nonneg_right (le_trans hsq hsq2) hQ3
    _ = (27 / 8) * (Q1 * Q2 * Q3) := by ring

/-- Case 2, sub-case `M₂ < q₁`: with `M₁ < q₁ + M₂`, `M₂ < (43/27) q₂`, the product
`M₁ M₂ q₃` is at most `(27/8) q₁ q₂ q₃`. -/
private lemma key2b (Q1 Q2 Q3 M1 M2 : ℝ) (hM1 : M1 < Q1 + M2) (hM2Q1 : M2 < Q1)
    (hM2 : M2 < (43 / 27) * Q2) (hM2n : 0 ≤ M2) (hQ1 : 0 ≤ Q1) (hQ2 : 0 ≤ Q2)
    (hQ3 : 0 ≤ Q3) :
    M1 * M2 * Q3 ≤ (27 / 8) * (Q1 * Q2 * Q3) := by
  have hM1le : M1 ≤ 2 * Q1 := by linarith
  have hprod : M1 * M2 ≤ (2 * Q1) * ((43 / 27) * Q2) :=
    mul_le_mul hM1le (le_of_lt hM2) hM2n (by positivity)
  have hnum : (2 * Q1) * ((43 / 27) * Q2) ≤ (27 / 8) * (Q1 * Q2) := by
    have h : (86 / 27 : ℝ) ≤ 27 / 8 := by norm_num
    have hQ12 : 0 ≤ Q1 * Q2 := mul_nonneg hQ1 hQ2
    calc (2 * Q1) * ((43 / 27) * Q2) = (86 / 27) * (Q1 * Q2) := by ring
      _ ≤ (27 / 8) * (Q1 * Q2) := mul_le_mul_of_nonneg_right h hQ12
  calc M1 * M2 * Q3 = (M1 * M2) * Q3 := by ring
    _ ≤ ((27 / 8) * (Q1 * Q2)) * Q3 := mul_le_mul_of_nonneg_right (le_trans hprod hnum) hQ3
    _ = (27 / 8) * (Q1 * Q2 * Q3) := by ring

theorem exists_chain3 {x1 x2 x3 : ℝ} (h1 : 0 ≤ x1) (h21 : x2 ≤ x1) (h32 : x3 ≤ x2) (h3 : 0 ≤ x3) :
    ∃ m1 m2 m3 : ℕ, 0 < m1 ∧ 0 < m2 ∧ 0 < m3 ∧ m3 ∣ m2 ∧ m2 ∣ m1 ∧
      (2 * x1 < (m1 : ℝ)) ∧ (2 * x2 < (m2 : ℝ)) ∧ (2 * x3 < (m3 : ℝ)) ∧
      ((m1 : ℝ) * (m2 : ℝ) * (m3 : ℝ)) ≤ 27 * (1 + x1) * (1 + x2) * (1 + x3) := by
  -- the integers `qᵢ = ⌊2xᵢ⌋ + 1` satisfy `2xᵢ < qᵢ` and `q₁ ≥ q₂ ≥ q₃ ≥ 1`.
  set q1 : ℕ := Nat.floor (2 * x1) + 1 with hq1
  set q2 : ℕ := Nat.floor (2 * x2) + 1 with hq2
  set q3 : ℕ := Nat.floor (2 * x3) + 1 with hq3
  have hq1g : 2 * x1 < (q1 : ℝ) := by
    rw [hq1]; push_cast; exact Nat.lt_floor_add_one (2 * x1)
  have hq2g : 2 * x2 < (q2 : ℝ) := by
    rw [hq2]; push_cast; exact Nat.lt_floor_add_one (2 * x2)
  have hq3g : 2 * x3 < (q3 : ℝ) := by
    rw [hq3]; push_cast; exact Nat.lt_floor_add_one (2 * x3)
  have hq1le : (q1 : ℝ) ≤ 2 * (1 + x1) := by
    have hf := Nat.floor_le (by linarith : (0 : ℝ) ≤ 2 * x1)
    rw [hq1]; push_cast; linarith
  have hq2le : (q2 : ℝ) ≤ 2 * (1 + x2) := by
    have hf := Nat.floor_le (by linarith : (0 : ℝ) ≤ 2 * x2)
    rw [hq2]; push_cast; linarith
  have hq3le : (q3 : ℝ) ≤ 2 * (1 + x3) := by
    have hf := Nat.floor_le (by linarith : (0 : ℝ) ≤ 2 * x3)
    rw [hq3]; push_cast; linarith
  have hq21 : q2 ≤ q1 := by
    rw [hq2, hq1]
    exact Nat.add_le_add_right (Nat.floor_mono (by linarith : 2 * x2 ≤ 2 * x1)) 1
  have hq32 : q3 ≤ q2 := by
    rw [hq3, hq2]
    exact Nat.add_le_add_right (Nat.floor_mono (by linarith : 2 * x3 ≤ 2 * x2)) 1
  have hq3pos : 0 < q3 := by rw [hq3]; omega
  have hq2pos : 0 < q2 := lt_of_lt_of_le hq3pos hq32
  have hq1pos : 0 < q1 := lt_of_lt_of_le hq2pos hq21
  -- nonnegativity of the `qᵢ` as reals
  have hQ1n : (0 : ℝ) ≤ (q1 : ℝ) := by positivity
  have hQ2n : (0 : ℝ) ≤ (q2 : ℝ) := by positivity
  have hQ3n : (0 : ℝ) ≤ (q3 : ℝ) := by positivity
  have hQ21 : (q2 : ℝ) ≤ (q1 : ℝ) := by exact_mod_cast hq21
  have hQ32 : (q3 : ℝ) ≤ (q2 : ℝ) := by exact_mod_cast hq32
  -- bound of the `q`-product by `8 (1+x₁)(1+x₂)(1+x₃)`
  have hqprod : (q1 : ℝ) * (q2 : ℝ) * (q3 : ℝ) ≤ 8 * ((1 + x1) * (1 + x2) * (1 + x3)) := by
    have hp1 : (0 : ℝ) ≤ 2 * (1 + x1) := by linarith
    have hp2 : (0 : ℝ) ≤ 2 * (1 + x2) := by linarith
    have h12 : (q1 : ℝ) * (q2 : ℝ) ≤ (2 * (1 + x1)) * (2 * (1 + x2)) :=
      mul_le_mul hq1le hq2le hQ2n hp1
    have h123 : ((q1 : ℝ) * (q2 : ℝ)) * (q3 : ℝ) ≤
        ((2 * (1 + x1)) * (2 * (1 + x2))) * (2 * (1 + x3)) :=
      mul_le_mul h12 hq3le hQ3n (mul_nonneg hp1 hp2)
    calc (q1 : ℝ) * (q2 : ℝ) * (q3 : ℝ)
        = ((q1 : ℝ) * (q2 : ℝ)) * (q3 : ℝ) := by ring
      _ ≤ ((2 * (1 + x1)) * (2 * (1 + x2))) * (2 * (1 + x3)) := h123
      _ = 8 * ((1 + x1) * (1 + x2) * (1 + x3)) := by ring
  have hbound : (27 / 8) * ((q1 : ℝ) * (q2 : ℝ) * (q3 : ℝ))
      ≤ 27 * (1 + x1) * (1 + x2) * (1 + x3) := by
    calc (27 / 8) * ((q1 : ℝ) * (q2 : ℝ) * (q3 : ℝ))
        ≤ (27 / 8) * (8 * ((1 + x1) * (1 + x2) * (1 + x3))) :=
          mul_le_mul_of_nonneg_left hqprod (by norm_num)
      _ = 27 * (1 + x1) * (1 + x2) * (1 + x3) := by ring
  by_cases hcase : 16 * q2 ≤ 27 * q3
  · -- Case 1: `q₂` is not much larger than `q₃`.
    set m3 : ℕ := q2 with hm3
    set m2 : ℕ := q2 with hm2
    set m1 : ℕ := q2 * (q1 ⌈/⌉ q2) with hm1
    have hm1pos : 0 < m1 := by
      rw [hm1]
      have h := le_nextMul (a := q2) (q := q1) hq2pos
      omega
    have hm2pos : 0 < m2 := by rw [hm2]; exact hq2pos
    have hm3pos : 0 < m3 := by rw [hm3]; exact hq2pos
    have hdvd32 : m3 ∣ m2 := by rw [hm3, hm2]
    have hdvd21 : m2 ∣ m1 := by rw [hm2, hm1]; exact dvd_mul_right _ _
    have hlt1 : 2 * x1 < (m1 : ℝ) := by
      have h := le_nextMul (a := q2) (q := q1) hq2pos
      have hR : (q1 : ℝ) ≤ (m1 : ℝ) := by
        rw [hm1]
        exact_mod_cast h
      linarith [hq1g, hR]
    have hlt2 : 2 * x2 < (m2 : ℝ) := by rw [hm2]; exact hq2g
    have hlt3 : 2 * x3 < (m3 : ℝ) := by
      rw [hm3]
      linarith [hq3g, hQ32]
    have hprod : (m1 : ℝ) * (m2 : ℝ) * (m3 : ℝ) ≤ (27 / 8) * ((q1 : ℝ) * (q2 : ℝ) * (q3 : ℝ)) := by
      have hM1 : (m1 : ℝ) < (q1 : ℝ) + (q2 : ℝ) := by
        rw [hm1]
        have h := nextMul_lt_add (a := q2) (q := q1) hq2pos
        push_cast
        exact_mod_cast h
      have hcR : 16 * (q2 : ℝ) ≤ 27 * (q3 : ℝ) := by exact_mod_cast hcase
      have h := key1 (q1 : ℝ) (q2 : ℝ) (q3 : ℝ) (m1 : ℝ) hM1 hQ21 hcR hQ1n hQ2n hQ3n
      rw [hm2, hm3]
      exact h
    exact ⟨m1, m2, m3, hm1pos, hm2pos, hm3pos, hdvd32, hdvd21, hlt1, hlt2, hlt3,
      le_trans hprod hbound⟩
  · -- Case 2: `q₂ > (27/16) q₃`.
    have hcR : 27 * (q3 : ℝ) < 16 * (q2 : ℝ) := by
      have h' : 27 * q3 < 16 * q2 := Nat.lt_of_not_le hcase
      exact_mod_cast h'
    have hQ3lt : (q3 : ℝ) < (16 / 27) * (q2 : ℝ) := by linarith
    set m3 : ℕ := q3 with hm3
    set m2 : ℕ := q3 * (q2 ⌈/⌉ q3) with hm2
    set m1 : ℕ := m2 * (q1 ⌈/⌉ m2) with hm1
    have hq2lem2 : q2 ≤ m2 := le_nextMul (a := q3) (q := q2) hq3pos
    have hm2pos : 0 < m2 := lt_of_lt_of_le hq2pos hq2lem2
    have hm2ge : (q2 : ℝ) ≤ (m2 : ℝ) := by exact_mod_cast hq2lem2
    have hm2n : (0 : ℝ) ≤ m2 := le_trans (by positivity : (0:ℝ) ≤ (q2:ℝ)) hm2ge
    have hm2lt : (m2 : ℝ) < (q2 : ℝ) + (q3 : ℝ) := by
      rw [hm2]
      have h := nextMul_lt_add (a := q3) (q := q2) hq3pos
      push_cast
      exact_mod_cast h
    have hm2lt2 : (m2 : ℝ) < (43 / 27) * (q2 : ℝ) := by linarith
    have hm1ge : (q1 : ℝ) ≤ (m1 : ℝ) := by
      rw [hm1]
      have h := le_nextMul (a := m2) (q := q1) hm2pos
      exact_mod_cast h
    have hm1lt : (m1 : ℝ) < (q1 : ℝ) + (m2 : ℝ) := by
      rw [hm1]
      have h := nextMul_lt_add (a := m2) (q := q1) hm2pos
      push_cast
      exact_mod_cast h
    have hq1lem1 : q1 ≤ m1 := le_nextMul (a := m2) (q := q1) hm2pos
    have hm1pos : 0 < m1 := lt_of_lt_of_le hq1pos hq1lem1
    have hm3pos : 0 < m3 := by rw [hm3]; exact hq3pos
    have hdvd32 : m3 ∣ m2 := by rw [hm3, hm2]; exact dvd_mul_right _ _
    have hdvd21 : m2 ∣ m1 := by rw [hm1]; exact dvd_mul_right _ _
    have hlt1 : 2 * x1 < (m1 : ℝ) := lt_of_lt_of_le hq1g hm1ge
    have hlt2 : 2 * x2 < (m2 : ℝ) := lt_of_lt_of_le hq2g hm2ge
    have hlt3 : 2 * x3 < (m3 : ℝ) := by rw [hm3]; exact hq3g
    have hprod : (m1 : ℝ) * (m2 : ℝ) * (m3 : ℝ) ≤ (27 / 8) * ((q1 : ℝ) * (q2 : ℝ) * (q3 : ℝ)) := by
      by_cases hq1m2 : q1 ≤ m2
      · -- sub-case `q₁ ≤ m₂`: then `m₁ = m₂`.
        have hm1eq : m1 = m2 := by
          rw [hm1]
          exact nextMul_of_le hm2pos (by omega) hq1m2
        have h := key2a (q1 : ℝ) (q2 : ℝ) (q3 : ℝ) (m2 : ℝ) hm2lt2 hQ21 hm2n hQ1n hQ2n hQ3n
        rw [hm1eq, hm3]
        exact h
      · -- sub-case `m₂ < q₁`.
        have hm2q1 : (m2 : ℝ) < (q1 : ℝ) := by
          have h' : m2 < q1 := Nat.lt_of_not_le hq1m2
          exact_mod_cast h'
        have h := key2b (q1 : ℝ) (q2 : ℝ) (q3 : ℝ) (m1 : ℝ) (m2 : ℝ)
          hm1lt hm2q1 hm2lt2 hm2n hQ1n hQ2n hQ3n
        rw [hm3]
        exact h
    exact ⟨m1, m2, m3, hm1pos, hm2pos, hm3pos, hdvd32, hdvd21, hlt1, hlt2, hlt3,
      le_trans hprod hbound⟩

end Work.HP.Q44Child
