import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

theorem q0_from_bound (k : ℕ) (hk : 1 ≤ k) (cE c₂ K N q₀ A : ℝ) (ℓ : ℕ)
    (hA : 0 < A) (hcE : 0 < cE) (hc₂ : 0 < c₂) (hK : 0 < K) (hℓ : 1 ≤ ℓ)
    (hN : 0 < N) (hq₀ : 1 ≤ q₀) (hlog : 2 * A * K ^ ℓ * (c₂ / cE) ^ ℓ < Real.log N)
    (h : (cE / c₂) ^ ℓ ≤ A * K ^ ℓ * (q₀ ^ (-(1 / (2 * (k : ℝ)))) + 1 / Real.log N)) :
    q₀ ≤ (2 * A * K ^ ℓ * (c₂ / cE) ^ ℓ) ^ (2 * k) := by
  have hq₀pos : 0 < q₀ := lt_of_lt_of_le zero_lt_one hq₀
  have hbpos : 0 < 2 * A * K ^ ℓ * (c₂ / cE) ^ ℓ := by positivity
  have hdpos : 0 < (c₂ / cE) ^ ℓ := by positivity
  -- product of the two reciprocal power bases is one
  have hone : (cE / c₂) ^ ℓ * (c₂ / cE) ^ ℓ = 1 := by
    rw [← mul_pow]
    have : cE / c₂ * (c₂ / cE) = 1 := by field_simp
    rw [this, one_pow]
  -- multiply the main hypothesis by (c₂/cE)^ℓ, turning the left side into 1
  have hmul : 1 ≤ A * K ^ ℓ * (q₀ ^ (-(1 / (2 * (k : ℝ)))) + 1 / Real.log N) * (c₂ / cE) ^ ℓ := by
    have h2 := mul_le_mul_of_nonneg_right h (le_of_lt hdpos)
    rwa [hone] at h2
  set b : ℝ := 2 * A * K ^ ℓ * (c₂ / cE) ^ ℓ with hb
  have hLpos : 0 < Real.log N := by linarith
  set q : ℝ := q₀ ^ (-(1 / (2 * (k : ℝ)))) with hq
  set u : ℝ := 1 / Real.log N with hu
  -- log N exceeds b, hence 1/log N < 1/b
  have hu_lt : u < 1 / b := by
    rw [hu, hb]
    exact one_div_lt_one_div_of_lt (by positivity) hlog
  have h1 : 1 ≤ b / 2 * (q + u) := by
    have heq : A * K ^ ℓ * (q + u) * (c₂ / cE) ^ ℓ = b / 2 * (q + u) := by
      rw [hb]; ring
    rw [heq] at hmul; exact hmul
  have h2 : 2 / b ≤ q + u := by
    have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 2 / b)
    have heq2 : 2 / b * (b / 2 * (q + u)) = q + u := by field_simp
    linarith [h3, heq2]
  -- hence 1/b < q
  have hqgt : 1 / b < q := by
    have heqc : 2 / b - 1 / b = 1 / b := by ring
    linarith [h2, hu_lt, heqc]
  set z : ℝ := q₀ ^ (1 / (2 * (k : ℝ))) with hz
  have hzpos : 0 < z := by rw [hz]; exact Real.rpow_pos_of_pos hq₀pos _
  have hq_eq : q = z⁻¹ := by
    rw [hq, hz]
    exact Real.rpow_neg (le_of_lt hq₀pos) _
  -- 1/b < z⁻¹ forces z < b
  have hz_lt : z < b := by
    have hzq : z * (1 / b) < 1 := by
      have := mul_lt_mul_of_pos_left hqgt hzpos
      rw [hq_eq, mul_inv_cancel₀ (ne_of_gt hzpos)] at this
      exact this
    rw [mul_one_div, div_lt_one hbpos] at hzq
    exact hzq
  have hkpos : (0:ℝ) < (k : ℝ) := by
    have : (0:ℕ) < k := lt_of_lt_of_le zero_lt_one hk
    exact_mod_cast this
  -- raise to the power 2k
  have hfin : z ^ (2 * (k : ℝ)) < b ^ (2 * (k : ℝ)) :=
    Real.rpow_lt_rpow (le_of_lt hzpos) hz_lt (by linarith)
  have hLHS : z ^ (2 * (k : ℝ)) = q₀ := by
    rw [hz, ← Real.rpow_mul (le_of_lt hq₀pos)]
    have : (1 / (2 * (k : ℝ))) * (2 * (k : ℝ)) = 1 := by field_simp
    rw [this, Real.rpow_one]
  have hRHS : b ^ (2 * (k : ℝ)) = b ^ (2 * k) := by
    have hcast : (2 * (k:ℝ)) = ((2*k : ℕ) : ℝ) := by push_cast; ring
    rw [hcast, Real.rpow_natCast]
  rw [hLHS, hRHS] at hfin
  exact le_of_lt hfin

end Work.N8
