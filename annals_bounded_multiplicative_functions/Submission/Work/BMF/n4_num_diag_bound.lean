import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Real

/-- Growth of `P` against any power of `log P`: for `a, b > 0` and `n : ℕ`, one has
`a (log P)^n ≤ b P` for all sufficiently large real `P`. -/
lemma log_pow_mul_le_linear (n : ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ P₀ : ℝ, ∀ P : ℝ, P₀ ≤ P → a * (Real.log P) ^ n ≤ b * P := by
  have hba : 0 < b / a := div_pos hb ha
  have htend : Filter.Tendsto (fun x : ℝ => Real.log x ^ n / (1 * x + 0)) Filter.atTop (nhds 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 0 n (by norm_num)
  have htend' : Filter.Tendsto (fun x : ℝ => Real.log x ^ n / x) Filter.atTop (nhds 0) := by
    simpa only [one_mul, add_zero] using htend
  have hev : ∀ᶠ x in Filter.atTop, Real.log x ^ n / x ≤ b / a :=
    htend'.eventually (eventually_le_nhds hba)
  obtain ⟨Q₀, hQ₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max Q₀ 1, ?_⟩
  intro P hP
  have hP1 : 1 ≤ P := le_trans (le_max_right _ _) hP
  have hPpos : 0 < P := lt_of_lt_of_le zero_lt_one hP1
  have hle : Real.log P ^ n ≤ (b / a) * P := by
    have h := hQ₀ P (le_trans (le_max_left _ _) hP)
    rwa [div_le_iff₀ hPpos] at h
  calc a * Real.log P ^ n ≤ a * ((b / a) * P) := mul_le_mul_of_nonneg_left hle ha.le
    _ = b * P := by rw [← mul_assoc, mul_div_cancel₀ b ha.ne']

/-- `N log N ≤ P^(ℓ-1) · (ℓ-1) log P` when `1 < P`, `3 ≤ N ≤ P^(ℓ-1)` and `2 ≤ ℓ`. -/
lemma logN_mul_le (ℓ : ℕ) (_hℓ : 2 ≤ ℓ) (P N : ℝ) (hP : 1 < P) (hN : 3 ≤ N)
    (hNP : N ≤ P ^ (ℓ - 1)) :
    N * Real.log N ≤ P ^ (ℓ - 1) * (((ℓ - 1 : ℕ) : ℝ) * Real.log P) := by
  have hNpos : 0 < N := by linarith
  have hPpos : 0 < P := by linarith
  have hPpow : 0 < P ^ (ℓ - 1) := by positivity
  have hlogN : Real.log N ≤ ((ℓ - 1 : ℕ) : ℝ) * Real.log P := by
    have h1 : Real.log N ≤ Real.log (P ^ (ℓ - 1)) := Real.log_le_log hNpos hNP
    rwa [Real.log_pow] at h1
  exact mul_le_mul hNP hlogN (Real.log_nonneg (by linarith)) hPpow.le

lemma n4_num_diag_bound (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (C₁ K : ℝ) (hC₁ : 0 < C₁) (hK : 0 < K) :
    ∃ P₀ : ℝ, ∀ P N C₀ : ℝ, P₀ ≤ P → 3 ≤ N → N ≤ P ^ (ℓ - 1) → 1 / Real.log P ≤ C₀ →
      (C₁ * pi0 P) ^ ℓ * ((ℓ + 1 : ℕ) : ℝ) ^ ℓ ≤
        K * C₀ * pi0 P ^ (2 * ℓ) / N * (1 / Real.log N) := by
  have hℓm1 : (ℓ - 1 : ℕ) + 1 = ℓ := Nat.sub_add_cancel (by omega : 1 ≤ ℓ)
  have hℓm1pos : (0 : ℝ) < ((ℓ - 1 : ℕ) : ℝ) := by
    have : 0 < ℓ - 1 := by omega
    exact_mod_cast this
  have hbase : (0 : ℝ) < ((ℓ + 1 : ℕ) : ℝ) := by
    have : 0 < ℓ + 1 := by omega
    exact_mod_cast this
  have hprod : 0 < C₁ ^ ℓ * (((ℓ + 1 : ℕ) : ℝ)) ^ ℓ * (((ℓ - 1 : ℕ) : ℝ)) :=
    mul_pos (mul_pos (pow_pos hC₁ ℓ) (pow_pos hbase ℓ)) hℓm1pos
  obtain ⟨Pg, hPg⟩ :=
    log_pow_mul_le_linear (ℓ + 2) (C₁ ^ ℓ * (((ℓ + 1 : ℕ) : ℝ)) ^ ℓ * (((ℓ - 1 : ℕ) : ℝ))) K
      hprod hK
  refine ⟨max Pg 4, ?_⟩
  intro P N C₀ hP hN3 hNP hC₀
  have hP4 : 4 ≤ P := le_trans (le_max_right _ _) hP
  have hP1 : 1 < P := by linarith
  have hPpos : 0 < P := by linarith
  have hL : 0 < Real.log P := Real.log_pos hP1
  have hNpos : 0 < N := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith : 1 < N)
  have hgr : C₁ ^ ℓ * (((ℓ + 1 : ℕ) : ℝ)) ^ ℓ * (((ℓ - 1 : ℕ) : ℝ)) * (Real.log P) ^ (ℓ + 2)
      ≤ K * P := hPg P (le_trans (le_max_left _ _) hP)
  have hNlogN := logN_mul_le ℓ hℓ P N hP1 hN3 hNP
  have hkey : C₁ ^ ℓ * (((ℓ + 1 : ℕ) : ℝ)) ^ ℓ * (N * Real.log N) * (Real.log P) ^ ℓ
      ≤ K * C₀ * P ^ ℓ := by
    have hnn1 : (0 : ℝ) ≤ C₁ ^ ℓ * (((ℓ + 1 : ℕ) : ℝ)) ^ ℓ * (Real.log P) ^ ℓ :=
      mul_nonneg (mul_nonneg (pow_nonneg hC₁.le ℓ) (pow_nonneg hbase.le ℓ)) (pow_nonneg hL.le ℓ)
    have hnn2 : (0 : ℝ) ≤ P ^ (ℓ - 1) / Real.log P :=
      div_nonneg (pow_nonneg hPpos.le _) hL.le
    calc C₁ ^ ℓ * (((ℓ + 1 : ℕ) : ℝ)) ^ ℓ * (N * Real.log N) * (Real.log P) ^ ℓ
        = C₁ ^ ℓ * (((ℓ + 1 : ℕ) : ℝ)) ^ ℓ * (Real.log P) ^ ℓ * (N * Real.log N) := by ring
      _ ≤ C₁ ^ ℓ * (((ℓ + 1 : ℕ) : ℝ)) ^ ℓ * (Real.log P) ^ ℓ
            * (P ^ (ℓ - 1) * (((ℓ - 1 : ℕ) : ℝ) * Real.log P)) :=
          mul_le_mul_of_nonneg_left hNlogN hnn1
      _ = (C₁ ^ ℓ * (((ℓ + 1 : ℕ) : ℝ)) ^ ℓ * (((ℓ - 1 : ℕ) : ℝ)) * (Real.log P) ^ (ℓ + 2))
            * (P ^ (ℓ - 1) / Real.log P) := by
          rw [pow_add]
          field_simp
      _ ≤ (K * P) * (P ^ (ℓ - 1) / Real.log P) :=
          mul_le_mul_of_nonneg_right hgr hnn2
      _ = K * P ^ ℓ / Real.log P := by
          rw [← mul_div_assoc, mul_assoc K P (P ^ (ℓ - 1)), ← pow_succ' P (ℓ - 1), hℓm1]
      _ ≤ K * C₀ * P ^ ℓ := by
          rw [div_le_iff₀ hL]
          have h1 : 1 ≤ C₀ * Real.log P := by
            have h2 : (1 / Real.log P) * Real.log P ≤ C₀ * Real.log P :=
              mul_le_mul_of_nonneg_right hC₀ hL.le
            rwa [one_div_mul_cancel hL.ne'] at h2
          calc K * P ^ ℓ = K * P ^ ℓ * 1 := by ring
            _ ≤ K * P ^ ℓ * (C₀ * Real.log P) :=
                mul_le_mul_of_nonneg_left h1 (mul_nonneg hK.le (pow_nonneg hPpos.le ℓ))
            _ = K * C₀ * P ^ ℓ * Real.log P := by ring
  have hX : C₁ ^ ℓ * (((ℓ + 1 : ℕ) : ℝ)) ^ ℓ * (N * Real.log N)
      ≤ K * C₀ * P ^ ℓ / (Real.log P) ^ ℓ := by
    rw [le_div_iff₀ (pow_pos hL ℓ)]
    exact hkey
  rw [pi0, two_mul, pow_add, mul_pow, div_pow]
  rw [mul_one_div, div_div]
  rw [le_div_iff₀ (mul_pos hNpos hlogN)]
  calc C₁ ^ ℓ * (P ^ ℓ / (Real.log P) ^ ℓ) * (((ℓ + 1 : ℕ) : ℝ)) ^ ℓ * (N * Real.log N)
      = (C₁ ^ ℓ * (((ℓ + 1 : ℕ) : ℝ)) ^ ℓ * (N * Real.log N)) * (P ^ ℓ / (Real.log P) ^ ℓ) := by
        ring_nf
    _ ≤ (K * C₀ * P ^ ℓ / (Real.log P) ^ ℓ) * (P ^ ℓ / (Real.log P) ^ ℓ) :=
        mul_le_mul_of_nonneg_right hX
          (div_nonneg (pow_nonneg hPpos.le ℓ) (pow_nonneg hL.le ℓ))
    _ = K * C₀ * ((P ^ ℓ / (Real.log P) ^ ℓ) * (P ^ ℓ / (Real.log P) ^ ℓ)) := by ring_nf

end Work.BMF
