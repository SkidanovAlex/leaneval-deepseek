import Mathlib

/-!
# Error bookkeeping for the `expNeg` "reduction to small argument" step

Given `X ≈ 2^(2p+60) · (π j / k)`, `L ≈ 2^(2p+60) · log 2` and a natural number `τ` with
`|τ - (πj/k)/log 2| ≤ 2`, `τ ≤ 6(p+2)`, set `Z = τ L - X` and `z = Z / 2^(2p+60)`,
`y = τ log 2 - πj/k`.  Then `z` approximates `y` to within `2^-(p+50)`, `|z| ≤ 32`, and
`Z` still fits in `3p + 80` bits.

The proof is purely numerical: `Z - P y = τ (L - P log 2) - (X - P πj/k)` where
`P = 2^(2p+60)`, so `|z - y| ≤ (τ + (p+3))/P ≤ (7p+15)/2^(p+60) ≤ 2^-(p+50)`; moreover
`y = log 2 · (τ - (πj/k)/log 2)` so `|y| ≤ 2 log 2 < 2`, giving `|z| ≤ 32`; finally
`|Z| = |z| P ≤ 2^(2p+65) < 2^(3p+80)` so `Z` has at most `3p+80` bits.
-/

namespace Work.Fx

theorem expNegZ (p j k : ℕ) (X L : ℤ) (τ : ℕ)
    (hp : 100 ≤ p) (hk : 1 ≤ k) (hj : j < k * (p + 2))
    (hL : |(L : ℝ) - 2 ^ (2 * p + 60) * Real.log 2| ≤ 1)
    (hX : |(X : ℝ) - 2 ^ (2 * p + 60) * (Real.pi * j / k)| ≤ ((p + 3 : ℕ) : ℝ))
    (hτ : |(τ : ℝ) - (Real.pi * j / k) / Real.log 2| ≤ 2)
    (hτb : τ ≤ 6 * (p + 2)) :
    (let Z : ℤ := (τ : ℤ) * L - X
     let z : ℝ := (Z : ℝ) / 2 ^ (2 * p + 60)
     let y : ℝ := (τ : ℝ) * Real.log 2 - Real.pi * j / k
     |z - y| ≤ 1 / 2 ^ (p + 50) ∧ |z| ≤ 32 ∧ Z.natAbs.size ≤ 3 * p + 80) := by
  dsimp only
  set P : ℝ := 2 ^ (2 * p + 60) with hP
  set Z : ℤ := (τ : ℤ) * L - X with hZ
  set z : ℝ := (Z : ℝ) / P with hzdef
  set y : ℝ := (τ : ℝ) * Real.log 2 - Real.pi * j / k with hy
  have hPpos : 0 < P := by rw [hP]; exact pow_pos (by norm_num) _
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hZcast : (Z : ℝ) = (τ : ℝ) * (L : ℝ) - (X : ℝ) := by
    rw [hZ]; push_cast; ring
  -- `y = log 2 · (τ - (πj/k)/log 2)` and hence `|y| ≤ 2 log 2`
  have hy_eq : y = Real.log 2 * ((τ : ℝ) - (Real.pi * j / k) / Real.log 2) := by
    rw [hy]; field_simp
  have habsy : |y| ≤ 2 * Real.log 2 := by
    rw [hy_eq, abs_mul, abs_of_pos hlog2pos]
    have := mul_le_mul_of_nonneg_left hτ hlog2pos.le
    linarith
  -- the exact decomposition of `Z - P·y`
  have hZy : (Z : ℝ) - P * y =
      (τ : ℝ) * ((L : ℝ) - P * Real.log 2) -
        ((X : ℝ) - P * (Real.pi * j / k)) := by
    rw [hZcast, hy]; ring
  have hzy_eq : z - y = ((Z : ℝ) - P * y) / P := by
    rw [hzdef]; field_simp
  have habsZy : |(Z : ℝ) - P * y| ≤ (τ : ℝ) + ((p + 3 : ℕ) : ℝ) := by
    rw [hZy]
    have htri : |(τ : ℝ) * ((L : ℝ) - P * Real.log 2) -
          ((X : ℝ) - P * (Real.pi * j / k))| ≤
        |(τ : ℝ) * ((L : ℝ) - P * Real.log 2)| +
          |(X : ℝ) - P * (Real.pi * j / k)| := by
      rw [abs_sub_le_iff]
      constructor <;>
        linarith [le_abs_self ((τ : ℝ) * ((L : ℝ) - P * Real.log 2)),
          neg_le_abs ((X : ℝ) - P * (Real.pi * j / k)),
          le_abs_self ((X : ℝ) - P * (Real.pi * j / k)),
          neg_le_abs ((τ : ℝ) * ((L : ℝ) - P * Real.log 2))]
    refine htri.trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg τ)]
      exact mul_le_of_le_one_right (Nat.cast_nonneg τ) hL
    · exact hX
  have hzy_abs : |z - y| ≤ ((τ : ℝ) + ((p + 3 : ℕ) : ℝ)) / P := by
    rw [hzy_eq, abs_div, abs_of_pos hPpos]
    exact div_le_div_of_nonneg_right habsZy hPpos.le
  -- numeric bounds
  have hτcast : (τ : ℝ) ≤ 6 * ((p : ℝ) + 2) := by
    have h : (τ : ℝ) ≤ ((6 * (p + 2) : ℕ) : ℝ) := by exact_mod_cast hτb
    push_cast at h
    linarith
  have hnum : (τ : ℝ) + ((p + 3 : ℕ) : ℝ) ≤ 7 * (p : ℝ) + 15 := by
    have h3 : ((p + 3 : ℕ) : ℝ) = (p : ℝ) + 3 := by push_cast; ring
    linarith
  have hPfac : P = (2 : ℝ) ^ (p + 50) * (2 : ℝ) ^ (p + 10) := by
    rw [hP, show 2 * p + 60 = (p + 50) + (p + 10) from by omega, pow_add]
  have hbig : 7 * (p : ℝ) + 15 ≤ (2 : ℝ) ^ (p + 10) := by
    have hp2 : (p : ℝ) ≤ (2 : ℝ) ^ p := by
      have := Nat.lt_two_pow_self (n := p)
      exact_mod_cast this.le
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ p := one_le_pow₀ (by norm_num)
    have h2 : (2 : ℝ) ^ (p + 10) = 2 ^ 10 * (2 : ℝ) ^ p := by rw [pow_add, mul_comm]
    rw [h2]
    nlinarith
  have hmain : ((τ : ℝ) + ((p + 3 : ℕ) : ℝ)) / P ≤ 1 / 2 ^ (p + 50) := by
    calc ((τ : ℝ) + ((p + 3 : ℕ) : ℝ)) / P ≤ (7 * (p : ℝ) + 15) / P :=
          div_le_div_of_nonneg_right hnum hPpos.le
      _ = (7 * (p : ℝ) + 15) / ((2 : ℝ) ^ (p + 50) * (2 : ℝ) ^ (p + 10)) := by
            rw [hPfac]
      _ ≤ ((2 : ℝ) ^ (p + 10)) / ((2 : ℝ) ^ (p + 50) * (2 : ℝ) ^ (p + 10)) :=
            div_le_div_of_nonneg_right hbig
              (mul_pos (pow_pos (by norm_num) _) (pow_pos (by norm_num) _)).le
      _ = 1 / (2 : ℝ) ^ (p + 50) := by
            field_simp
  have hB : |z - y| ≤ 1 / 2 ^ (p + 50) := hzy_abs.trans hmain
  -- `|z| ≤ 32`
  have hsmall : 1 / 2 ^ (p + 50) ≤ (1 : ℝ) := by
    rw [div_le_one (show (0 : ℝ) < 2 ^ (p + 50) from pow_pos (by norm_num) _)]
    exact one_le_pow₀ (by norm_num)
  have hC : |z| ≤ 32 := by
    have h1 : -(2 * Real.log 2) ≤ y ∧ y ≤ 2 * Real.log 2 := abs_le.mp habsy
    have h2 : -(1 : ℝ) ≤ z - y ∧ z - y ≤ (1 : ℝ) := abs_le.mp (hB.trans hsmall)
    have hloglt : Real.log 2 < 1 := Real.log_two_lt_d9.trans_le (by norm_num)
    rw [abs_le]
    constructor <;> linarith
  -- `Z` fits in `3p + 80` bits
  have hzP : (Z : ℝ) = z * P := by
    rw [hzdef, div_mul_cancel₀ _ (ne_of_gt hPpos)]
  have hZabs : (Z.natAbs : ℝ) = |z| * P := by
    rw [Nat.cast_natAbs, Int.cast_abs, hzP, abs_mul, abs_of_pos hPpos]
  have hZle : (Z.natAbs : ℝ) ≤ (2 : ℝ) ^ (2 * p + 65) := by
    rw [hZabs]
    calc |z| * P ≤ 32 * P := mul_le_mul_of_nonneg_right hC hPpos.le
      _ = (2 : ℝ) ^ (2 * p + 65) := by
          rw [hP, show (32 : ℝ) = 2 ^ 5 by norm_num, ← pow_add,
            show 5 + (2 * p + 60) = 2 * p + 65 from by omega]
  have hnat : Z.natAbs ≤ 2 ^ (2 * p + 65) := by exact_mod_cast hZle
  have hD : Z.natAbs.size ≤ 3 * p + 80 := by
    rw [Nat.size_le]
    calc Z.natAbs ≤ 2 ^ (2 * p + 65) := hnat
      _ < 2 ^ (3 * p + 80) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  exact ⟨hB, hC, hD⟩

end Work.Fx
