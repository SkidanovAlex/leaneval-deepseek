import Mathlib.Algebra.Order.Star.Real

namespace Commons.Combinatorics.Hypergraph

theorem nearfull_useful_caseA {k n : ℕ} {δ : ℝ}
    (hk : 1000 ≤ k) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 10000)
    (hnlo : k * k - k + 2 ≤ n) (hnhi : n ≤ k * k + k + 1) :
    ((k : ℝ) - 1) * ((k : ℝ) - 2) + ((n : ℝ) - 1) / ((1 - δ) * Real.sqrt (n : ℝ) - 1)
      ≤ (n : ℝ) - 2 := by
  have hkR : (1000 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk1 : 1 ≤ k := by omega
  have hkRpos : (0 : ℝ) < (k : ℝ) := by linarith
  -- n bounds in ℝ
  have hnhiR : (n : ℝ) ≤ (k : ℝ) * (k : ℝ) + (k : ℝ) + 1 := by exact_mod_cast hnhi
  have hkk : k ≤ k * k := Nat.le_mul_of_pos_right k (by omega)
  have hnloR : (k : ℝ) * (k : ℝ) - (k : ℝ) + 2 ≤ (n : ℝ) := by
    have hcast : ((k * k - k + 2 : ℕ) : ℝ) = (k : ℝ) * (k : ℝ) - (k : ℝ) + 2 := by
      push_cast [Nat.cast_sub hkk]
      ring
    calc (k : ℝ) * (k : ℝ) - (k : ℝ) + 2 = ((k * k - k + 2 : ℕ) : ℝ) := hcast.symm
      _ ≤ (n : ℝ) := by exact_mod_cast hnlo
  -- sqrt bound
  have hNnonneg : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hsfloor : (k : ℝ) - 1 / 2 ≤ Real.sqrt (n : ℝ) := by
    rw [Real.le_sqrt (by linarith) hNnonneg]
    nlinarith [hnloR]
  -- denominator positivity
  have h1mδ_nonneg : 0 ≤ 1 - δ := by linarith [hδ1]
  have hDpos : 0 < (1 - δ) * Real.sqrt (n : ℝ) - 1 := by
    have hmul : (1 - δ) * ((k : ℝ) - 1 / 2) ≤ (1 - δ) * Real.sqrt (n : ℝ) :=
      mul_le_mul_of_nonneg_left hsfloor h1mδ_nonneg
    have hden : 1 < (1 - δ) * ((k : ℝ) - 1 / 2) := by nlinarith [hkR, hδ1, hδ0]
    linarith
  -- fraction bound
  have hfrac : ((n : ℝ) - 1) / ((1 - δ) * Real.sqrt (n : ℝ) - 1) ≤ 2 * (k : ℝ) - 2 := by
    rw [div_le_iff₀ hDpos]
    have hB_le_D : (1 - δ) * ((k : ℝ) - 1 / 2) - 1 ≤ (1 - δ) * Real.sqrt (n : ℝ) - 1 := by
      have hmul : (1 - δ) * ((k : ℝ) - 1 / 2) ≤ (1 - δ) * Real.sqrt (n : ℝ) :=
        mul_le_mul_of_nonneg_left hsfloor h1mδ_nonneg
      linarith
    have hmain : (k : ℝ) * (k : ℝ) + (k : ℝ)
        ≤ (2 * (k : ℝ) - 2) * ((1 - δ) * ((k : ℝ) - 1 / 2) - 1) := by
      nlinarith [hkR, hδ1, hδ0]
    have h2k : 0 ≤ 2 * (k : ℝ) - 2 := by linarith
    have hstep : (2 * (k : ℝ) - 2) * ((1 - δ) * ((k : ℝ) - 1 / 2) - 1)
        ≤ (2 * (k : ℝ) - 2) * ((1 - δ) * Real.sqrt (n : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left hB_le_D h2k
    nlinarith [hnhiR, hmain, hstep]
  -- R bound
  have hR : 2 * (k : ℝ) - 2 ≤ (n : ℝ) - (k : ℝ) * (k : ℝ) + 3 * (k : ℝ) - 4 := by
    nlinarith [hnloR]
  have hNK : ((k : ℝ) - 1) * ((k : ℝ) - 2) + ((n : ℝ) - (k : ℝ) * (k : ℝ) + 3 * (k : ℝ) - 4)
      = (n : ℝ) - 2 := by ring
  calc ((k : ℝ) - 1) * ((k : ℝ) - 2) + ((n : ℝ) - 1) / ((1 - δ) * Real.sqrt (n : ℝ) - 1)
      ≤ ((k : ℝ) - 1) * ((k : ℝ) - 2) + ((n : ℝ) - (k : ℝ) * (k : ℝ) + 3 * (k : ℝ) - 4) := by
        linarith [hfrac, hR]
    _ = (n : ℝ) - 2 := hNK

end Commons.Combinatorics.Hypergraph