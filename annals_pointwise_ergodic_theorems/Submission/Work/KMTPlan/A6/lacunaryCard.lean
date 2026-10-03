import Mathlib
import Submission.Work.KMTContract.Defs

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators

/-- **Counting a lacunary set of scales.**  If `a` is `Λ`-lacunary with `Λ > 1` and `a n ≥ 1` for
every `n`, then the set of indices `n` for which `a n < B` (with `B ≥ 1`) has at most
`log B / log Λ + 1` elements.

Indeed a `Λ`-lacunary sequence with `a n ≥ 1` grows at least like `Λ ^ n` (proved below as
`hpow`), so `Λ ^ n ≤ a n < B`, hence `n ≤ log B / log Λ`; the claim follows from
`Nat.le_floor` and `Nat.floor_le`. -/
theorem lacunaryCard (Λ : ℝ≥0) (hΛ : 1 < Λ) (a : ℕ → ℝ≥0)
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
    (s : Finset ℕ) (B : ℝ) (hB : 1 ≤ B) (hs : ∀ n ∈ s, (a n : ℝ) < B) :
    (s.card : ℝ) ≤ Real.log B / Real.log Λ + 1 := by
  have hΛ1 : (1 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
  have hlogΛ : 0 < Real.log (Λ : ℝ) := Real.log_pos hΛ1
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  -- a lacunary sequence with `a n ≥ 1` grows at least like `Λ ^ n`
  have hpow : ∀ n, Λ ^ n ≤ a n := by
    intro n
    induction n with
    | zero => simpa using ha1 0
    | succ k ih =>
      have hpos : (0 : ℝ≥0) < a k := lt_of_lt_of_le zero_lt_one (ha1 k)
      have hstep : Λ * a k ≤ a (k + 1) := le_of_lt ((lt_div_iff₀ hpos).mp (ha k))
      calc Λ ^ (k + 1) = Λ * Λ ^ k := pow_succ' Λ k
        _ ≤ Λ * a k := mul_le_mul_of_nonneg_left ih (by positivity)
        _ ≤ a (k + 1) := hstep
  -- every index of `s` is at most `log B / log Λ`
  have key : ∀ n ∈ s, (n : ℝ) ≤ Real.log B / Real.log Λ := by
    intro n hn
    have h1 : (Λ : ℝ) ^ n ≤ (a n : ℝ) := by exact_mod_cast hpow n
    have h2 : (Λ : ℝ) ^ n ≤ B := le_of_lt (lt_of_le_of_lt h1 (hs n hn))
    have h3 : Real.log ((Λ : ℝ) ^ n) ≤ Real.log B :=
      Real.log_le_log (pow_pos (by linarith) n) h2
    rw [Real.log_pow] at h3
    exact (le_div_iff₀ hlogΛ).mpr h3
  have hsub : s ⊆ Finset.range (Nat.floor (Real.log B / Real.log Λ) + 1) := by
    intro n hn
    simp only [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.le_floor (key n hn)
  have hcard : s.card ≤ Nat.floor (Real.log B / Real.log Λ) + 1 := by
    calc s.card ≤ (Finset.range (Nat.floor (Real.log B / Real.log Λ) + 1)).card :=
          Finset.card_le_card hsub
      _ = Nat.floor (Real.log B / Real.log Λ) + 1 := Finset.card_range _
  have hx0 : 0 ≤ Real.log B / Real.log Λ := div_nonneg hlogB hlogΛ.le
  have hfloor : ((Nat.floor (Real.log B / Real.log Λ) : ℕ) : ℝ) ≤ Real.log B / Real.log Λ :=
    Nat.floor_le hx0
  calc (s.card : ℝ)
      ≤ ((Nat.floor (Real.log B / Real.log Λ) + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = ((Nat.floor (Real.log B / Real.log Λ) : ℕ) : ℝ) + 1 := by push_cast; ring
    _ ≤ Real.log B / Real.log Λ + 1 := by linarith

end Work.KMTPlan.A6
