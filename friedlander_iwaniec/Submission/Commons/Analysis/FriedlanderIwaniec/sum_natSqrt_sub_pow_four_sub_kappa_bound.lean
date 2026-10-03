import Mathlib
import Submission.Commons.Analysis.FriedlanderIwaniec.sum_sqrt_sub_pow_four_sub_kappa_le

open scoped BigOperators
open MeasureTheory intervalIntegral

namespace Commons.Analysis.FriedlanderIwaniec

/-- For a natural number `m`, the integer square root `Nat.sqrt m` differs from the real
square root `Real.sqrt m` by at most `1`. -/
private lemma natSqrt_sub_realSqrt_abs_le_one (m : ℕ) :
    |(Nat.sqrt m : ℝ) - Real.sqrt (m : ℝ)| ≤ 1 := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hs_le : (Nat.sqrt m : ℝ) ≤ Real.sqrt (m : ℝ) := by
    rw [Real.le_sqrt (by positivity) hm0]
    calc (Nat.sqrt m : ℝ) ^ 2 = ((Nat.sqrt m) ^ 2 : ℕ) := by push_cast; ring
      _ ≤ (m : ℝ) := by exact_mod_cast (Nat.sqrt_le' m)
  have hs_lt : Real.sqrt (m : ℝ) < (Nat.sqrt m : ℝ) + 1 := by
    rw [Real.sqrt_lt hm0 (by positivity)]
    calc (m : ℝ) < ((Nat.sqrt m + 1 : ℕ) : ℝ) ^ 2 := by
          exact_mod_cast (by
            have := Nat.sqrt_lt'.mp (Nat.lt_succ_self (Nat.sqrt m)); simpa using this)
      _ = ((Nat.sqrt m : ℝ) + 1) ^ 2 := by push_cast; ring
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- `Nat.sqrt (Nat.sqrt x)` equals the floor of the real fourth root of `x`. -/
private lemma natSqrt_natSqrt_eq_floor_fourthRoot (x : ℕ) :
    Nat.sqrt (Nat.sqrt x) = ⌊((x : ℝ) ^ (1 / 4 : ℝ))⌋₊ := by
  have hN4 : (Nat.sqrt (Nat.sqrt x)) ^ 4 ≤ x := by
    have h1 : (Nat.sqrt (Nat.sqrt x)) ^ 2 ≤ Nat.sqrt x := Nat.sqrt_le' _
    have h2 : (Nat.sqrt x) ^ 2 ≤ x := Nat.sqrt_le' _
    calc (Nat.sqrt (Nat.sqrt x)) ^ 4 = ((Nat.sqrt (Nat.sqrt x)) ^ 2) ^ 2 := by ring
      _ ≤ (Nat.sqrt x) ^ 2 := by nlinarith [h1]
      _ ≤ x := h2
  have hN4lt : x < (Nat.sqrt (Nat.sqrt x) + 1) ^ 4 := by
    have h1 : Nat.sqrt x < (Nat.sqrt (Nat.sqrt x) + 1) ^ 2 := by
      have := Nat.sqrt_lt'.mp (Nat.lt_succ_self (Nat.sqrt (Nat.sqrt x)))
      simpa using this
    have h2 : x < ((Nat.sqrt (Nat.sqrt x) + 1) ^ 2) * ((Nat.sqrt (Nat.sqrt x) + 1) ^ 2) := by
      have := Nat.sqrt_lt.mp h1
      simpa using this
    calc x < ((Nat.sqrt (Nat.sqrt x) + 1) ^ 2) ^ 2 := by simpa [pow_two] using h2
      _ = (Nat.sqrt (Nat.sqrt x) + 1) ^ 4 := by ring
  have hX0 : (0 : ℝ) ≤ (x : ℝ) := by positivity
  have hY0 : (0 : ℝ) ≤ (x : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_nonneg hX0 _
  have hNnn : (0 : ℝ) ≤ (Nat.sqrt (Nat.sqrt x) : ℝ) := by positivity
  have hN1nn : (0 : ℝ) ≤ (Nat.sqrt (Nat.sqrt x) : ℝ) + 1 := by positivity
  have hpoweq : (((Nat.sqrt (Nat.sqrt x) : ℝ)) ^ 4) ^ (1 / 4 : ℝ)
      = (Nat.sqrt (Nat.sqrt x) : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNnn]; norm_num
  have hpoweq1 : (((Nat.sqrt (Nat.sqrt x) : ℝ) + 1) ^ 4) ^ (1 / 4 : ℝ)
      = (Nat.sqrt (Nat.sqrt x) : ℝ) + 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN1nn]; norm_num
  have hle : (Nat.sqrt (Nat.sqrt x) : ℝ) ≤ (x : ℝ) ^ (1 / 4 : ℝ) := by
    have h : (((Nat.sqrt (Nat.sqrt x) : ℝ)) ^ 4) ^ (1 / 4 : ℝ) ≤ (x : ℝ) ^ (1 / 4 : ℝ) := by
      rw [Real.rpow_le_rpow_iff (by positivity) hX0 (by norm_num : (0 : ℝ) < 1 / 4)]
      exact_mod_cast hN4
    rwa [hpoweq] at h
  have hlt : (x : ℝ) ^ (1 / 4 : ℝ) < (Nat.sqrt (Nat.sqrt x) : ℝ) + 1 := by
    have h : (x : ℝ) ^ (1 / 4 : ℝ) < (((Nat.sqrt (Nat.sqrt x) : ℝ) + 1) ^ 4) ^ (1 / 4 : ℝ) := by
      rw [Real.rpow_lt_rpow_iff hX0 (by positivity) (by norm_num : (0 : ℝ) < 1 / 4)]
      exact_mod_cast hN4lt
    rwa [hpoweq1] at h
  exact ((Nat.floor_eq_iff hY0).mpr ⟨hle, hlt⟩).symm

/-- `(X ^ (1/4)) ^ 4 = X` for `X ≥ 0`. -/
private lemma rpow_quarter_pow_four (X : ℝ) (hX : 0 ≤ X) : (X ^ (1 / 4 : ℝ)) ^ (4 : ℕ) = X := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hX]; norm_num

/-- `(X ^ (1/4)) ^ 2 = Real.sqrt X` for `X ≥ 0`. -/
private lemma rpow_quarter_pow_two (X : ℝ) (hX : 0 ≤ X) :
    (X ^ (1 / 4 : ℝ)) ^ (2 : ℕ) = Real.sqrt X := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hX]; norm_num

/-- `(X ^ (1/4)) ^ 3 = X ^ (3/4)` for `X ≥ 0`. -/
private lemma rpow_quarter_pow_three (X : ℝ) (hX : 0 ≤ X) :
    (X ^ (1 / 4 : ℝ)) ^ (3 : ℕ) = X ^ (3 / 4 : ℝ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hX]; norm_num

lemma sum_natSqrt_sub_pow_four_sub_kappa_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, 1 ≤ x →
      |(((∑ c ∈ Finset.range (Nat.sqrt (Nat.sqrt x) + 1), Nat.sqrt (x - c ^ 4)) : ℕ) : ℝ) -
        (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * (x : ℝ) ^ (3 / 4 : ℝ)| ≤ C * Real.sqrt x := by
  refine ⟨4, by norm_num, ?_⟩
  intro x hx
  set X : ℝ := (x : ℝ) with hXdef
  set N : ℕ := Nat.sqrt (Nat.sqrt x) with hNdef
  set I : ℝ := ∫ u in (0)..1, Real.sqrt (1 - u ^ 4) with hIdef
  set Y : ℝ := X ^ (1 / 4 : ℝ) with hYdef
  have hX1 : (1 : ℝ) ≤ X := by rw [hXdef]; exact_mod_cast hx
  have hX0 : (0 : ℝ) ≤ X := le_trans zero_le_one hX1
  -- basic facts about Y
  have hY1 : (1 : ℝ) ≤ Y := by
    rw [hYdef]
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hX1 (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rwa [Real.one_rpow] at h
  have hY4 : Y ^ (4 : ℕ) = X := by rw [hYdef]; exact rpow_quarter_pow_four X hX0
  have hY2 : Y ^ (2 : ℕ) = Real.sqrt X := by rw [hYdef]; exact rpow_quarter_pow_two X hX0
  have hY3 : Y ^ (3 : ℕ) = X ^ (3 / 4 : ℝ) := by rw [hYdef]; exact rpow_quarter_pow_three X hX0
  have hNfloor : N = ⌊Y⌋₊ := by
    rw [hNdef, hYdef, hXdef]; exact natSqrt_natSqrt_eq_floor_fourthRoot x
  -- split into the real-sqrt sum `A` and the floor error
  set S : ℝ := ∑ c ∈ Finset.range (N + 1), (Nat.sqrt (x - c ^ 4) : ℝ) with hSdef
  set A : ℝ := ∑ c ∈ Finset.range (N + 1), Real.sqrt (X - (c : ℝ) ^ 4) with hAdef
  have hcast : (((∑ c ∈ Finset.range (N + 1), Nat.sqrt (x - c ^ 4)) : ℕ) : ℝ) = S := by
    rw [hSdef, Nat.cast_sum]
  have hN4 : N ^ 4 ≤ x := by
    rw [hNdef]
    have h1 : (Nat.sqrt (Nat.sqrt x)) ^ 2 ≤ Nat.sqrt x := Nat.sqrt_le' _
    have h2 : (Nat.sqrt x) ^ 2 ≤ x := Nat.sqrt_le' _
    calc (Nat.sqrt (Nat.sqrt x)) ^ 4 = ((Nat.sqrt (Nat.sqrt x)) ^ 2) ^ 2 := by ring
      _ ≤ (Nat.sqrt x) ^ 2 := by nlinarith [h1]
      _ ≤ x := h2
  have hterm : ∀ c ∈ Finset.range (N + 1),
      |(Nat.sqrt (x - c ^ 4) : ℝ) - Real.sqrt (X - (c : ℝ) ^ 4)| ≤ 1 := by
    intro c hc
    have hcN : c ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)
    have hc4x : c ^ 4 ≤ x := le_trans (Nat.pow_le_pow_left hcN 4) hN4
    have hcastsub : ((x - c ^ 4 : ℕ) : ℝ) = X - (c : ℝ) ^ 4 := by
      rw [hXdef, Nat.cast_sub hc4x]; push_cast; ring
    rw [← hcastsub]
    exact natSqrt_sub_realSqrt_abs_le_one (x - c ^ 4)
  have hSdiff : |S - A| ≤ (N : ℝ) + 1 := by
    have hSA : S - A = ∑ c ∈ Finset.range (N + 1),
        ((Nat.sqrt (x - c ^ 4) : ℝ) - Real.sqrt (X - (c : ℝ) ^ 4)) := by
      rw [hSdef, hAdef, Finset.sum_sub_distrib]
    rw [hSA]
    calc |∑ c ∈ Finset.range (N + 1),
            ((Nat.sqrt (x - c ^ 4) : ℝ) - Real.sqrt (X - (c : ℝ) ^ 4))|
        ≤ ∑ c ∈ Finset.range (N + 1),
            |(Nat.sqrt (x - c ^ 4) : ℝ) - Real.sqrt (X - (c : ℝ) ^ 4)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _c ∈ Finset.range (N + 1), (1 : ℝ) := by
          apply Finset.sum_le_sum; intro c hc; exact hterm c hc
      _ = (N : ℝ) + 1 := by
          rw [Finset.sum_const, Finset.card_range]; simp
  have hA_bound : |A - I * X ^ (3 / 4 : ℝ)| ≤ Real.sqrt X := by
    have hB := sum_sqrt_sub_pow_four_sub_kappa_le (y := Y) hY1
    rw [← hIdef] at hB
    rw [← hNfloor] at hB
    rw [hY4, hY3, hY2] at hB
    rw [hAdef]; exact hB
  have hNleY : (N : ℝ) ≤ Y := by
    rw [hNfloor]; exact Nat.floor_le (le_trans zero_le_one hY1)
  have hYle_sqrt : Y ≤ Real.sqrt X := by rw [← hY2]; nlinarith [hY1]
  have hNle_sqrt : (N : ℝ) ≤ Real.sqrt X := le_trans hNleY hYle_sqrt
  have h1sqrt : (1 : ℝ) ≤ Real.sqrt X := by rw [← hY2]; nlinarith [hY1]
  have hle1 : (N : ℝ) + 1 ≤ 2 * Real.sqrt X := by linarith
  have hS_bound : |S - I * X ^ (3 / 4 : ℝ)| ≤ Real.sqrt X + ((N : ℝ) + 1) := by
    have htri : |S - I * X ^ (3 / 4 : ℝ)| ≤ |S - A| + |A - I * X ^ (3 / 4 : ℝ)| := by
      have heq : S - I * X ^ (3 / 4 : ℝ) = (S - A) + (A - I * X ^ (3 / 4 : ℝ)) := by ring
      rw [heq]; exact abs_add_le _ _
    linarith [htri, hSdiff, hA_bound]
  have hfinal : |S - I * X ^ (3 / 4 : ℝ)| ≤ 4 * Real.sqrt X := by
    have hsq0 : (0 : ℝ) ≤ Real.sqrt X := Real.sqrt_nonneg X
    calc |S - I * X ^ (3 / 4 : ℝ)| ≤ Real.sqrt X + ((N : ℝ) + 1) := hS_bound
      _ ≤ Real.sqrt X + 2 * Real.sqrt X := by linarith
      _ = 3 * Real.sqrt X := by ring
      _ ≤ 4 * Real.sqrt X := by linarith
  rw [hcast]
  exact hfinal

end Commons.Analysis.FriedlanderIwaniec
