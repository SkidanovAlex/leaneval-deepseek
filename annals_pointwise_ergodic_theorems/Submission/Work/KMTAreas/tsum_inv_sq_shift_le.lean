/-
# A uniform bound for the periodised kernel `∑_{m : ℤ} 1 / (1 + (y + m) ^ 2)`

For every real `y` the series `∑_{m : ℤ} 1 / (1 + (y + m) ^ 2)` converges, and
its sum is bounded independently of `y` (the supremum is attained at `y = 1/2`
and is close to `2.5`); here we prove the crude uniform bound `≤ 6`.

The proof has three ingredients.

* The series is summable for every real `y`.  For `t ∈ [0, 1)` this follows by
  splitting the `ℤ`-series into its two halves and comparing them with summable
  `ℕ`-series (`Summable.of_add_one_of_neg_add_one`), and for general `y` it is
  transported along the integer translation `m ↦ m + ⌊y⌋`
  (`Equiv.summable_iff` for `Equiv.addRight`).
* For `t ∈ [0, 1)` the estimate is elementary: with
  `φ m = 1 / (1 + (t + m) ^ 2)` the decomposition
  `∑_{m : ℤ} φ m = ∑_{n : ℕ} φ (n + 1) + φ 0 + ∑_{n : ℕ} φ (-(n + 1))`
  (`tsum_of_add_one_of_neg_add_one`) bounds the three pieces by the `ℕ`-series
  `∑_{n ≥ 0} 1 / (n + 1) ^ 2 ≤ 2` (`hasSum_zeta_two` and `π < 3.15`), by `1`,
  and by `∑_{n ≥ 0} 1 / (1 + n ^ 2) ≤ 3` (dominated by the former after
  splitting off the `n = 0` term).
* Finally `∑_{m : ℤ} 1 / (1 + (y + m) ^ 2)` only depends on `Int.fract y`,
  because the map `m ↦ m + k` is a bijection of `ℤ` (`Equiv.tsum_eq` for
  `Equiv.addRight`); writing `y = Int.fract y + ⌊y⌋` reduces the general case to
  the one just treated, with `0 ≤ Int.fract y < 1`.
-/
import Mathlib
import Submission.Work.KMTAreas.tsum_one_div_sq_succ_le_two

namespace Work.KMTAreas

open scoped BigOperators

/-- Elementary comparison for `1 / (1 + u ^ 2)`: if `0 < v ≤ u` then
`1 / (1 + u ^ 2) ≤ 1 / v ^ 2`. -/
private lemma one_div_one_add_sq_le_inv_sq {u v : ℝ} (hv : 0 < v) (h : v ≤ u) :
    (1 : ℝ) / (1 + u ^ 2) ≤ 1 / v ^ 2 := by
  apply one_div_le_one_div_of_le (pow_pos hv 2)
  have hsq : v ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ hv.le h 2
  linarith [hsq, sq_nonneg u]

/-- Elementary comparison for `1 / (1 + u ^ 2)`: if `0 ≤ v ≤ |u|` then
`1 / (1 + u ^ 2) ≤ 1 / (1 + v ^ 2)`. -/
private lemma one_div_one_add_sq_le_of_le_abs {u v : ℝ} (hv : 0 ≤ v) (h : v ≤ |u|) :
    (1 : ℝ) / (1 + u ^ 2) ≤ 1 / (1 + v ^ 2) := by
  apply one_div_le_one_div_of_le (by positivity)
  have hsq : v ^ 2 ≤ u ^ 2 := by
    have h2 := pow_le_pow_left₀ hv h 2
    rwa [sq_abs] at h2
  linarith [hsq]

/-- The series `∑_{n ≥ 0} 1 / (1 + n ^ 2)` converges and its sum is at most `3`.
The `n = 0` term contributes `1` and the remaining terms are dominated by
`∑_{n ≥ 1} 1 / n ^ 2 = π ^ 2 / 6 ≤ 2`. -/
private theorem summable_tsum_one_div_one_add_sq_nat :
    Summable (fun n : ℕ => (1 : ℝ) / (1 + (n : ℝ) ^ 2)) ∧
      ∑' n : ℕ, (1 : ℝ) / (1 + (n : ℝ) ^ 2) ≤ 3 := by
  have htail : Summable (fun n : ℕ => (1 : ℝ) / (1 + ((n : ℝ) + 1) ^ 2)) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      tsum_one_div_sq_succ_le_two.1
    apply one_div_le_one_div_of_le (pow_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1) 2)
    linarith [sq_nonneg ((n : ℝ) + 1)]
  have hsum : Summable (fun n : ℕ => (1 : ℝ) / (1 + (n : ℝ) ^ 2)) :=
    (summable_nat_add_iff (f := fun k : ℕ => (1 : ℝ) / (1 + (k : ℝ) ^ 2)) 1).mp
      (by simpa [Nat.cast_add, Nat.cast_one] using htail)
  have htail_le : (∑' n : ℕ, (1 : ℝ) / (1 + ((n : ℝ) + 1) ^ 2)) ≤ 2 := by
    calc ∑' n : ℕ, (1 : ℝ) / (1 + ((n : ℝ) + 1) ^ 2)
        ≤ ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2 :=
          Summable.tsum_le_tsum (fun n => by
            apply one_div_le_one_div_of_le (pow_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1) 2)
            linarith [sq_nonneg ((n : ℝ) + 1)]) htail tsum_one_div_sq_succ_le_two.1
      _ ≤ 2 := tsum_one_div_sq_succ_le_two.2
  refine ⟨hsum, ?_⟩
  rw [Summable.tsum_eq_zero_add hsum]
  have h0 : (1 : ℝ) / (1 + ((0 : ℕ) : ℝ) ^ 2) = 1 := by norm_num
  rw [h0]
  have : (∑' n : ℕ, (1 : ℝ) / (1 + (↑(n + 1) : ℝ) ^ 2)) ≤ 2 := by
    simpa [Nat.cast_add, Nat.cast_one] using htail_le
  linarith

/-- Translation invariance of `ℤ`-indexed series (value). -/
private theorem tsum_int_add_right (g : ℤ → ℝ) (k : ℤ) :
    ∑' n : ℤ, g (n + k) = ∑' n : ℤ, g n := by
  simpa [Equiv.coe_addRight] using (Equiv.tsum_eq (Equiv.addRight k) g)

/-- Translation invariance of `ℤ`-indexed series (summability). -/
private theorem summable_int_add_right (g : ℤ → ℝ) (k : ℤ) :
    Summable (fun n : ℤ => g (n + k)) ↔ Summable g := by
  have h := (Equiv.summable_iff (f := g) (Equiv.addRight k))
  simpa [Function.comp_def, Equiv.coe_addRight] using h

/-- The periodised kernel for a parameter `t` in the unit interval: the series
`∑_{m : ℤ} 1 / (1 + (t + m) ^ 2)` converges and is at most `6`. -/
private theorem summable_tsum_int_le_six (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Summable (fun m : ℤ => (1 : ℝ) / (1 + (t + (m : ℝ)) ^ 2)) ∧
      ∑' m : ℤ, (1 : ℝ) / (1 + (t + (m : ℝ)) ^ 2) ≤ 6 := by
  let φ : ℤ → ℝ := fun m => (1 : ℝ) / (1 + (t + (m : ℝ)) ^ 2)
  have hφ : φ = (fun m : ℤ => (1 : ℝ) / (1 + (t + (m : ℝ)) ^ 2)) := rfl
  change Summable φ ∧ ∑' m : ℤ, φ m ≤ 6
  -- the half of the series above zero
  have hA : Summable (fun n : ℕ => φ ((n : ℤ) + 1)) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
      tsum_one_div_sq_succ_le_two.1
    · simp only [hφ]; positivity
    · simp only [hφ]; push_cast
      exact one_div_one_add_sq_le_inv_sq (by positivity) (by linarith)
  -- the half of the series below zero
  have hB : Summable (fun n : ℕ => φ (-((n : ℤ) + 1))) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
      summable_tsum_one_div_one_add_sq_nat.1
    · simp only [hφ]; positivity
    · simp only [hφ]; push_cast
      apply one_div_one_add_sq_le_of_le_abs (Nat.cast_nonneg n)
      rw [abs_of_nonpos (by linarith)]
      linarith
  refine ⟨Summable.of_add_one_of_neg_add_one hA hB, ?_⟩
  rw [tsum_of_add_one_of_neg_add_one hA hB]
  have h1 : (∑' n : ℕ, φ ((n : ℤ) + 1)) ≤ 2 := by
    calc ∑' n : ℕ, φ ((n : ℤ) + 1)
        ≤ ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2 :=
          Summable.tsum_le_tsum (fun n => by
            simp only [hφ]; push_cast
            exact one_div_one_add_sq_le_inv_sq (by positivity) (by linarith))
            hA tsum_one_div_sq_succ_le_two.1
      _ ≤ 2 := tsum_one_div_sq_succ_le_two.2
  have h2 : φ 0 ≤ 1 := by
    simp only [hφ]
    rw [div_le_one (by positivity)]
    nlinarith [sq_nonneg (t + (((0 : ℤ) : ℝ)))]
  have h3 : (∑' n : ℕ, φ (-((n : ℤ) + 1))) ≤ 3 := by
    calc ∑' n : ℕ, φ (-((n : ℤ) + 1))
        ≤ ∑' n : ℕ, (1 : ℝ) / (1 + (n : ℝ) ^ 2) :=
          Summable.tsum_le_tsum (fun n => by
            simp only [hφ]; push_cast
            apply one_div_one_add_sq_le_of_le_abs (Nat.cast_nonneg n)
            rw [abs_of_nonpos (by linarith)]
            linarith) hB summable_tsum_one_div_one_add_sq_nat.1
      _ ≤ 3 := summable_tsum_one_div_one_add_sq_nat.2
  linarith

theorem tsum_inv_sq_shift_le :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ, Summable (fun m : ℤ => 1 / (1 + (y + (m : ℝ)) ^ 2)) ∧
      ∑' m : ℤ, 1 / (1 + (y + (m : ℝ)) ^ 2) ≤ B := by
  refine ⟨6, by norm_num, fun y => ?_⟩
  have ht0 : 0 ≤ Int.fract y := Int.fract_nonneg y
  have ht1 : Int.fract y < 1 := Int.fract_lt_one y
  have hfk : Int.fract y + ((⌊y⌋ : ℤ) : ℝ) = y := Int.fract_add_floor y
  have harg : ∀ m : ℤ, y + (m : ℝ) = Int.fract y + ((m + ⌊y⌋ : ℤ) : ℝ) := by
    intro m
    push_cast
    linarith
  have hfun : (fun m : ℤ => (1 : ℝ) / (1 + (y + (m : ℝ)) ^ 2))
      = fun m : ℤ => (1 : ℝ) / (1 + (Int.fract y + ((m + ⌊y⌋ : ℤ) : ℝ)) ^ 2) := by
    funext m
    rw [harg m]
  have hmain := summable_tsum_int_le_six (Int.fract y) ht0 ht1
  have htrans_summ :
      Summable (fun m : ℤ => (1 : ℝ) / (1 + (Int.fract y + ((m + ⌊y⌋ : ℤ) : ℝ)) ^ 2))
        ↔ Summable (fun j : ℤ => (1 : ℝ) / (1 + (Int.fract y + (j : ℝ)) ^ 2)) :=
    summable_int_add_right (fun j : ℤ => (1 : ℝ) / (1 + (Int.fract y + (j : ℝ)) ^ 2)) ⌊y⌋
  have htrans_tsum :
      (∑' m : ℤ, (1 : ℝ) / (1 + (Int.fract y + ((m + ⌊y⌋ : ℤ) : ℝ)) ^ 2))
        = ∑' j : ℤ, (1 : ℝ) / (1 + (Int.fract y + (j : ℝ)) ^ 2) :=
    tsum_int_add_right (fun j : ℤ => (1 : ℝ) / (1 + (Int.fract y + (j : ℝ)) ^ 2)) ⌊y⌋
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact htrans_summ.mpr hmain.1
  · rw [hfun, htrans_tsum]; exact hmain.2

end Work.KMTAreas
