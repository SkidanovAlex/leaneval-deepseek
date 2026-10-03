import Mathlib
import Submission.Work.KMTAreas.schwartz_decay_bound

/-!
# Uniform bound for the periodised Schwartz kernel

For a Schwartz function `K : ℝ → ℂ`, the sum over the integer translates
`∑' m : ℤ, ‖K (y + m)‖ₑ` is bounded uniformly in `y` (the periodisation of a Schwartz
function is bounded on the circle).

The proof splits into two elementary steps.

* Schwartz decay gives `‖K x‖ ≤ C/(1+x²)` for a constant `C ≥ 0`
  (`schwartz_decay_bound` plus `(1+x²) ≤ (1+|x|)²`).
* The model sum `∑' m : ℤ, 1/(1+(y+m)²)` is bounded uniformly in `y`: writing
  `y = n + θ` with `n = ⌊y + 1/2⌋` and `|θ| ≤ 1/2`, reindexing by `m ↦ m + n` and
  splitting the `ℤ`-sum into the two `ℕ`-sums `k` and `-(k+1)`
  (`tsum_nat_add_neg_add_one`) gives the termwise bound `1/(1+(θ±k)²) ≤ 32/(k+1)²`,
  whence the sum is at most `64 ∑' k, 1/(k+1)² = 64 π²/6 ≤ 128`.
-/

set_option maxHeartbeats 1000000

open scoped NNReal ENNReal BigOperators

namespace Work.KMTAreas

/-- Schwartz decay, in the form `‖K x‖ ≤ C / (1 + x ^ 2)`. -/
private lemma schwartz_le_inv_sq_aux (K : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖K x‖ ≤ C / (1 + x ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := schwartz_decay_bound K
  refine ⟨C, hC0, fun x => ?_⟩
  refine (hC x).trans ?_
  have hle : (1 : ℝ) + x ^ 2 ≤ (1 + |x|) ^ 2 := by
    nlinarith [abs_nonneg x, sq_abs x]
  have h1 : (0 : ℝ) < 1 + x ^ 2 := by positivity
  calc C / (1 + |x|) ^ 2 = C * (1 / (1 + |x|) ^ 2) := by ring
    _ ≤ C * (1 / (1 + x ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hC0
        exact one_div_le_one_div_of_le h1 hle
    _ = C / (1 + x ^ 2) := by ring

private theorem tsum_inv_sq_shift_le_aux :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ, Summable (fun m : ℤ => 1 / (1 + (y + (m : ℝ)) ^ 2)) ∧
      ∑' m : ℤ, 1 / (1 + (y + (m : ℝ)) ^ 2) ≤ B := by
  -- the `ℕ`-majorant `32/(n+1)^2`
  have hzetas : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have hps : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
      (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    have h := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).mpr hps
    simpa [Nat.cast_add, Nat.cast_one] using h
  have hzeta : ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 = Real.pi ^ 2 / 6 := by
    have h := hasSum_zeta_two.summable.tsum_eq_zero_add
    rw [hasSum_zeta_two.tsum_eq] at h
    simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      div_zero, zero_add] at h
    rw [h]
    refine tsum_congr (fun n => ?_)
    push_cast
    ring
  have hM : Summable (fun n : ℕ => 32 * (1 / ((n : ℝ) + 1) ^ 2)) := hzetas.mul_left 32
  refine ⟨128, by norm_num, fun y => ?_⟩
  set n : ℤ := ⌊y + 1 / 2⌋ with hn
  set θ : ℝ := y - (n : ℝ) with hθ
  have hθle : θ ≤ 1 / 2 := by
    have h := Int.lt_floor_add_one (y + 1 / 2)
    rw [← hn] at h
    have h2 : θ = y - (n : ℝ) := hθ
    linarith
  have hθge : -(1 / 2) ≤ θ := by
    have h := Int.floor_le (y + 1 / 2)
    rw [← hn] at h
    have h2 : θ = y - (n : ℝ) := hθ
    linarith
  have hcast : ∀ k : ℕ, (((-((k : ℤ) + 1)) : ℤ) : ℝ) = -((k : ℝ) + 1) := by
    intro k
    push_cast
    ring
  -- reindex the `ℤ`-sum by `n`
  have hreindex : (fun m : ℤ => 1 / (1 + (y + (m : ℝ)) ^ 2))
      = (fun m : ℤ => 1 / (1 + (θ + ((m + n : ℤ) : ℝ)) ^ 2)) := by
    funext m
    have h1 : y + (m : ℝ) = θ + ((m + n : ℤ) : ℝ) := by
      rw [hθ]; push_cast; ring
    rw [h1]
  have hshift : ∑' m : ℤ, 1 / (1 + (y + (m : ℝ)) ^ 2)
      = ∑' k : ℤ, 1 / (1 + (θ + (k : ℝ)) ^ 2) := by
    rw [hreindex]
    have h := Equiv.tsum_eq (Equiv.addRight n) (fun k : ℤ => 1 / (1 + (θ + (k : ℝ)) ^ 2))
    simpa using h
  -- the key arithmetic bound at each natural number
  have key : ∀ k : ℕ, ((k : ℝ) + 1) ^ 2 / 32 ≤ 1 + (θ + (k : ℝ)) ^ 2 := by
    intro k
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      norm_num
      nlinarith [sq_nonneg θ]
    · have hk : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
      have hpos : (0 : ℝ) ≤ (k : ℝ) / 2 := by positivity
      have hθk : (k : ℝ) / 2 ≤ θ + (k : ℝ) := by linarith
      have h2 : ((k : ℝ) / 2) ^ 2 ≤ (θ + (k : ℝ)) ^ 2 := by nlinarith
      have h3 : ((k : ℝ) + 1) ^ 2 / 32 ≤ ((k : ℝ) / 2) ^ 2 := by nlinarith
      linarith
  have hbdd1 : ∀ k : ℕ, 1 / (1 + (θ + (k : ℝ)) ^ 2) ≤ 32 * (1 / ((k : ℝ) + 1) ^ 2) := by
    intro k
    calc 1 / (1 + (θ + (k : ℝ)) ^ 2) ≤ 1 / (((k : ℝ) + 1) ^ 2 / 32) :=
          one_div_le_one_div_of_le (by positivity) (key k)
      _ = 32 * (1 / ((k : ℝ) + 1) ^ 2) := by rw [one_div_div, mul_one_div]
  have hbdd2 : ∀ k : ℕ, 1 / (1 + (θ - ((k : ℝ) + 1)) ^ 2) ≤ 32 * (1 / ((k : ℝ) + 1) ^ 2) := by
    intro k
    have h2 : ((k : ℝ) + 1) / 2 ≤ |θ - ((k : ℝ) + 1)| := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith [hθle])]
      linarith [hθle]
    have h3 : (((k : ℝ) + 1) / 2) ^ 2 ≤ (θ - ((k : ℝ) + 1)) ^ 2 := by
      have h4 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ((k : ℝ) + 1) / 2) h2 2
      rwa [sq_abs] at h4
    have h5 : ((k : ℝ) + 1) ^ 2 / 32 ≤ 1 + (((k : ℝ) + 1) / 2) ^ 2 := by
      have h6 : ((k : ℝ) + 1) ^ 2 / 32 ≤ (((k : ℝ) + 1) / 2) ^ 2 := by nlinarith
      linarith
    calc 1 / (1 + (θ - ((k : ℝ) + 1)) ^ 2) ≤ 1 / (((k : ℝ) + 1) ^ 2 / 32) :=
          one_div_le_one_div_of_le (by positivity) (by linarith)
      _ = 32 * (1 / ((k : ℝ) + 1) ^ 2) := by rw [one_div_div, mul_one_div]
  have hnat1 : Summable (fun k : ℕ => 1 / (1 + (θ + (k : ℝ)) ^ 2)) :=
    Summable.of_nonneg_of_le (fun k => by positivity) hbdd1 hM
  have hnat2 : Summable (fun k : ℕ => 1 / (1 + (θ - ((k : ℝ) + 1)) ^ 2)) :=
    Summable.of_nonneg_of_le (fun k => by positivity) hbdd2 hM
  have hnat2' : Summable (fun k : ℕ => 1 / (1 + (θ + (((-((k : ℤ) + 1)) : ℤ) : ℝ)) ^ 2)) := by
    refine hnat2.congr (fun k => ?_)
    rw [hcast k]
    ring
  have hsummable : Summable (fun k : ℤ => 1 / (1 + (θ + (k : ℝ)) ^ 2)) :=
    Summable.of_nat_of_neg_add_one hnat1 hnat2'
  have hbound : ∑' k : ℕ, (1 / (1 + (θ + (k : ℝ)) ^ 2)
      + 1 / (1 + (θ + (((-((k : ℤ) + 1)) : ℤ) : ℝ)) ^ 2)) ≤ 128 := by
    have hcongr : (fun k : ℕ => 1 / (1 + (θ + (k : ℝ)) ^ 2)
        + 1 / (1 + (θ + (((-((k : ℤ) + 1)) : ℤ) : ℝ)) ^ 2))
        = (fun k : ℕ => 1 / (1 + (θ + (k : ℝ)) ^ 2)
        + 1 / (1 + (θ - ((k : ℝ) + 1)) ^ 2)) := by
      funext k
      rw [hcast k]
      ring
    rw [hcongr]
    have step : ∑' k : ℕ, (1 / (1 + (θ + (k : ℝ)) ^ 2) + 1 / (1 + (θ - ((k : ℝ) + 1)) ^ 2))
        ≤ ∑' k : ℕ, (32 * (1 / ((k : ℝ) + 1) ^ 2) + 32 * (1 / ((k : ℝ) + 1) ^ 2)) :=
      Summable.tsum_le_tsum (fun k => add_le_add (hbdd1 k) (hbdd2 k))
        (hnat1.add hnat2) (hM.add hM)
    refine step.trans ?_
    rw [Summable.tsum_add hM hM, tsum_mul_left, hzeta]
    have hpi : Real.pi ^ 2 < 12 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    linarith
  constructor
  · rw [hreindex]
    exact (Equiv.summable_iff (Equiv.addRight n)).mpr hsummable
  · calc ∑' m : ℤ, 1 / (1 + (y + (m : ℝ)) ^ 2)
        = ∑' k : ℤ, 1 / (1 + (θ + (k : ℝ)) ^ 2) := hshift
      _ = ∑' k : ℕ, (1 / (1 + (θ + (k : ℝ)) ^ 2)
            + 1 / (1 + (θ + (((-((k : ℤ) + 1)) : ℤ) : ℝ)) ^ 2)) :=
          (tsum_nat_add_neg_add_one hsummable).symm
      _ ≤ 128 := hbound

/-- **Uniform bound for the periodisation of a Schwartz function.**
For a Schwartz function `K` on `ℝ` there is a constant `A` with
`∑' m : ℤ, ‖K (y + m)‖ₑ ≤ A` for every `y : ℝ`. -/
theorem MSW_tsum_norm_bound (K : SchwartzMap ℝ ℂ) :
    ∃ A : NNReal, ∀ y : ℝ, ∑' m : ℤ, ‖K (y + m)‖ₑ ≤ (A : ENNReal) := by
  obtain ⟨C, hC0, hpt⟩ := schwartz_le_inv_sq_aux K
  obtain ⟨B, hB0, hB⟩ := tsum_inv_sq_shift_le_aux
  let A : NNReal := ⟨C * B, mul_nonneg hC0 hB0⟩
  have hcoe : (A : ENNReal) = ENNReal.ofReal (C * B) := by
    rw [ENNReal.coe_nnreal_eq, show (A : ℝ) = C * B from rfl]
  refine ⟨A, fun y => ?_⟩
  have hg : Summable (fun m : ℤ => 1 / (1 + (y + (m : ℝ)) ^ 2)) := (hB y).1
  have hgb : ∑' m : ℤ, 1 / (1 + (y + (m : ℝ)) ^ 2) ≤ B := (hB y).2
  have hgC : Summable (fun m : ℤ => C * (1 / (1 + (y + (m : ℝ)) ^ 2))) := hg.mul_left C
  have hterm : ∀ m : ℤ, ‖K (y + (m : ℝ))‖ ≤ C * (1 / (1 + (y + (m : ℝ)) ^ 2)) :=
    fun m => (hpt _).trans (le_of_eq (mul_one_div C _).symm)
  have hf : Summable (fun m : ℤ => ‖K (y + (m : ℝ))‖) :=
    hgC.of_nonneg_of_le (fun m => norm_nonneg _) hterm
  have hle : ∑' m : ℤ, ‖K (y + (m : ℝ))‖ ≤ C * B := by
    calc ∑' m : ℤ, ‖K (y + (m : ℝ))‖
        ≤ ∑' m : ℤ, C * (1 / (1 + (y + (m : ℝ)) ^ 2)) :=
          hf.tsum_le_tsum hterm hgC
      _ = C * ∑' m : ℤ, 1 / (1 + (y + (m : ℝ)) ^ 2) := tsum_mul_left
      _ ≤ C * B := mul_le_mul_of_nonneg_left hgb hC0
  calc ∑' m : ℤ, ‖K (y + m)‖ₑ
      = ∑' m : ℤ, ENNReal.ofReal ‖K (y + (m : ℝ))‖ := by
        refine tsum_congr (fun m => ?_)
        rw [enorm_eq_nnnorm, ENNReal.coe_nnreal_eq]
        norm_cast
    _ = ENNReal.ofReal (∑' m : ℤ, ‖K (y + (m : ℝ))‖) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun m => norm_nonneg _) hf).symm
    _ ≤ ENNReal.ofReal (C * B) := ENNReal.ofReal_le_ofReal hle
    _ = (A : ENNReal) := hcoe.symm

end Work.KMTAreas
