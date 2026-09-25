import Mathlib
import Submission.Work.BourgainPlan.Oscillation.defs

namespace Work.BourgainPlan.Oscillation

/-- For `ρ > 1` and `t > 0` the sums `Σ_{i ∈ S} ⌊ρ^i⌋₊ ^ (-t)` are uniformly bounded in the finite
set `S ⊆ ℕ`: the lacunary sequence `⌊ρ^i⌋` grows geometrically, so `⌊ρ^i⌋ ^ (-t) ≤ 2^t (ρ^{-t})^i`
with ratio `ρ^{-t} ∈ [0, 1)`. -/
theorem lacunary_inv_pow_summable (ρ : ℝ) (hρ : 1 < ρ) (t : ℝ) (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : Finset ℕ,
      ∑ i ∈ S, (((⌊ρ ^ i⌋₊ : ℕ) : ℝ)) ^ (-t) ≤ C := by
  have hρ0 : 0 < ρ := lt_trans zero_lt_one hρ
  have hρ1 : 0 ≤ ρ := le_of_lt hρ0
  set q : ℝ := ρ ^ (-t) with hqdef
  have hq0 : 0 ≤ q := Real.rpow_nonneg hρ1 _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg hρ (by linarith)
  -- The geometric bound for a single term: `⌊ρ^i⌋ ^ (-t) ≤ 2^t q^i`.
  have hterm : ∀ i : ℕ, (((⌊ρ ^ i⌋₊ : ℕ) : ℝ)) ^ (-t) ≤ 2 ^ t * q ^ i := by
    intro i
    have hx1 : (1:ℝ) ≤ ρ ^ i := one_le_pow₀ (le_of_lt hρ)
    have hx0 : (0:ℝ) < ρ ^ i := pow_pos hρ0 i
    -- `ρ^i / 2 ≤ ⌊ρ^i⌋`
    have hfloor : ρ ^ i / 2 ≤ (((⌊ρ ^ i⌋₊ : ℕ) : ℝ)) := by
      rcases lt_or_ge (ρ ^ i) 2 with h2 | h2
      · have h' : ((1:ℕ):ℝ) ≤ ρ ^ i := by exact_mod_cast hx1
        have h3 : (1:ℝ) ≤ (((⌊ρ ^ i⌋₊ : ℕ) : ℝ)) := by
          exact_mod_cast Nat.le_floor h'
        linarith
      · have h3 : ρ ^ i - 1 < (((⌊ρ ^ i⌋₊ : ℕ) : ℝ)) := by
          have := Nat.lt_floor_add_one (ρ ^ i)
          linarith
        linarith
    -- monotonicity of `x ↦ x ^ (-t)` (decreasing) at `ρ^i/2 ≤ ⌊ρ^i⌋`
    have step1 : (((⌊ρ ^ i⌋₊ : ℕ) : ℝ)) ^ (-t) ≤ (ρ ^ i / 2) ^ (-t) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hfloor (by linarith)
    have step2 : (ρ ^ i / 2) ^ (-t) = 2 ^ t * (ρ ^ i) ^ (-t) := by
      have h1 : (ρ ^ i / 2) = ρ ^ i * (1/2) := by ring
      rw [h1, Real.mul_rpow (le_of_lt hx0) (by norm_num : (0:ℝ) ≤ 1/2)]
      have h2 : ((1:ℝ)/2) ^ (-t) = 2 ^ t := by
        rw [one_div, Real.inv_rpow (by norm_num : (0:ℝ) ≤ 2),
          ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), neg_neg]
      rw [h2]
      ring
    have step3 : (ρ ^ i) ^ (-t) = q ^ i := by
      rw [hqdef]
      rw [← Real.rpow_natCast ρ i, ← Real.rpow_mul hρ1 (i:ℝ) (-t),
          ← Real.rpow_natCast (ρ ^ (-t)) i, ← Real.rpow_mul hρ1 (-t) (i:ℝ)]
      ring_nf
    rw [step3] at step2
    linarith [step1, step2]
  refine ⟨∑' i : ℕ, 2 ^ t * q ^ i, ?_, ?_⟩
  · exact tsum_nonneg
      (fun i => mul_nonneg (le_of_lt (Real.rpow_pos_of_pos two_pos t)) (pow_nonneg hq0 i))
  · intro S
    have hnn : ∀ i : ℕ, 0 ≤ 2 ^ t * q ^ i :=
      fun i => mul_nonneg (le_of_lt (Real.rpow_pos_of_pos two_pos t)) (pow_nonneg hq0 i)
    have hsumm : Summable (fun i : ℕ => 2 ^ t * q ^ i) :=
      (summable_geometric_of_lt_one hq0 hq1).mul_left (2 ^ t)
    calc ∑ i ∈ S, (((⌊ρ ^ i⌋₊ : ℕ) : ℝ)) ^ (-t)
        ≤ ∑ i ∈ S, 2 ^ t * q ^ i := Finset.sum_le_sum (fun i _ => hterm i)
      _ ≤ ∑' i, 2 ^ t * q ^ i := Summable.sum_le_tsum S (fun i _ => hnn i) hsumm

end Work.BourgainPlan.Oscillation
