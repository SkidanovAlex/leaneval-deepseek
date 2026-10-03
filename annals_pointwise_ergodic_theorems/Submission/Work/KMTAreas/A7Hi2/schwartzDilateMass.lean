/-
# The mass of a dilated Schwartz function on the lattice `τ⁻¹ℤ`

For a Schwartz function `K : ℝ → ℂ` the lattice sum `τ⁻¹ ∑_{j ∈ ℤ} ‖K (j / τ)‖` is bounded
uniformly in `τ ≥ 1`.  This is the discrete analogue of the finiteness of `∫ ‖K‖` and controls
the mass of the dilated kernel `K(·/τ)` sampled on the lattice `τ⁻¹ℤ`.

The proof is elementary.  Schwartz decay gives `‖K x‖ ≤ C (1 + |x|)⁻²`, so the `j`-th term is
bounded by `C τ / (τ + |j|)²`.  The two-sided series `∑_j τ/(τ+|j|)²` is bounded by `4` uniformly
for `τ ≥ 1`; the key estimate is the telescoping bound

  `τ/(τ+n)² ≤ 2τ/((τ+n)(τ+n+1)) = 2τ (1/(τ+n) - 1/(τ+n+1))`,  valid for `τ ≥ 1`, `n ≥ 0`
  because `τ + n + 1 ≤ 2 (τ + n)`.
-/
import Mathlib
import Submission.Work.KMTAreas.schwartz_decay_bound

open scoped BigOperators

namespace Work.KMTAreas.A7Hi2

/-- For `τ ≥ 1` the one-sided model series `∑_{n : ℕ} τ / (τ + n)²` is summable with sum `≤ 2`.
The proof compares `τ/(τ+n)²` with the telescoping term
`2τ/((τ+n)(τ+n+1)) = 2τ (1/(τ+n) - 1/(τ+n+1))` and telescopes the partial sums. -/
private lemma summable_tsum_nat_div_sq_le (τ : ℝ) (hτ : 1 ≤ τ) :
    Summable (fun n : ℕ => τ / (τ + (n : ℝ)) ^ 2) ∧
      ∑' n : ℕ, τ / (τ + (n : ℝ)) ^ 2 ≤ 2 := by
  have hτpos : (0 : ℝ) < τ := by linarith
  set B : ℕ → ℝ := fun n => 2 * τ / ((τ + (n : ℝ)) * ((τ + (n : ℝ)) + 1)) with hB
  -- the termwise comparison
  have hAB : ∀ n : ℕ, τ / (τ + (n : ℝ)) ^ 2 ≤ B n := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    simp only [hB]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  -- the telescoping bound for the partial sums of `B`
  have hBsum_range : ∀ N : ℕ, ∑ i ∈ Finset.range N, B i ≤ 2 := by
    intro N
    have hfun : ∀ i : ℕ, B i = 2 * τ / (τ + (i : ℝ)) - 2 * τ / (τ + ((i : ℝ) + 1)) := by
      intro i
      simp only [hB]
      have h1 : (0 : ℝ) < τ + (i : ℝ) := by positivity
      have h2 : (0 : ℝ) < τ + ((i : ℝ) + 1) := by positivity
      field_simp
      ring
    calc ∑ i ∈ Finset.range N, B i
        = ∑ i ∈ Finset.range N, (2 * τ / (τ + (i : ℝ)) - 2 * τ / (τ + ((i : ℝ) + 1))) :=
          Finset.sum_congr rfl (fun i _ => hfun i)
      _ = 2 * τ / (τ + (0 : ℝ)) - 2 * τ / (τ + (N : ℝ)) := by
          have h := Finset.sum_range_sub' (fun i : ℕ => 2 * τ / (τ + (i : ℝ))) N
          simpa [Nat.cast_add, Nat.cast_one] using h
      _ ≤ 2 := by
          have h3 : (2 : ℝ) * τ / (τ + (0 : ℝ)) = 2 := by
            simp only [add_zero]
            field_simp
          have h2 : (0 : ℝ) ≤ 2 * τ / (τ + (N : ℝ)) := by positivity
          rw [h3]
          linarith
  have hBsum : Summable B :=
    summable_of_sum_range_le (fun n => by simp only [hB]; positivity) hBsum_range
  have hAsum : Summable (fun n : ℕ => τ / (τ + (n : ℝ)) ^ 2) :=
    hBsum.of_nonneg_of_le (fun n => by positivity) hAB
  refine ⟨hAsum, Summable.tsum_le_of_sum_range_le hAsum (fun N => ?_)⟩
  calc ∑ i ∈ Finset.range N, τ / (τ + (i : ℝ)) ^ 2
      ≤ ∑ i ∈ Finset.range N, B i := Finset.sum_le_sum (fun i _ => hAB i)
    _ ≤ 2 := hBsum_range N

theorem schwartzDilateMass (K : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ : ℝ) (hτ : 1 ≤ τ),
      (∑' j : ℤ, (1 / τ) * ‖K ((j : ℝ) / τ)‖) ≤ C := by
  obtain ⟨C, hC0, hC⟩ := Work.KMTAreas.schwartz_decay_bound K
  refine ⟨max (4 * C) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun τ hτ => ?_⟩
  have hτpos : (0 : ℝ) < τ := by linarith
  -- the one-sided model series
  obtain ⟨hAsum0, hAle0⟩ := summable_tsum_nat_div_sq_le τ hτ
  set A : ℕ → ℝ := fun n => τ / (τ + (n : ℝ)) ^ 2 with hA
  have hAsum : Summable A := hAsum0
  have hAle : ∑' n : ℕ, A n ≤ 2 := hAle0
  have hle : ∀ n : ℕ, A (n + 1) ≤ A n := by
    intro n
    simp only [hA]
    have hn : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hn, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hAle_succ : Summable (fun n : ℕ => A (n + 1)) :=
    hAsum.of_nonneg_of_le (fun n => by positivity) hle
  have hAle_succ_le : ∑' n : ℕ, A (n + 1) ≤ 2 :=
    (Summable.tsum_le_tsum hle hAle_succ hAsum).trans hAle
  -- the `ℤ`-majorant family
  set G : ℤ → ℝ := fun j => C * τ / (τ + |(j : ℝ)|) ^ 2 with hG
  have hcongr1 : ∀ n : ℕ, G (n : ℤ) = C * A n := by
    intro n
    simp only [hG, hA]
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n), mul_div_assoc]
  have hcongr2 : ∀ n : ℕ, G (-(n + 1 : ℤ)) = C * A (n + 1) := by
    intro n
    simp only [hG, hA]
    have harg : ((-(n + 1 : ℤ) : ℤ) : ℝ) = -((n : ℝ) + 1) := by push_cast; ring
    rw [harg, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
    have hn : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hn, mul_div_assoc]
  have hGnat : Summable (fun n : ℕ => G (n : ℤ)) := by
    rw [show (fun n : ℕ => G (n : ℤ)) = fun n : ℕ => C * A n from funext hcongr1]
    exact hAsum.mul_left C
  have hGneg : Summable (fun n : ℕ => G (-(n + 1 : ℤ))) := by
    rw [show (fun n : ℕ => G (-(n + 1 : ℤ))) = fun n : ℕ => C * A (n + 1) from funext hcongr2]
    exact hAle_succ.mul_left C
  have hGsum : Summable G := Summable.of_nat_of_neg_add_one hGnat hGneg
  have htsum1 : ∑' n : ℕ, G (n : ℤ) ≤ 2 * C := by
    rw [tsum_congr hcongr1, tsum_mul_left]
    calc C * ∑' n : ℕ, A n ≤ C * 2 := mul_le_mul_of_nonneg_left hAle hC0
      _ = 2 * C := by ring
  have htsum2 : ∑' n : ℕ, G (-(n + 1 : ℤ)) ≤ 2 * C := by
    rw [tsum_congr hcongr2, tsum_mul_left]
    calc C * ∑' n : ℕ, A (n + 1) ≤ C * 2 := mul_le_mul_of_nonneg_left hAle_succ_le hC0
      _ = 2 * C := by ring
  have hGtsum : ∑' j : ℤ, G j ≤ 4 * C := by
    rw [← tsum_nat_add_neg_add_one hGsum, Summable.tsum_add hGnat hGneg]
    linarith
  -- comparison of the true summand with the majorant
  set F : ℤ → ℝ := fun j => (1 / τ) * ‖K ((j : ℝ) / τ)‖ with hF
  have hFnn : ∀ j, 0 ≤ F j := by intro j; simp only [hF]; positivity
  have hFG : ∀ j, F j ≤ G j := by
    intro j
    simp only [hF, hG]
    calc (1 / τ) * ‖K ((j : ℝ) / τ)‖
        ≤ (1 / τ) * (C / (1 + |(j : ℝ) / τ|) ^ 2) :=
          mul_le_mul_of_nonneg_left (hC _) (by positivity)
      _ = C * τ / (τ + |(j : ℝ)|) ^ 2 := by
          rw [abs_div, abs_of_pos hτpos]
          field_simp
  have hFsum : Summable F := hGsum.of_nonneg_of_le hFnn hFG
  calc ∑' j : ℤ, (1 / τ) * ‖K ((j : ℝ) / τ)‖
      = ∑' j : ℤ, F j := rfl
    _ ≤ ∑' j : ℤ, G j := Summable.tsum_le_tsum hFG hFsum hGsum
    _ ≤ 4 * C := hGtsum
    _ ≤ max (4 * C) 1 := le_max_left _ _

end Work.KMTAreas.A7Hi2
