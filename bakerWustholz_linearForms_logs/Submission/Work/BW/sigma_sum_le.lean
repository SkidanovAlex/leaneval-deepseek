import Mathlib
import Submission.Work.BW.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- If every `σ j ≥ 1/d` (with `d = [K:ℚ]`), then `∑ j, σ j ≤ r * d^(r-1) * ∏ j, σ j`.
Indeed `σ j ≤ d^(r-1) * ∏ i, σ i` because `∏ i, σ i ≥ σ j * (1/d)^(r-1)`. -/
theorem sigma_sum_le {K : Type*} [Field K] [NumberField K] {r : ℕ}
    (σ : Fin r → ℝ) (hσ : ∀ j, 1 / (Module.finrank ℚ K : ℝ) ≤ σ j) :
    (∑ j, σ j) ≤ (r : ℝ) * (Module.finrank ℚ K : ℝ) ^ (r - 1) * ∏ j, σ j := by
  set n : ℝ := (Module.finrank ℚ K : ℝ) with hn_def
  -- `n = [K:ℚ]` is positive, since `K` is a nontrivial `ℚ`-vector space.
  have hn : 0 < n := by
    rw [hn_def]
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K))
  have hc : (0 : ℝ) < 1 / n := one_div_pos.mpr hn
  have hσ' : ∀ j, 1 / n ≤ σ j := fun j => by simpa only [hn_def] using hσ j
  -- For each `j`, `σ j ≤ n ^ (r-1) * ∏ i, σ i`.
  have key : ∀ j, σ j ≤ n ^ (r - 1) * ∏ i, σ i := by
    intro j
    have hσj : 0 ≤ σ j := le_trans (le_of_lt hc) (hσ' j)
    have hcard : (Finset.univ.erase j).card = r - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
    -- the product over the other indices is at least `(1/n) ^ (r-1)`.
    have hpe : (1 / n) ^ (r - 1) ≤ ∏ i ∈ Finset.univ.erase j, σ i := by
      have h1 : ∏ i ∈ Finset.univ.erase j, (1 / n : ℝ) = (1 / n) ^ (r - 1) := by
        rw [Finset.prod_const, hcard]
      rw [← h1]
      exact Finset.prod_le_prod₀ (fun i _ => le_of_lt hc) (fun i _ => hσ' i)
    have hprod : (1 / n) ^ (r - 1) * σ j ≤ ∏ i, σ i := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
      rw [mul_comm (σ j)]
      exact mul_le_mul_of_nonneg_right hpe hσj
    calc σ j = n ^ (r - 1) * ((1 / n) ^ (r - 1) * σ j) := by
          rw [← mul_assoc, ← mul_pow, mul_one_div, div_self (ne_of_gt hn), one_pow, one_mul]
      _ ≤ n ^ (r - 1) * ∏ i, σ i :=
          mul_le_mul_of_nonneg_left hprod (le_of_lt (pow_pos hn _))
  calc ∑ j, σ j ≤ ∑ j, n ^ (r - 1) * ∏ i, σ i := Finset.sum_le_sum (fun j _ => key j)
    _ = (r : ℝ) * (n ^ (r - 1) * ∏ i, σ i) := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (r : ℝ) * n ^ (r - 1) * ∏ i, σ i := by ring

end Work.BW
