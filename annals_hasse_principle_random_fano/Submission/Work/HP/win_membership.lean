import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux

namespace Work.HP

set_option linter.unusedVariables false

/-- The window exponents `kwin r L` are monotone (given), and the sum/product of the
window exponents of a rank-`r` integral lattice `L` is bounded by the single dyadic
threshold `⌈log₂ (2^r · K_mink · (Δ+1))⌉`: indeed `2^{kwin j} ≤ 2 λ_{j+1}(L)`, so the
product of the thresholds is at most `2^r · ∏ λ_{j+1}(L) ≤ 2^r · K_mink · detL L ≤ 2^r ·
K_mink · (Δ+1)`, and the assumed window property upgrades this product bound to a bound
on the sum (hence on each individual term). -/
theorem win_membership (n r : ℕ) (hr : 3 ≤ r)
    (Kmink Δ : ℝ) (hKmink : 1 ≤ Kmink) (hΔ : 1 ≤ Δ)
    (L : Submodule ℤ (Fin (n + 1) → ℤ)) (hrL : rk L = r) (hdet : detL L ≤ Δ + 1)
    (hmink : (∏ j ∈ Finset.range (rk L), lam L (j + 1)) ≤ Kmink * detL L)
    (hwin : (∀ j : Fin r, lam L (j.1 + 1) ≤ (2 : ℝ) ^ (kwin r L j)) ∧
      (∀ j : Fin r, (2 : ℝ) ^ (kwin r L j) ≤ 2 * lam L (j.1 + 1)) ∧
      Monotone (kwin r L) ∧
      (∀ M : ℝ, 1 ≤ M → (∏ j : Fin r, (2 : ℝ) ^ (kwin r L j)) ≤ M →
        (∑ j : Fin r, kwin r L j) ≤ ⌈Real.logb 2 M⌉₊)) :
    Monotone (kwin r L) ∧
      (∑ j : Fin r, kwin r L j) ≤ ⌈Real.logb 2 ((2 : ℝ) ^ r * Kmink * (Δ + 1))⌉₊ ∧
      (∀ j : Fin r, kwin r L j ≤ ⌈Real.logb 2 ((2 : ℝ) ^ r * Kmink * (Δ + 1))⌉₊) := by
  -- Bound the product of the successive minima by `Kmink * (Δ+1)`, using `hmink`, `hrL`
  -- and `hdet`.
  have hlam : ∏ j : Fin r, lam L (j.1 + 1) ≤ Kmink * (Δ + 1) := by
    rw [Fin.prod_univ_eq_prod_range (fun j => lam L (j + 1)) r, ← hrL]
    calc ∏ j ∈ Finset.range (rk L), lam L (j + 1)
        ≤ Kmink * detL L := hmink
      _ ≤ Kmink * (Δ + 1) := mul_le_mul_of_nonneg_left hdet (by linarith)
  -- Convert this into a bound on the product of the dyadic thresholds.
  have hprod : ∏ j : Fin r, (2 : ℝ) ^ (kwin r L j) ≤ (2 : ℝ) ^ r * Kmink * (Δ + 1) := by
    have hstep1 : ∏ j : Fin r, (2 : ℝ) ^ (kwin r L j) ≤ ∏ j : Fin r, (2 * lam L (j.1 + 1)) := by
      apply Finset.prod_le_prod₀
      · intro j _; positivity
      · intro j _; exact hwin.2.1 j
    have hstep2 : ∏ j : Fin r, (2 * lam L (j.1 + 1))
        = (2 : ℝ) ^ r * ∏ j : Fin r, lam L (j.1 + 1) := by
      rw [Finset.prod_mul_distrib]
      congr 1
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc ∏ j : Fin r, (2 : ℝ) ^ (kwin r L j)
        ≤ ∏ j : Fin r, (2 * lam L (j.1 + 1)) := hstep1
      _ = (2 : ℝ) ^ r * ∏ j : Fin r, lam L (j.1 + 1) := hstep2
      _ ≤ (2 : ℝ) ^ r * (Kmink * (Δ + 1)) :=
            mul_le_mul_of_nonneg_left hlam (by positivity)
      _ = (2 : ℝ) ^ r * Kmink * (Δ + 1) := by ring
  -- The threshold `M = 2^r * Kmink * (Δ+1)` is at least one.
  have hM : 1 ≤ (2 : ℝ) ^ r * Kmink * (Δ + 1) := by
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ r := one_le_pow₀ (by norm_num)
    have h2 : (1 : ℝ) ≤ Δ + 1 := by linarith
    have ha : (1 : ℝ) ≤ (2 : ℝ) ^ r * Kmink := by
      nlinarith [h1, hKmink, pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) r]
    have hb : (0 : ℝ) < (2 : ℝ) ^ r * Kmink := by positivity
    nlinarith [ha, h2, hb]
  refine ⟨hwin.2.2.1, hwin.2.2.2 _ hM hprod, ?_⟩
  -- Each individual window exponent is at most the sum, hence at most the threshold.
  intro j
  exact le_trans (Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ j))
    (hwin.2.2.2 _ hM hprod)

end Work.HP
