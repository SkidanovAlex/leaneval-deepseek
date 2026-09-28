import Mathlib
import Submission.Work.HP.PairsAux
import Submission.Work.HP.Defs

/-!
# The rank-`2` window-membership bound

Specialisation of the general window-membership estimate to rank `2`.  Given an integral
lattice `L ⊆ ℤ^{n+1}` of rank `2` whose successive minima satisfy the dyadic window
property `λ_{j+1} ≤ 2^{kwin j} ≤ 2 λ_{j+1}` (with `kwin` monotone and the product bound
upgraded to a sum bound), and given `∏_{j=1}^{2} λ_j ≤ K_mink · detL L` together with
`detL L ≤ Δ+1`, the window exponents are monotone and are all bounded by the single
dyadic threshold `⌈log₂ (2^2 · K_mink · (Δ+1))⌉`.

Indeed `2^{kwin j} ≤ 2 λ_{j+1}`, so `∏_j 2^{kwin j} ≤ 2^2 · ∏_j λ_{j+1} ≤ 2^2 · K_mink ·
(Δ+1)`, and the window property turns this product bound into a bound on the sum, hence
on each individual exponent.
-/

namespace Work.HP.Sig2

set_option linter.unusedVariables false

theorem win_membership_r2 (n : ℕ)
    (Kmink Δ : ℝ) (hKmink : 1 ≤ Kmink) (hΔ : 1 ≤ Δ)
    (L : Submodule ℤ (Fin (n + 1) → ℤ)) (hrL : rk L = 2) (hdet : detL L ≤ Δ + 1)
    (hmink : (∏ j ∈ Finset.range (rk L), lam L (j + 1)) ≤ Kmink * detL L)
    (hwin : (∀ j : Fin 2, lam L (j.1 + 1) ≤ (2 : ℝ) ^ (kwin 2 L j)) ∧
      (∀ j : Fin 2, (2 : ℝ) ^ (kwin 2 L j) ≤ 2 * lam L (j.1 + 1)) ∧
      Monotone (kwin 2 L) ∧
      (∀ M : ℝ, 1 ≤ M → (∏ j : Fin 2, (2 : ℝ) ^ (kwin 2 L j)) ≤ M →
        (∑ j : Fin 2, kwin 2 L j) ≤ ⌈Real.logb 2 M⌉₊)) :
    Monotone (kwin 2 L) ∧
      (∑ j : Fin 2, kwin 2 L j) ≤ ⌈Real.logb 2 ((2 : ℝ) ^ 2 * Kmink * (Δ + 1))⌉₊ ∧
      (∀ j : Fin 2, kwin 2 L j ≤ ⌈Real.logb 2 ((2 : ℝ) ^ 2 * Kmink * (Δ + 1))⌉₊) := by
  obtain ⟨_, hwin2, hmono, hwin4⟩ := hwin
  -- Bound the product of the two successive minima by `Kmink * (Δ+1)`.
  have hlam : ∏ j : Fin 2, lam L (j.1 + 1) ≤ Kmink * (Δ + 1) := by
    rw [Fin.prod_univ_eq_prod_range (fun j => lam L (j + 1)) 2, ← hrL]
    calc ∏ j ∈ Finset.range (rk L), lam L (j + 1)
        ≤ Kmink * detL L := hmink
      _ ≤ Kmink * (Δ + 1) := mul_le_mul_of_nonneg_left hdet (by linarith)
  -- Convert this into a bound on the product of the dyadic thresholds.
  have hprod : ∏ j : Fin 2, (2 : ℝ) ^ (kwin 2 L j) ≤ (2 : ℝ) ^ 2 * Kmink * (Δ + 1) := by
    have hstep1 : ∏ j : Fin 2, (2 : ℝ) ^ (kwin 2 L j) ≤ ∏ j : Fin 2, (2 * lam L (j.1 + 1)) := by
      apply Finset.prod_le_prod₀
      · intro j _; positivity
      · intro j _; exact hwin2 j
    have hstep2 : ∏ j : Fin 2, (2 * lam L (j.1 + 1))
        = (2 : ℝ) ^ 2 * ∏ j : Fin 2, lam L (j.1 + 1) := by
      rw [Finset.prod_mul_distrib]
      congr 1
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc ∏ j : Fin 2, (2 : ℝ) ^ (kwin 2 L j)
        ≤ ∏ j : Fin 2, (2 * lam L (j.1 + 1)) := hstep1
      _ = (2 : ℝ) ^ 2 * ∏ j : Fin 2, lam L (j.1 + 1) := hstep2
      _ ≤ (2 : ℝ) ^ 2 * (Kmink * (Δ + 1)) :=
            mul_le_mul_of_nonneg_left hlam (by positivity)
      _ = (2 : ℝ) ^ 2 * Kmink * (Δ + 1) := by ring
  -- The threshold `M = 2^2 * Kmink * (Δ+1)` is at least one.
  have hM : 1 ≤ (2 : ℝ) ^ 2 * Kmink * (Δ + 1) := by
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ 2 := one_le_pow₀ (by norm_num)
    have h2 : (1 : ℝ) ≤ Δ + 1 := by linarith
    have ha : (1 : ℝ) ≤ (2 : ℝ) ^ 2 * Kmink := by
      nlinarith [h1, hKmink, pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) 2]
    have hb : (0 : ℝ) < (2 : ℝ) ^ 2 * Kmink := by positivity
    nlinarith [ha, h2, hb]
  refine ⟨hmono, hwin4 _ hM hprod, ?_⟩
  -- Each individual exponent is at most the sum, hence at most the threshold.
  intro j
  exact le_trans (Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ j))
    (hwin4 _ hM hprod)

end Work.HP.Sig2
