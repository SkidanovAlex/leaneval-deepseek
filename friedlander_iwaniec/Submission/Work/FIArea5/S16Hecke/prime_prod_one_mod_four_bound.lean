import Mathlib
import Submission.Commons.NumberTheory.LSeries.riemannZeta_norm_le_inv_sub_one
import Submission.Work.FIArea5.S16Hecke.prod_le_zeta_mul_chi4LSeries
import Submission.Work.FIArea5.S16Hecke.chi4LSeries_rpow_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped BigOperators

namespace Work.FIArea5.S16Hecke

/-- Euler-product comparison `P(σ) ≤ ζ(σ)·L(σ,χ₄)` (proved in
`prod_le_zeta_mul_chi4LSeries`), combined with the bound `ζ(σ) ≤ 2/(σ-1)` and the
uniform boundedness of `L(σ,χ₄)` on `1 < σ ≤ 2` (`chi4LSeries_rpow_bound`). -/
theorem prime_prod_one_mod_four_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      (∏' p : Nat.Primes,
        (if (p : ℕ) % 4 = 1 then (1 + ((p : ℕ) : ℝ) ^ (-σ)) ^ 2
         else (1 + ((p : ℕ) : ℝ) ^ (-2 * σ)))) ≤ C / (σ - 1) := by
  obtain ⟨C, hCpos, hC⟩ := chi4LSeries_rpow_bound
  refine ⟨2 * C, by linarith, fun σ h1 h2 => ?_⟩
  have hA := prod_le_zeta_mul_chi4LSeries σ h1
  have hL := hC σ h1 h2
  have hZ0 := Commons.NumberTheory.LSeries.tsum_nat_rpow_neg_le_inv σ h1
  have hZ : (∑' n : ℕ, (n : ℝ) ^ (-σ)) ≤ 2 / (σ - 1) := by
    refine le_trans hZ0 ?_
    have h1' : (1 : ℝ) ≤ 1 / (σ - 1) := by
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < σ - 1)]
      linarith
    have h2e : (2 : ℝ) / (σ - 1) = 2 * (1 / (σ - 1)) := by ring
    rw [h2e]; linarith
  have hs1 : 0 ≤ ∑' n : ℕ, (n : ℝ) ^ (-σ) :=
    tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  calc ∏' p : Nat.Primes,
        (if (p : ℕ) % 4 = 1 then (1 + ((p : ℕ) : ℝ) ^ (-σ)) ^ 2
         else (1 + ((p : ℕ) : ℝ) ^ (-2 * σ)))
      ≤ (∑' n : ℕ, (n : ℝ) ^ (-σ))
          * (∑' n : ℕ, ((ZMod.χ₄ ((n : ℕ) : ZMod 4) : ℤ) : ℝ) * (n : ℝ) ^ (-σ)) := hA
    _ ≤ (∑' n : ℕ, (n : ℝ) ^ (-σ))
          * |∑' n : ℕ, ((ZMod.χ₄ ((n : ℕ) : ZMod 4) : ℤ) : ℝ) * (n : ℝ) ^ (-σ)| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hs1
    _ ≤ (2 / (σ - 1)) * C := mul_le_mul hZ hL (abs_nonneg _) (by positivity)
    _ = 2 * C / (σ - 1) := by rw [div_mul_eq_mul_div]

end Work.FIArea5.S16Hecke
