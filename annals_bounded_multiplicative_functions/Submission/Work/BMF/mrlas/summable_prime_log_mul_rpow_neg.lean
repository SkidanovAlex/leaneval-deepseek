import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Summability of `∑_p log p · p^{-σ}` over the primes, for `σ > 1`

This is the elementary estimate that the series `∑_{p prime} log p / p ^ σ` converges for
`σ > 1`.  Since `Real.log n = O(n ^ ε)` for every `ε > 0`, the general term is dominated by
`n ^ (ε - σ)`, which is a convergent `p`-series as soon as `ε < σ - 1`.  Summability over `ℕ`
then restricts to the subtype `Nat.Primes`.
-/

open Filter Asymptotics

namespace Work.BMF.mrlas

theorem summable_prime_log_mul_rpow_neg (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun p : Nat.Primes => Real.log (p : ℝ) * (p : ℝ) ^ (-σ)) := by
  -- Step 1: the same series over all natural numbers is summable.
  have hmain : Summable (fun n : ℕ => Real.log (n : ℝ) * (n : ℝ) ^ (-σ)) := by
    set ε : ℝ := (σ - 1) / 2 with hε
    have hεpos : 0 < ε := by rw [hε]; linarith
    have hlt : ε - σ < -1 := by rw [hε]; linarith
    have hg : Summable (fun n : ℕ => (n : ℝ) ^ (ε - σ)) := Real.summable_nat_rpow.mpr hlt
    refine summable_of_isBigO_nat hg ?_
    -- `Real.log n = O(n ^ ε)`, hence `log n * n ^ (-σ) = O(n ^ (ε - σ))`.
    have hlogO : (fun n : ℕ => Real.log (n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ ε) := by
      exact (isLittleO_log_rpow_atTop hεpos).isBigO.comp_tendsto
        (tendsto_natCast_atTop_atTop : Tendsto (Nat.cast : ℕ → ℝ) atTop atTop)
    have hmul := hlogO.mul (isBigO_refl (fun n : ℕ => (n : ℝ) ^ (-σ)) atTop)
    refine hmul.congr' (Filter.EventuallyEq.rfl) ?_
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hpos : (0 : ℝ) < n := by exact_mod_cast hn
    rw [← Real.rpow_add hpos ε (-σ)]
    ring_nf
  -- Step 2: restrict to the subtype of primes.
  exact hmain.subtype (fun n : ℕ => n.Prime)

end Work.BMF.mrlas
