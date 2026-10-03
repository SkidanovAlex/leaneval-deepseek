import Mathlib
import Submission.Work.FIArea5.S16Hecke.heckeLam_bound

namespace Work.FIArea5.S16Hecke

open scoped BigOperators

noncomputable section

/-- The comparison series `Σ_e (e+1) r^e` converges for `‖r‖ < 1`.  This is the convergence of the
local Hecke factor `Σ_ν λ(p^ν) p^{-νs}` at a prime, once `‖λ(p^ν)‖ = O(ν+1)`. -/
theorem summable_nat_succ_mul_geo {r : ℝ} (hr : ‖r‖ < 1) :
    Summable (fun e : ℕ => ((e : ℝ) + 1) * r ^ e) := by
  have h1 : Summable (fun e : ℕ => (e : ℝ) * r ^ e) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 (r := r) hr
  have h2 : Summable (fun e : ℕ => r ^ e) := summable_geometric_of_norm_lt_one hr
  simpa [add_mul, one_mul] using h1.add h2

/-- **Summability of the local Hecke factor.**  For a prime `p` and `‖z‖ < 1` the series
`Σ_e λ(p^e) z^e` converges (indeed absolutely), because `‖λ(p^e)‖ ≤ 4·(e+1)` — the number of
divisors of `p^e` being `e+1` — and `Σ_e (e+1) ‖z‖^e < ∞`.

This is the structural input that makes the Euler product of the Hecke `L`-series valid and that
bounds each local factor `Σ_ν λ(p^ν) p^{-νs} = 1 + O(p^{-σ})` for `σ > 1`. -/
theorem summable_heckeLam_pow_mul {chi : GaussianInt → ℂ} {k : ℤ} {p : ℕ} (hp : p.Prime)
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun e : ℕ => heckeLam chi k (p ^ e) * z ^ e) := by
  have hrz : ‖(‖z‖ : ℝ)‖ < 1 := by
    rwa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)]
  have hcmp : Summable (fun e : ℕ => 4 * ((e : ℝ) + 1) * ‖z‖ ^ e) := by
    simpa [mul_assoc] using (summable_nat_succ_mul_geo hrz).mul_left 4
  refine Summable.of_norm_bounded (f := fun e : ℕ => heckeLam chi k (p ^ e) * z ^ e)
    (g := fun e : ℕ => 4 * ((e : ℝ) + 1) * ‖z‖ ^ e) hcmp fun e => ?_
  have hp1 : 1 ≤ p ^ e := one_le_pow₀ hp.one_le
  have hbnd := heckeLam_bound chi k hb hp1
  have hcard : ((p ^ e).divisors.card : ℝ) = (e : ℝ) + 1 := by
    have h : (p ^ e).divisors.card = e + 1 := by
      rw [Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]
    rw [h]
    push_cast
    ring
  rw [norm_mul, norm_pow]
  calc ‖heckeLam chi k (p ^ e)‖ * ‖z‖ ^ e
      ≤ (4 * ((p ^ e).divisors.card : ℝ)) * ‖z‖ ^ e :=
        mul_le_mul_of_nonneg_right hbnd (by positivity)
    _ = 4 * ((e : ℝ) + 1) * ‖z‖ ^ e := by rw [hcard]

end

end Work.FIArea5.S16Hecke
