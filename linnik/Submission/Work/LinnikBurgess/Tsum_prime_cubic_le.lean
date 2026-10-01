import Mathlib
import Submission.Work.LinnikBurgess.cubic_phase_defs
import Submission.Work.LinnikBurgess.additive_weil_bound_poly_explicit

/-!
# The `K = 1` cubic Weyl bound over a prime field

This module proves

`‖Tsum p (CubicPhase p β γ δ R)‖ ≤ 8 · p^(2/3)`

for `p` a prime with `p ≥ 5` and `δ` a `p`-unit.

Since `p · R` is divisible by `p`, the phase only matters modulo `p`, so `Tsum p H` is the
complete exponential sum over `F_p` of a *cubic* polynomial with a unit leading coefficient.
Weil's bound for additive exponential sums over a prime field, in its quantitative form
(`additive_weil_bound_poly_explicit`, proved from the Artin–Schreier point count via Stepanov's
method), gives

`‖Tsum p H‖ ≤ 2 · 3 · √p = 6 √p ≤ 8 p^(2/3)`.

This is the base case `K = 1` of `cubic_phase_prime_pow`.
-/

namespace Work.LinnikBurgess

open Polynomial
open scoped BigOperators

/-- The reduction of the phase `CubicPhase p β γ δ R` modulo `p`: the term `p · R` disappears,
leaving the cubic polynomial `β X + γ X² + δ X³`. -/
lemma cubicPhase_map_eq_modP (p : ℕ) (β γ δ : ℤ) (R : Polynomial ℤ) :
    (CubicPhase p β γ δ R).map (Int.castRingHom (ZMod p))
      = Polynomial.C (β : ZMod p) * Polynomial.X + Polynomial.C (γ : ZMod p) * Polynomial.X ^ 2
        + Polynomial.C (δ : ZMod p) * Polynomial.X ^ 3 := by
  simp [CubicPhase]

/-- The reduction modulo `p` of a genuine cubic phase is a cubic polynomial: its leading
coefficient is the `p`-unit `δ`. -/
lemma cubicPhase_map_natDegree_eq_three (p : ℕ) [Fact p.Prime] (β γ δ : ℤ) (R : Polynomial ℤ)
    (hδ : ¬ (p : ℤ) ∣ δ) :
    ((CubicPhase p β γ δ R).map (Int.castRingHom (ZMod p))).natDegree = 3 := by
  rw [cubicPhase_map_eq_modP]
  have hδz : (δ : ZMod p) ≠ 0 := fun h => hδ ((ZMod.intCast_zmod_eq_zero_iff_dvd δ p).mp h)
  compute_degree!

/-- `Tsum` of a polynomial with integer coefficients is the complete additive-character sum over
`ZMod p` of its reduction modulo `p`. -/
lemma Tsum_eq_zmod_stdAddChar_sum (p : ℕ) [Fact p.Prime] (H : Polynomial ℤ) :
    Commons.NumberTheory.GaussSum.Tsum p H
      = ∑ x : ZMod p, ZMod.stdAddChar ((H.map (Int.castRingHom (ZMod p))).eval x) := by
  rw [← Commons.NumberTheory.GaussSum.gsum_eq_Tsum p H]
  simp only [Commons.NumberTheory.GaussSum.gsum]
  exact Finset.sum_congr rfl (fun x _ => by rw [Polynomial.eval₂_eq_eval_map])

/-- **The `K = 1` cubic Weyl bound.**  For a prime `p ≥ 5` and a cubic phase with `p`-unit
cubic coefficient, the complete exponential sum over `ZMod p` is `O(√p)`, in particular
`≤ 8 p^(2/3)`. -/
theorem Tsum_prime_cubic_le (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (β γ δ : ℤ) (R : Polynomial ℤ)
    (hδ : ¬ (p : ℤ) ∣ δ) :
    ‖Commons.NumberTheory.GaussSum.Tsum p (Work.LinnikBurgess.CubicPhase p β γ δ R)‖
      ≤ 8 * (p : ℝ) ^ ((2 : ℝ) / 3) := by
  have hp3 : 3 < p := by omega
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  -- `√p ≤ p^(2/3)` since `p ≥ 1`
  have hsqrt : Real.sqrt (p : ℝ) ≤ (p : ℝ) ^ ((2 : ℝ) / 3) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hp1 (by norm_num)
  have hdeg := cubicPhase_map_natDegree_eq_three p β γ δ R hδ
  have hT := Tsum_eq_zmod_stdAddChar_sum p (CubicPhase p β γ δ R)
  -- Weil's bound for the reduced cubic phase
  have hb := additive_weil_bound_poly_explicit p
    ((CubicPhase p β γ δ R).map (Int.castRingHom (ZMod p)))
    (by rw [hdeg]; norm_num) (by rw [hdeg]; exact hp3)
  rw [hT]
  refine hb.trans ?_
  rw [hdeg]
  have h6 : (6 : ℝ) * Real.sqrt (p : ℝ) ≤ 6 * (p : ℝ) ^ ((2 : ℝ) / 3) :=
    mul_le_mul_of_nonneg_left hsqrt (by norm_num)
  have h0 : (0 : ℝ) ≤ (p : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_nonneg (by positivity) _
  have h68 : (6 : ℝ) * (p : ℝ) ^ ((2 : ℝ) / 3) ≤ 8 * (p : ℝ) ^ ((2 : ℝ) / 3) := by linarith
  linarith

end Work.LinnikBurgess
