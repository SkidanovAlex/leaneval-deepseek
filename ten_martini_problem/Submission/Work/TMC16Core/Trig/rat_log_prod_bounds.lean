import Mathlib
import Submission.Work.TMC16Core.Basic.nnDist
import Submission.Work.TMC16Core.Trig.rat_prod_erase_sharp
import Submission.Work.TMC16Core.Trig.rat_prod_min_removed_v2

/-!
# Logarithmic bounds for the rational block product with the minimal factor removed

Avila–Jitomirskaya, *The Ten Martini Problem*, §9, use the two-sided estimate

  `2π^{-1} q ≤ ∏_{k ≠ k₁} 2|sin (2π (x + k p/(2q)))| ≤ 2q`

for `k₁ ∈ {1,…,q}` a minimiser of `k ↦ nn (2x + k p/q)` (`p, q` coprime, `q ≥ 1`), where
`nn` is the distance to the nearest integer.  In logarithms this reads

  `log (2q/π) ≤ log (∏_{k ≠ k₁} 2|sin (2π (x + k p/(2q)))|) ≤ log q.`

The lower bound is the sharp form of AJ (9.25) (`Trig/rat_prod_min_removed_v2`), the upper
bound is `Trig/rat_prod_erase_sharp`.  Both are stated for the product of `|sin|` factors;
multiplying by `2` at each of the `q - 1` remaining indices is exactly the factor
`2^{q-1}`, which together with the normalisation `q(2/π)/2^{q-1}` produces the `2q/π` above.
-/

namespace Work.TMC16Core.Trig

open Finset Work.TMC16Core.Basic

theorem rat_log_prod_bounds {L : ℕ} (hL : 0 < L) {p : ℤ} (hcop : Nat.Coprime p.natAbs L) (x : ℝ)
    {j₁ : ℕ} (hj₁ : j₁ ∈ Finset.Icc 1 L)
    (hmin : ∀ j ∈ Finset.Icc 1 L,
      Work.TMC16Core.Basic.nn (2 * x + (j₁ : ℝ) * ((p : ℝ) / (L : ℝ)))
        ≤ Work.TMC16Core.Basic.nn (2 * x + (j : ℝ) * ((p : ℝ) / (L : ℝ)))) :
    Real.log (2 * (L : ℝ) / Real.pi)
        ≤ Real.log (∏ j ∈ (Finset.Icc 1 L).erase j₁,
            (2 * Work.TMC16Core.Basic.S (2 * x + (j : ℝ) * ((p : ℝ) / (L : ℝ)))))
      ∧ Real.log (∏ j ∈ (Finset.Icc 1 L).erase j₁,
            (2 * Work.TMC16Core.Basic.S (2 * x + (j : ℝ) * ((p : ℝ) / (L : ℝ)))))
        ≤ Real.log (L : ℝ) := by
  classical
  set T : ℝ := ∏ j ∈ (Finset.Icc 1 L).erase j₁,
      (2 * S (2 * x + (j : ℝ) * ((p : ℝ) / (L : ℝ)))) with hT
  have hcard : ((Finset.Icc 1 L).erase j₁).card = L - 1 := by
    rw [Finset.card_erase_of_mem hj₁, Nat.card_Icc]
    omega
  -- minimality, transferred to the sine factors and to `S`
  have hminSin : ∀ k ∈ Finset.Icc 1 L,
      |Real.sin (2 * Real.pi * (x + (k : ℝ) * ((p : ℝ) / (2 * (L : ℝ)))))| ≥
        |Real.sin (2 * Real.pi * (x + (j₁ : ℝ) * ((p : ℝ) / (2 * (L : ℝ)))))| := by
    intro k hk
    rw [rpm_term_eq_S p L x k, rpm_term_eq_S p L x j₁]
    exact S_mono_of_nn_le (hmin k hk)
  -- the product of the `S` factors, split off from `T`
  have hTsplit : T = (2 : ℝ) ^ (L - 1) *
      ∏ j ∈ (Finset.Icc 1 L).erase j₁, S (2 * x + (j : ℝ) * ((p : ℝ) / (L : ℝ))) := by
    rw [hT, Finset.prod_mul_distrib, Finset.prod_const, hcard]
  -- lower bound for the product of `S` factors (AJ (9.25))
  have hSlow : (L : ℝ) * (2 / Real.pi) / 2 ^ (L - 1) ≤
      ∏ j ∈ (Finset.Icc 1 L).erase j₁, S (2 * x + (j : ℝ) * ((p : ℝ) / (L : ℝ))) := by
    have hprod : (∏ j ∈ (Finset.Icc 1 L).erase j₁,
          S (2 * x + (j : ℝ) * ((p : ℝ) / (L : ℝ))))
        = ∏ j ∈ (Finset.Icc 1 L).erase j₁,
            |Real.sin (2 * Real.pi * (x + (j : ℝ) * ((p : ℝ) / (2 * (L : ℝ)))))| :=
      Finset.prod_congr rfl (fun k _ => (rpm_term_eq_S p L x k).symm)
    rw [hprod]
    exact rat_prod_min_removed_v2 hL hcop x hj₁ hminSin
  -- upper bound for `T` (the sharp product bound)
  have hTup : T ≤ (L : ℝ) := by
    rw [hT]
    exact rat_prod_erase_sharp hL hcop x hj₁ hmin
  -- the `2^{L-1}` scaling turns `q(2/π)/2^{q-1}` into `2q/π`
  have hscal : (2 : ℝ) ^ (L - 1) * ((L : ℝ) * (2 / Real.pi) / 2 ^ (L - 1))
      = 2 * (L : ℝ) / Real.pi := by
    have hne : (2 : ℝ) ^ (L - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
  have hTlow : 2 * (L : ℝ) / Real.pi ≤ T := by
    rw [hTsplit, ← hscal]
    exact mul_le_mul_of_nonneg_left hSlow (by positivity)
  have hLpos : 0 < 2 * (L : ℝ) / Real.pi := by positivity
  have hTpos : 0 < T := lt_of_lt_of_le hLpos hTlow
  constructor
  · exact Real.log_le_log hLpos hTlow
  · exact Real.log_le_log hTpos hTup

end Work.TMC16Core.Trig
