import Mathlib
import Submission.Work.FunctionalEquations.Basic

/-!
# Summability and exponential decay of a polynomially bounded coefficient tail

This file proves `Work.FunctionalEquations.SummableNormExpTail`, the estimate used
when bounding the tails of the Dirichlet series attached to the interpolation
basis.

Given coefficients `c m` (indexed by the integers `m ≥ 1`) with polynomial growth
`‖c m‖ ≤ C (m+1)^N` and with `c 1 = 0`, the weighted exponential tail
`∑_m ‖c m‖ e^{-2π m y}` is bounded by a constant times `e^{-4π y}` for every
`y ≥ 1`.

The only analytic input is the summability of `n ↦ n^N r^n` for `0 ≤ r < 1`,
combined with the elementary pointwise estimate `e^{-2π m y} ≤ e^{4π} e^{-4π y} e^{-2π m}`
valid for `m ≥ 2` and `y ≥ 1` (which is just `(m-2)(y-1) ≥ 0`).

## Main result

* `Work.FunctionalEquations.SummableNormExpTail`
-/

namespace Work.FunctionalEquations

open scoped BigOperators

/-- The weight `n ↦ ((n:ℝ)+1)^N e^{-2π n}` is summable.

We obtain it from Mathlib's `Real.summable_pow_mul_exp_neg_nat_mul` (summability of
`n ↦ n^N e^{-r n}` for `r > 0`) by shifting the index: with `r = 2π > 0`,
`((n+1))^N e^{-2π(n+1)}` is summable, and multiplying by `e^{2π}` recovers
`((n:ℝ)+1)^N e^{-2π n}`. -/
lemma summable_exp_tail_weight (N : ℕ) :
    Summable (fun n : ℕ => ((n:ℝ)+1)^N * Real.exp (-(2*Real.pi * (n:ℝ)))) := by
  have hP : 0 < 2 * Real.pi := by positivity
  have hF : Summable (fun n : ℕ => (n:ℝ)^N * Real.exp (-(2*Real.pi) * (n:ℝ))) := by
    have := Real.summable_pow_mul_exp_neg_nat_mul N hP
    simpa only [neg_mul] using this
  have hG : Summable (fun n : ℕ => (((n:ℝ)+1)^N) * Real.exp (-(2*Real.pi * ((n:ℝ)+1)))) := by
    have := (summable_nat_add_iff 1).mpr hF
    simpa only [Nat.cast_add, Nat.cast_one, neg_mul] using this
  have hW : Summable (fun n : ℕ =>
      Real.exp (2*Real.pi) * ((((n:ℝ)+1)^N) * Real.exp (-(2*Real.pi * ((n:ℝ)+1))))) :=
    hG.mul_left (Real.exp (2*Real.pi))
  refine hW.congr (fun n => ?_)
  have he : Real.exp (2*Real.pi) * Real.exp (-(2*Real.pi * ((n:ℝ)+1)))
      = Real.exp (-(2*Real.pi * (n:ℝ))) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [← he]; ring

/-- The same weight, restricted to the subtype of integers `m ≥ 1` and multiplied by
the constant `C`. -/
lemma summable_exp_tail_weight_subtype (C : ℝ) (N : ℕ) :
    Summable (fun m : Set.Ici (1:ℕ) =>
      C * (((m.1:ℝ)+1)^N * Real.exp (-(2*Real.pi * (m.1:ℝ))))) := by
  have h := (summable_exp_tail_weight N).comp_injective
    (Subtype.val_injective (p := fun n : ℕ => 1 ≤ n))
  exact h.mul_left C

/-- **Exponential decay of a polynomially bounded tail.**

If `‖c m‖ ≤ C (m+1)^N` for all `m ≥ 1` and `c 1 = 0`, then for every `y ≥ 1` the
weighted exponential tail `∑_m ‖c m‖ e^{-2π m y}` is bounded by a constant
(depending only on `c`, `C`, `N`) times `e^{-4π y}`. -/
theorem SummableNormExpTail {c : Set.Ici (1:ℕ) → ℂ} {C : ℝ} {N : ℕ} (hC : 0 ≤ C)
    (hc : ∀ m : Set.Ici (1:ℕ), ‖c m‖ ≤ C * ((m.1:ℝ) + 1) ^ N)
    (h1 : c ⟨1, by simp⟩ = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, 1 ≤ y →
      (∑' m : Set.Ici (1:ℕ), ‖c m‖ * Real.exp (-(2 * Real.pi * (m.1:ℝ) * y)))
        ≤ K * Real.exp (-(4 * Real.pi * y)) := by
  have hW_summable : Summable (fun m : Set.Ici (1:ℕ) =>
      C * (((m.1:ℝ)+1)^N * Real.exp (-(2*Real.pi * (m.1:ℝ))))) :=
    summable_exp_tail_weight_subtype C N
  have hW_nonneg : ∀ m : Set.Ici (1:ℕ),
      0 ≤ C * (((m.1:ℝ)+1)^N * Real.exp (-(2*Real.pi * (m.1:ℝ)))) := by
    intro m
    exact mul_nonneg hC (mul_nonneg (pow_nonneg (by positivity) N) (Real.exp_nonneg _))
  refine ⟨Real.exp (4*Real.pi) *
      (∑' m : Set.Ici (1:ℕ), C * (((m.1:ℝ)+1)^N * Real.exp (-(2*Real.pi * (m.1:ℝ))))), ?_, ?_⟩
  · exact mul_nonneg (Real.exp_nonneg _) (tsum_nonneg hW_nonneg)
  · intro y hy
    -- Pointwise bound of the summand by `e^{4π} e^{-4π y}` times the summable weight.
    have hFG : ∀ m : Set.Ici (1:ℕ),
        ‖c m‖ * Real.exp (-(2*Real.pi * (m.1:ℝ) * y))
          ≤ Real.exp (4*Real.pi) * Real.exp (-(4*Real.pi*y))
              * (C * (((m.1:ℝ)+1)^N * Real.exp (-(2*Real.pi * (m.1:ℝ))))) := by
      intro m
      by_cases hm1 : m.1 = 1
      · -- the `m = 1` term vanishes because `c 1 = 0`
        have hm_eq : m = ⟨1, by simp⟩ := Subtype.ext hm1
        rw [hm_eq, h1, norm_zero, zero_mul]
        exact mul_nonneg (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)) (hW_nonneg _)
      · -- for `m ≥ 2` use the exponential comparison
        have hm_ge : 1 ≤ m.1 := m.2
        have hm2 : (2:ℝ) ≤ (m.1:ℝ) := by
          have h2 : 2 ≤ m.1 := by omega
          exact_mod_cast h2
        have hA : 0 ≤ C * ((m.1:ℝ)+1)^N := mul_nonneg hC (pow_nonneg (by positivity) N)
        have hexp : Real.exp (-(2*Real.pi*(m.1:ℝ)*y))
            ≤ Real.exp (4*Real.pi) * Real.exp (-(4*Real.pi*y))
                * Real.exp (-(2*Real.pi*(m.1:ℝ))) := by
          rw [← Real.exp_add, ← Real.exp_add]
          apply Real.exp_le_exp.mpr
          -- the exponent inequality is `(m-2)(y-1) ≥ 0`
          have h1' : 0 ≤ ((m.1:ℝ) - 2) * (y - 1) := mul_nonneg (by linarith) (by linarith)
          nlinarith [Real.pi_pos, h1']
        calc ‖c m‖ * Real.exp (-(2*Real.pi*(m.1:ℝ)*y))
            ≤ (C * ((m.1:ℝ)+1)^N) * Real.exp (-(2*Real.pi*(m.1:ℝ)*y)) :=
              mul_le_mul_of_nonneg_right (hc m) (Real.exp_nonneg _)
          _ ≤ (C * ((m.1:ℝ)+1)^N)
                * (Real.exp (4*Real.pi) * Real.exp (-(4*Real.pi*y))
                    * Real.exp (-(2*Real.pi*(m.1:ℝ)))) :=
              mul_le_mul_of_nonneg_left hexp hA
          _ = Real.exp (4*Real.pi) * Real.exp (-(4*Real.pi*y))
                * (C * (((m.1:ℝ)+1)^N * Real.exp (-(2*Real.pi * (m.1:ℝ))))) := by ring
    have hG_summable : Summable (fun m : Set.Ici (1:ℕ) =>
        Real.exp (4*Real.pi) * Real.exp (-(4*Real.pi*y))
          * (C * (((m.1:ℝ)+1)^N * Real.exp (-(2*Real.pi * (m.1:ℝ)))))) :=
      hW_summable.mul_left (Real.exp (4*Real.pi) * Real.exp (-(4*Real.pi*y)))
    have hF_summable : Summable (fun m : Set.Ici (1:ℕ) =>
        ‖c m‖ * Real.exp (-(2*Real.pi * (m.1:ℝ) * y))) :=
      Summable.of_nonneg_of_le
        (fun m => mul_nonneg (norm_nonneg _) (Real.exp_nonneg _)) hFG hG_summable
    have hle := Summable.tsum_le_tsum hFG hF_summable hG_summable
    have htsum_eq : (∑' m : Set.Ici (1:ℕ), Real.exp (4*Real.pi) * Real.exp (-(4*Real.pi*y))
          * (C * (((m.1:ℝ)+1)^N * Real.exp (-(2*Real.pi * (m.1:ℝ))))))
        = (Real.exp (4*Real.pi) *
            (∑' m : Set.Ici (1:ℕ), C * (((m.1:ℝ)+1)^N * Real.exp (-(2*Real.pi * (m.1:ℝ))))))
          * Real.exp (-(4*Real.pi*y)) := by
      rw [tsum_mul_left]; ring
    rw [htsum_eq] at hle
    exact hle

end Work.FunctionalEquations
