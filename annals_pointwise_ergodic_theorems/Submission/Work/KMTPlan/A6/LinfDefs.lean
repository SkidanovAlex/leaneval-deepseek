/-
# Helper layer for the `Linf` (bounded-bump) versions of the Case B chain

The interface `Work.KMTPlan.A6.SSUBodyAtLinf` differs from `SSUBodyAt` by the two extra
hypotheses `MemLp (periodize φ) ⊤ circleMeasure`, `MemLp (periodize ψ) ⊤ circleMeasure` on the
bumps.  Consequently every consumer of the single-scale estimate has to *produce* those two facts
at its own bumps.  This module collects the closure lemmas that do it:

* `memLp_periodize_of_arc`: a measurable function supported in the arc `|ξ| ≤ R` and bounded by
  `C` has a periodisation in `L^∞(ℝ/ℤ)` (a wrapper of `memLp_periodize`);
* `memLp_periodize_randSymb`: the same for the randomised symbol
  `randSymb φ ε K = ∑_{n < K} ε n • (φ (n+1) - φ n)`, whose members all share the arc `|ξ| ≤ R`
  and a common bound `B`;
* `measurable_varphiNtj`, `measurable_varphitildeNtj`: the (uncurried) measurability of the two
  modified bumps, in the frequency variable.

Everything is placed in the namespace `Work.KMTPlan.A6.Linf` so that it cannot collide with the
declarations of the original Case B chain.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.lowModSymbFAux

namespace Work.KMTPlan.A6.Linf

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

/-! ## `MemLp ⊤` from measurability, narrow support and boundedness -/

/-- **The periodisation of a measurable function supported in `|ξ| ≤ R` and bounded by `C` is in
`L^∞(ℝ/ℤ)`.**  This is `Work.Analysis.IonescuWainger.memLp_periodize` with the support hypothesis
in the "non-vanishing" form used by the Case B chain. -/
theorem memLp_periodize_of_arc (φ : ℝ → ℂ) (hmeas : Measurable φ) (R C : ℝ) (hR : 0 ≤ R)
    (harc : ∀ ξ : ℝ, φ ξ ≠ 0 → |ξ| ≤ R) (hC : ∀ ξ : ℝ, ‖φ ξ‖ ≤ C) :
    MeasureTheory.MemLp (periodize φ) ⊤ circleMeasure :=
  Work.Analysis.IonescuWainger.memLp_periodize hmeas hR
    (fun x hx => by
      by_contra h
      exact absurd (harc x h) (not_le.mpr hx)) hC

/-- **The periodisation of a randomised symbol is in `L^∞(ℝ/ℤ)`.**  If every member of the family
`φ` is measurable, supported in `|ξ| ≤ R` (in the non-vanishing form) and bounded by `B`, and the
coefficients obey `‖ε n‖ ≤ 1`, then `periodize (randSymb φ ε K)` is bounded by `∑_{n<K} 2 B` and
measurable. -/
theorem memLp_periodize_randSymb {φ : ℕ → ℝ → ℂ} {R B : ℝ} (hR : 0 ≤ R)
    (hmeas : ∀ n : ℕ, Measurable (φ n))
    (harc : ∀ (n : ℕ) (ξ : ℝ), φ n ξ ≠ 0 → |ξ| ≤ R)
    (hbd : ∀ (n : ℕ) (ξ : ℝ), ‖φ n ξ‖ ≤ B) (ε : ℕ → ℂ) (hε : ∀ n : ℕ, ‖ε n‖ ≤ 1) (K : ℕ) :
    MeasureTheory.MemLp (periodize (Work.KMTAreas.A7.randSymb φ ε K)) ⊤ circleMeasure := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hbd 0 0)
  refine memLp_periodize_of_arc (Work.KMTAreas.A7.randSymb φ ε K) ?_ R ((K : ℝ) * (2 * B))
    hR ?_ ?_
  · change Measurable fun ξ : ℝ => ∑ n ∈ Finset.range K, ε n * (φ (n + 1) ξ - φ n ξ)
    exact Finset.measurable_sum _ fun n _ =>
      (Measurable.sub (hmeas (n + 1)) (hmeas n)).const_mul (ε n)
  · intro x hx
    obtain ⟨n, _, hn⟩ := Work.KMTPlan.A6.exists_ne_zero_of_randSymb_ne_zero hx
    exact harc n x hn
  · intro x
    change ‖∑ n ∈ Finset.range K, ε n * (φ (n + 1) x - φ n x)‖ ≤ (K : ℝ) * (2 * B)
    calc ‖∑ n ∈ Finset.range K, ε n * (φ (n + 1) x - φ n x)‖
        ≤ ∑ n ∈ Finset.range K, ‖ε n * (φ (n + 1) x - φ n x)‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.range K, 2 * B := by
          refine Finset.sum_le_sum fun n _ => ?_
          rw [norm_mul]
          calc ‖ε n‖ * ‖φ (n + 1) x - φ n x‖
              ≤ 1 * (‖φ (n + 1) x‖ + ‖φ n x‖) :=
                mul_le_mul (hε n) (norm_sub_le _ _) (norm_nonneg _) (by norm_num)
            _ ≤ 1 * (B + B) := by
                have h := add_le_add (hbd (n + 1) x) (hbd n x)
                linarith
            _ = 2 * B := by ring
      _ = (K : ℝ) * (2 * B) := by simp

/-! ## Measurability of the modified bumps -/

/-- The modified `f`-side bump `varphiNtj N k j t` is measurable in its frequency variable. -/
theorem measurable_varphiNtj (N k : ℕ) (j : ℤ) (hj : j ∈ ({-1, 0, 1} : Finset ℤ)) (t : ℝ) :
    Measurable (Work.KMTPlan.A6.varphiNtj N k j t) :=
  (Work.KMTPlan.A6.measurable_varphiNtj_uncurryEx N k j hj).comp
    (measurable_const.prodMk measurable_id)

/-- The modified `g`-side bump `varphitildeNtj P N k j t` is measurable in its frequency
variable. -/
theorem measurable_varphitildeNtj (P : Polynomial ℤ) (N k : ℕ) (j : ℤ)
    (hj : j ∈ ({-1, 0, 1} : Finset ℤ)) (t : ℝ) :
    Measurable (Work.KMTPlan.A6.varphitildeNtj P N k j t) :=
  (Work.KMTPlan.A6.measurable_varphitildeNtj_uncurryEx P N k j hj).comp
    (measurable_const.prodMk measurable_id)

end Work.KMTPlan.A6.Linf
