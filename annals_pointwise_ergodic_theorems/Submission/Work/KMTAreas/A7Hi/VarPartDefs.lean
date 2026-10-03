/-
# The two summands of the variational norm, and the chaining bound

`PointwiseErgodicTheorems.variationalNorm r a` is, by definition, the sum of the supremum norm
`⨆ n, ‖a n‖ₑ` and the *variation part* `varPart r a` (a supremum over all chains of indices of
the `ℓ^r` norm of the successive differences).

This file names the second summand (`varPart`) and records the two elementary facts about it that
the variational estimates use:

* `variationalNorm_eq_sup_add_varPart` (definitional);
* `varPart_le_variationalNorm` (the variation part is dominated by the full norm);
* `enorm_le_enorm_zero_add_varPart` — **the chaining bound**: for `1 ≤ r` and every `n`,
  `‖a n‖ₑ ≤ ‖a 0‖ₑ + varPart r a`, since `a n = a 0 + (a n - a 0)` and `(a n - a 0)` is the single
  jump of the chain `0, n`.
-/
import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.FourierL2Defs
import Submission.Work.KMTAreas.A7.LargeInterface

namespace Work.KMTAreas.A7Hi

open MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- The **variation part** of the variational norm: the second summand of
`PointwiseErgodicTheorems.variationalNorm`, i.e. the supremum, over all chains
`N : ℕ → ℕ` (monotone) and all lengths `J`, of the `ℓ^r` norm of the jumps
`a (N (i+1)) - a (N i)`. -/
def varPart (r : NNReal) (a : ℕ → ℂ) : ℝ≥0∞ :=
  ⨆ (J : ℕ) (N : ℕ → ℕ) (_ : Monotone N),
    ENNReal.ofReal ‖(WithLp.toLp r (fun (i : Fin J) ↦ a (N (i + 1)) - a (N i)))‖

/-- The variational norm is the supremum norm plus the variation part. -/
theorem variationalNorm_eq_sup_add_varPart (r : NNReal) (a : ℕ → ℂ) :
    PointwiseErgodicTheorems.variationalNorm r a = (⨆ n, ‖a n‖ₑ) + varPart r a := rfl

/-- The variation part is dominated by the full variational norm. -/
theorem varPart_le_variationalNorm (r : NNReal) (a : ℕ → ℂ) :
    varPart r a ≤ PointwiseErgodicTheorems.variationalNorm r a := le_add_left le_rfl

/-- The `ℓ^r` norm (`WithLp`/`PiLp` norm) of a one-element family is the modulus. -/
theorem norm_toLp_fin_one (r : NNReal) (hr : 1 ≤ r) (c : ℂ) :
    ‖(WithLp.toLp r (fun _ : Fin 1 ↦ c) : WithLp r (Fin 1 → ℂ))‖ = ‖c‖ := by
  have hrpos : (0 : ℝ) < (r : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hr)
  have hp : 0 < ((r : ℝ≥0∞)).toReal := by
    simpa using hrpos
  rw [PiLp.norm_eq_sum hp, Fin.sum_univ_one]
  have hcoe : ((r : ℝ≥0∞)).toReal = (r : ℝ) := ENNReal.coe_toReal r
  rw [hcoe, ← Real.rpow_mul (norm_nonneg c), one_div, mul_inv_cancel₀ (ne_of_gt hrpos),
    Real.rpow_one]

/-- **The chaining bound.**  Every value of the sequence is bounded by the initial value plus the
variation part. -/
theorem enorm_le_enorm_zero_add_varPart (r : NNReal) (hr : 1 ≤ r) (a : ℕ → ℂ) (n : ℕ) :
    ‖a n‖ₑ ≤ ‖a 0‖ₑ + varPart r a := by
  let N : ℕ → ℕ := fun k ↦ if k = 0 then 0 else n
  have hmono : Monotone N := by
    intro k l hkl
    by_cases hk : k = 0
    · subst hk
      simp only [N]
      split_ifs <;> omega
    · have hl0 : l ≠ 0 := by omega
      simp only [N, hk, hl0, if_false]
      exact le_rfl
  have hterm : ENNReal.ofReal ‖a n - a 0‖ ≤ varPart r a := by
    refine le_iSup_of_le (1 : ℕ) ?_
    refine le_iSup_of_le N ?_
    refine le_iSup_of_le hmono ?_
    have hvec : (fun i : Fin 1 ↦ a (N (i + 1)) - a (N i)) = fun _ : Fin 1 ↦ a n - a 0 := by
      funext i
      have hi : (i : ℕ) = 0 := by have := i.isLt; omega
      simp [N, hi]
    rw [hvec, norm_toLp_fin_one r hr]
  calc ‖a n‖ₑ = ‖a 0 + (a n - a 0)‖ₑ := by rw [add_sub_cancel]
    _ ≤ ‖a 0‖ₑ + ‖a n - a 0‖ₑ := enorm_add_le _ _
    _ = ‖a 0‖ₑ + ENNReal.ofReal ‖a n - a 0‖ := by rw [ofReal_norm]
    _ ≤ ‖a 0‖ₑ + varPart r a := add_le_add le_rfl hterm

end

end Work.KMTAreas.A7Hi
