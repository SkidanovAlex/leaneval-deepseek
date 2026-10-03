/-
# Shared helpers for the clamping lemma `vNormK_basic` (area A8)

The challenge's variational norm (`PointwiseErgodicTheorems.variationalNorm`) is the sum of the
supremum norm `⨆ n, ‖a n‖ₑ` and the *variation part*

`varPart r a = ⨆ (J : ℕ) (N : ℕ → ℕ) (_ : Monotone N),
  ENNReal.ofReal ‖WithLp.toLp r (fun i : Fin J ↦ a (N (i + 1)) - a (N i))‖`

(`variationalNorm_eq_add`, which holds by `rfl`).  The clamped quantities `supK` and `varK` of
`Submission.Work.KMTAreas.A8Defs` are the same two objects truncated at `K`.

This module contains the vocabulary and the bridge between the two forms of the `ℓ^r` norm of a
finite vector:
* `Work.KMTAreas.A8.varPart`;
* `Work.KMTAreas.A8.norm_toLp_eq_sum_rpow` / `ofReal_norm_toLp_eq_sum`: the norm of
  `WithLp.toLp r F` is `(∑ i, ‖F i‖ ^ r) ^ (1/r)`, in `ℝ` and in `ℝ≥0∞`.
-/
import Mathlib
import Submission.Work.KMTAreas.A8Defs

set_option autoImplicit false

namespace Work.KMTAreas.A8

open scoped BigOperators ENNReal NNReal

/-- The **variation part** of the challenge's variational norm: the second summand of
`PointwiseErgodicTheorems.variationalNorm`. -/
noncomputable def varPart (r : ℝ≥0) (a : ℕ → ℂ) : ℝ≥0∞ :=
  ⨆ (J : ℕ) (N : ℕ → ℕ) (_ : Monotone N),
    ENNReal.ofReal ‖(WithLp.toLp r (fun (i : Fin J) ↦ a (N (i + 1)) - a (N i)))‖

/-- `variationalNorm` is the supremum norm plus its variation part (definitional). -/
theorem variationalNorm_eq_add (r : ℝ≥0) (a : ℕ → ℂ) :
    PointwiseErgodicTheorems.variationalNorm r a = (⨆ n, ‖a n‖ₑ) + varPart r a := rfl

/-- The `ℓ^r` norm of a finite vector, in real `rpow`-sum form.  This is the bridge between the
`WithLp.toLp` form of the challenge's definition and the `rpow`-sum form of the clamped variation
`varK`. -/
theorem norm_toLp_eq_sum_rpow {J : ℕ} {r : ℝ≥0} (hr : 1 ≤ r) (F : Fin J → ℂ) :
    ‖WithLp.toLp r F‖ = (∑ i : Fin J, ‖F i‖ ^ (r : ℝ)) ^ (1 / (r : ℝ)) := by
  have hrt : ((r : ℝ≥0∞)).toReal = (r : ℝ) := ENNReal.coe_toReal r
  have hp : 0 < ((r : ℝ≥0∞)).toReal := by
    rw [hrt]
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hr)
  rw [PiLp.norm_eq_sum (p := (r : ℝ≥0∞)) hp, hrt]

/-- The same bridge in `ℝ≥0∞` form: `ENNReal.ofReal` of the `ℓ^r` norm of `WithLp.toLp r F` is
the `rpow`-sum of the extended norms of the coordinates. -/
theorem ofReal_norm_toLp_eq_sum {J : ℕ} {r : ℝ≥0} (hr : 1 ≤ r) (F : Fin J → ℂ) :
    ENNReal.ofReal ‖WithLp.toLp r F‖ = (∑ i : Fin J, ‖F i‖ₑ ^ (r : ℝ)) ^ (1 / (r : ℝ)) := by
  rw [norm_toLp_eq_sum_rpow hr F]
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hr)
  rw [← ENNReal.ofReal_rpow_of_nonneg
        (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _) (by positivity)]
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => by
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (le_of_lt hr0), ofReal_norm])

end Work.KMTAreas.A8
