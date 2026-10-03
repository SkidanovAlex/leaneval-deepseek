import Mathlib
import Submission.Work.Analysis.Paraproduct.SmallScale
import Submission.Work.KMTAreas.A7Hi.LowpassDefs
import Submission.Work.BourgainPlan.Maximal.varRhoSplitting
import Submission.Commons.Analysis.ExponentialSums.monic_poly_major_arc_approx_coeff
import Submission.Commons.Analysis.ExponentialSums.weyl_inequality
import Submission.Commons.Analysis.Fourier.fourier_comp_mul_left
import Submission.Commons.Analysis.HardyLittlewood.discrete_forward_maximal
import Submission.Work.Analysis.ExponentialSums.model721_bundle
import Submission.Work.BourgainPlan.IonescuWainger.ArcFinsetDefs
import Submission.Work.BourgainPlan.IonescuWainger.OpArcDefs
import Submission.Work.BourgainPlan.IonescuWainger.tsum_norm_sq_eq_norm_ftLp
import Submission.Work.BourgainPlan.Maximal.rhoVarReductions

set_option autoImplicit false

namespace Work.KMTAreas.A7G

open scoped ENNReal NNReal BigOperators

open Work.BourgainPlan.Maximal (chainLp)

/-! ## Elementary bookkeeping for the variational norms

This file proves the abstract bookkeeping lemma that lets an estimate for the `2`-variation of a
sequence `a` control the `V^r`-norm (`r ≥ 2`) of any *subsequence* `n ↦ a (σ n)` of it, at the price
of the initial value `‖a 0‖` and a factor `2`.  No analysis is involved: the content is (i) the
elementary `V^r ≤ V^2` for `r ≥ 2` (landed in `Work.Analysis.Paraproduct.SmallScale`), (ii) the
`ℓ²` identification of the `WithLp` norm with the `chainLp 2` sum, and (iii) the fact that a monotone
reindexing of a chain is again a chain. -/

/-- **The `ℓ^r` norm of `WithLp.toLp r F` in terms of extended norms**: for `1 ≤ r`,

`ofReal ‖WithLp.toLp r F‖ = (∑ i, ‖F i‖ₑ ^ r) ^ (1/r)`.

This is the bridge between the challenge's `WithLp`-based model of the `ℓ^r` norm and the
`ℝ≥0∞`-valued `rpow`-sum model used by the `varRho`/`Vr` machinery. -/
lemma ofReal_norm_toLp_eq_sum (r : NNReal) (hr : 1 ≤ r) {J : ℕ} (F : Fin J → ℂ) :
    ENNReal.ofReal ‖WithLp.toLp r F‖ = (∑ i : Fin J, ‖F i‖ₑ ^ (r : ℝ)) ^ (1 / (r : ℝ)) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hr)
  have hrt : ((r : ℝ≥0∞)).toReal = (r : ℝ) := ENNReal.coe_toReal r
  have hp : 0 < ((r : ℝ≥0∞)).toReal := by rw [hrt]; linarith
  rw [PiLp.norm_eq_sum (p := (r : ℝ≥0∞)) hp]
  rw [hrt]
  rw [← ENNReal.ofReal_rpow_of_nonneg
        (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _) (by positivity)]
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => by
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (le_of_lt hr0), ofReal_norm])

/-- **The `chainLp` sum as an `ℝ≥0∞`-valued `rpow`-sum**: for `ρ > 0`,

`ofReal (chainLp ρ J a t) = (∑_{j < J} ‖a (t (j+1)) - a (t j)‖ₑ ^ ρ) ^ (1/ρ)`. -/
lemma ofReal_chainLp_eq_sum (ρ : ℝ) (hρ : 0 < ρ) (J : ℕ) (a : ℕ → ℂ) (t : ℕ → ℕ) :
    ENNReal.ofReal (chainLp ρ J a t)
      = (∑ j ∈ Finset.range J, ‖a (t (j + 1)) - a (t j)‖ₑ ^ ρ) ^ (1 / ρ) := by
  rw [chainLp]
  rw [← ENNReal.ofReal_rpow_of_nonneg
        (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (norm_nonneg _) _) (by positivity)]
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => Real.rpow_nonneg (norm_nonneg _) _)]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => by
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hρ.le, ofReal_norm])

/-- **The `WithLp 2`-norm of the increments of a chain equals `chainLp 2`.** -/
lemma ofReal_norm_toLp_two_eq_ofReal_chainLp (J : ℕ) (a : ℕ → ℂ) (t : ℕ → ℕ) :
    ENNReal.ofReal ‖WithLp.toLp (2 : NNReal)
        (fun i : Fin J => a (t (i + 1)) - a (t i))‖
      = ENNReal.ofReal (chainLp 2 J a t) := by
  rw [ofReal_norm_toLp_eq_sum 2 (by norm_num)
        (F := fun i : Fin J => a (t (i + 1)) - a (t i))]
  rw [ofReal_chainLp_eq_sum 2 (by norm_num) J a t]
  rw [show ((2 : NNReal) : ℝ) = 2 by norm_num]
  apply congrArg (fun x : ℝ≥0∞ => x ^ (1 / (2 : ℝ)))
  rw [Fin.sum_univ_eq_sum_range
        (f := fun j : ℕ => ‖a (t (j + 1)) - a (t j)‖ₑ ^ (2 : ℝ)) (n := J)]

end Work.KMTAreas.A7G
