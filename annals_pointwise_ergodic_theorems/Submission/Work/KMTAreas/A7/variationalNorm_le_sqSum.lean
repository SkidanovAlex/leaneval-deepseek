/-
# The variational norm of a sequence is controlled by its `ℓ²`-norm

`Work.KMTAreas.A7.variationalNorm_le_sqSum` is the elementary bound relating the `𝕍^r` norm of the
trusted layer (`ChallengeDeps.PointwiseErgodicTheorems.variationalNorm`) to the `ℓ²`-norm of the
sequence: for `2 ≤ r` and every `a : ℕ → ℂ`,

  `V^r(a) ≤ (2 · 2^{1/r} + 1) · (∑'_n ‖a n‖ₑ^{2})^{1/2}`.

The proof splits the variational norm (a sum of two suprema, see
`ChallengeDeps.PointwiseErgodicTheorems.variationalNorm`) into

* the supremum term `⨆_n ‖a n‖ₑ ≤ X` (`sSup_enorm_le_sqSum`, `Work.KMTAreas.A7.sSup_enorm_le_sqSum`),
* the variation term: for a monotone chain `N : ℕ → ℕ` and `J : ℕ` the jump sum
  `∑_{i<J} ‖a (N (i+1)) − a (N i)‖ₑ^r` is at most `2^r ∑'_n ‖a n‖ₑ^r`
  (`chainSum_le_tsum`), and `(∑'_n ‖a n‖ₑ^r)^{1/r} ≤ X` for `r ≥ 2`
  (`rpow_tsum_le_sq_tsum`); hence the `WithLp.toLp`-norm of the jump vector is at most `2 X`.

Altogether `V^r(a) ≤ X + 2X = 3X ≤ (2 · 2^{1/r} + 1) X`, the last step because `2^{1/r} ≥ 1` for
`r ≥ 2`.

The three ingredients are proved in the sibling modules named above; the only thing specific to the
trusted layer here is the identification of the `ℓ^r`-norm of the `WithLp`-vector with the
`rpow`-sum `(∑_i ‖·‖ₑ^r)^{1/r}` (`ofReal_norm_toLp`, from `PiLp.norm_eq_sum`).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.chainSum_le_tsum
import Submission.Work.KMTAreas.A7.rpow_tsum_le_sq_tsum
import Submission.Work.KMTAreas.A7.sSup_enorm_le_sqSum
import Submission.Work.Analysis.CzShift.Main
import Submission.Work.Analysis.CzShift.exists_isCZSeed_of_fourierInv
import Submission.Work.BourgainPlan.Maximal.main_narrow_taoSetS
import Submission.Work.BourgainPlan.Maximal.mikhlinConvolutionLp
import Submission.Work.KMTAreas.A7.LargeInterface

namespace Work.KMTAreas.A7

open scoped ENNReal NNReal BigOperators
open MeasureTheory

/-- `(x ^ r) ^ (1/r) = x` in `ℝ≥0∞` (for `r ≠ 0`), the `one_div`-form of
`ENNReal.rpow_rpow_inv`. -/
private lemma rpow_rpow_one_div_inv {r : ℝ} (hr : r ≠ 0) (x : ℝ≥0∞) :
    (x ^ r) ^ (1 / r) = x := by
  rw [one_div]
  exact ENNReal.rpow_rpow_inv hr x

/-- `(x ^ (1/r)) ^ r = x` in `ℝ≥0∞` (for `r ≠ 0`), the `one_div`-form of
`ENNReal.rpow_inv_rpow`. -/
private lemma rpow_one_div_rpow {r : ℝ} (hr : r ≠ 0) (x : ℝ≥0∞) :
    (x ^ (1 / r)) ^ r = x := by
  rw [one_div]
  exact ENNReal.rpow_inv_rpow hr x

/-- The extended norm of `WithLp.toLp r v` (`v : Fin J → ℂ`, `r ≥ 2`) is the `r`-th power sum of
the extended norms of the coordinates: `‖WithLp.toLp r v‖ₑ = (∑_i ‖v i‖ₑ^r)^(1/r)`.  This is
`PiLp.norm_eq_sum` transported along `ENNReal.ofReal_rpow_of_nonneg` and `ofReal_norm`. -/
lemma ofReal_norm_toLp (r : NNReal) (hr : 2 ≤ r) (J : ℕ) (v : Fin J → ℂ) :
    ENNReal.ofReal ‖WithLp.toLp r v‖ = (∑ i, ‖v i‖ₑ ^ ((r : ℝ))) ^ (1 / (r : ℝ)) := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by
    have h2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  rw [PiLp.norm_eq_sum (p := (r : ENNReal)) (by rwa [ENNReal.coe_toReal])]
  simp only [ENNReal.coe_toReal]
  rw [← ENNReal.ofReal_rpow_of_nonneg (p := (1 / (r : ℝ))) (x := ∑ i, ‖v i‖ ^ (r : ℝ))
    (by positivity) (by positivity)]
  congr 1
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr0.le, ofReal_norm]

/-- **The `ℓ²`-bound for the variational norm.**  For `2 ≤ r` and any `a : ℕ → ℂ`, the `𝕍^r`-norm
of `a` is at most `(2 · 2^{1/r} + 1)` times the `ℓ²`-norm of `a`. -/
theorem variationalNorm_le_sqSum {r : NNReal} (hr : 2 ≤ r) (a : ℕ → ℂ) :
    PointwiseErgodicTheorems.variationalNorm r a ≤
      ENNReal.ofReal (2 * (2 : ℝ) ^ (1 / (r : ℝ)) + 1) *
        (∑' n : ℕ, ‖a n‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by linarith
  have hr0 : (0 : ℝ) < (r : ℝ) := by linarith
  set Y : ℝ≥0∞ := ∑' n : ℕ, ‖a n‖ₑ ^ (2 : ℝ) with hY
  -- the supremum term
  have hsup : (⨆ n, ‖a n‖ₑ) ≤ Y ^ (1 / 2 : ℝ) := sSup_enorm_le_sqSum a
  -- the variation term
  have hvar : ∀ (J : ℕ) (N : ℕ → ℕ) (_ : Monotone N),
      ENNReal.ofReal ‖WithLp.toLp r (fun i : Fin J => a (N (i + 1)) - a (N i))‖
        ≤ 2 * Y ^ (1 / 2 : ℝ) := by
    intro J N hN
    rw [ofReal_norm_toLp r hr J (fun i : Fin J => a (N (i + 1)) - a (N i))]
    have h1 : ∑ i : Fin J, ‖a (N (i + 1)) - a (N i)‖ₑ ^ (r : ℝ)
        ≤ 2 ^ (r : ℝ) * (Y ^ (1 / 2 : ℝ)) ^ (r : ℝ) := by
      refine le_trans (chainSum_le_tsum hr1 a hN J) ?_
      gcongr
      have hd := rpow_tsum_le_sq_tsum hr2 a
      rw [← hY] at hd
      calc ∑' n : ℕ, ‖a n‖ₑ ^ (r : ℝ)
          = ((∑' n : ℕ, ‖a n‖ₑ ^ (r : ℝ)) ^ (1 / (r : ℝ))) ^ (r : ℝ) :=
            (rpow_one_div_rpow hr0.ne' _).symm
        _ ≤ (Y ^ (1 / 2 : ℝ)) ^ (r : ℝ) := ENNReal.rpow_le_rpow hd hr0.le
    calc (∑ i : Fin J, ‖a (N (i + 1)) - a (N i)‖ₑ ^ (r : ℝ)) ^ (1 / (r : ℝ))
        ≤ (2 ^ (r : ℝ) * (Y ^ (1 / 2 : ℝ)) ^ (r : ℝ)) ^ (1 / (r : ℝ)) :=
          ENNReal.rpow_le_rpow h1 (by positivity)
      _ = ((2 * Y ^ (1 / 2 : ℝ)) ^ (r : ℝ)) ^ (1 / (r : ℝ)) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le]
      _ = 2 * Y ^ (1 / 2 : ℝ) := rpow_rpow_one_div_inv hr0.ne' _
  have hmain : PointwiseErgodicTheorems.variationalNorm r a
      ≤ Y ^ (1 / 2 : ℝ) + 2 * Y ^ (1 / 2 : ℝ) := by
    rw [PointwiseErgodicTheorems.variationalNorm]
    exact add_le_add hsup (iSup_le fun J => iSup_le fun N => iSup_le fun hN => hvar J N hN)
  have h3 : Y ^ (1 / 2 : ℝ) + 2 * Y ^ (1 / 2 : ℝ) = 3 * Y ^ (1 / 2 : ℝ) := by
    calc Y ^ (1 / 2 : ℝ) + 2 * Y ^ (1 / 2 : ℝ)
        = 1 * Y ^ (1 / 2 : ℝ) + 2 * Y ^ (1 / 2 : ℝ) := by rw [one_mul]
      _ = (1 + 2) * Y ^ (1 / 2 : ℝ) := (add_mul 1 2 _).symm
      _ = 3 * Y ^ (1 / 2 : ℝ) := by norm_num
  have hconst : (3 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * (2 : ℝ) ^ (1 / (r : ℝ)) + 1) := by
    rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num]
    apply ENNReal.ofReal_le_ofReal
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (1 / (r : ℝ)) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    linarith
  calc PointwiseErgodicTheorems.variationalNorm r a
      ≤ Y ^ (1 / 2 : ℝ) + 2 * Y ^ (1 / 2 : ℝ) := hmain
    _ = 3 * Y ^ (1 / 2 : ℝ) := h3
    _ ≤ ENNReal.ofReal (2 * (2 : ℝ) ^ (1 / (r : ℝ)) + 1) * Y ^ (1 / 2 : ℝ) :=
        mul_le_mul_left hconst _
    _ = ENNReal.ofReal (2 * (2 : ℝ) ^ (1 / (r : ℝ)) + 1) *
        (∑' n : ℕ, ‖a n‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by rw [hY]

end Work.KMTAreas.A7
