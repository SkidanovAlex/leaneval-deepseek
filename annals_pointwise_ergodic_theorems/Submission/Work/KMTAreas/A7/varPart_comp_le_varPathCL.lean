/-
# `varPart (y ∘ lev) ≤ varPathCL L y r` for a monotone `lev` bounded by `L`

The variation part of the challenge's variational norm, evaluated on a sequence `n ↦ y (lev n)` with
`lev` monotone and bounded by `L`, is dominated by the truncated path variation `varPathCL L y r`,
whose defining supremum runs only over *strictly increasing* chains with values `≤ L`.

The mathematical content is entirely combinatorial: a monotone chain `u 0 ≤ u 1 ≤ ⋯ ≤ u J` of levels
may be replaced, at equal cost, by the strictly increasing chain of its *distinct* values.  Indeed,
consecutive repetitions of a value contribute the jump `y a - y a = 0` to the `r`-sum, which one may
simply drop, and what remains is the sum of the jumps `y (v (k+1)) - y (v k)` along the strictly
increasing chain `v` of distinct values.  This replacement is precisely the lemma
`Work.Analysis.Variation.monotone_chain_strictify` (proved elsewhere in the workspace), which we
apply to the `ℕ`-indexed chain `w j = lev (N j)`.

The rest is the (definitional) bookkeeping identifying the `ℓ^r` norm of the challenge's `varPart`
with an `rpow`-sum, and the range/`Fin` indexing of the chain sums.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.lacDilTriVarDefs
import Submission.Work.Analysis.Variation.monotone_chain_strictify

set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

open scoped ENNReal NNReal BigOperators

noncomputable section

/-- The `ℓ^r` norm (`r ≥ 1`) of a finite vector, written as an `rpow`-sum: the form in which the
second term `varPart` of `variationalNorm` is stated. -/
private theorem ofReal_norm_toLp_eq_sumFin (r : ℝ≥0) (hr : 1 ≤ r) {J : ℕ} (F : Fin J → ℂ) :
    ENNReal.ofReal ‖WithLp.toLp r F‖ = (∑ i : Fin J, ‖F i‖ₑ ^ (r : ℝ)) ^ (1 / (r : ℝ)) := by
  haveI : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hr⟩
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

/-- **Strict chains dominate monotone chains.**  For `r ≥ 1`, the `r`-sum of the jumps of a monotone
chain `w : ℕ → ℕ` with values `≤ L` is a term appearing in the supremum defining `varPathCL L y r`
(namely the term of the strictly increasing chain of its distinct values). -/
private theorem rangeSum_le_varPathCL (L : ℕ) (y : ℕ → ℂ) {r : ℝ} (hr : 1 ≤ r) (J : ℕ)
    (w : ℕ → ℕ) (hw : Monotone w) (hwL : ∀ j, w j ≤ L) :
    (∑ j ∈ Finset.range J, ‖y (w (j + 1)) - y (w j)‖ₑ ^ r) ^ (1 / r)
      ≤ varPathCL L y r := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  -- the cost function vanishes on the diagonal, so repeated values may be dropped
  have hG : ∀ a, (fun a b : ℕ => ‖y b - y a‖ₑ ^ r) a a = 0 := by
    intro a
    show ‖y a - y a‖ₑ ^ r = 0
    rw [sub_self, enorm_zero, ENNReal.zero_rpow_of_pos hr0]
  obtain ⟨J', v, hvstrict, hvP, hvsum⟩ :=
    Work.Analysis.Variation.monotone_chain_strictify
      (G := fun a b : ℕ => ‖y b - y a‖ₑ ^ r) (P := fun k : ℕ => k ≤ L) hG w hw hwL J
  -- restate the strictification with the cost function unfolded
  have h1 : (∑ j ∈ Finset.range J, ‖y (w (j + 1)) - y (w j)‖ₑ ^ r)
      = ∑ j ∈ Finset.range J, (fun a b : ℕ => ‖y b - y a‖ₑ ^ r) (w j) (w (j + 1)) :=
    Finset.sum_congr rfl (fun j _ => rfl)
  have h3 : (∑ i ∈ Finset.range J', (fun a b : ℕ => ‖y b - y a‖ₑ ^ r) (v i) (v (i + 1)))
      = ∑ i ∈ Finset.range J', ‖y (v (i + 1)) - y (v i)‖ₑ ^ r :=
    Finset.sum_congr rfl (fun i _ => rfl)
  have hvsum' : (∑ j ∈ Finset.range J, ‖y (w (j + 1)) - y (w j)‖ₑ ^ r)
      = ∑ i ∈ Finset.range J', ‖y (v (i + 1)) - y (v i)‖ₑ ^ r :=
    h1.trans (hvsum.trans h3)
  rw [hvsum']
  -- `v` is the strictly increasing chain of levels; feed it to `varPathCL`
  refine le_iSup_of_le J' (le_iSup_of_le (fun i : Fin (J' + 1) => v (i : ℕ))
    (le_iSup_of_le ?_ (le_iSup_of_le ?_ ?_)))
  · intro a b hab
    exact hvstrict hab
  · intro i
    exact hvP (i : ℕ) (by omega)
  · -- the sums of the jumps agree
    have hpt : ∀ i : ℕ, ‖y (v (i + 1)) - y (v i)‖ₑ ^ r
        = ENNReal.ofReal (‖y (v (i + 1)) - y (v i)‖ ^ r) := fun i => by
      rw [← ofReal_norm, ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr0.le]
    have hsum : (∑ i ∈ Finset.range J', ‖y (v (i + 1)) - y (v i)‖ₑ ^ r)
        = ENNReal.ofReal (∑ i ∈ Finset.range J', ‖y (v (i + 1)) - y (v i)‖ ^ r) :=
      calc (∑ i ∈ Finset.range J', ‖y (v (i + 1)) - y (v i)‖ₑ ^ r)
          = ∑ i ∈ Finset.range J',
              ENNReal.ofReal (‖y (v (i + 1)) - y (v i)‖ ^ r) :=
            Finset.sum_congr rfl (fun i _ => hpt i)
        _ = ENNReal.ofReal (∑ i ∈ Finset.range J', ‖y (v (i + 1)) - y (v i)‖ ^ r) :=
            (ENNReal.ofReal_sum_of_nonneg
              (fun i _ => Real.rpow_nonneg (norm_nonneg (y (v (i + 1)) - y (v i))) r)).symm
    have hFin : (∑ i ∈ Finset.range J', ‖y (v (i + 1)) - y (v i)‖ ^ r)
        = ∑ i : Fin J', ‖y (v ((i : ℕ) + 1)) - y (v (i : ℕ))‖ ^ r :=
      (Fin.sum_univ_eq_sum_range (fun i : ℕ => ‖y (v (i + 1)) - y (v i)‖ ^ r) J').symm
    have hchain : (∑ i : Fin J', ‖y (v ((i : ℕ) + 1)) - y (v (i : ℕ))‖ ^ r)
        = ∑ j : Fin J', ‖y ((fun i : Fin (J' + 1) => v (i : ℕ)) j.succ)
            - y ((fun i : Fin (J' + 1) => v (i : ℕ)) j.castSucc)‖ ^ r := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [Fin.val_succ, Fin.val_castSucc]
    have hX : (0 : ℝ) ≤ ∑ i ∈ Finset.range J', ‖y (v (i + 1)) - y (v i)‖ ^ r :=
      Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg (y (v (i + 1)) - y (v i))) r)
    have hq : (0 : ℝ) ≤ 1 / r := div_nonneg zero_le_one hr0.le
    have hpow : ENNReal.ofReal (∑ i ∈ Finset.range J', ‖y (v (i + 1)) - y (v i)‖ ^ r) ^ (1 / r)
        = ENNReal.ofReal ((∑ i ∈ Finset.range J', ‖y (v (i + 1)) - y (v i)‖ ^ r) ^ (1 / r)) :=
      ENNReal.ofReal_rpow_of_nonneg hX hq
    have hgoal : (∑ i ∈ Finset.range J', ‖y (v (i + 1)) - y (v i)‖ₑ ^ r) ^ (1 / r)
        = ENNReal.ofReal ((∑ j : Fin J', ‖y ((fun i : Fin (J' + 1) => v (i : ℕ)) j.succ)
            - y ((fun i : Fin (J' + 1) => v (i : ℕ)) j.castSucc)‖ ^ r) ^ (1 / r)) := by
      rw [hsum, hpow, hFin, hchain]
    exact hgoal.le

/-- The `Fin`-indexed form of `rangeSum_le_varPathCL`, matching the index type of `varPart`. -/
private theorem chainSum_le_varPathCL (L : ℕ) (y : ℕ → ℂ) {r : ℝ} (hr : 1 ≤ r) (J : ℕ)
    (w : ℕ → ℕ) (hw : Monotone w) (hwL : ∀ j, w j ≤ L) :
    (∑ j : Fin J, ‖y (w ((j : ℕ) + 1)) - y (w (j : ℕ))‖ₑ ^ r) ^ (1 / r)
      ≤ varPathCL L y r := by
  have hconv : (∑ j : Fin J, ‖y (w ((j : ℕ) + 1)) - y (w (j : ℕ))‖ₑ ^ r)
      = ∑ j ∈ Finset.range J, ‖y (w (j + 1)) - y (w j)‖ₑ ^ r :=
    Fin.sum_univ_eq_sum_range (fun j : ℕ => ‖y (w (j + 1)) - y (w j)‖ₑ ^ r) J
  rw [hconv]
  exact rangeSum_le_varPathCL L y hr J w hw hwL

/-- **The lemma.**  For `1 ≤ r`, a monotone `lev` with `lev n ≤ L` for all `n`, the variation part
of the variational norm of the composed sequence `n ↦ y (lev n)` is bounded by the truncated path
variation `varPathCL L y r` over strictly increasing chains of levels `≤ L`. -/
theorem varPart_comp_le_varPathCL {r : NNReal} (hr : 1 ≤ r) (y : ℕ → ℂ) (lev : ℕ → ℕ)
    (hlev : Monotone lev) (L : ℕ) (hL : ∀ n, lev n ≤ L) :
    Submission.PointwiseErgodicTheorems.varPart r (fun n => y (lev n))
      ≤ Work.KMTAreas.A7.varPathCL L y (r : ℝ) := by
  refine iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_
  rw [ofReal_norm_toLp_eq_sumFin r hr]
  exact chainSum_le_varPathCL L y (by exact_mod_cast hr) J (fun n => lev (N n))
    (fun a b hab => hlev (hN hab)) (fun n => hL (N n))

end

end Work.KMTAreas.A7
