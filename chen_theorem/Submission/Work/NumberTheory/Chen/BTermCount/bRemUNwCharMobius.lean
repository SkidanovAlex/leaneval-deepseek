import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.CorrectionDefs
import Submission.Work.NumberTheory.Chen.BTermCount.bRemCorrCharSum
import Submission.Work.NumberTheory.Chen.BTermCount.BLodConductorDecomp
import Submission.Work.NumberTheory.Chen.BTermCount.BLodCharReduction
import Submission.Work.NumberTheory.Chen.BTermCount.BLodAssembly

namespace Work.NumberTheory.Chen.BTermCount

attribute [local instance] Classical.propDecidable

/-!
# The unweighted character/Möbius reduction for the corrected remainder

`BLodStepChar` and `BLodCharReduction` carry an extra weight `3 ^ ω(d)` throughout, which is
what the subsequent analytic estimates need.  Here we record the *unweighted* version of the
same reduction, i.e. the statement in which both sides are stripped of the factor
`3 ^ ω(d)`: since `3 ^ ω(d)` is not present on the left, the reduction has to be run directly
for the absolute values `|bRemCorr x M Y d|` rather than for their weighted sums.

The content is exactly the same two steps: the character identity `abs_bRemCorr_le` together with
the conductor decomposition `BLodConductorDecomp`, followed by the per-conductor Möbius bound
`bProdCharSumDivSum_le_divisors`.
-/

/-- The index set `d.divisors.filter (fun c => 2 ≤ c)` and its attached twin
`d.divisors.attach.filter (fun c => 2 ≤ c.1)` carry the same sum. -/
theorem sum_divisors_filter_eq_sum_attach_filter (d : ℕ) (F : ℕ → ℝ) :
    (∑ c ∈ d.divisors.attach.filter (fun c => 2 ≤ c.1), F c.1)
      = ∑ c ∈ d.divisors.filter (fun c => 2 ≤ c), F c := by
  rw [Finset.sum_filter, Finset.sum_filter]
  exact Finset.sum_attach d.divisors (fun c => if 2 ≤ c then F c else 0)

/-- **The unweighted character reduction.**  Summed over the odd `d ≤ D`, the absolute values of
the corrected remainders are bounded by the totient-weighted sum of the `t`-twisted primitive
character sums at the conductor level. -/
theorem bRemUNwCharMobius (x M Y D : ℕ) (hD : 2 ≤ D) :
    (∑ d ∈ (Finset.Icc 1 D).filter (fun d => d % 2 = 1), |bRemCorr x M Y d|)
      ≤ ∑ d ∈ (Finset.Icc 1 D).filter (fun d => d % 2 = 1),
          (Nat.totient d : ℝ)⁻¹ *
            (∑ c ∈ d.divisors.filter (fun c => 2 ≤ c),
              ∑ t ∈ (d / c).divisors, bProdCharSumDivSum x M Y t c) := by
  refine Finset.sum_le_sum (fun d hd => ?_)
  obtain ⟨hdmem, hodd⟩ := Finset.mem_filter.mp hd
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdmem).1
  haveI : NeZero d := ⟨by omega⟩
  have hphi_nonneg : (0:ℝ) ≤ (Nat.totient d : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  refine le_trans (abs_bRemCorr_le x M Y d hodd) (mul_le_mul_of_nonneg_left ?_ hphi_nonneg)
  rw [BLodConductorDecomp x M Y d]
  rw [← sum_divisors_filter_eq_sum_attach_filter d
      (fun c => ∑ t ∈ (d / c).divisors, bProdCharSumDivSum x M Y t c)]
  exact Finset.sum_le_sum (fun c _ =>
      bProdCharSumDivSum_le_divisors x M Y d c.1 (Nat.mem_divisors.mp c.2).1)

end Work.NumberTheory.Chen.BTermCount
