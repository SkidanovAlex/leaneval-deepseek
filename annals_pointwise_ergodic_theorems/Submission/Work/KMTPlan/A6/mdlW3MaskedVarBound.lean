import Mathlib
import Submission.Work.KMTPlan.A6.lowWeightMaskBound

namespace Work.KMTPlan.A6

/-- **The masked variational bound for the weight `mdlW3`.**  The mask `Bw ≤ ⌊a n⌋` is an
upward-closed tail of the monotone sequence `n ↦ ⌊a n⌋` (monotone by
`floor_monotone_of_lacunary`, since `a` is `Λ`-lacunary with `Λ > 1`), so the result is the
`mdlW3` conjunct of `lowWeightMaskBound` applied to the monotone scale sequence
`N = fun n => ⌊a n⌋`. -/
theorem mdlW3MaskedVarBound (P : Polynomial ℤ) (hdeg : 1 ≤ P.natDegree) (r : NNReal)
    (hr : 1 ≤ r) :
    ∃ Bw : ℕ, 0 < Bw ∧ ∃ Cw : ℝ, 0 < Cw ∧
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (t : ℝ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → t ∈ Set.Icc (1 / 2 : ℝ) 1 →
        PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => if Bw ≤ Nat.floor (a n)
              then Work.KMTPlan.A6.mdlW3 P (Nat.floor (a n)) t else 0)
          ≤ ENNReal.ofReal Cw := by
  obtain ⟨B, hBpos, C, hCpos, hbound⟩ := lowWeightMaskBound P hdeg r hr
  refine ⟨B, hBpos, C, hCpos, ?_⟩
  intro a Λ t hΛ hlac ht
  exact (hbound (fun n => Nat.floor (a n)) t (floor_monotone_of_lacunary hΛ hlac) ht).2.2

end Work.KMTPlan.A6
