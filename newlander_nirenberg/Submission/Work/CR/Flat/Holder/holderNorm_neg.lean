import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Holder.holderNorm_smul

namespace Work.CR.Flat.Holder

open scoped NNReal ENNReal
open Set

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The `C^{k,α}` norm of `Submission/Work/CR/Flat/Holder.lean` is invariant under
negation: `holderNorm k α (-f) Ω = holderNorm k α f Ω`. -/
theorem holderNorm_neg {k : ℕ} {α : ℝ} {f : X → ℂ} {Ω : Set X}
    (hf : ContDiffOn ℝ (k : ℕ∞) f Ω) (hΩ : UniqueDiffOn ℝ Ω) :
    holderNorm k α (-f) Ω = holderNorm k α f Ω := by
  have hneg : (-f : X → ℂ) = (-1 : ℂ) • f := by
    ext x; simp
  rw [hneg, holderNorm_smul (-1) hf hΩ]
  norm_num

end Work.CR.Flat.Holder
