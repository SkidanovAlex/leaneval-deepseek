import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Holder.holderNorm_add_le

namespace Work.CR.Flat.Holder

open scoped NNReal ENNReal
open MeasureTheory Set

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Functions of finite `C^{k,α}` norm (`holderNorm k α f Ω ≠ ⊤`) on `Ω` are closed
under addition: this is the vector-space structure of the Hölder space that the
small-perturbation argument of Newlander–Nirenberg needs.  Immediate from the
subadditivity of `holderNorm`. -/
theorem holderNorm_add_ne_top {k : ℕ} {α : ℝ} {f g : X → ℂ} {Ω : Set X}
    (hf : ContDiffOn ℝ (k : ℕ∞) f Ω) (hg : ContDiffOn ℝ (k : ℕ∞) g Ω)
    (hΩ : UniqueDiffOn ℝ Ω)
    (hf' : holderNorm k α f Ω ≠ ⊤) (hg' : holderNorm k α g Ω ≠ ⊤) :
    holderNorm k α (f + g) Ω ≠ ⊤ := by
  have hle : holderNorm k α (f + g) Ω
      ≤ holderNorm k α f Ω + holderNorm k α g Ω :=
    holderNorm_add_le (k := k) (α := α) (Ω := Ω) hf hg hΩ
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hf', hg'⟩) hle

end Work.CR.Flat.Holder
