import Mathlib
import Submission.Work.CR.Flat.Holder

open scoped NNReal ENNReal
open Set

namespace Work.NN.Ratio

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The Hölder seminorm of order `0` is the supremum of the finite differences of `f` itself:
the `0`-th iterated derivative is the function `f` (as a `0`-multilinear map), and the norm of
a difference of `0`-multilinear maps is the distance of the underlying values. -/
lemma holderSeminorm_zero_eq (f : X → ℂ) (Ω : Set X) (α : ℝ) :
    Work.CR.Flat.holderSeminorm 0 α f Ω =
      ⨆ x ∈ Ω, ⨆ y ∈ Ω, ⨆ (_ : x ≠ y), ENNReal.ofReal (‖f x - f y‖ / ‖x - y‖ ^ α) := by
  simp only [Work.CR.Flat.holderSeminorm]
  refine iSup_congr fun x => iSup_congr fun _ => iSup_congr fun y =>
    iSup_congr fun _ => iSup_congr fun _ => ?_
  rw [← dist_eq_norm, dist_iteratedFDerivWithin_zero, dist_eq_norm]

/-- The `C^{0,α}` norm splits as the sup-norm of `f` plus the degree-`0` Hölder seminorm. -/
lemma holderNorm_zero_eq (α : ℝ) (f : X → ℂ) (Ω : Set X) :
    Work.CR.Flat.holderNorm 0 α f Ω
      = Work.CR.Flat.iterDerivNorm 0 f Ω + Work.CR.Flat.holderSeminorm 0 α f Ω := by
  simp [Work.CR.Flat.holderNorm]

/-- `holderNorm 0 α · Ω` only depends on the values of the function on `Ω`. -/
theorem holderNorm_zero_congr {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {α : ℝ} {Ω : Set X} {f g : X → ℂ} (h : ∀ x ∈ Ω, f x = g x) :
    Work.CR.Flat.holderNorm 0 α f Ω = Work.CR.Flat.holderNorm 0 α g Ω := by
  rw [holderNorm_zero_eq α f Ω, holderNorm_zero_eq α g Ω]
  congr 1
  · rw [Work.CR.Flat.iterDerivNorm_zero, Work.CR.Flat.iterDerivNorm_zero]
    exact iSup_congr fun x => iSup_congr fun hx => by rw [h x hx]
  · rw [holderSeminorm_zero_eq f Ω α, holderSeminorm_zero_eq g Ω α]
    exact iSup_congr fun x => iSup_congr fun hx => iSup_congr fun y =>
      iSup_congr fun hy => iSup_congr fun _ => by rw [h x hx, h y hy]

end Work.NN.Ratio
