import Mathlib
import Submission.Work.Smooth.Jordan.Family
import Submission.Work.Smooth.Jordan.family_insideOpen_trans

namespace Work.Smooth.Jordan

/-- **The containment relation `FamilyDiscs.InsideOpen` is a strict partial order on the index
type.**  Irreflexivity is `FamilyDiscs.not_insideOpen_self` (a curve does not meet the interior of
its own spanning disc) and transitivity is `family_insideOpen_trans`. -/
theorem family_insideOpen_strictOrder {A : Set LeanEval.KnotTheory.PardonDistortion.R3} {ι : Type} [Fintype ι] {c : ι → ℝ → LeanEval.KnotTheory.PardonDistortion.R3} (h : FamilyDiscs A ι c) :
    (∀ i, ¬ h.InsideOpen i i) ∧
      (∀ ⦃i j k⦄, h.InsideOpen i j → h.InsideOpen j k → h.InsideOpen i k) :=
  ⟨fun i => h.not_insideOpen_self i,
   fun _ _ _ hij hjk => family_insideOpen_trans h hij hjk⟩

end Work.Smooth.Jordan
