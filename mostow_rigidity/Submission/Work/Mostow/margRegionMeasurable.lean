import Mathlib
import Submission.Work.Mostow.geodSetup
import Submission.Work.Mostow.measurableSetNearIdAt
import Submission.Work.Mostow.HaarBase

namespace Work.Mostow

open MeasureTheory

/-- Helper: the Margulis region is the union, over the (countable, by discreteness) set of
non-identity elements of `Λ` that fix the standard geodesic pointwise, of the corresponding
near-identity sets. -/
private def margIndex (m : ℕ) (Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO (1 + m) 1)) :
    Set (LeanEval.Geometry.MostowRigidity.PO (1 + m) 1) :=
  {a | a ∈ Λ ∧ a ∈ Submission.Mostow.SetStabStd 1 m ∧ Submission.Mostow.resStd 1 m a = 1 ∧ a ≠ 1}

private theorem margRegion_eq_iUnion (m : ℕ)
    (Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO (1 + m) 1)) (η₁ : ℝ) :
    margRegion m Λ η₁ = ⋃ a ∈ margIndex m Λ,
      {u : Submission.Mostow.E (1 + m) | Submission.Mostow.NearIdAt a u η₁} := by
  ext u
  simp only [margRegion, margIndex, Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨a, h1, h2, h3, h4, h5⟩
    exact ⟨a, ⟨h1, h2, h3, h4⟩, h5⟩
  · rintro ⟨a, ⟨h1, h2, h3, h4⟩, h5⟩
    exact ⟨a, h1, h2, h3, h4, h5⟩

theorem margRegionMeasurable (m : ℕ) (hA : Submission.Mostow.POActionProp (1 + m)) (hI : Submission.Mostow.HypIsometryProp (1 + m))
    (Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO (1 + m) 1))
    (hdisc : _root_.IsDiscrete (Λ : Set (LeanEval.Geometry.MostowRigidity.PO (1 + m) 1))) (η₁ : ℝ) :
    MeasurableSet (Work.Mostow.margRegion m Λ η₁) := by
  have hcount : (Λ : Set (LeanEval.Geometry.MostowRigidity.PO (1 + m) 1)).Countable :=
    countable_of_isDiscrete _ hdisc
  have hs : (margIndex m Λ).Countable :=
    hcount.mono (fun a ha => ha.1)
  rw [margRegion_eq_iUnion m Λ η₁]
  exact MeasurableSet.biUnion hs (fun a _ => measurableSetNearIdAt hA hI a η₁)

end Work.Mostow
