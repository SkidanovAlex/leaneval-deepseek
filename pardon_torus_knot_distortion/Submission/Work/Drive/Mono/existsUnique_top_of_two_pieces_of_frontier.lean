import Mathlib
import Submission.Work.Drive.EpsFormSphere.bigComponent_compl_inessentialCurves
import Submission.Work.SurgeryInvariance.Defs
import Submission.Work.Drive.EpsForm.wallTwoPieces

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion
open Set

/-- **The frontier condition makes the far side open.**

If `X` is open in the carrier, `Y` is disjoint from it, `X ∪ Y` is the complement of a finite union
`T` of closed curve images in the carrier, and every carrier point of `closure X` which is not in `X`
lies in `T`, then `Y` is open in the carrier. -/
theorem isOpenInCarrier_right_of_frontier {P : Work.CoreTopology.ParamTorus}
    {X Y : Set R3} {n : ℕ} {cs : Fin n → Work.CoreTopology.ClosedCurve P}
    (hYc : Y ⊆ P.carrier) (hXY : Disjoint X Y)
    (hcover : P.carrier \ (⋃ i, Set.range (cs i).γ) = X ∪ Y)
    (hfront : ∀ z : R3, z ∈ P.carrier → z ∈ closure X → z ∉ X →
      z ∈ ⋃ i, Set.range (cs i).γ) :
    Work.SurgeryInvariance.IsOpenInCarrier P Y := by
  set T : Set R3 := ⋃ i, Set.range (cs i).γ with hT
  have hTclosed : IsClosed T := by
    rw [hT]
    exact Work.Drive.EpsFormSphere.isClosed_iUnion_range_closedCurve cs
  -- `Y` avoids both `closure X` and `T`
  have hYclosure : ∀ z, z ∈ Y → z ∉ closure X := by
    intro z hz hzcl
    have hznotX : z ∉ X := fun hx => Set.disjoint_left.mp hXY hx hz
    have hzT : z ∈ T := hfront z (hYc hz) hzcl hznotX
    have : z ∈ P.carrier \ T := by
      rw [hcover]
      exact Set.mem_union_right X hz
    exact this.2 hzT
  have hYT : ∀ z, z ∈ Y → z ∉ T := by
    intro z hz
    have : z ∈ P.carrier \ T := by
      rw [hcover]
      exact Set.mem_union_right X hz
    exact this.2
  have hYeq : Y = P.carrier ∩ (closure X ∪ T)ᶜ := by
    ext z
    constructor
    · intro hz
      exact ⟨hYc hz, by
        simp only [Set.mem_compl_iff, Set.mem_union, not_or]
        exact ⟨hYclosure z hz, hYT z hz⟩⟩
    · rintro ⟨hzc, hznot⟩
      simp only [Set.mem_compl_iff, Set.mem_union, not_or] at hznot
      have hzC : z ∈ P.carrier \ T := ⟨hzc, hznot.2⟩
      rw [hcover] at hzC
      rcases hzC with h | h
      · exact absurd (subset_closure h) hznot.1
      · exact h
  rw [hYeq]
  exact Work.SurgeryInvariance.isOpenInCarrier_carrier_inter (P := P)
    (isClosed_closure.union hTclosed).isOpen_compl

theorem existsUnique_top_of_two_pieces_of_frontier {P : Work.CoreTopology.ParamTorus}
    {X Y : Set LeanEval.KnotTheory.PardonDistortion.R3} {n : ℕ}
    {cs : Fin n → Work.CoreTopology.ClosedCurve P}
    (hsimple : ∀ i, Work.CoreTopology.IsSimple P (cs i))
    (hess : ∀ i, ¬ Work.CoreTopology.IsEssential P (cs i))
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint (Set.range (cs i).γ) (Set.range (cs j).γ))
    (hXc : X ⊆ P.carrier) (hYc : Y ⊆ P.carrier)
    (hXopen : Work.SurgeryInvariance.IsOpenInCarrier P X)
    (hXY : Disjoint X Y)
    (hcover : P.carrier \ (⋃ i, Set.range (cs i).γ) = X ∪ Y)
    (hfront : ∀ z : LeanEval.KnotTheory.PardonDistortion.R3, z ∈ P.carrier →
      z ∈ closure X → z ∉ X → z ∈ ⋃ i, Set.range (cs i).γ) :
    (Work.SurgeryInvariance.WindingSpan P X = ⊤ ∧ Work.SurgeryInvariance.WindingSpan P Y = ⊥) ∨
      (Work.SurgeryInvariance.WindingSpan P X = ⊥ ∧ Work.SurgeryInvariance.WindingSpan P Y = ⊤) := by
  exact Work.Drive.EpsForm.Wall.existsUnique_top_of_two_pieces hsimple hess hdisj hXc hYc
    hXopen
    (isOpenInCarrier_right_of_frontier (P := P) hYc hXY hcover hfront)
    hXY hcover

end Work.Drive.Mono
