import Mathlib
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.DivisionClosure
import Submission.Work.ORHughesFree.DivisionClosure.divisionClosure_le_of_vonNeumannRegular
import Submission.Work.ORHughesFree.DivisionClosure.divisionClosure_map_le
import Submission.Work.ORHughesFree.DivisionClosure.inverse_mem_divisionClosure
import Submission.Work.ORHughesFree.DivisionClosure.divisionClosure_idem
import Submission.Work.ORHughesFree.DivisionClosure.divisionClosure_mono

namespace Work.DivisionClosure

open Work.ORHughesFree

/-- The division closure commutes with the inclusion of a von Neumann regular subring: for a
von Neumann regular subring `V ≤ R`, the division closure (computed in `R`) of the image of a
subset `S ⊆ V` is the image of the division closure of `S` (computed in `V`).

Both inclusions are elementary. The `≤` direction uses that `V` is von Neumann regular, so the
inverse in `R` of any element of `V` already lies in `V`; the `≥` direction is the general
functoriality of the division closure under ring homomorphisms. -/
theorem divisionClosure_map_subtype {R : Type} [Ring R] {V : Subring R}
    [Work.ORHughesFree.VonNeumannRegularRing V] (S : Set V) :
    (Work.ORHughesFree.divisionClosure (Subtype.val '' S) : Subring R)
      = (Work.ORHughesFree.divisionClosure S).map (Subring.subtype V) := by
  apply le_antisymm
  · -- `divisionClosure (Subtype.val '' S) ≤ (divisionClosure S).map (Subring.subtype V)`
    intro x hx
    have hclosed : ∀ a ∈ (Work.ORHughesFree.divisionClosure S).map (Subring.subtype V),
        ∀ y : R, a * y = 1 → y * a = 1 →
          y ∈ (Work.ORHughesFree.divisionClosure S).map (Subring.subtype V) := by
      intro a ha y hay hya
      obtain ⟨v, hv, rfl⟩ := Subring.mem_map.mp ha
      -- `V` is von Neumann regular, so the inverse in `R` of an element of `V` lies in `V`.
      have hyV : y ∈ (V : Set R) :=
        Work.ORHughesFree.DivisionClosure.mem_of_mul_eq_one_of_vonNeumannRegular
          (show ((v : V) : R) ∈ (V : Set R) from v.2) hay hya
      -- `divisionClosure S` is closed under inverses in `V`.
      refine Subring.mem_map.mpr ⟨⟨y, hyV⟩, ?_, rfl⟩
      exact Work.ORHughesFree.DivisionClosure.inverse_mem_divisionClosure hv
        (Subtype.coe_injective (by simpa using hay))
        (Subtype.coe_injective (by simpa using hya))
    have hmono : (divisionClosure (Subtype.val '' S) : Subring R) ≤
        divisionClosure ↑((divisionClosure S).map (Subring.subtype V)) :=
      Work.ORHughesFree.DivisionClosure.divisionClosure_mono (by
        rintro z ⟨s, hs, rfl⟩
        exact Subring.mem_map.mpr ⟨s, Work.ORHughesFree.subset_divisionClosure S hs, rfl⟩)
    exact Work.ORHughesFree.DivisionClosure.divisionClosure_le_of_invClosed _ hclosed (hmono hx)
  · -- `(divisionClosure S).map (Subring.subtype V) ≤ divisionClosure (Subtype.val '' S)`
    have h := Work.ORHughesFree.DivisionClosure.divisionClosure_map_le (Subring.subtype V) S
    rwa [Subring.coe_subtype] at h

end Work.DivisionClosure
