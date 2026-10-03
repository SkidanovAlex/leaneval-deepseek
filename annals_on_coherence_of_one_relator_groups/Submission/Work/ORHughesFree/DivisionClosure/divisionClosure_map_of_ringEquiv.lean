import Mathlib
import Submission.Work.ORHughesFree.DivisionClosure
import Submission.Work.ORHughesFree.DivisionClosure.divisionClosure_idem
import Submission.Work.ORHughesFree.DivisionClosure.divisionClosure_map_le

namespace Work.ORHughesFree.DivisionClosure

/-- A ring isomorphism sends the division closure of `R` onto the division closure of the image
of `R`: `Subring.map` along a ring equivalence commutes with `divisionClosure`.  One inclusion is
`divisionClosure_map_le`; for the other, `(divisionClosure R).map e.toRingHom` is a subring of `T`
containing `e '' R` and closed under two-sided inverses in `T` (inverses transport along the ring
isomorphism `e`), so `divisionClosure_le_of_invClosed` applies. -/
theorem divisionClosure_map_of_ringEquiv {S T : Type} [Ring S] [Ring T] (e : S ≃+* T)
    (R : Set S) : (divisionClosure R).map e.toRingHom = divisionClosure (e '' R) := by
  apply le_antisymm
  · -- `⊆`: functoriality of the division closure along the ring homomorphism `e`
    exact divisionClosure_map_le e.toRingHom R
  · -- `⊇`: `(divisionClosure R).map e.toRingHom` is inverse-closed in `T` and contains `e '' R`
    have hclosed : ∀ x ∈ (divisionClosure R).map e.toRingHom, ∀ y : T,
        x * y = 1 → y * x = 1 → y ∈ (divisionClosure R).map e.toRingHom := by
      intro x hx y hxy hyx
      rw [Subring.mem_map] at hx ⊢
      obtain ⟨a, ha, rfl⟩ := hx
      -- `e.symm y` is the two-sided inverse of `a`, hence lies in `divisionClosure R`
      refine ⟨e.symm y, divisionClosure_inv_mem R ha ?_ ?_, ?_⟩
      · have h := congrArg e.symm hxy
        simpa [map_mul] using h
      · have h := congrArg e.symm hyx
        simpa [map_mul] using h
      · simp
    have hEA : (e '' R : Set T) ⊆ (((divisionClosure R).map e.toRingHom : Subring T) : Set T) := by
      rintro x ⟨r, hr, rfl⟩
      exact Subring.mem_map.mpr ⟨r, subset_divisionClosure R hr, rfl⟩
    exact le_trans (divisionClosure_mono hEA)
      (divisionClosure_le_of_invClosed ((divisionClosure R).map e.toRingHom) hclosed)

end Work.ORHughesFree.DivisionClosure
