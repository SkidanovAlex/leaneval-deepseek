import Mathlib
import Submission.Work.ORHughesFree.DivisionClosure
import Submission.Work.ORHughesFree.DivisionClosure.divisionClosure_mono
import Submission.Work.ORHughesFree.DivisionClosure.divisionClosure_idem
import Submission.Work.ORHughesFree.DivisionClosure.inverse_mem_divisionClosure

namespace Work.ORHughesFree.DivisionClosure

/-- The division closure is functorial with respect to ring homomorphisms: the image of
`divisionClosure R` under `f` is contained in the division closure of the image of `R`. -/
theorem divisionClosure_map_le {S S' : Type*} [Ring S] [Ring S'] (f : S →+* S') (R : Set S) :
    (divisionClosure R).map f ≤ divisionClosure (f '' R) := by
  rw [Subring.map_le_iff_le_comap]
  set D : Subring S' := divisionClosure (f '' R)
  have hR : R ⊆ (Subring.comap f D : Set S) := by
    intro x hx
    show f x ∈ D
    exact subset_divisionClosure (f '' R) ⟨x, hx, rfl⟩
  have hC : ∀ x ∈ (Subring.comap f D : Set S), ∀ y, x * y = 1 → y * x = 1 →
      y ∈ (Subring.comap f D : Set S) := by
    intro x hx y hxy hyx
    have hxD : f x ∈ D := hx
    show f y ∈ D
    exact divisionClosure_inv_mem (f '' R) hxD (by rw [← map_mul, hxy, map_one])
      (by rw [← map_mul, hyx, map_one])
  intro x hx
  exact divisionClosure_le_of_invClosed (Subring.comap f D) hC (divisionClosure_mono hR hx)

end Work.ORHughesFree.DivisionClosure
