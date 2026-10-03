import Mathlib
import Submission.Work.ORHughesFree.Section6.RatStruct
import Submission.Work.ORHughesFree.Section6.UnitOf
import Submission.Work.ORHughesFree.Section6.Reduce

namespace Work.Section6

theorem Phi_ofGroup_mem_of_N {K : Type} [Field K] {H : Type} [Group H] {P : Type} [Ring P]
    {DN : Subring P} (φP : MonoidAlgebra K H →+* P) (N : Subgroup H)
    (hNmem : ∀ x : MonoidAlgebra K ↥N,
      φP (MonoidAlgebra.mapDomainRingHom K N.subtype x) ∈ DN)
    (u : Kˣ × H) (hu : u ∈ Work.ORHughesFree.unitsTimesSubgroup (K := K) N) :
    ((Work.ORHughesFree.divisionClosure (Set.range φP)).subtype.comp
      (Work.ORHughesFree.Phi φP)) (Work.ORHughesFree.RatU.ofGroup u) ∈ DN := by
  have huN : u.2 ∈ N := Work.ORHughesFree.mem_unitsTimesSubgroup.mp hu
  have hmem := hNmem (MonoidAlgebra.single ⟨u.2, huN⟩ (u.1 : K))
  have hsingle : MonoidAlgebra.mapDomainRingHom K N.subtype
      (MonoidAlgebra.single ⟨u.2, huN⟩ (u.1 : K)) = Work.ORHughesFree.unitOf u := by
    rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]
    rfl
  rw [RingHom.comp_apply, Work.ORHughesFree.Phi_ofGroup]
  change φP (Work.ORHughesFree.unitOf u) ∈ DN
  rw [← hsingle]
  exact hmem

end Work.Section6
