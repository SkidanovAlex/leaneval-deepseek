import Mathlib
import Submission.Work.CORE4.A7S4Defs

namespace Work.CORE4.A7S4

/-- The eight permutations of `Fin 7` satisfying `PartnerCond`, i.e. the involutions of
`C_{A₇}(t)` different from `1` and `t`:
`(2 3)(5 6)`, `(2 3)(4 5)`, `(2 3)(4 6)`, `(0 1)(5 6)`, `(0 1)(4 5)`, `(0 1)(4 6)`,
`(0 2)(1 3)` and `(0 3)(1 2)`. -/
private def partnerList : Finset (Equiv.Perm (Fin 7)) :=
  {(Equiv.swap 2 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 6 : Equiv.Perm (Fin 7)),
    (Equiv.swap 2 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 5 : Equiv.Perm (Fin 7)),
    (Equiv.swap 2 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 6 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 6 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 5 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 1 : Equiv.Perm (Fin 7)) * (Equiv.swap 4 6 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 2 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 3 : Equiv.Perm (Fin 7)),
    (Equiv.swap 0 3 : Equiv.Perm (Fin 7)) * (Equiv.swap 1 2 : Equiv.Perm (Fin 7))}

/- Every element satisfying `PartnerCond` lies in the explicit list `partnerList`.  A closed
decidable computation over the `5040` permutations of `Fin 7`. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem mem_partnerList :
    ∀ w : Equiv.Perm (Fin 7), PartnerCond w → w ∈ partnerList := by decide

theorem partnerConj : ∀ w : Equiv.Perm (Fin 7), PartnerCond w → ∃ h : Equiv.Perm (Fin 7), h ∈ ctList ∧ Equiv.Perm.sign h = 1 ∧ h * tP * h⁻¹ = tP ∧ (h * w * h⁻¹ = uP ∨ h * w * h⁻¹ = tP * uP ∨ h * w * h⁻¹ = vP ∨ h * w * h⁻¹ = tP * vP) := by
  intro w hw
  have hmem := mem_partnerList w hw
  rw [partnerList] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨(Equiv.swap 4 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 6 5), by decide⟩
  · exact ⟨1, by decide⟩
  · exact ⟨(Equiv.swap 4 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 6), by decide⟩
  · exact ⟨(Equiv.swap 4 6 : Equiv.Perm (Fin 7)) * (Equiv.swap 6 5), by decide⟩
  · exact ⟨1, by decide⟩
  · exact ⟨(Equiv.swap 4 5 : Equiv.Perm (Fin 7)) * (Equiv.swap 5 6), by decide⟩
  · exact ⟨1, by decide⟩
  · exact ⟨1, by decide⟩

end Work.CORE4.A7S4
