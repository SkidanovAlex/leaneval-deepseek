import Mathlib
import Submission.Work.ORHughesFree.DivisionClosure
import Submission.Work.ORHughesFree.DivisionClosure.divisionClosure_map_of_ringEquiv

namespace Work.ORHughesFree.DivisionClosure

/-- **A ring automorphism preserving a set of generators preserves its division closure.**
If `e '' R = R` then `e` maps `divisionClosure R` into itself.

This is the tool used to show that the division closure `D_{N,U_N}` of `φ(K[N])` in `U_N` is
invariant under the twist `τ` of [JZLA20, Theorem 6.1] (conjugation by `φ(t)`, which fixes
`φ(K[N])` because `N ⊴ H`). -/
theorem mapsTo_divisionClosure_of_image_eq {S : Type} [Ring S] (e : S ≃+* S) (R : Set S)
    (h : e '' R = R) :
    Set.MapsTo e (divisionClosure R : Set S) (divisionClosure R : Set S) := by
  have hmap : (divisionClosure R).map e.toRingHom = divisionClosure R := by
    rw [divisionClosure_map_of_ringEquiv, h]
  intro x hx
  have : e x ∈ (divisionClosure R).map e.toRingHom := Subring.mem_map.mpr ⟨x, hx, rfl⟩
  rwa [hmap] at this

/-- The same for an automorphism which preserves `R` only as a set under `e` *and* `e.symm`
(the hypothesis `e '' R = R` is the conjunction of the two). -/
theorem mapsTo_divisionClosure_of_mapsTo {S : Type} [Ring S] (e : S ≃+* S) (R : Set S)
    (h : ∀ x ∈ R, e x ∈ R) (h' : ∀ x ∈ R, e.symm x ∈ R) :
    Set.MapsTo e (divisionClosure R : Set S) (divisionClosure R : Set S) := by
  refine mapsTo_divisionClosure_of_image_eq e R (Set.Subset.antisymm ?_ ?_)
  · rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  · intro x hx
    refine ⟨e.symm x, h' x hx, ?_⟩
    simp

end Work.ORHughesFree.DivisionClosure
