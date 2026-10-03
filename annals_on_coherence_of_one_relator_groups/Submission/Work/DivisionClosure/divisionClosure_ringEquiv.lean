import Mathlib
import Submission.Work.ORHughesFree.DivisionClosure
import Submission.Work.ORHughesFree.DivisionClosure.divisionClosure_map_of_ringEquiv
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.Instances

namespace Work.DivisionClosure

theorem divisionClosure_ringEquiv {S U P : Type} [Ring S] [Ring U] [Ring P]
    (φ₁ : S →+* U) (φ₂ : S →+* P) (e : U ≃+* P) (he : ∀ x : S, e (φ₁ x) = φ₂ x) :
    ∃ ê : ↥(Work.ORHughesFree.divisionClosure (Set.range φ₁)) ≃+*
      ↥(Work.ORHughesFree.divisionClosure (Set.range φ₂)),
      ∀ x : S, ê ⟨φ₁ x, Work.ORHughesFree.subset_divisionClosure _ ⟨x, rfl⟩⟩ =
        ⟨φ₂ x, Work.ORHughesFree.subset_divisionClosure _ ⟨x, rfl⟩⟩ := by
  -- The two generators have the same image under `e`: `e '' range φ₁ = range φ₂`.
  have hset : e '' Set.range φ₁ = Set.range φ₂ := by
    ext y
    constructor
    · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
      exact ⟨s, (he s).symm⟩
    · rintro ⟨s, rfl⟩
      exact ⟨φ₁ s, ⟨s, rfl⟩, he s⟩
  -- Hence `e` maps the two division closures onto each other.
  have hmap : (Work.ORHughesFree.divisionClosure (Set.range φ₁)).map e.toRingHom =
      Work.ORHughesFree.divisionClosure (Set.range φ₂) := by
    rw [Work.ORHughesFree.DivisionClosure.divisionClosure_map_of_ringEquiv, hset]
  -- `RingEquiv.restrict` restricts `e` to the pair of subrings, given the membership
  -- correspondence `x ∈ D₁ ↔ e x ∈ D₂`.
  refine ⟨RingEquiv.restrict e _ _ ?_, ?_⟩
  · intro x
    rw [← hmap]
    constructor
    · intro hx
      exact Subring.mem_map.mpr ⟨x, hx, rfl⟩
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subring.mem_map.mp hx
      exact e.injective hyx ▸ hy
  · intro x
    exact Subtype.ext (by
      rw [RingEquiv.restrict_apply_coe]
      exact he x)

end Work.DivisionClosure
