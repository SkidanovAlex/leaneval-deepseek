import Mathlib
import Submission.Work.DivisionClosure.divisionClosure_map_subtype
import Submission.Work.ORHughesFree.DivisionClosure
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.Instances

namespace Work.DivisionClosure

open Work.ORHughesFree

theorem divisionClosure_transport {R S : Type} [Ring R] [Ring S] {V : Subring R}
    [Work.ORHughesFree.VonNeumannRegularRing V]
    (φ : S →+* ↥V) :
    ∃ ê : ↥(Work.ORHughesFree.divisionClosure (Set.range (fun x : S => ((φ x : ↥V) : R)))) ≃+*
          ↥(Work.ORHughesFree.divisionClosure (Set.range φ)),
      ∀ x : S, ê ⟨((φ x : ↥V) : R), Work.ORHughesFree.subset_divisionClosure _ ⟨x, rfl⟩⟩ =
        ⟨φ x, Work.ORHughesFree.subset_divisionClosure _ ⟨x, rfl⟩⟩ := by
  have hsub : (Work.ORHughesFree.divisionClosure (Set.range (fun x : S => ((φ x : ↥V) : R))) :
        Subring R) =
      (Work.ORHughesFree.divisionClosure (Set.range φ)).map (Subring.subtype V) := by
    have hrange : Set.range (fun x : S => ((φ x : ↥V) : R)) = Subtype.val '' Set.range φ := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨φ x, ⟨x, rfl⟩, rfl⟩
      · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, rfl⟩
    rw [hrange, Work.DivisionClosure.divisionClosure_map_subtype (Set.range φ)]
  let D : Subring ↥V := Work.ORHughesFree.divisionClosure (Set.range φ)
  let ι : ↥D →+* ↥(D.map (Subring.subtype V)) :=
    { toFun := fun x => ⟨((x : ↥V) : R), Subring.mem_map.mpr ⟨x, x.2, rfl⟩⟩
      map_one' := Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun x y => Subtype.ext rfl
      map_mul' := fun x y => Subtype.ext rfl }
  have hι : Function.Bijective ι := by
    constructor
    · intro x y hxy
      refine Subtype.ext (Subtype.ext ?_)
      exact congrArg (fun z : ↥(D.map (Subring.subtype V)) => (z : R)) hxy
    · rintro ⟨y, hy⟩
      obtain ⟨x, hx, hxy⟩ := Subring.mem_map.mp hy
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let e₁ : ↥(Work.ORHughesFree.divisionClosure (Set.range (fun x : S => ((φ x : ↥V) : R)))) ≃+*
      ↥((Work.ORHughesFree.divisionClosure (Set.range φ)).map (Subring.subtype V)) :=
    RingEquiv.subringCongr hsub
  let e₂ : ↥((Work.ORHughesFree.divisionClosure (Set.range φ)).map (Subring.subtype V)) ≃+*
      ↥(Work.ORHughesFree.divisionClosure (Set.range φ)) :=
    (RingEquiv.ofBijective ι hι).symm
  refine ⟨e₁.trans e₂, ?_⟩
  intro x
  rw [RingEquiv.trans_apply]
  exact RingEquiv.symm_apply_apply (RingEquiv.ofBijective ι hι)
    ⟨φ x, Work.ORHughesFree.subset_divisionClosure _ ⟨x, rfl⟩⟩

end Work.DivisionClosure
