import Mathlib
import Submission.Work.PSTAB.Defs

namespace Work.PSTAB

/-- `DihCycShape` passes to subgroups: if `R` witnesses `DihCycShape T`, then `R.subgroupOf S`
witnesses `DihCycShape ↥S`.

* `R.subgroupOf S = R ⊓ S`, viewed inside `S`; it is normal in `S` because `R` is normal in `T`;
* it is cyclic, being (isomorphic to) a subgroup of the cyclic group `↥R` via the injection
  `↥(R.subgroupOf S) →* ↥R`;
* if `g ∈ S` lies outside `R.subgroupOf S`, then `g` (viewed in `T`) lies outside `R`, so
  `g ^ 2 = 1`;
* and similarly a product of two such elements lies in `R.subgroupOf S`. -/
theorem DihCycShapeSubgroup {T : Type*} [Group T] (hT : Work.PSTAB.DihCycShape T)
    (S : Subgroup T) : Work.PSTAB.DihCycShape ↥S := by
  obtain ⟨R, hRn, hRc, hsq, hmul⟩ := hT
  refine ⟨R.subgroupOf S, hRn.subgroupOf S, ?_, ?_, ?_⟩
  · refine @isCyclic_of_injective ↥(R.subgroupOf S) ↥R _ _ hRc ?_ ?_
    · refine { toFun := fun x => ⟨(x : ↥S), Subgroup.mem_subgroupOf.mp x.2⟩,
               map_one' := rfl, map_mul' := fun a b => rfl }
    · intro a b h
      exact Subtype.ext (Subtype.ext (congrArg (fun z : ↥R => (z : T)) h))
  · intro g hg
    exact Subtype.ext (hsq (g : T) (fun hm => hg (Subgroup.mem_subgroupOf.mpr hm)))
  · intro g h hg hh
    exact Subgroup.mem_subgroupOf.mpr
      (hmul (g : T) (h : T) (fun hm => hg (Subgroup.mem_subgroupOf.mpr hm))
                                (fun hm => hh (Subgroup.mem_subgroupOf.mpr hm)))

end Work.PSTAB
