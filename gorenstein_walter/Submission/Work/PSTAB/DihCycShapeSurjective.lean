import Mathlib
import Submission.Work.PSTAB.Defs

namespace Work.PSTAB

/-- `DihCycShape` descends along a surjective homomorphism `f : T →* U`: if `R` witnesses
`DihCycShape T`, then `R.map f` witnesses `DihCycShape U`.

* `R.map f` is normal in `U` because `R` is normal and `f` is surjective;
* it is cyclic, being the surjective image of `R` under `f.subgroupMap R`;
* if `u ∉ R.map f` then any preimage `t` of `u` lies outside `R`, so `u ^ 2 = f (t ^ 2) = 1`;
* and if `u, v ∉ R.map f` with preimages `t, s`, then `t, s ∉ R`, so
  `u * v = f (t * s) ∈ R.map f`. -/
theorem DihCycShapeSurjective {T U : Type*} [Group T] [Group U] (hT : Work.PSTAB.DihCycShape T)
    (f : T →* U) (hf : Function.Surjective f) : Work.PSTAB.DihCycShape U := by
  obtain ⟨R, hRnorm, _hRcyc, hinv, hclos⟩ := hT
  refine ⟨R.map f, hRnorm.map f hf, ?_, ?_, ?_⟩
  · exact isCyclic_of_surjective (f.subgroupMap R) (f.subgroupMap_surjective R)
  · intro u hu
    obtain ⟨t, rfl⟩ := hf u
    have ht : t ∉ R := fun ht => hu (Subgroup.mem_map_of_mem f ht)
    rw [← map_pow, hinv t ht, map_one]
  · intro u v hu hv
    obtain ⟨t, rfl⟩ := hf u
    obtain ⟨s, rfl⟩ := hf v
    have ht : t ∉ R := fun ht => hu (Subgroup.mem_map_of_mem f ht)
    have hs : s ∉ R := fun hs => hv (Subgroup.mem_map_of_mem f hs)
    rw [← map_mul]
    exact Subgroup.mem_map_of_mem f (hclos t s ht hs)

end Work.PSTAB
