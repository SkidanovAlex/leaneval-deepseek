import Mathlib
import Submission.NK.BrauerHasse.Profinite

namespace NK.HassePrinciple

universe u

/-- The level-wise restriction `levelInclHom hV L : V/(V ⊓ Gal(K'/L)) →* U/(U ⊓ Gal(K'/L))` induced
by an inclusion `V ≤ U` of subgroups of `Gal(K'/K)` is injective. -/
theorem levelInclHom_injective {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] {U V : Subgroup Gal(K'/K)} (hV : V ≤ U)
    (L : FiniteGaloisIntermediateField K K') :
    Function.Injective (NK.BrauerHasse.levelInclHom hV L) := by
  -- It suffices to see that the kernel is trivial.
  rw [← MonoidHom.ker_eq_bot_iff]
  unfold NK.BrauerHasse.levelInclHom
  -- The kernel of `QuotientGroup.map` is the image of `M.comap f` in `V ⟶ V/(V ⊓ Gal(K'/L))`.
  rw [QuotientGroup.ker_map]
  -- But `M.comap f` is precisely `V ⊓ Gal(K'/L)`: an element of `V` is fixed by `L` in `U`
  -- exactly when it is fixed by `L` in `Gal(K'/K)`, the two notions being the same element.
  have hcomap : Subgroup.comap (Subgroup.inclusion hV) (L.fixingSubgroup.subgroupOf U) =
      L.fixingSubgroup.subgroupOf V := by
    ext v
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      Subgroup.coe_inclusion]
  rw [hcomap, QuotientGroup.map_mk'_self]

end NK.HassePrinciple
