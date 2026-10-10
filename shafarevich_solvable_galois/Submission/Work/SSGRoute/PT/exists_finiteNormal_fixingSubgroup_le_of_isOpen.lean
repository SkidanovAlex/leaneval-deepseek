import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Topology

namespace Work.SSGRoute.PT

/-- In an algebraic closure `Ω` of a number field `k`, any open subgroup `U` of the absolute
Galois group `Gal(Ω/k)` (Krull topology) contains the fixing subgroup of a finite-dimensional
normal intermediate field `L` that contains a prescribed finite intermediate field `K`.

This is the standard fact that basic Krull neighbourhoods of the identity are fixing subgroups
of finite subextensions; taking a normal closure below the given finite subextension upgrades
the witness to a normal one containing `K`. -/
theorem exists_finiteNormal_fixingSubgroup_le_of_isOpen
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K]
    (U : Subgroup (Ω ≃ₐ[k] Ω)) (hU : IsOpen (U : Set (Ω ≃ₐ[k] Ω))) :
    ∃ (L : IntermediateField k Ω) (_ : FiniteDimensional k L) (_ : Normal k L),
      K ≤ L ∧ L.fixingSubgroup ≤ U := by
  -- `U` is a neighbourhood of the identity for the Krull topology.
  have hmem : (U : Set (Ω ≃ₐ[k] Ω)) ∈ 𝓝 (1 : Ω ≃ₐ[k] Ω) :=
    hU.mem_nhds U.one_mem
  -- Extract a *finite normal* subextension whose fixing subgroup lies in `U`.
  obtain ⟨E, hEfin, _hEnorm, hsub⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal k Ω (U : Set (Ω ≃ₐ[k] Ω))).mp hmem
  -- The compositum `K ⊔ E` is finite over `k`.
  let K' : IntermediateField k Ω := K ⊔ E
  haveI hK'fin : FiniteDimensional k K' := K.finiteDimensional_sup E
  -- Its normal closure `L` inside `Ω` is finite, normal, and contains `K ⊔ E`.
  let L : IntermediateField k Ω := IntermediateField.normalClosure k ↥K' Ω
  haveI hLfin : FiniteDimensional k L := normalClosure.is_finiteDimensional k ↥K' Ω
  haveI hLnorm : Normal k L := normalClosure.normal k ↥K' Ω
  have hK'L : K' ≤ L := IntermediateField.le_normalClosure K'
  have hKL : K ≤ L := le_trans le_sup_left hK'L
  have hEL : E ≤ L := le_trans le_sup_right hK'L
  refine ⟨L, hLfin, hLnorm, hKL, ?_⟩
  -- Since `E ≤ L`, the fixing subgroup of `L` sits inside that of `E`, hence inside `U`.
  exact le_trans (IntermediateField.fixingSubgroup_antitone hEL) hsub

end Work.SSGRoute.PT
