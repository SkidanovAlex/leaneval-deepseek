import Mathlib
import Submission.NK.LocalStructure.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u

namespace NK.Ramification

set_option linter.style.haveILetI false

open IsDedekindDomain.HeightOneSpectrum
open scoped Topology

/-- **A correspondence of finite extension lattices forces the group isomorphism to be
continuous.**

`Φ` carries `M.fixingSubgroup` — for `M` ranging over the finite extensions of the source, a basis
of neighbourhoods of `1` — onto `(C.level M).fixingSubgroup`, a fixing subgroup of a finite
extension, hence an open subgroup of the target.  Since the `M.fixingSubgroup` form a fundamental
system of neighbourhoods of `1`, `Φ` is open at `1`, hence (being a group homomorphism) an open
map.  A bijective open map with compact source and Hausdorff target is a homeomorphism, so `Φ` is
continuous. -/
theorem continuous_of_finiteExtensionCorrespondence
    (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (L' : Type u) [Field L'] [Algebra (𝔮.adicCompletion L) L']
    [IsSepClosure (𝔮.adicCompletion L) L']
    (N : IntermediateField (𝔮.adicCompletion L) L') [FiniteDimensional (𝔮.adicCompletion L) ↥N]
    (K' : Type u) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K']
    (Φ : Gal(L'/↥N) ≃* Gal(K'/𝔭.adicCompletion K))
    (C : NK.LocalStructure.FiniteExtensionCorrespondence Φ) :
    Continuous ⇑Φ := by
  classical
  haveI : IsGalois (𝔮.adicCompletion L) L' := inferInstance
  haveI : IsGalois ↥N L' := inferInstance
  haveI : IsGalois (𝔭.adicCompletion K) K' := inferInstance
  -- Step 1: `Φ` is an open map, because it carries the neighbourhood basis at `1` of the source
  -- onto fixing subgroups of finite extensions of the target, which are open.
  have hopen : IsOpenMap ⇑Φ := by
    rw [IsTopologicalGroup.isOpenMap_iff_nhds_one]
    refine Filter.le_map fun s hs => ?_
    obtain ⟨M, hMfin, hMs⟩ := (krullTopology_mem_nhds_one_iff ↥N L' s).mp hs
    haveI := C.level_finite ⟨M, hMfin⟩
    -- `Φ` sends the fixing subgroup of `M` onto the fixing subgroup of `C.level M`.
    have hfix : ((C.level ⟨M, hMfin⟩).fixingSubgroup : Set Gal(K'/𝔭.adicCompletion K)) =
        ⇑Φ '' (M.fixingSubgroup : Set Gal(L'/↥N)) := by
      rw [C.level_fixing ⟨M, hMfin⟩, Subgroup.coe_map]
      rfl
    have hmem : ((C.level ⟨M, hMfin⟩).fixingSubgroup :
        Set Gal(K'/𝔭.adicCompletion K)) ∈ 𝓝 1 :=
      (IntermediateField.fixingSubgroup_isOpen (C.level ⟨M, hMfin⟩)).mem_nhds (Subgroup.one_mem _)
    refine Filter.mem_of_superset hmem ?_
    rw [hfix]
    exact Set.image_mono hMs
  -- Step 2: hence the inverse `Φ⁻¹` is continuous.
  have hcont_symm : Continuous ⇑Φ.symm := (Equiv.continuous_symm_iff Φ.toEquiv).2 hopen
  -- Step 3: a continuous bijection from a compact space to a Hausdorff space is a homeomorphism;
  -- applying this to `Φ⁻¹ : Gal(K'/κ) → Gal(L'/N)` makes `Φ⁻¹` an open map.
  have hhomeo : IsHomeomorph ⇑Φ.symm :=
    (isHomeomorph_iff_continuous_bijective (f := ⇑Φ.symm)).2 ⟨hcont_symm, Φ.symm.bijective⟩
  -- Step 4: `Φ⁻¹` open means exactly that `Φ` is continuous.
  exact (Equiv.continuous_symm_iff Φ.symm.toEquiv).2 hhomeo.isOpenMap

end NK.Ramification
