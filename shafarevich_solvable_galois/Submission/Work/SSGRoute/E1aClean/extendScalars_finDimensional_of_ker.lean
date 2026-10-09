import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Finiteness of a base-changed intermediate field from a finite quotient

Let `K'/κ` be a Galois extension (possibly infinite), `U ≤ F` intermediate fields, and
`φ : Gal(K'/U) →* γ` a homomorphism to a finite group whose kernel is the fixing subgroup
`Gal(K'/F) ⊆ Gal(K'/U)`.  Then `F`, viewed as an intermediate field of `K'/U`, is finite
dimensional over `U`.

The point is that `Gal(K'/F)` has finite index in `Gal(K'/U)` (it is the kernel of `φ`), and by the
fundamental theorem of infinite Galois theory the degree of `F/U` is that index.

The proof does not go through the Krull topology: we use the identity
`IntermediateField.finrank_eq_fixingSubgroup_index`, namely that for a Galois extension `K'/U` and
an intermediate field `L`, the natural number `[L : U]` equals the index of the fixing subgroup
`L.fixingSubgroup ≤ Gal(K'/U)` (both being `0` when infinite).  Transporting the fixing subgroup
along `IntermediateField.fixingSubgroupEquiv U` (the isomorphism between `Gal(K'/U)` and the fixing
subgroup of `U` inside `Gal(K'/κ)`) turns the hypothesis on `φ.ker` into `L.fixingSubgroup = φ'.ker`
for the transported homomorphism `φ'`, whose kernel has index `Nat.card φ'.range ≤ Nat.card γ`,
which is nonzero.  Hence `[F : U] = Nat.card φ'.range ≠ 0` and in particular finite.
-/

namespace Work.SSGRoute.E1aClean

open IntermediateField

/-- Change of base for fixing subgroups: for intermediate fields `U ≤ F` of a Galois extension
`K'/κ`, the fixing subgroup of `F` inside `Gal(K'/U)` is the image of the fixing subgroup of `F`
inside `Gal(K'/κ)` under the isomorphism `IntermediateField.fixingSubgroupEquiv U`. -/
theorem map_fixingSubgroupEquiv_subgroupOf {κ K' : Type*} [Field κ] [Field K']
    [Algebra κ K'] [IsGalois κ K'] {U F : IntermediateField κ K'} (h : U ≤ F) :
    Subgroup.map (↑(IntermediateField.fixingSubgroupEquiv U))
        (F.fixingSubgroup.subgroupOf U.fixingSubgroup) =
      (IntermediateField.extendScalars h).fixingSubgroup := by
  ext f
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact hg ⟨x, hx⟩
  · intro hf
    refine ⟨(IntermediateField.fixingSubgroupEquiv U).symm f, ?_, ?_⟩
    · intro x
      show ((IntermediateField.fixingSubgroupEquiv U).symm f : Gal(K'/κ)) x = x
      exact (IntermediateField.mem_fixingSubgroup_iff _ f).mp hf x x.2
    · exact (IntermediateField.fixingSubgroupEquiv U).apply_symm_apply f

theorem extendScalars_finDimensional_of_ker {κ K' : Type*} [Field κ] [Field K']
    [Algebra κ K'] [IsGalois κ K'] {U F : IntermediateField κ K'} (h : U ≤ F)
    {γ : Type*} [Group γ] [Finite γ] (φ : ↥(U.fixingSubgroup) →* γ)
    (hker : φ.ker = F.fixingSubgroup.subgroupOf U.fixingSubgroup) :
    FiniteDimensional ↥U ↥(IntermediateField.extendScalars h) := by
  let e := IntermediateField.fixingSubgroupEquiv U
  let φ' : Gal(K'/↥U) →* γ := φ.comp (e.symm : Gal(K'/↥U) →* ↥U.fixingSubgroup)
  have hker' : φ'.ker = (IntermediateField.extendScalars h).fixingSubgroup := by
    have h1 : φ'.ker = Subgroup.map (e : ↥U.fixingSubgroup →* Gal(K'/↥U)) φ.ker := by
      simp [φ']
    rw [h1, hker]
    exact map_fixingSubgroupEquiv_subgroupOf h
  have hfr : Module.finrank ↥U ↥(IntermediateField.extendScalars h) = Nat.card ↥φ'.range := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index K' (IntermediateField.extendScalars h),
      ← hker', Subgroup.index_ker φ']
  have hpos : 0 < Nat.card ↥φ'.range :=
    Nat.card_pos_iff.mpr ⟨⟨1, Subgroup.one_mem _⟩, inferInstance⟩
  by_contra hinf
  rw [Module.finrank_of_infinite_dimensional hinf] at hfr
  omega

end Work.SSGRoute.E1aClean
