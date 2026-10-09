import Mathlib
import Submission.NK.ResidueFrob.Inertia
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level triviality locus on the residue field is closed (indeed clopen)

The predicate `NK.FrobeniusBridge.IsTrivialOnResidueAtLevel A N g` ("`g` acts trivially on the
residue field of the finite normal level `N` at the prime below the place `A`") refers to `g` only
through its restriction `g|_N` to `N`.  Hence the set of `g : Gal(K'/K)` satisfying it is a union
of cosets of the fixing subgroup `Gal(K'/N)` of `N`; and since `N/K` is finite-dimensional, that
subgroup is *open* in the Krull topology (Mathlib's `IntermediateField.fixingSubgroup_isOpen`), so
both the set and its complement are open.

We prove this in the form in which it is consumed: `IsClosed` for the level-`N` triviality locus.
-/

namespace NK.ResidueFrob

open scoped Pointwise Topology

/-- **The level triviality locus is constant on the cosets of the fixing subgroup.**

If `k` fixes the finite normal level `N` pointwise, then the two elements `h * k` and `h` have the
same restriction to `N`, hence the same action on the residue field of `N` at the prime below `A`.
-/
theorem isTrivialOnResidueAtLevel_mul_mem_fixingSubgroup_iff {K : Type*} [Field K] [NumberField K]
    {K' : Type*} [Field K'] [Algebra K K'] [IsSepClosure K K']
    (A : NK.FrobeniusBridge.FinitePlaceOf K K') (N : IntermediateField K K')
    [FiniteDimensional K N] [Normal K N] [NumberField ↥N]
    {h k : Gal(K'/K)} (hk : k ∈ N.fixingSubgroup) :
    NK.FrobeniusBridge.IsTrivialOnResidueAtLevel A N (h * k) ↔
      NK.FrobeniusBridge.IsTrivialOnResidueAtLevel A N h := by
  have hk1 : AlgEquiv.restrictNormalHom N k = 1 := by
    rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker]
    exact hk
  have hres : AlgEquiv.restrictNormalHom N (h * k) = AlgEquiv.restrictNormalHom N h := by
    rw [map_mul, hk1, mul_one]
  simp only [NK.FrobeniusBridge.IsTrivialOnResidueAtLevel, hres]

/-- **Closedness of the level triviality locus.**  The set of `h : Gal(K'/K)` acting trivially on
the residue field of the finite normal level `N` at the prime below the place `A` is closed in the
Krull topology — in fact clopen, since the fixing subgroup of `N` is open and the locus is a union
of its cosets. -/
theorem isClosed_setOf_isTrivialOnResidueAtLevel {K : Type*} [Field K] [NumberField K]
    {K' : Type*} [Field K'] [Algebra K K'] [IsSepClosure K K']
    (A : NK.FrobeniusBridge.FinitePlaceOf K K') (N : IntermediateField K K')
    [FiniteDimensional K N] [Normal K N] [NumberField ↥N] :
    IsClosed {h : Gal(K'/K) | NK.FrobeniusBridge.IsTrivialOnResidueAtLevel A N h} := by
  rw [← isOpen_compl_iff]
  rw [isOpen_iff_mem_nhds]
  intro h hh
  -- the coset `h * Gal(K'/N)` is an open neighbourhood of `h` on which the predicate is constant
  have hopen : IsOpen (N.fixingSubgroup : Set Gal(K'/K)) :=
    IntermediateField.fixingSubgroup_isOpen N
  have hnhds : h • (N.fixingSubgroup : Set Gal(K'/K)) ∈ 𝓝 h :=
    (hopen.leftCoset h).mem_nhds ⟨1, N.fixingSubgroup.one_mem, mul_one h⟩
  refine Filter.mem_of_superset hnhds ?_
  rintro g ⟨k, hk, rfl⟩
  exact fun hg => hh ((isTrivialOnResidueAtLevel_mul_mem_fixingSubgroup_iff A N hk).mp hg)

end NK.ResidueFrob
