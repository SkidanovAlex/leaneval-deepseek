import Mathlib
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Base change of an intermediate field to a subfield

For intermediate fields `K ≤ L` of `Ω / k`, `baseChange K L h` is the same field `L`, viewed as an
intermediate field of `Ω` over `↥K` rather than over `k`.  This is the bookkeeping needed to apply
the `↥K`-based Galois-theoretic lemmas (the extension lemma
`exists_algEquiv_restrict_eq_of_fixing` and the transport `isGalois_comap_of_le_over`) to fields
that the escape construction produces over `k`.

Mathlib's `IntermediateField.restrictScalars` only goes from a larger base to a smaller one, so the
construction is written out directly: the carrier is `L` and the only new datum is the
`algebraMap ↥K Ω`-membership, which is `K ≤ L`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open scoped Pointwise

namespace Work.SSGRoute.EscapeCoreLib

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- The field `L`, viewed as an intermediate field of `Ω` over `↥K` (for `K ≤ L`). -/
def baseChange (K : IntermediateField k Ω) (L : IntermediateField k Ω) (h : K ≤ L) :
    IntermediateField ↥K Ω where
  toSubalgebra :=
    { carrier := (L : Set Ω)
      mul_mem' := fun ha hb => L.mul_mem ha hb
      one_mem' := L.one_mem
      add_mem' := fun ha hb => L.add_mem ha hb
      zero_mem' := L.zero_mem
      algebraMap_mem' := fun x => h x.2 }
  inv_mem' := fun x hx => L.inv_mem hx

@[simp] theorem mem_baseChange (K L : IntermediateField k Ω) (h : K ≤ L) {x : Ω} :
    x ∈ baseChange K L h ↔ x ∈ L := by
  change x ∈ (L : Set Ω) ↔ x ∈ (L : Set Ω)
  exact Iff.rfl

theorem le_baseChange_iff (K L : IntermediateField k Ω) (h : K ≤ L)
    {M : IntermediateField ↥K Ω} :
    M ≤ baseChange K L h ↔ (M : Set Ω) ⊆ (L : Set Ω) := by
  constructor
  · intro hM x hx
    exact (mem_baseChange K L h).mp (hM hx)
  · intro hM x hx
    exact (mem_baseChange K L h).mpr (hM hx)



/-- The identity `AlgEquiv` between `↥L` and its base change to `↥K` (same carrier). -/
noncomputable def baseChangeAlgEquiv (K L : IntermediateField k Ω) (h : K ≤ L) :
    ↥L ≃ₐ[k] ↥(baseChange K L h) :=
  AlgEquiv.ofBijective
    { toFun := fun x => ⟨(x : Ω), (mem_baseChange K L h).mpr x.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun a b => Subtype.ext rfl
      commutes' := fun r => Subtype.ext rfl }
    (by
      constructor
      · intro a b hab
        refine Subtype.ext ?_
        simpa using congrArg (fun z : ↥(baseChange K L h) => (z : Ω)) hab
      · intro y
        exact ⟨⟨(y : Ω), (mem_baseChange K L h).mp y.2⟩, Subtype.ext rfl⟩)

/-- `L` is Galois over `↥K` whenever it is Galois over `k` (and contains `K`). -/
theorem isGalois_baseChange (K L : IntermediateField k Ω) (h : K ≤ L) [IsGalois k L] :
    IsGalois ↥K (baseChange K L h) := by
  haveI : IsGalois k ↥(baseChange K L h) := IsGalois.of_algEquiv (baseChangeAlgEquiv K L h)
  exact IsGalois.tower_top_of_isGalois k ↥K _

/-- `L` stays finite over `k` after the base change. -/
theorem finiteDimensional_baseChange (K L : IntermediateField k Ω) (h : K ≤ L)
    [FiniteDimensional k L] : FiniteDimensional k ↥(baseChange K L h) :=
  FiniteDimensional.of_injective (baseChangeAlgEquiv K L h).symm.toLinearEquiv.toLinearMap
    (baseChangeAlgEquiv K L h).symm.injective

end Work.SSGRoute.EscapeCoreLib
