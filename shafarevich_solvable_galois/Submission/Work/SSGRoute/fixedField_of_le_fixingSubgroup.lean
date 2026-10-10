import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

set_option linter.style.haveILetI false

/-- **The infinite Galois correspondence, in the form the Shafarevich route needs.**

Let `Ω` be an algebraic closure of a number field `k`, let `K ⊆ Ω` be a finite normal
subextension, and let `H ≤ Gal(Ω/k)` be a subgroup which
* fixes `K` pointwise (`H ≤ K.fixingSubgroup`) and is normal in `Gal(Ω/k)`, and
* contains the fixing subgroup of some finite normal subextension `E ⊆ Ω`.

Then the fixed field of `H` sits between `K` and `E`, is finite and normal over `k`, and
its fixing subgroup is `H` itself.

The two "non-obvious" inputs are that `H` is clopen (it contains the open subgroup
`E.fixingSubgroup`) and hence that the infinite Galois correspondence applies verbatim. -/
theorem fixedField_of_le_fixingSubgroup (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [Normal k K]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (hHK : H ≤ K.fixingSubgroup) (hHN : H.Normal)
    (E : IntermediateField k Ω) [FiniteDimensional k E] [Normal k E]
    (hE : E.fixingSubgroup ≤ H) :
    K ≤ IntermediateField.fixedField H ∧ FiniteDimensional k (IntermediateField.fixedField H) ∧
      Normal k (IntermediateField.fixedField H) ∧
      (IntermediateField.fixedField H).fixingSubgroup = H := by
  -- The Krull topology on `Gal(Ω/k)` (here: on `Ω ≃ₐ[k] Ω`).
  haveI hgal : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  -- (1) `K ≤ fixedField H` is the Galois connection applied to `hHK`.
  have hKH : K ≤ IntermediateField.fixedField H := (IntermediateField.le_iff_le H K).mpr hHK
  -- (2) `fixedField H ≤ E`, since `fixedField` is antitone and `fixedField E.fixingSubgroup = E`.
  have hfixE : IntermediateField.fixedField E.fixingSubgroup = E :=
    InfiniteGalois.fixedField_fixingSubgroup (k := k) (K := Ω) E
  have hle : IntermediateField.fixedField H ≤ E := by
    rw [← hfixE]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx ⊢
    exact fun σ hσ => hx σ (hE hσ)
  -- (3) hence `fixedField H` is finite over `k`, being a `k`-subspace of the finite `E`.
  have hfin : FiniteDimensional k (IntermediateField.fixedField H) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion hle).injective
  -- (4) `fixedField H` is normal over `k`: the fixed field of a normal subgroup.
  haveI : IsGalois k (IntermediateField.fixedField H) :=
    IsGalois.of_fixedField_normal_subgroup (K := k) (L := Ω) H (hn := hHN)
  have hNorm : Normal k (IntermediateField.fixedField H) := IsGalois.to_normal
  -- (5) `H` is open because it contains `E.fixingSubgroup`, hence closed, hence equal to the
  -- fixing subgroup of its fixed field (infinite Galois correspondence).
  have hopen : IsOpen (H : Set (Ω ≃ₐ[k] Ω)) :=
    Subgroup.isOpen_mono hE (IntermediateField.fixingSubgroup_isOpen E)
  have hclosed : IsClosed (H : Set (Ω ≃ₐ[k] Ω)) := Subgroup.isClosed_of_isOpen H hopen
  have hfix : (IntermediateField.fixedField H).fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField (k := k) (K := Ω) ⟨H, hclosed⟩
  exact ⟨hKH, hfin, hNorm, hfix⟩

end Work.SSGRoute
