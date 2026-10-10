import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.E1aClean.decompField_embeds_completion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The decomposition-field datum of a finite place

For a finite place `A` of `Ω` over the prime `q` of `K`, the *decomposition field*
`k^h = Ω^{D_A}` (fixed field of `D_A = decomp k A`) and the *henselisation*
`K^h = K·Ω^{D_A} = Ω^{D_A ⊓ Gal(Ω/K)}` are the fields at which the local dictionary of
`E1aClean.localDictionary_natural_family` is built: `Gal(Ω/k^h) = D_A` and `Gal(K^h/k^h) ≅ D_q`,
so that the field-generic `E1cGeneric` dictionary at the datum `(k^h, Ω, K^h)` has the local
cohomology groups on both sides, and its coefficient can be pushed from `(K^h)ˣ` to the completion
`K_qˣ`.

The whole point of staying inside `Ω` (rather than passing to the completion `Ω_v`, as the
earlier route did) is that the coinduced coefficient module `homCoind k Ω K R = (R.V →+ Ωˣ)` is
*literally the same type* at both levels, so that the base-change comparison (BC) is a comparison
of cocycles with values in one and the same group.
-/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt

noncomputable section

variable (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
variable (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]

/-- **The decomposition field of a place `A` of `Ω`**: the fixed field `Ω^{D_A}` of the
decomposition group of `A`.  This is the base field of the local datum. -/
noncomputable def decompField (A : ValuationSubring Ω) : IntermediateField k Ω :=
  IntermediateField.fixedField (SSGRoute.decomp k A)

/-- **The henselisation of `K` at the place `A`**: the fixed field `Ω^{D_A ⊓ Gal(Ω/K)}` of the
decomposition group of `A` over `K`.  It is the compositum `K · Ω^{D_A}`. -/
noncomputable def henselField (A : ValuationSubring Ω) :
    IntermediateField k Ω :=
  IntermediateField.fixedField (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker)

/-- The decomposition field is contained in the henselisation: `k^h ≤ K^h`. -/
theorem decompField_le_henselField (A : ValuationSubring Ω) :
    decompField k Ω A ≤ henselField k Ω K A := by
  exact IntermediateField.fixedField_le inf_le_left

/-- `K` is contained in its henselisation `K^h = K·Ω^{D_A}`: the elements of `K` are fixed by
`Gal(Ω/K) ⊇ D_A ⊓ Gal(Ω/K)`. -/
theorem le_henselField (A : ValuationSubring Ω) : K ≤ henselField k Ω K A := by
  have hker : (SSGRoute.res k K).ker = K.fixingSubgroup :=
    IntermediateField.restrictNormalHom_ker K
  intro x hx
  rw [henselField, hker, IntermediateField.mem_fixedField_iff]
  intro h hh
  exact hh.2 ⟨x, hx⟩

/-- **The henselisation as an extension of the decomposition field**: `K^h / k^h`.  This is the
local datum `(k^h, Ω, K^h)` of the dictionary. -/
noncomputable def henselOverDecomp (A : ValuationSubring Ω) :
    IntermediateField ↥(decompField k Ω A) Ω :=
  IntermediateField.extendScalars (decompField_le_henselField k Ω K A)

/-- The two descriptions of the same field: the henselisation `Ω^{D_A ⊓ G_K}` over `k` has, as an
extension of the decomposition field, the same elements. -/
theorem henselOverDecomp_coe (A : ValuationSubring Ω) (x : ↥(henselOverDecomp k Ω K A)) :
    (x : Ω) ∈ henselField k Ω K A := x.2

end

end Work.SSGRoute.E1aClean
