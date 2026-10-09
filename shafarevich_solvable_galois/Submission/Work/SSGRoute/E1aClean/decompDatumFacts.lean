import Mathlib
import Submission.Work.SSGRoute.E1aClean.decompDatum
import Submission.Work.SSGRoute.E1aClean.decompField_datum_facts
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The decomposition-field datum: the four structural facts, named

`E1aClean/decompField_datum_facts` proves the four facts of the level-2 datum
`(k^h, Ω, K^h) = (decompField k Ω A, Ω, henselOverDecomp k Ω K A)` in one conjuction; here they are
re-exported under separate names so that the local-dictionary assembly can install them as
instances (`haveI`) one at a time:

* `decompField_isAlgClosure` — `Ω` is an algebraic closure of `k^h`;
* `decompField_fixingSubgroup` — `D_A = Gal(Ω/k^h)`;
* `henselOverDecomp_finiteDimensional` — `K^h/k^h` is finite;
* `henselOverDecomp_isGalois` — `K^h/k^h` is Galois.
-/

namespace Work.SSGRoute.E1aClean

noncomputable section

variable (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsGalois k Ω]
variable (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]

/-- `Ω` is an algebraic closure of the decomposition field `k^h = Ω^{D_A}` (projection of
`decompField_datum_facts`; stated there in the conjunction because it does not mention `K`). -/
theorem decompField_isAlgClosure_via (A : ValuationSubring Ω) (hK : K = K) :
    IsAlgClosure ↥(decompField k Ω A) Ω :=
  (decompField_datum_facts k Ω K A).1

/-- The decomposition group is exactly the Galois group over the decomposition field:
`Gal(Ω/k^h) = D_A` (projection of `decompField_datum_facts`). -/
theorem decompField_fixingSubgroup_via (A : ValuationSubring Ω) (hK : K = K) :
    (decompField k Ω A).fixingSubgroup = SSGRoute.decomp k A :=
  (decompField_datum_facts k Ω K A).2.1

/-- The henselisation `K^h` is finite over the decomposition field `k^h`. -/
theorem henselOverDecomp_finiteDimensional (A : ValuationSubring Ω) :
    FiniteDimensional ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A) :=
  (decompField_datum_facts k Ω K A).2.2.1

/-- The henselisation `K^h` is Galois over the decomposition field `k^h`. -/
theorem henselOverDecomp_isGalois (A : ValuationSubring Ω) :
    IsGalois ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A) :=
  (decompField_datum_facts k Ω K A).2.2.2

/-- **The henselisation is the compositum of the decomposition field with `K`**:
`K^h = k^h ⊔ K`.  Both are fixed fields of closed subgroups (`K = Ω^{Gal(Ω/K)}`,
`k^h = Ω^{D_A}`, `K^h = Ω^{D_A ⊓ Gal(Ω/K)}`) and `fixingSubgroup` sends joins to meets
(`IntermediateField.fixingSubgroup_sup`), so the Galois correspondence gives the claim. -/
theorem henselField_eq_sup (A : ValuationSubring Ω) :
    henselField k Ω K A = decompField k Ω A ⊔ K := by
  have hker : (SSGRoute.res k K).ker = K.fixingSubgroup :=
    IntermediateField.restrictNormalHom_ker K
  rw [henselField, hker, ← InfiniteGalois.fixedField_fixingSubgroup
      (decompField k Ω A ⊔ K), IntermediateField.fixingSubgroup_sup,
    decompField_fixingSubgroup_via k Ω K A rfl]

end

end Work.SSGRoute.E1aClean
