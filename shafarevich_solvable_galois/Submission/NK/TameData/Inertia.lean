import Mathlib.FieldTheory.IsSepClosed
import Submission.NK.LocalStructure.Tame.exists_notMem_inertiaSubgroup_of_unramifiedQuotient
import Submission.NK.TameData.Definitions
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open NK.LocalTame

namespace NK.TameData

universe u

variable {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K'] [IsSepClosure κ K']
variable {G : Type*} [Group G]

/-! ## The image of a normal subgroup in a quotient -/

/-- **The image of a normal subgroup in a quotient is normal.**  This is the field
`(quotientImage V I).Normal` of `IsMaxNormalProCyclicInQuotient`, which is therefore automatic
whenever `I` is normal in `G` — in particular for the inertia subgroup, which is normal in
`Gal(K'/κ)` (`NK.LocalAnabelian.inertiaSubgroup_normal`). -/
theorem quotientImage_normal {V I : Subgroup G} [V.Normal] (hI : I.Normal) :
    (quotientImage V I).Normal :=
  hI.map (QuotientGroup.mk' V) (QuotientGroup.mk'_surjective V)

/-- **`IsMaxNormalProCyclicInQuotient` from its pieces.**  Only the containment `V ≤ I`, the
pro-cyclicity of `I/V` and the maximality condition need to be checked; the normality of `I/V` in
`G/V` is `quotientImage_normal`. -/
theorem isMaxNormalProCyclicInQuotient_of_normal {V I : Subgroup G} [V.Normal] (hI : I.Normal)
    (hVI : V ≤ I) (hcyc : IsProCyclic ↥(quotientImage V I))
    (hmax : ∀ J : Subgroup G, V ≤ J → (quotientImage V J).Normal →
      IsProCyclic ↥(quotientImage V J) → J ≤ I) :
    IsMaxNormalProCyclicInQuotient V I :=
  ⟨hVI, quotientImage_normal hI, hcyc, hmax⟩

/-! ## The tame structure theorem from the reduced input -/

/-- **Component 1: `TameInertiaInput` implies `TameStructureInput`** (NSW (7.5.7) Corollary,
(7.5.11); Iwasawa).  The two fields of `TameStructureInput` that the reduced input does not carry
are supplied as described in the file header. -/
theorem TameInertiaInput.toStructureInput {p q : ℕ} (h : TameInertiaInput p κ K')
    (hq : ∃ f : ℕ, 0 < f ∧ q = p ^ f) :
    TameStructureInput p q κ K' where
  hp := h.hp
  q_eq := hq
  wildInertia_le_inertia := h.isTameInertia.1
  isTameInertia := h.isTameInertia
  isProPrimeToP_tameInertia := h.isProPrimeToP_tameInertia
  tameInertia_commutator_mem := h.tameInertia_commutator_mem
  unramifiedQuotient := h.unramifiedQuotient
  exists_frobeniusLift :=
    NK.LocalStructure.Tame.exists_notMem_inertiaSubgroup_of_unramifiedQuotient h.unramifiedQuotient

end NK.TameData
