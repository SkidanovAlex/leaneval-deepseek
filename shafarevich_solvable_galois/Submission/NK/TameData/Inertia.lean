/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Component 1: the structure of the tame quotient

This file derives `NK.LocalTame.TameStructureInput p q κ K'` — the structure of the tame
quotient `G_κ^{tr} = G_κ/V_κ` of a `p`-adic field (NSW, *Cohomology of Number Fields*, (7.5.7)
Corollary and (7.5.11); Iwasawa, *On Galois groups of local fields*) — from the reduced input
`NK.TameData.TameInertiaInput p κ K'` and the arithmetic of `q`.

Two of the eight fields of `TameStructureInput` are *proved* rather than assumed:

* `wildInertia_le_inertia` is the first component of `IsMaxNormalProCyclicInQuotient`
  (`TameInertiaInput.isTameInertia`);
* `exists_frobeniusLift` follows from the unramified quotient `G_κ/I_κ ≅ Ẑ` and the
  non-triviality of `Ẑ`
  (`NK.LocalStructure.Tame.exists_notMem_inertiaSubgroup_of_unramifiedQuotient`): `Ẑ` surjects
  onto `ℤ/2`, so it is not the trivial group, and the inertia subgroup is therefore proper.

Also recorded here: the *normality* of the image of the inertia subgroup in the tame quotient,
which is what makes `TameInertiaInput.isTameInertia` a condition on the *abelian* pair
`(V_κ/V_κ, I_κ/V_κ)` rather than on the pair of subgroups alone.
-/
import Submission.NK.TameData.Definitions
import Submission.NK.LocalStructure.Tame.exists_notMem_inertiaSubgroup_of_unramifiedQuotient
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
