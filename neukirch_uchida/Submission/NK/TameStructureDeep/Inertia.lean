/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The tame inertia, from the residual of `NK.TameStructureDeep`

This file proves, from the single residual `NK.TameStructureDeep.TameRamificationCore`, the
whole of `NK.TameData.TameInertiaInput p κ K'` (NSW, *Cohomology of Number Fields*, (7.5.7)
Corollary and (7.5.11); Iwasawa, *On Galois groups of local fields*) except the group-theoretic
superstructure, together with the two auxiliary facts that the sibling chapters carried as
*inputs*:

* `NK.TameStructureDeep.inertiaSubgroup_isClosed` — `I_κ` is closed in the Krull topology (it is
  a fixing subgroup, and a separable closure is integral over `κ`);
* `NK.TameStructureDeep.isProPrimeToP_tameInertia` — `I_κ/V_κ` is pro-prime-to-`p`.  This is
  *derived* from the maximality of the wild inertia: a pro-cyclic profinite group which is not
  pro-prime-to-`p` has a nontrivial characteristic pro-`p` subgroup, whose preimage in `G_κ` would
  be a normal pro-`p` subgroup strictly containing `V_κ`.
* `NK.TameStructureDeep.tameInertia_commutator_mem` — `[I_κ, I_κ] ≤ V_κ`, derived from the
  maximality of `I_κ/V_κ` alone, using that a pro-cyclic profinite group is abelian.
* `NK.TameStructureDeep.tameInertiaInput_of_core` — the reduced input catalogue
  `NK.TameData.TameInertiaInput`.
-/
import Submission.NK.TameStructureDeep.Defs
import Submission.NK.TameStructure.ProfiniteAux.isProPrimeToP_of_maxNormalProP
import Submission.NK.TameStructure.ProfiniteAux.commutator_mem_of_isMaxNormalProCyclicInQuotient
import Submission.NK.TameStructure.ProfiniteAux.fixingSubgroup_isClosed_of_isIntegral
import Submission.NK.TameStructureDeep.Support.wildInertiaSubgroup_isClosed

open scoped Classical

namespace NK.TameStructureDeep

universe u

noncomputable section

variable {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K']

/-- **The wild inertia is closed** (Serre, *Local Fields* IV §2; Hilbert).  This is *not* a field
of the residual: it is derived in
`NK.TameStructureDeep.Support.wildInertiaSubgroup_isClosed` from the fact that the join
`V_κ = ⨆ {N ⊴ G_κ : IsProP p ↥N}` of the normal pro-`p` subgroups is itself pro-`p`
(`NK.LocalTame.wildInertiaSubgroup_isProP`) together with the general bridge
`NK.TameStructureDeep.Support.isProP_of_openNormal_index` ("open normal subgroups of `p`-power
index ⟹ pro-`p`") — which is what replaces the *false* rule "finite index ⟹ open" in a profinite
group. -/
theorem TameRamificationCore.wildInertia_closed {p q : ℕ} [IsSepClosure κ K']
    (h : TameRamificationCore p q κ K') :
    IsClosed (NK.LocalTame.wildInertiaSubgroup (κ := κ) (K' := K') p : Set (Gal(K'/κ))) :=
  NK.TameStructureDeep.Support.wildInertiaSubgroup_isClosed p h.hp

/-- **The inertia subgroup is closed.**  `I_κ = Gal(K'/κ(μ_{p'}))` is the fixing subgroup of the
intermediate field `κ(μ_{p'}) = unramifiedClosure p`
(`NK.LocalAnabelian.ResidueField.inertiaSubgroup_eq_fixingSubgroup_unramifiedClosure`), and the
fixing subgroup of an intermediate field of an integral extension is closed for the Krull topology
(`NK.TameStructure.ProfiniteAux.fixingSubgroup_isClosed_of_isIntegral`). -/
theorem inertiaSubgroup_isClosed (p : ℕ) [IsSepClosure κ K'] :
    IsClosed (NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p :
      Set (Gal(K'/κ))) := by
  rw [NK.LocalAnabelian.ResidueField.inertiaSubgroup_eq_fixingSubgroup_unramifiedClosure p]
  exact NK.TameStructure.ProfiniteAux.fixingSubgroup_isClosed_of_isIntegral _

/-- **`I_κ/V_κ` is pro-prime-to-`p`** (NSW (7.5.11)), derived from the maximality of the wild
inertia.  The hypotheses are exactly the fields of the residual: `V_κ` is closed, pro-`p`
(`NK.LocalTame.wildInertiaSubgroup_isProP`) and maximal among normal pro-`p` subgroups
(`NK.LocalTame.le_wildInertiaSubgroup`, which holds by the *definition* of `V_κ` as the join of
the normal pro-`p` subgroups), and `I_κ/V_κ` is pro-cyclic by `isTameInertia`. -/
theorem isProPrimeToP_tameInertia {p q : ℕ} [IsSepClosure κ K']
    (h : TameRamificationCore p q κ K') :
    NK.LocalTame.IsProPrimeToP p
      ↥(NK.LocalTame.tameInertiaSubgroup (κ := κ) (K' := K') p) := by
  rw [NK.LocalTame.tameInertiaSubgroup_eq_quotientImage]
  exact NK.TameStructure.ProfiniteAux.isProPrimeToP_of_maxNormalProP h.hp h.wildInertia_closed
    (NK.LocalAnabelian.inertiaSubgroup_normal p) (inertiaSubgroup_isClosed p)
    (NK.LocalTame.wildInertiaSubgroup_isProP p)
    (fun N hN hNp => NK.LocalTame.le_wildInertiaSubgroup hN hNp)
    h.isTameInertia.2.1 h.isTameInertia.2.2.1

/-- **The commutator of two inertia elements lies in the wild inertia**, derived from the
maximality of `I_κ/V_κ`: `I_κ/V_κ` is a pro-cyclic *profinite* group (it is a quotient of the
compact group `I_κ`, `V_κ` being closed), and a profinite group all of whose finite quotients are
cyclic is abelian. -/
theorem tameInertia_commutator_mem {p q : ℕ} [IsSepClosure κ K']
    (h : TameRamificationCore p q κ K') :
    ∀ y ∈ NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p,
      ∀ z ∈ NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p,
        y * z * y⁻¹ * z⁻¹ ∈ NK.LocalTame.wildInertiaSubgroup (κ := κ) (K' := K') p :=
  NK.TameStructure.ProfiniteAux.commutator_mem_of_isMaxNormalProCyclicInQuotient
    h.wildInertia_closed (NK.LocalAnabelian.inertiaSubgroup_normal p)
    (inertiaSubgroup_isClosed p) h.isTameInertia

/-- **The reduced input catalogue `NK.TameData.TameInertiaInput`** (NSW (7.5.7) Corollary and
(7.5.11); Iwasawa) from the residual `TameRamificationCore`.

Two of its four fields are *derived*: `isProPrimeToP_tameInertia` and
`tameInertia_commutator_mem`; the other two are fields of the residual. -/
theorem tameInertiaInput_of_core {p q : ℕ} [IsSepClosure κ K'] [IsSepClosure κ K']
    (h : TameRamificationCore p q κ K') :
    NK.TameData.TameInertiaInput p κ K' where
  hp := h.hp
  isTameInertia := h.isTameInertia
  isProPrimeToP_tameInertia := isProPrimeToP_tameInertia h
  tameInertia_commutator_mem := tameInertia_commutator_mem h
  unramifiedQuotient := h.unramifiedQuotient

/-! ## The boundary form at a `𝔭`-adic completion -/

/-- **The reduced input catalogue `NK.TameData.TameInertiaInput` at a genuine local field**
`κ = K_𝔭`, from the residual `TameRamificationCore` at `κ`
(NSW (7.5.7) Corollary, (7.5.11); Iwasawa).  This is the boundary theorem consumed by the
Neukirch–Uchida endgame. -/
theorem tameInertiaInput_adicCompletion {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type u}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    {p q : ℕ} (hchar : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    (h : TameRamificationCore p q (𝔭.adicCompletion K) K') :
    NK.TameData.TameInertiaInput p (𝔭.adicCompletion K) K' :=
  tameInertiaInput_of_core h

end

end NK.TameStructureDeep
