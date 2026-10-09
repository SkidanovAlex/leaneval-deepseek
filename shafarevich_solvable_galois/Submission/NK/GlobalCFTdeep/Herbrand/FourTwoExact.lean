/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.NK.GlobalCFTdeep.Herbrand.Reduction
import Submission.NK.GlobalCFTdeep.Herbrand.top_eq_principal_sup_TIdeles
import Submission.NK.GlobalCFTdeep.Herbrand.quot_TIdeles_mulEquiv_ideleClassGroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The exact sequence `0 → U(T) → 𝕀_{L,T} → C_L → 0` as `ℤ[Gal(L/K)]`-modules

Milne's Theorem 4.3 (via Lemma 4.2) uses the identification
`C_L ≅ 𝕀_{L,T} ⧸ U(T)`, where `𝕀_{L,T}` is the group of `T`-idèles and `U(T) = Lˣ ∩ 𝕀_{L,T}`
the `T`-units, and both are `Gal(L/K)`-stable.  At the level of groups this is
`quot_TIdeles_mulEquiv_ideleClassGroup`; the *equivariant* form needed by the Herbrand assembly
(`herbrandQuotient_of_milneShortExact`) is the short exact sequence of `Rep ℤ Gal(L/K)`-modules
recorded here as the structure `MilneFourTwoExact`, whose inhabitation is the technical gap
`milneFourTwoExact_nonempty` (the second isomorphism theorem for `Rep`-subobjects, plus the two
`Rep`-morphisms built from the group homomorphisms).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain
open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **The `Gal(L/K)`-equivariant form of Milne's Lemma 4.2**: the short exact sequence
`0 → U(T) → 𝕀_{L,T} → C_L → 0` of `ℤ[Gal(L/K)]`-modules, where `U(T) = TUnits T` is the group of
`T`-units, `𝕀_{L,T} = TIdeles T` the group of `T`-idèles and `T` is a `Gal(L/K)`-stable set of
places for which `𝕀_L = Lˣ·𝕀_{L,T}` (`h`). -/
structure MilneFourTwoExact (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (h : (⊤ : Subgroup (Idele L)) = Idele.principalSubgroup L ⊔ TIdeles T) where
  /-- the inclusion `U(T) → 𝕀_{L,T}`. -/
  i : tUnitsRep (K := K) (L := L) T hT ⟶ tIdelesRep (K := K) (L := L) T hT
  /-- the quotient map `𝕀_{L,T} → C_L`. -/
  p : tIdelesRep (K := K) (L := L) T hT ⟶ IdeleClassGroup.rep K L
  /-- `i ≫ p = 0`. -/
  w : i ≫ p = 0
  /-- exactness. -/
  shortExact : (ShortComplex.mk i p w).ShortExact

/-! ## Inhabitation

The inhabitation of `MilneFourTwoExact` — the equivariant second isomorphism theorem for the
`Rep`-submodules `TUnits T ⊆ TIdeles T ⊆ 𝕀_L` — is proved in
`Submission/Work/GlobalCFTdeep/Herbrand/milneFourTwoExact_nonempty.lean`
(`NK.GlobalCFTdeep.milneFourTwoExact_nonempty`), which imports this file for the structure
definition.  It is *not* restated here. -/

end NK.GlobalCFTdeep
