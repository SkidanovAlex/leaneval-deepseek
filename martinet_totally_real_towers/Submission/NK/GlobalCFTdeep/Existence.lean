/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.NK.GlobalCFTdeep.CoCore.Reciprocity

/-!
# The existence theorem (Takagi)

`NK.GlobalCFT.ExistenceTheorem K` of the delivered chapter says that the norm groups
`N_{L/K}C_L` of finite abelian extensions are *exactly* the open subgroups of finite index of the
idèle class group `C_K`.  This file splits that statement into the two classical theorems from
which it is proved, and derives it.

* `TakagiExistence`: **Takagi's existence theorem in the form in which it is proved** — every open
  subgroup of finite index of `C_K` *contains* the norm group of a finite abelian extension of `K`.
  This is the form proved in Milne, *Class Field Theory*, §9 ("we prove the Existence Theorem ...
  by showing that every (open) subgroup of finite index in `C_K` contains the norm group of some
  subextension of the extension obtained by first adjoining a root of unity ... and then making a
  Kummer extension"), and it is strictly weaker than the statement with `=`.
* `NormGroupCorrespondence`: the **Galois correspondence for the norm groups** — for a finite
  abelian extension `L/K`, every subgroup of `C_K` containing `N_{L/K}C_L` is the norm group of
  another finite abelian extension.  Classically this is the compatibility of the Artin
  isomorphism with the norm of a subextension (Neukirch, *Algebraic Number Theory*, V.5.5–V.5.6);
  it is the functoriality half of the reciprocity law, and it is what turns "contains" into
  "equals".

From the two, `NK.GlobalCFT.ExistenceTheorem K` follows: given an open subgroup `N` of finite
index, Takagi's theorem supplies a finite abelian `L/K` with `N_{L/K}C_L ≤ N`, and the
correspondence applies to the pair `N_{L/K}C_L ≤ N`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain
open CategoryTheory

noncomputable section

universe u v w

namespace NK.GlobalCFTdeep

open NK.GlobalCFT

/-- **Takagi's existence theorem**, in the form in which it is proved: every open subgroup of
finite index of `C_K` contains the norm group of a finite abelian extension of `K`.

Classically (Takagi 1920; Milne, *CFT*, §9; Neukirch, *Algebraic Number Theory*, V.9.1) the proof
goes through the cyclotomic-then-Kummer extensions: given `N`, one finds a cyclotomic extension
`K'` of `K` with `N ∩ Kˣ ⊆ (K')^{p}`-conditions and constructs `L/K` by Kummer theory. -/
structure TakagiExistence (K : Type u) [Field K] [NumberField K] : Prop where
  /-- the existence of a finite abelian extension whose norm group is contained in `N`. -/
  exists_normSubgroup_le : ∀ (N : Subgroup C[K]), N.FiniteIndex → IsOpen (N : Set C[K]) →
      ∃ (L : Type v) (_ : Field L) (_ : NumberField L) (_ : Algebra K L)
        (_ : FiniteDimensional K L) (_ : IsGalois K L) (_ : IsMulCommutative (L ≃ₐ[K] L)),
        Idele.normClassSubgroup K L ≤ N

/-- **The Galois correspondence for the norm groups**: for a finite abelian extension `L/K`, every
subgroup of `C_K` containing the norm group `N_{L/K}C_L` is itself the norm group of a finite
abelian extension of `K`.

This is the functoriality of the Artin isomorphism with respect to subextensions: under the
reciprocity isomorphism `C_K ⧸ N_{L/K}C_L ≅ Gal(L/K)`, the intermediate extensions `M/K` of `L/K`
correspond to the subgroups of `Gal(L/K)`, and `N_{M/K}C_M` is the preimage of `Gal(L/M)`
(Neukirch, *Algebraic Number Theory*, V.5.5–V.5.6). -/
structure NormGroupCorrespondence (K : Type u) [Field K] [NumberField K] : Prop where
  /-- every subgroup containing a norm group is a norm group. -/
  exists_normSubgroup_eq : ∀ {L : Type v} [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
    (N : Subgroup C[K]), Idele.normClassSubgroup K L ≤ N →
      ∃ (L' : Type w) (_ : Field L') (_ : NumberField L') (_ : Algebra K L')
        (_ : FiniteDimensional K L') (_ : IsGalois K L') (_ : IsMulCommutative (L' ≃ₐ[K] L')),
        Idele.normClassSubgroup K L' = N

/-- **The existence theorem of global class field theory** (`NK.GlobalCFT.ExistenceTheorem`)
from Takagi's theorem and the Galois correspondence for the norm groups. -/
theorem existenceTheorem_of_takagi {K : Type u} [Field K] [NumberField K]
    (hT : TakagiExistence.{u, v} K) (hC : NormGroupCorrespondence.{u, v, w} K) :
    NK.GlobalCFT.ExistenceTheorem.{u, w} K where
  exists_normSubgroup := by
    intro N hfi hop
    obtain ⟨L, hF, hN, hA, hfd, hG, hcomm, hle⟩ := hT.exists_normSubgroup_le N hfi hop
    obtain ⟨L', hF', hN', hA', hfd', hG', hcomm', heq⟩ :=
      hC.exists_normSubgroup_eq (K := K) (L := L) N hle
    exact ⟨L', hF', hN', hA', hfd', hG', heq⟩

end NK.GlobalCFTdeep
