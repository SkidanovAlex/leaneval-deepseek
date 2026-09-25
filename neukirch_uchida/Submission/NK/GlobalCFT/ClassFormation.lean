/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.NK.GlobalCFT.NormGroup
import Submission.NK.GlobalCFT.Reciprocity
import Submission.NK.GlobalCFT.Norm.globalCFT_normIdeleHom_trans
import Submission.NK.ClassFormation.Basic
import Submission.NK.ClassFormation.H2
import Mathlib.FieldTheory.Galois.Abelian

/-!
# The axioms of a class formation for the idèle class groups

This file records, for the family `K ↦ C_K` of idèle class groups with the family of norm
subgroups `N_{L/K} C_L`, the two axioms of a class formation (Artin–Tate), as structures.  The
structures are *definitions*: they bundle the axioms as data so that the consequences of the
class formation machinery can be stated conditionally on them and proved.

* `NK.GlobalCFT.ExtensionAxiom`: the extension property, i.e. transitivity of the norm in a
  tower `M / L / K`.
* `NK.GlobalCFT.FieldAxiom`: the field axiom, in index form: `[C_K : N_{L/K} C_L] = [L : K]`
  (equivalently, the cohomological form `Ĥ¹(Gal(L/K), C_L) = 0` together with
  `|Ĥ⁰(Gal(L/K), C_L)| = [L : K]`; the equivalence requires the Galois action on `C_L`).

The abstract cohomological machinery for class formations (Tate's theorem, the `H⁰` computation
`Ĥ⁰(H, C) = C^H ⧸ N_H C`) lives in `Submission/Work/ClassFormation/Basic.lean` and
`Submission/Work/ClassFormation/H2.lean` (namespace `Commons.ClassFormation`) and is reused here.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT

/-- The **extension property** of the norm subgroups, for a tower of number fields `M / L / K`:
for every idèle `x` of `M` there is an idèle `y` of `L` with `y w = N_{M/L}(x)_w` for all places
`w` of `L` (i.e. the componentwise norm formula for `M/L` is an idèle), and the norm `M/K` factors
as the norm `M/L` followed by the norm `L/K`. -/
structure ExtensionAxiom (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Field M] [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] [FiniteDimensional K L] [FiniteDimensional L M]
    [FiniteDimensional K M] : Prop where
  norm_isIdele : ∀ (x : Idele M), ∃ y : Idele L, ∀ w : Place L, y w = Idele.normIdeleFun L M x w
  norm_trans : ∀ (x : Idele M) (y : Idele L), (∀ w : Place L, y w = Idele.normIdeleFun L M x w) →
    ∀ v : Place K, Idele.normIdeleFun K M x v = Idele.normIdeleFun K L y v

variable {K L M : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]

/-- **The extension property holds** for the idèle class groups: it is the transitivity
`N_{M/K} = N_{L/K} ∘ N_{M/L}` of the idèlic norm
(`NK.GlobalCFT.Norm.globalCFT_normIdeleHom_trans`), together with the fact that the
componentwise formula is an idèle (`globalCFT_eventually_normIdeleFun_mem`). -/
theorem extensionAxiom_holds : ExtensionAxiom K L M where
  norm_isIdele x := ⟨Idele.normIdeleHom L M x, fun w => rfl⟩
  norm_trans x y hy v := by
    have hy' : y = Idele.normIdeleHom L M x := Idele.ext fun w => (hy w).symm ▸ rfl
    rw [hy', ← Idele.normIdeleHom_apply (K := K) (L := L) (x := Idele.normIdeleHom L M x) (v := v),
      ← Idele.normIdeleHom_apply (K := K) (L := M) (x := x) (v := v)]
    exact congrFun (congrArg DFunLike.coe
      (NK.GlobalCFT.Norm.globalCFT_normIdeleHom_trans (K := K) (L := L) (M := M))) x ▸ rfl

/-- The **field axiom** of a class formation for the idèle class groups, in index form: the norm
subgroup `N_{L/K} C_L` has finite index `[L : K]` in `C_K`.

This is the *abelian* statement of class field theory: for a finite Galois `L/K` the reciprocity
isomorphism computes the index as `|Gal(L/K)ᵃᵇ|` (`NK.GlobalCFT.index_eq_card_abelianization`),
which equals `[L : K]` exactly when `L/K` is abelian.  The two *inequalities* of class field
theory are precisely the two halves of the index statement below, and the non-circular proof of
the first of them is `NK.GlobalCFT.first_inequality_of_herbrandQuotient`. -/
structure FieldAxiom (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] : Prop where
  finiteIndex : (Idele.normClassSubgroup K L).FiniteIndex
  index_eq : (Idele.normClassSubgroup K L).index = Module.finrank K L

/-- The first and second inequalities of global class field theory, i.e. the two halves of the
field axiom:

* (first inequality) `[C_K : N_{L/K} C_L] ≥ [L : K]`;
* (second inequality) `[C_K : N_{L/K} C_L] ≤ [L : K]`

for a finite Galois extension `L / K`. -/
structure TwoInequalities (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] : Prop where
  first : Module.finrank K L ≤ (Idele.normClassSubgroup K L).index
  second : (Idele.normClassSubgroup K L).index ≤ Module.finrank K L

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

/-- The field axiom implies both inequalities. -/
theorem twoInequalities_of_fieldAxiom (h : FieldAxiom K L) : TwoInequalities K L where
  first := le_of_eq h.index_eq.symm
  second := le_of_eq h.index_eq

/-- **Artin's reciprocity isomorphism computes the norm index**: the index of the norm subgroup
`N_{L/K} C_L` in `C_K` is the degree `[L : K]`. -/
theorem index_normClassSubgroup_eq_finrank (h : ArtinReciprocity K L) :
    (Idele.normClassSubgroup K L).index = Module.finrank K L := by
  rw [Subgroup.index_eq_card, Nat.card_congr h.iso.toEquiv, IsGalois.card_aut_eq_finrank]

/-- The field axiom follows from Artin's reciprocity isomorphism. -/
theorem fieldAxiom_of_artinReciprocity (h : ArtinReciprocity K L) : FieldAxiom K L where
  finiteIndex := by
    haveI : Finite (C[K] ⧸ Idele.normClassSubgroup K L) :=
      Finite.of_injective h.iso.toEquiv.toFun h.iso.toEquiv.injective
    haveI : Nonempty (C[K] ⧸ Idele.normClassSubgroup K L) := ⟨h.iso.symm 1⟩
    rw [Subgroup.finiteIndex_iff, Subgroup.index_eq_card]
    exact (Nat.card_pos).ne'
  index_eq := index_normClassSubgroup_eq_finrank h

/-- **The first inequality** of global class field theory, obtained from Artin's reciprocity
isomorphism: `[C_K : N_{L/K} C_L] ≥ [L : K]`.  (This route *uses* reciprocity, so the inequality
is immediate; the non-circular route via the Herbrand quotient of `C_L` is
`NK.GlobalCFT.first_inequality_of_herbrandQuotient`.) -/
theorem first_inequality_of_artinReciprocity (h : ArtinReciprocity K L) :
    Module.finrank K L ≤ (Idele.normClassSubgroup K L).index :=
  le_of_eq (index_normClassSubgroup_eq_finrank h).symm

/-- **The second inequality** of global class field theory, proved from Artin's reciprocity
isomorphism: `[C_K : N_{L/K} C_L] ≤ [L : K]`. -/
theorem second_inequality_of_artinReciprocity (h : ArtinReciprocity K L) :
    (Idele.normClassSubgroup K L).index ≤ Module.finrank K L :=
  le_of_eq (index_normClassSubgroup_eq_finrank h)

/-- The field axiom is equivalent (given the finiteness of the index) to the two inequalities.

Note that the two inequalities in the form stated here (with `[L : K]` on the right) are the
*abelian* statement; see the discussion in `Submission/Work/GlobalCFT/Cohomology.lean`. -/
theorem fieldAxiom_of_twoInequalities (h : TwoInequalities K L)
    (hfin : (Idele.normClassSubgroup K L).FiniteIndex) : FieldAxiom K L where
  finiteIndex := hfin
  index_eq := le_antisymm h.second h.first

end NK.GlobalCFT
