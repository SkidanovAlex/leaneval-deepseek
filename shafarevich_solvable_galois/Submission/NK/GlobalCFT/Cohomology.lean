/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.NK.GlobalCFT.GaloisClassGroup
import Submission.NK.GlobalCFT.ClassFormation
import Mathlib.RepresentationTheory.Rep.Basic
import Submission.Commons.RepresentationTheory.TateCohomology.natCard_tateCohomology_eq_of_fundamental_class
import Submission.Commons.RepresentationTheory.TateCohomology.tateCohomology_neg_two_iso_abelianization
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The cohomological form of the class-formation axioms

`Gal(L/K)` acts on the idèle class group `C_L` by group automorphisms (`GaloisClassGroup`), so
`C_L` is a `ℤ[Gal(L/K)]`-module and the abstract class-formation machinery of
`Commons.ClassFormation` and `Commons.RepresentationTheory.TateCohomology` applies to it.

This file provides

* `NK.GlobalCFT.IdeleClassGroup.rep`: `C_L` as a `Rep ℤ Gal(L/K)`;
* `NK.GlobalCFT.CohomologicalFieldAxiom`: the hypothesis that `C_•` satisfies the *field axiom*
  of a class formation in its cohomological form, namely
  `H¹(H, C_L) = 0` for every subgroup `H ≤ Gal(L/K)` and
  `H²(H, C_L)` cyclic of order `|H|`, with a *fundamental class* `u ∈ H²(Gal(L/K), C_L)` of order
  `[L : K]`;
* the consequence of the *fundamental class* and Tate's theorem
  (`NK.GlobalCFT.natCard_tateCohomology_zero_eq_abelianization`):
  `|Ĥ⁰(Gal(L/K), C_L)| = |Gal(L/K)ᵃᵇ|`, and its abelian special case
  `|Ĥ⁰(Gal(L/K), C_L)| = [L : K]`
  (`NK.GlobalCFT.natCard_tateCohomology_zero_eq_finrank`);
* `NK.GlobalCFT.H0Computation`: the `H⁰`-computation
  `C_K ⧸ N_{L/K} C_L ≅ Ĥ⁰(Gal(L/K), C_L)` (Milne, *CFT*, Lemma 4.1), and the two
  inequalities of class field theory derived from it
  (`NK.GlobalCFT.first_inequality_of_herbrandQuotient`,
  `NK.GlobalCFT.second_inequality_of_herbrandQuotient_of_subsingleton`).

## A warning about the two inequalities

For a finite Galois extension `L/K` with group `G`, class field theory gives
`C_K ⧸ N_{L/K} C_L ≅ Gᵃᵇ`, so the norm index is `|Gᵃᵇ|` — which is strictly smaller than
`[L : K]` as soon as `G` is nonabelian.  The two inequalities are therefore statements about
*abelian* (classically: cyclic) extensions: for abelian `L/K` one has `|Gᵃᵇ| = [L : K]` and the
two inequalities are the two halves of `[C_K : N_{L/K} C_L] = [L : K]`.

## Universes

Mathlib's `tateCohomology` ties the universe of the coefficient ring to that of the group, so
everything in this file that mentions `tateCohomology` is stated for number fields in `Type 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain
open CategoryTheory

noncomputable section

namespace NK.GlobalCFT

namespace IdeleClassGroup

/-- The idèle class group `C_L` as a `ℤ[Gal(L/K)]`-module, i.e. as a representation of the Galois
group (in additive notation).  This is the Galois module of the class-formation axioms. -/
def rep (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    Rep ℤ (L ≃ₐ[K] L) :=
  Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (IdeleClassGroup L)

end IdeleClassGroup

/-- **The cohomological field axiom** for the idèle class group formation: for a finite Galois
extension `L / K`,

* `H¹(H, C_L) = 0` for every subgroup `H ≤ Gal(L/K)`, and
* `H²(H, C_L)` has order `|H|` for every subgroup `H`,

and there is a **fundamental class** `u ∈ H²(Gal(L/K), C_L)` of order `[L : K]` (this is the input
to Tate's theorem; it is the deep arithmetic content of global class field theory, and it is *not*
reciprocity). -/
structure CohomologicalFieldAxiom (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] : Prop where
  /-- `H¹(H, C_L) = 0` for every subgroup `H ≤ Gal(L/K)`. -/
  h1_trivial : ∀ H : Subgroup (L ≃ₐ[K] L),
    Subsingleton (groupCohomology (Rep.res H.subtype (IdeleClassGroup.rep K L)) 1)
  /-- `|H²(H, C_L)| = |H|` for every subgroup `H ≤ Gal(L/K)`. -/
  h2_card : ∀ H : Subgroup (L ≃ₐ[K] L),
    Nat.card (groupCohomology (Rep.res H.subtype (IdeleClassGroup.rep K L)) 2) = Nat.card H
  /-- the fundamental class, of order `[L : K]`. -/
  fundamentalClass : ∃ α : groupCohomology (IdeleClassGroup.rep K L) 2,
    addOrderOf α = Nat.card (L ≃ₐ[K] L)

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **Tate's theorem for the idèle class group formation**: a fundamental class of order `|G|`
computes `Ĥ⁰(G, C_L)` as the abelianisation of `G = Gal(L/K)`, i.e.
`Ĥ⁰(G, C_L) ≅ Ĥ⁻²(G, ℤ) ≅ Gᵃᵇ`.

(For solvable `G` this is the commons' Tate theorem
`Commons.RepresentationTheory.TateCohomology.natCard_tateCohomology_eq_of_fundamental_class`
combined with `tateCohomology_neg_two_iso_abelianization`; for general `G` the theorem is the same
statement, which the commons proves only in the solvable case.) -/
theorem natCard_tateCohomology_zero_eq_abelianization (h : CohomologicalFieldAxiom K L)
    [Group.IsSolvable (L ≃ₐ[K] L)] :
    Nat.card (tateCohomology (IdeleClassGroup.rep K L) 0) =
      Nat.card (Abelianization (L ≃ₐ[K] L)) := by
  obtain ⟨α, hα⟩ := h.fundamentalClass
  have hmain :=
    Commons.RepresentationTheory.TateCohomology.natCard_tateCohomology_eq_of_fundamental_class
      (IdeleClassGroup.rep K L) h.h1_trivial h.h2_card α hα
  obtain ⟨e⟩ :=
    Commons.RepresentationTheory.TateCohomology.tateCohomology_neg_two_iso_abelianization
      (L ≃ₐ[K] L)
  rw [← hmain]
  exact Nat.card_congr e.toEquiv

/-- For an **abelian** extension `L/K` the abelianisation of the Galois group is the whole group,
so Tate's theorem computes `|Ĥ⁰(Gal(L/K), C_L)| = [L : K]`. -/
theorem natCard_tateCohomology_zero_eq_finrank (h : CohomologicalFieldAxiom K L)
    [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] :
    Nat.card (tateCohomology (IdeleClassGroup.rep K L) 0) = Module.finrank K L := by
  rw [natCard_tateCohomology_zero_eq_abelianization h, ← IsGalois.card_aut_eq_finrank]
  exact Nat.card_congr (Abelianization.equivOfComm (H := (L ≃ₐ[K] L))).symm.toEquiv

/-- **The `H⁰`-computation** (Milne, *Class Field Theory*, Lemma 4.1): for a finite Galois
extension `L/K` the zeroth Tate cohomology of `C_L` is the quotient of `C_L` by the norms,
i.e. there is an isomorphism `C_K ⧸ N_{L/K} C_L ≅ Ĥ⁰(Gal(L/K), C_L)`.  Equivalently: the natural
map `C_K → C_L` identifies `C_K` with the Galois invariants `(C_L)^{Gal(L/K)}` and carries the
norm subgroup `N_{L/K} C_L` onto the image of the norm map.

This computation is the input to the two inequalities; it is stated here as a structure so that
everything derived from it is a proved conditional theorem. -/
structure H0Computation (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] : Prop where
  /-- `C_K ⧸ N_{L/K} C_L` is the quotient of the invariants of `C_L` by the norm. -/
  quotientEquiv : Nonempty (C[K] ⧸ Idele.normClassSubgroup K L ≃*
    Multiplicative (↥((IdeleClassGroup.rep K L).ρ.invariants) ⧸
      Submodule.comap ((IdeleClassGroup.rep K L).ρ.invariants).subtype
        (LinearMap.range (IdeleClassGroup.rep K L).ρ.norm)))

/-- The `H⁰`-computation identifies the index of the norm subgroup with the order of `Ĥ⁰`. -/
theorem H0Computation.index_eq_natCard (h : H0Computation K L) :
    (Idele.normClassSubgroup K L).index =
      Nat.card (tateCohomology (IdeleClassGroup.rep K L) 0) := by
  obtain ⟨e⟩ := h.quotientEquiv
  obtain ⟨e2⟩ :=
    Commons.RepresentationTheory.TateCohomology.tateCohomology_zero_iso
      (IdeleClassGroup.rep K L).ρ
  rw [Subgroup.index_eq_card]
  exact (Nat.card_congr e.toEquiv).trans (Nat.card_congr e2.toEquiv.symm)

/-- **The Herbrand quotient of the idèle class group.**  For `L/K` finite Galois the Herbrand
quotient of `C_L` is `h(G, C_L) = |Ĥ⁰| / |Ĥ¹| = [L : K]`, i.e.
`|Ĥ⁰(G, C_L)| = [L : K] · |Ĥ¹(G, C_L)|` with `Ĥ¹(G, C_L)` finite.

This is Milne, *Class Field Theory*, Theorem 4.3 (classically stated for *cyclic* `L/K`); its proof
uses the ideal class group of `L`, the `S`-units (`IL,T`), Dirichlet's unit theorem and the local
computations — *not* reciprocity.  For nonabelian `Gal(L/K)` the structure is unsatisfiable, which
is consistent with the fact that the inequalities are statements about abelian extensions. -/
structure HerbrandQuotient (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] : Prop where
  /-- `Ĥ¹(Gal(L/K), C_L)` is finite (it is the denominator of the Herbrand quotient). -/
  finite_h1 : 0 < Nat.card (tateCohomology (IdeleClassGroup.rep K L) 1)
  /-- `h(Gal(L/K), C_L) = [L : K]`. -/
  herbrand : Nat.card (tateCohomology (IdeleClassGroup.rep K L) 0) =
    Module.finrank K L * Nat.card (tateCohomology (IdeleClassGroup.rep K L) 1)

variable [FiniteDimensional K L]

/-- **The first inequality** of global class field theory, in the form
`[C_K : N_{L/K} C_L] ≥ [L : K]`.

The proof is *not* circular: from the `H⁰`-computation the index is the order of `Ĥ⁰`, and from
the Herbrand quotient computation `h(G, C_L) = [L : K]` this order is at least
`[L : K] · |Ĥ¹| ≥ [L : K]`. -/
theorem first_inequality_of_herbrandQuotient (h0 : H0Computation K L)
    (hh : HerbrandQuotient K L) :
    Module.finrank K L ≤ (Idele.normClassSubgroup K L).index := by
  rw [H0Computation.index_eq_natCard h0, hh.herbrand]
  exact Nat.le_mul_of_pos_right _ hh.finite_h1

/-- **The second inequality** of global class field theory, `[C_K : N_{L/K} C_L] ≤ [L : K]`: with
the `H⁰`-computation and the Herbrand quotient computation `h(G, C_L) = [L : K]`, the field axiom
`H¹(Gal(L/K), C_L) = 0` computes the index exactly as `[L : K]`. -/
theorem second_inequality_of_herbrandQuotient_of_subsingleton
    (h0 : H0Computation K L) (hh : HerbrandQuotient K L)
    (h1 : Subsingleton (tateCohomology (IdeleClassGroup.rep K L) 1)) :
    (Idele.normClassSubgroup K L).index ≤ Module.finrank K L := by
  have hcard : Nat.card (tateCohomology (IdeleClassGroup.rep K L) 1) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨h1, ⟨0⟩⟩
  rw [H0Computation.index_eq_natCard h0, hh.herbrand, hcard, mul_one]

/-- **The field axiom in its general form**: for any finite Galois `L/K` with solvable group, the
cohomological field axiom and the `H⁰`-computation give
`[C_K : N_{L/K} C_L] = |Gal(L/K)ᵃᵇ|` — the reciprocity isomorphism's index statement.  It
specialises to `[C_K : N_{L/K} C_L] = [L : K]` exactly when `Gal(L/K)` is abelian
(`fieldAxiom_of_cohomologicalFieldAxiom`). -/
theorem index_eq_card_abelianization (h : CohomologicalFieldAxiom K L)
    [Group.IsSolvable (L ≃ₐ[K] L)] (h0 : H0Computation K L) :
    (Idele.normClassSubgroup K L).index = Nat.card (Abelianization (L ≃ₐ[K] L)) := by
  rw [H0Computation.index_eq_natCard h0, natCard_tateCohomology_zero_eq_abelianization h]

variable [IsGalois K L]

/-- **The field axiom from the cohomological field axiom**: for an abelian extension `L/K` the
cohomological field axiom (a fundamental class plus the vanishing of `H¹` and the order of `H²`)
and the `H⁰`-computation give `[C_K : N_{L/K} C_L] = [L : K]` — hence both inequalities. -/
theorem fieldAxiom_of_cohomologicalFieldAxiom (h : CohomologicalFieldAxiom K L)
    (h0 : H0Computation K L) [IsMulCommutative (L ≃ₐ[K] L)] : FieldAxiom K L where
  finiteIndex := by
    rw [Subgroup.finiteIndex_iff, H0Computation.index_eq_natCard h0,
      natCard_tateCohomology_zero_eq_finrank h]
    exact (Module.finrank_pos).ne'
  index_eq := by
    rw [H0Computation.index_eq_natCard h0, natCard_tateCohomology_zero_eq_finrank h]

/-- **The two inequalities from the Herbrand quotient computation**: the `H⁰`-computation, the
Herbrand quotient `h(G, C_L) = [L : K]` and the vanishing of `Ĥ¹(Gal(L/K), C_L)` together give
the field axiom `[C_K : N_{L/K} C_L] = [L : K]` (no reciprocity is used). -/
theorem fieldAxiom_of_herbrandQuotient (h0 : H0Computation K L) (hh : HerbrandQuotient K L)
    (h1 : Subsingleton (tateCohomology (IdeleClassGroup.rep K L) 1))
    [IsMulCommutative (L ≃ₐ[K] L)] : FieldAxiom K L where
  finiteIndex := by
    rw [Subgroup.finiteIndex_iff, H0Computation.index_eq_natCard h0, hh.herbrand,
      Nat.card_eq_one_iff_unique.mpr ⟨h1, ⟨0⟩⟩, mul_one]
    exact (Module.finrank_pos).ne'
  index_eq := by
    rw [H0Computation.index_eq_natCard h0, hh.herbrand,
      Nat.card_eq_one_iff_unique.mpr ⟨h1, ⟨0⟩⟩, mul_one]

/-- **The two inequalities from the cohomological field axiom** (abelian case). -/
theorem twoInequalities_of_cohomologicalFieldAxiom (h : CohomologicalFieldAxiom K L)
    (h0 : H0Computation K L) [IsMulCommutative (L ≃ₐ[K] L)] : TwoInequalities K L :=
  twoInequalities_of_fieldAxiom (fieldAxiom_of_cohomologicalFieldAxiom h h0)

end NK.GlobalCFT
