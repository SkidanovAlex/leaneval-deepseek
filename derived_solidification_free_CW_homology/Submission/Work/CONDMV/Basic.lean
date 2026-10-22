/-
# AREA CONDMV — Mayer–Vietoris for `ℤ[−]` on open covers: basic definitions

This file sets up the vocabulary for the Mayer–Vietoris statement for free light condensed
abelian groups on an open cover `X = U ∪ V` of a topological space.

Mathematical content (see `REFS/01` F11): for a light profinite set `S`, every continuous map
`f : S → X` refines, along a clopen partition `S = A ⊔ B`, to a pair of maps `A → U`, `B → V`.
Consequently the light condensed set `X_cond` is the pushout of `U_cond ← (U ∩ V)_cond → V_cond`,
and `ℤ[−]` (a left adjoint) turns this into a pushout in `LightCondAb` with injective legs.

Main definitions:

* `Work.CONDMV.clopenLP` — a clopen subset of a light profinite set, as a light profinite set.
* `Work.CONDMV.clopenIncl` — its inclusion, as a morphism of light profinite sets.
* `Work.CONDMV.restrict` — restriction of sections of a light condensed set along a clopen
  inclusion.
* `Work.CONDMV.condOf` / `Work.CONDMV.setCond` — the light condensed set associated to a
  topological space (resp. to a subspace).
* `Work.CONDMV.iWU`, `iWV`, `iU`, `iV` — the four maps of the Mayer–Vietoris square.
-/
import Mathlib
import Submission.Blueprint.Interfaces

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open Opposite

noncomputable section

namespace Work.CONDMV

/-! ## Clopen subsets as light profinite sets -/

/-- A clopen subset of a light profinite set, viewed as a light profinite set. -/
def clopenLP (S : LightProfinite.{0}) (A : Set S) (hA : IsClopen A) : LightProfinite.{0} :=
  haveI : CompactSpace A := isCompact_iff_compactSpace.mp hA.1.isCompact
  ↧A

/-- The inclusion of a clopen subset, as a morphism of light profinite sets. -/
def clopenIncl (S : LightProfinite.{0}) (A : Set S) (hA : IsClopen A) :
    clopenLP S A hA ⟶ S := by
  haveI : CompactSpace A := isCompact_iff_compactSpace.mp hA.1.isCompact
  exact CompHausLike.ofHom _ ⟨Subtype.val, continuous_subtype_val⟩

@[simp]
lemma clopenIncl_apply (S : LightProfinite.{0}) (A : Set S) (hA : IsClopen A)
    (a : clopenLP S A hA) : (clopenIncl S A hA a : S) = Subtype.val (α := S) a := rfl

/-- Restriction of sections of a light condensed set along a clopen inclusion. -/
def restrict (Z : LightCondSet.{0}) (S : LightProfinite.{0}) (A : Set S) (hA : IsClopen A) :
    Z.obj.obj (op S) → Z.obj.obj (op (clopenLP S A hA)) :=
  Z.obj.map (clopenIncl S A hA).op

/-- The concrete form of the sections of the light condensed set associated to a topological
space: a `S`-section is a continuous map `S → X`. -/
lemma condOf_obj_obj (X : TopCat.{0}) (S : LightProfinite.{0}) :
    (topCatToLightCondSet.obj X).obj.obj (op S) = C(↥S, ↥X) := rfl

/-- The light condensed set associated to a topological space. -/
abbrev condOf (X : TopCat.{0}) : LightCondSet.{0} := topCatToLightCondSet.obj X

/-- The light condensed set associated to a subspace. -/
abbrev setCond {X : TopCat.{0}} (A : Set X) : LightCondSet.{0} :=
  topCatToLightCondSet.obj (TopCat.of A)

/-! ## The Mayer–Vietoris square -/

section Cover

variable {X : TopCat.{0}} (U V : Set X)

/-- The first leg `(U ∩ V)_cond ⟶ U_cond` of the Mayer–Vietoris square. -/
def iWU : setCond (U ∩ V) ⟶ setCond U :=
  topCatToLightCondSet.map (Submission.Blueprint.incl (Set.inter_subset_left : U ∩ V ⊆ U))

/-- The second leg `(U ∩ V)_cond ⟶ V_cond` of the Mayer–Vietoris square. -/
def iWV : setCond (U ∩ V) ⟶ setCond V :=
  topCatToLightCondSet.map (Submission.Blueprint.incl (Set.inter_subset_right : U ∩ V ⊆ V))

/-- The inclusion `U_cond ⟶ X_cond`. -/
def iU : setCond U ⟶ condOf X :=
  topCatToLightCondSet.map (Submission.Blueprint.inclTop U)

/-- The inclusion `V_cond ⟶ X_cond`. -/
def iV : setCond V ⟶ condOf X :=
  topCatToLightCondSet.map (Submission.Blueprint.inclTop V)

/-- The defining relation of the Mayer–Vietoris square commutes. -/
lemma iWU_iU_eq_iWV_iV : iWU U V ≫ iU U = iWV U V ≫ iV V := by
  have h : Submission.Blueprint.incl (Set.inter_subset_left : U ∩ V ⊆ U) ≫
        Submission.Blueprint.inclTop U =
      Submission.Blueprint.incl (Set.inter_subset_right : U ∩ V ⊆ V) ≫
        Submission.Blueprint.inclTop V := by
    ext x
    rfl
  rw [iWU, iWV, iU, iV, ← Functor.map_comp, ← Functor.map_comp, h]

end Cover

end Work.CONDMV
