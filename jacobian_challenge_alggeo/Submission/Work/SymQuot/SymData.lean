/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The `S_n`-action on `Cⁿ` and the quotient data for `Symⁿ C` (area SY)

This file assembles the two inputs of the construction of the symmetric power
`Symⁿ C = Cⁿ/S_n` (§2 of `NOTES_LEAD_jacobian_GC.md`):

* the action of `S_n` on the `n`-fold product `Cⁿ` (by permutation of the factors,
  `Work.SymQuot.permGAction`, lifted to the universe of `C` because `SymGeom`'s
  `Scheme`-valued data lives in the same universe);
* the `S_n`-invariant affine open cover of `Cⁿ` by the product opens `Vⁿ = piOpen C V n`
  for `V ⊆ C` affine; and the fact that intersections of affine opens of `Cⁿ` are affine
  (from the separatedness of `Cⁿ → Spec k`, delegated as `SymQuot.Prod.isSeparated_prod`).

The ubiquitous "every finite set of points of a curve lies in an affine open" (CB7) is the
class `Work.SymQuot.CurveAffineCover`; it holds for every curve
(`Submission.Work.SymQuot.CurveInstance`).
-/
import Submission.Work.SymQuot.CurveInput
import Submission.Work.SymQuot.ProdOpen
import Submission.Work.SymQuot.QuotientMap
import Submission.Work.SymQuot.QuotientHom
import Submission.Work.SymQuot.Prod.isSeparated_prod
import Submission.Work.SymQuot.Prod.isAffineOpen_piOpen

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot

variable {K : Type u} [Field K]

/-- **Intersections of affine opens are affine** for a `K`-scheme whose structure morphism is
separated.  This is the diagonal criterion: over an affine base, it suffices to know that the
diagonal `X ⟶ X ×_K X` is a closed immersion, hence affine. -/
theorem isAffineOpen_inf_of_isSeparated (X : Work.GCBasics.Sch K) [IsSeparated X.hom]
    {U V : X.left.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsAffineOpen (U ⊓ V) :=
  (isAffineHom_diagonal_iff.mp (inferInstance : IsAffineHom (pullback.diagonal X.hom)))
    ⊤ (isAffineOpen_top _) U (by simp) V (by simp) hU hV

/-- Separatedness of `X → Spec K` gives separatedness of `Xⁿ → Spec K`. -/
instance instIsSeparatedProd (X : Work.GCBasics.Sch K) [IsSeparated X.hom] (n : ℕ) :
    IsSeparated (prod X n).hom :=
  Prod.isSeparated_prod X n

/-- **The action of `S_n` on `Cⁿ`**, by permutation of the factors.

The group `Equiv.Perm (Fin n)` lives in `Type 0` while `C` lives in `Type u`; since
`QuotientData` (and `SymGeom`) ask for the group and the scheme in the same universe, the group
is lifted with `ULift`. -/
noncomputable def symAction (C : Work.CurveBasics.Curve K) (n : ℕ) :
    GAction (ULift.{u} (Equiv.Perm (Fin n))) (prod C.toOver n).left where
  hom σ := (permGAction C.toOver n).hom σ.down
  inv σ := (permGAction C.toOver n).inv σ.down
  hom_inv σ := (permGAction C.toOver n).hom_inv σ.down
  inv_hom σ := (permGAction C.toOver n).inv_hom σ.down
  hom_one := (permGAction C.toOver n).hom_one
  hom_mul σ τ := (permGAction C.toOver n).hom_mul σ.down τ.down

@[simp]
theorem symAction_hom (C : Work.CurveBasics.Curve K) (n : ℕ)
    (σ : ULift.{u} (Equiv.Perm (Fin n))) :
    (symAction C n).hom σ = (permGAction C.toOver n).hom σ.down := rfl

/-- **The quotient data for `Symⁿ C = Cⁿ/S_n`.**  The invariant affine opens of `Cⁿ` used as
charts are the product opens `Vⁿ` for `V ⊆ C` affine; they cover `Cⁿ` by CB7 (given a point of
`Cⁿ`, take an affine open of `C` containing its finitely many coordinates), and they are
stable under `S_n`. -/
noncomputable def symData (C : Work.CurveBasics.Curve K) (n : ℕ) [CurveAffineCover C] :
    QuotientData (ULift.{u} (Equiv.Perm (Fin n))) (prod C.toOver n).left where
  action := symAction C n
  isAffineOpen_inf U V hU hV := isAffineOpen_inf_of_isSeparated (prod C.toOver n) hU hV
  covers x := by
    obtain ⟨U, hU, hSU⟩ := CurveAffineCover.exists_isAffineOpen_superset (C := C)
      (Set.range fun m : Fin n => (proj C.toOver n m).left x) (Set.finite_range _)
    refine ⟨piOpen C.toOver U n, Prod.isAffineOpen_piOpen C.toOver n U hU, ?_, ?_⟩
    · intro σ
      exact piOpen_invariant C.toOver U n σ.down
    · rw [mem_piOpen]
      exact fun m => hSU ⟨m, rfl⟩

end Work.SymQuot
