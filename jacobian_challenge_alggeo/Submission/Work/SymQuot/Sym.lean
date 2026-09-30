/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The symmetric power `Symⁿ C` (area SY)

This file contains the symmetric power `Symⁿ C = Cⁿ/S_n` as a `K`-scheme, the quotient map
`Sym.quot : Cⁿ ⟶ Symⁿ C`, the universal property of the quotient (`Sym.desc`: an `S_n`-invariant
morphism out of `Cⁿ` factors uniquely through `Sym.quot`) and the `n`-fold sum map `Sym.powMap`
sending `n` points of `C` parametrised by a `K`-scheme `T` to their sum in `Symⁿ C`.

The construction of `Symⁿ C` is `QuotientData.Quotient` of the quotient data `symData C n`
(`Submission.Work.SymQuot.SymData`): the locally directed colimit of the charts
`Spec Γ(Cⁿ, Vⁿ)^{S_n}` over the affine opens `V ⊆ C`.

The *divisor* of a point of `Symⁿ C` (`SymGeom.divOf`) is built in the files
`Submission.Work.SymQuot.DivOf.*`; the scheme-theoretic properties of `Symⁿ C`
(properness, integrality, geometric irreducibility) in `SymQuot.Sym.*`.
-/
import Submission.Work.SymQuot.SymData
import Submission.Work.SymQuot.CurveInstance

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot

variable {K : Type u} [Field K]

/-- The structure morphism of `Cⁿ` is invariant under the `S_n`-action, because the action is
by automorphisms of `K`-schemes.  This is what gives `Symⁿ C` its structure morphism over
`Spec K`. -/
theorem sym_hom_invariant (C : Work.CurveBasics.Curve K) (n : ℕ) [CurveAffineCover C] :
    ∀ σ : ULift.{u} (Equiv.Perm (Fin n)),
      (symAction C n).hom σ ≫ (prod C.toOver n).hom = (prod C.toOver n).hom :=
  fun σ => (permIso C.toOver σ.down).hom.w

/-- **The `n`-th symmetric power `Symⁿ C = Cⁿ/S_n`** of a curve over `K`, as a `K`-scheme.

Its underlying scheme is the quotient `(prod C.toOver n).left / S_n` (`QuotientData.Quotient`),
and its structure morphism over `Spec K` is induced by the `S_n`-invariant morphism
`Cⁿ ⟶ Spec K`. -/
noncomputable def Sym (C : Work.CurveBasics.Curve K) (n : ℕ) [CurveAffineCover C] :
    Work.GCBasics.Sch K :=
  Over.mk ((symData C n).quotientHom (prod C.toOver n).hom (sym_hom_invariant C n))

/-- The structure morphism of `Symⁿ C` is the morphism induced on the quotient by the
`S_n`-invariant structure morphism of `Cⁿ`. -/
theorem Sym.hom_def (C : Work.CurveBasics.Curve K) (n : ℕ) [CurveAffineCover C] :
    (Sym C n).hom = (symData C n).quotientHom (prod C.toOver n).hom (sym_hom_invariant C n) :=
  rfl

/-- The quotient map `Cⁿ ⟶ Symⁿ C`. -/
noncomputable def Sym.quot (C : Work.CurveBasics.Curve K) (n : ℕ) [CurveAffineCover C] :
    prod C.toOver n ⟶ Sym C n :=
  Over.homMk (symData C n).quotientMap (by
    rw [Sym.hom_def]
    simp only [QuotientData.quotientMap_quotientHom])

/-- The underlying morphism of schemes of the quotient map. -/
@[simp]
theorem Sym.quot_left (C : Work.CurveBasics.Curve K) (n : ℕ) [CurveAffineCover C] :
    (Sym.quot C n).left = (symData C n).quotientMap :=
  rfl

/-- The compatibility of the quotient map with the structure morphisms. -/
theorem Sym.quot_hom (C : Work.CurveBasics.Curve K) (n : ℕ) [CurveAffineCover C] :
    (Sym.quot C n).left ≫ (Sym C n).hom = (prod C.toOver n).hom :=
  (Sym.quot C n).w

/-- The quotient map is surjective, hence every point of `Symⁿ C` has a lift to `Cⁿ`. -/
theorem Sym.quot_surjective (C : Work.CurveBasics.Curve K) (n : ℕ) [CurveAffineCover C] :
    Function.Surjective (Sym.quot C n).left :=
  QuotientData.quotientMap_surjective _

/-- **The universal property of `Symⁿ C`.**  A morphism `Cⁿ ⟶ Z` of `K`-schemes which is
invariant under the `S_n`-action factors uniquely through the quotient map `Sym.quot`. -/
theorem Sym.desc (C : Work.CurveBasics.Curve K) (n : ℕ) [CurveAffineCover C]
    {Z : Work.GCBasics.Sch K} (f : prod C.toOver n ⟶ Z)
    (hf : ∀ σ : ULift.{u} (Equiv.Perm (Fin n)),
      (symAction C n).hom σ ≫ f.left = f.left) :
    ∃! g : Sym C n ⟶ Z, Sym.quot C n ≫ g = f := by
  classical
  obtain ⟨g₀, hg₀, huniq⟩ := (symData C n).quotient_lift f.left hf
  have hinv : ∀ σ : ULift.{u} (Equiv.Perm (Fin n)),
      (symAction C n).hom σ ≫ (f.left ≫ Z.hom) = f.left ≫ Z.hom := by
    intro σ
    rw [← Category.assoc, hf σ]
  have hA : (symData C n).quotientMap ≫ (g₀ ≫ Z.hom) = f.left ≫ Z.hom := by
    rw [← Category.assoc, hg₀]
  have hB : (symData C n).quotientMap ≫ (Sym C n).hom = f.left ≫ Z.hom := by
    rw [Sym.hom_def]
    simp only [QuotientData.quotientMap_quotientHom]
    exact (f.w).symm
  have hw : g₀ ≫ Z.hom = (Sym C n).hom :=
    ((symData C n).quotient_lift (f.left ≫ Z.hom) hinv).unique hA hB
  refine ⟨Over.homMk g₀ hw, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    simp only [Over.comp_left, Sym.quot_left]
    exact hg₀
  · intro g hg
    apply Over.OverMorphism.ext
    refine huniq g.left ?_
    have h1 : (Sym.quot C n ≫ g).left = f.left := by rw [hg]
    simpa only [Over.comp_left, Sym.quot_left] using h1

/-- **The sum map**: `n` points of `C` parametrised by a `K`-scheme `T` give a point of
`Symⁿ C`.  This is the composite of the universal map `T ⟶ Cⁿ` with the quotient map. -/
noncomputable def Sym.powMap (C : Work.CurveBasics.Curve K) (n : ℕ) [CurveAffineCover C]
    {T : Work.GCBasics.Sch K} (x : Fin n → (T ⟶ C.toOver)) : T ⟶ Sym C n :=
  Limits.Pi.lift x ≫ Sym.quot C n

/-- Naturality of the sum map in the parameter scheme. -/
theorem Sym.powMap_comp (C : Work.CurveBasics.Curve K) (n : ℕ) [CurveAffineCover C]
    {T T' : Work.GCBasics.Sch K} (g : T' ⟶ T) (x : Fin n → (T ⟶ C.toOver)) :
    Sym.powMap C n (fun m => g ≫ x m) = g ≫ Sym.powMap C n x := by
  simp only [Sym.powMap, pi_lift_comp, Category.assoc]

end Work.SymQuot
