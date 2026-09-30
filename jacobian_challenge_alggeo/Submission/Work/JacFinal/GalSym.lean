/-
Copyright (c) 2025 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area JacFinal (the final assembly: `Work.DescentGeom.Input` from the areas)
-/
import Submission.Work.JacFinal.PermQuot
import Submission.Work.JacFinal.Assembly

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area `JacFinal` — the Galois action on the symmetric power (§1.4(b), (c))

This file provides §1.4(b), (c) of `Submission/Work/NOTES_LEAD_jacobian_final.md`, the input that
`Work.JacFinal.Orbit` needs in order to derive the permutation of the Brill–Noether charts by
`Γ` and hence the `Γ`-stable affine cover `hcover` of `Work.DescentGeom.Input`:

* `Work.JacFinal.Inputs.semilinC` — the semilinear identity `σ` on `C_{k'} = bc k' C`;
* `Work.JacFinal.Inputs.galProd` — the diagonal Galois action on the `n`-fold product
  `C_{k'}^n`, with its defining property against the projections (`Inputs.galProd_proj`) and its
  `S_n`-equivariance (`Inputs.galProd_perm`);
* `Work.JacFinal.Inputs.symGal` — the Galois action on `Sym^g C_{k'}`, i.e. the `τ` of §1.4(b),
  defined through the quotient property `Universal.SymQuotData.desc`;
* `Work.JacFinal.Inputs.AJSym_galAct` — **(c)** the equivariance of `AJSym`
  (`AJSym ≫ ψ_σ = τ_σ ≫ (tw σ).map AJSym`), in the `Sch k'` form and in the `Scheme` form
  `AJSym.left ≫ galActHom σ = τ_σ ≫ AJSym.left`.

**There is no hypothesis in this file.**  The one property that the quotient map needs for the
descent through `SymQuotData.desc` — its invariance under the permutation action,
`Inputs.PermQuot` — is not among the fields of `SpecLin.SymGeom`/`Universal.SymQuotData`, but it
*is* a consequence of them; it is proved in `Submission/Work/JacFinal/PermQuot.lean`
(`Inputs.permQuot`).  (This is the internal step `hB` of `Work.Charts.powMap_perm`, respelled in
the vocabulary of this area.)  The words `prodC`, `projC`, `permIsoC`, `quotMapC` and `PermQuot`
are defined in that file.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonObj MonoidalCategory CategoryTheory
open CartesianMonoidalCategory

universe u

namespace Work.JacFinal

noncomputable section

open Gal

variable {k : Type u} [Field k] {C : CurveBasics.Curve k} {P0 : 𝟙_ (Sch k) ⟶ C.toOver}

namespace Gal

variable {k' : Type u} [Field k'] [Algebra k k']

/-- **Composition into the twist.**  A semilinear morphism `φ` over `Spec σ`, followed by the
image of `u` under the twist, is the semilinear morphism `φ ≫ u.left`. -/
theorem semilinOver_comp_map (σ : Work.Descent.Gal k k') {G H H' : Sch k'} (φ : G.left ⟶ H.left)
    (hφ : φ ≫ H.hom = G.hom ≫ Work.DescentGeom.specGal σ) (u : H ⟶ H') :
    semilinOver σ φ hφ ≫ (tw σ).map u =
      semilinOver σ (φ ≫ u.left) (by rw [Category.assoc, Over.w u]; exact hφ) :=
  Over.OverMorphism.ext rfl

end Gal

namespace Inputs

variable {C : CurveBasics.Curve k} {P0 : 𝟙_ (Sch k) ⟶ C.toOver}

/-- **The semilinear identity of the curve**: the Galois action `galActK k' C σ` on
`C_{k'} = bc k' C`, as a morphism into the twist `(tw σ).obj C_{k'}`. -/
def semilinC (d : Inputs C P0) (σ : Work.Descent.Gal k d.k') :
    d.C' ⟶ (Gal.tw σ).obj d.C' :=
  Gal.semilinOver σ (Work.DescentGeom.galActK d.k' C.toOver σ)
    (Work.DescentGeom.galActK_hom C.toOver σ)

@[simp]
theorem semilinC_left (d : Inputs C P0) (σ : Work.Descent.Gal k d.k') :
    (d.semilinC σ).left = Work.DescentGeom.galActK d.k' C.toOver σ := rfl

/-! ## The `n`-fold product and its Galois action -/

/-- **The diagonal Galois action on the `n`-fold product `C_{k'}^n`.**  It is the morphism into
the twist whose `m`-th projection is the semilinear identity of the `m`-th factor
(`Inputs.galProd_proj`), i.e. the unique such morphism by `Inputs.galProd_ext`. -/
def galProd (d : Inputs C P0) (σ : Work.Descent.Gal k d.k') (n : ℕ) :
    prodC d n ⟶ (Gal.tw σ).obj (prodC d n) :=
  Limits.Pi.lift (fun m : Fin n => d.projC n m ≫ d.semilinC σ) ≫
    (PreservesProduct.iso (Gal.tw σ) (fun _ : Fin n => d.C')).inv

/-- The defining property of `Inputs.galProd`: its `m`-th projection is the semilinear identity
of the `m`-th factor. -/
theorem galProd_proj (d : Inputs C P0) (σ : Work.Descent.Gal k d.k') (n : ℕ) (m : Fin n) :
    d.galProd σ n ≫ (Gal.tw σ).map (d.projC n m) = d.projC n m ≫ d.semilinC σ := by
  rw [galProd, Category.assoc,
    ← Limits.piComparison_comp_π (G := Gal.tw σ) (f := fun _ : Fin n => d.C') m,
    ← PreservesProduct.iso_hom (G := Gal.tw σ) (f := fun _ : Fin n => d.C'),
    Iso.inv_hom_id_assoc, Limits.Pi.lift_comp_π]

/-- Two morphisms into the twisted product coincide as soon as their projections do. -/
theorem galProd_ext (d : Inputs C P0) (σ : Work.Descent.Gal k d.k') (n : ℕ)
    {Y : Sch d.k'} {f g : Y ⟶ (Gal.tw σ).obj (prodC d n)}
    (h : ∀ m : Fin n, f ≫ (Gal.tw σ).map (d.projC n m) =
      g ≫ (Gal.tw σ).map (d.projC n m)) : f = g := by
  have key : ∀ m : Fin n,
      (PreservesProduct.iso (Gal.tw σ) (fun _ : Fin n => d.C')).hom ≫
          Limits.Pi.π (fun _ : Fin n => (Gal.tw σ).obj d.C') m =
        (Gal.tw σ).map (d.projC n m) := by
    intro m
    rw [← Limits.piComparison_comp_π (G := Gal.tw σ) (f := fun _ : Fin n => d.C') m,
      ← PreservesProduct.iso_hom (G := Gal.tw σ) (f := fun _ : Fin n => d.C')]
  have h' : f ≫ (PreservesProduct.iso (Gal.tw σ) (fun _ : Fin n => d.C')).hom =
      g ≫ (PreservesProduct.iso (Gal.tw σ) (fun _ : Fin n => d.C')).hom := by
    apply Limits.Pi.hom_ext
    intro m
    rw [Category.assoc, Category.assoc, key m]
    exact h m
  exact (cancel_mono _).mp h'

/-- **The `S_n`-equivariance of the diagonal Galois action** on `C_{k'}^n`. -/
theorem galProd_perm (d : Inputs C P0) (σ : Work.Descent.Gal k d.k') (n : ℕ)
    (ρ : Equiv.Perm (Fin n)) :
    (d.permIsoC ρ).hom ≫ d.galProd σ n =
      d.galProd σ n ≫ (Gal.tw σ).map (d.permIsoC ρ).hom := by
  refine d.galProd_ext σ n fun m => ?_
  have hL : ((d.permIsoC ρ).hom ≫ d.galProd σ n) ≫ (Gal.tw σ).map (d.projC n m) =
      d.projC n (ρ.symm m) ≫ d.semilinC σ := by
    rw [Category.assoc, d.galProd_proj σ n m, ← Category.assoc, d.permIsoC_hom_proj ρ m]
  have hR : (d.galProd σ n ≫ (Gal.tw σ).map (d.permIsoC ρ).hom) ≫
        (Gal.tw σ).map (d.projC n m) = d.projC n (ρ.symm m) ≫ d.semilinC σ := by
    rw [Category.assoc, ← Functor.map_comp, d.permIsoC_hom_proj ρ m,
      d.galProd_proj σ n (ρ.symm m)]
  rw [hL, hR]

/-! ## The Galois action on `Sym^g C_{k'}` (§1.4(b)) -/

/-- The Abel–Jacobi map `C_{k'} ⟶ G'` of area `GC`, with the source and target spelled through
`Inputs.C'` and `Inputs.toChunk.G` (the two are definitionally equal to `bc k' C.toOver` and
`d.exports.glued.G`; the change of spelling is needed because `rw` matches only up to the
transparency of `def`s). -/
def AJ₀C (d : Inputs C P0) : d.C' ⟶ d.toChunk.G := d.exports.AJ₀

/-- The Abel–Jacobi map `Sym^g C_{k'} ⟶ G'` of area `GC`, in the spelling of this file. -/
def AJSymC (d : Inputs C P0) : d.chart.Sym d.chart.g ⟶ d.toChunk.G := d.exports.AJSym

/-- The Galois action on the group chunk (`Work.JacFinal.Gal.Chunk.galAct`), in the spelling of
this file. -/
def psiC (d : Inputs C P0) (σ : Work.Descent.Gal k d.k') :
    d.toChunk.G ⟶ (Gal.tw σ).obj d.toChunk.G := d.toChunk.psi σ

/-- **The `g`-fold sum of the Abel–Jacobi map** `Σ_m (pr_m ≫ AJ₀)` on `C_{k'}^g`; by
`Inputs.quotMapC_AJSym` it is `quotMapC ≫ AJSym`. -/
def sumTermC (d : Inputs C P0) : prodC d d.chart.g ⟶ d.toChunk.G :=
  ∏ m : Fin d.chart.g, (d.projC d.chart.g m ≫ d.AJ₀C)

/-- `AJSym` is the `g`-fold sum of `AJ₀`, read through the quotient map: this is the
`AJSym_powMap` field of area `GC` at the universal family of points of `C_{k'}^g`. -/
theorem quotMapC_AJSym (d : Inputs C P0) :
    d.quotMapC d.chart.g ≫ d.AJSymC = d.sumTermC := by
  haveI := d.exports
  simp only [quotMapC, sumTermC, AJSymC, AJ₀C]
  exact d.exports.AJSym_powMap (x := fun m : Fin d.chart.g => d.projC d.chart.g m)

/-- The morphism `galProd σ ≫ (tw σ).map quotMap` is invariant under `permIso ρ ≫ ·`: the
hypothesis of `SymQuotData.desc` that produces the Galois action on `Sym^g`.  It is a special
case of `Inputs.permQuot` (see `Submission/Work/JacFinal/PermQuot.lean`). -/
theorem galProd_quotMap_perm (d : Inputs C P0) (σ : Work.Descent.Gal k d.k')
    (n : ℕ) (ρ : Equiv.Perm (Fin n)) :
    (d.permIsoC ρ).hom ≫ (d.galProd σ n ≫ (Gal.tw σ).map (d.quotMapC n)) =
      d.galProd σ n ≫ (Gal.tw σ).map (d.quotMapC n) := by
  rw [← Category.assoc, d.galProd_perm σ n ρ, Category.assoc, ← Functor.map_comp,
    d.permQuot n ρ]

/-- **The Galois action on `Sym^g C_{k'}`**, as the `∃!`-statement produced by the quotient
property `Universal.SymQuotData.desc`, applied to the invariant morphism
`galProd σ ≫ (tw σ).map quotMap`. -/
theorem symGalData (d : Inputs C P0) (σ : Work.Descent.Gal k d.k') :
    ∃! g : d.chart.Sym d.chart.g ⟶ (Gal.tw σ).obj (d.chart.Sym d.chart.g),
      d.quotMapC d.chart.g ≫ g =
        d.galProd σ d.chart.g ≫ (Gal.tw σ).map (d.quotMapC d.chart.g) :=
  d.exports.desc d.chart.g _ (d.galProd_quotMap_perm σ d.chart.g)

/-- **`τ_σ`: the Galois action on the symmetric power `Sym^g C_{k'}`** of §1.4(b). -/
def symGal (d : Inputs C P0) (σ : Work.Descent.Gal k d.k') :
    d.chart.Sym d.chart.g ⟶ (Gal.tw σ).obj (d.chart.Sym d.chart.g) :=
  (d.symGalData σ).exists.choose

/-- The defining property of `Inputs.symGal`: it descends `galProd σ ≫ (tw σ).map quotMap`
through the quotient map `C_{k'}^g ⟶ Sym^g C_{k'}`. -/
theorem symGal_spec (d : Inputs C P0) (σ : Work.Descent.Gal k d.k') :
    d.quotMapC d.chart.g ≫ d.symGal σ =
      d.galProd σ d.chart.g ≫ (Gal.tw σ).map (d.quotMapC d.chart.g) :=
  (d.symGalData σ).exists.choose_spec

/-! ## §1.4(c): the equivariance of `AJSym` -/

/-- **The key computation of §1.4(b)**: the diagonal Galois action on the `g`-fold product
intertwines the `g`-fold sum `sumTermC` with the Galois action `ψ_σ` on the group chunk. -/
theorem galProd_sumTermC (d : Inputs C P0) (σ : Work.Descent.Gal k d.k') :
    d.galProd σ d.chart.g ≫ (Gal.tw σ).map d.sumTermC = d.sumTermC ≫ d.psiC σ := by
  haveI := d.exports
  have hfTw : d.semilinC σ ≫ (Gal.tw σ).map d.AJ₀C = d.toChunk.fTw σ :=
    Over.OverMorphism.ext rfl
  have hmap : (Gal.tw σ).map d.sumTermC =
      ∏ m : Fin d.chart.g, (Gal.tw σ).map (d.projC d.chart.g m ≫ d.AJ₀C) := by
    rw [sumTermC]
    exact map_prod (Functor.homMonoidHom (Gal.tw σ) (X := prodC d d.chart.g))
      (fun m : Fin d.chart.g => d.projC d.chart.g m ≫ d.AJ₀C) Finset.univ
  have hcomp := Work.Universal.comp_prod (d.galProd σ d.chart.g)
    (fun m : Fin d.chart.g => (Gal.tw σ).map (d.projC d.chart.g m ≫ d.AJ₀C))
  have hfac : ∀ m : Fin d.chart.g,
      (d.galProd σ d.chart.g ≫ (Gal.tw σ).map (d.projC d.chart.g m ≫ d.AJ₀C)) =
        d.projC d.chart.g m ≫ d.AJ₀C ≫ d.psiC σ := by
    intro m
    rw [Functor.map_comp, ← Category.assoc, d.galProd_proj σ d.chart.g m, Category.assoc,
      hfTw, d.toChunk.psi_spec σ]
    rfl
  calc d.galProd σ d.chart.g ≫ (Gal.tw σ).map d.sumTermC
      = d.galProd σ d.chart.g ≫
          ∏ m : Fin d.chart.g, (Gal.tw σ).map (d.projC d.chart.g m ≫ d.AJ₀C) := by
        rw [hmap]
    _ = ∏ m : Fin d.chart.g,
          (d.galProd σ d.chart.g ≫
            (Gal.tw σ).map (d.projC d.chart.g m ≫ d.AJ₀C)) := hcomp
    _ = ∏ m : Fin d.chart.g, (d.projC d.chart.g m ≫ d.AJ₀C ≫ d.psiC σ) :=
        Finset.prod_congr rfl (fun m _ => hfac m)
    _ = (∏ m : Fin d.chart.g, (d.projC d.chart.g m ≫ d.AJ₀C)) ≫ d.psiC σ := by
        haveI : IsMonHom (d.psiC σ) := d.toChunk.psi_isMonHom σ
        exact (Work.Universal.prod_comp (fun m : Fin d.chart.g => d.projC d.chart.g m ≫ d.AJ₀C)
          (d.psiC σ)).symm
    _ = d.sumTermC ≫ d.psiC σ := rfl

/-- The invariance of `galProd σ ≫ (tw σ).map (quotMap ≫ AJSym)`: the same computation as
above, read through the quotient map. -/
theorem galProd_quotMap_AJSym_perm (d : Inputs C P0)
    (σ : Work.Descent.Gal k d.k') (ρ : Equiv.Perm (Fin d.chart.g)) :
    (d.permIsoC ρ).hom ≫
        (d.galProd σ d.chart.g ≫ (Gal.tw σ).map (d.quotMapC d.chart.g ≫ d.AJSymC)) =
      d.galProd σ d.chart.g ≫
        (Gal.tw σ).map (d.quotMapC d.chart.g ≫ d.AJSymC) := by
  rw [← Category.assoc, d.galProd_perm σ d.chart.g ρ, Category.assoc, ← Functor.map_comp,
    ← Category.assoc, d.permQuot d.chart.g ρ]

/-- The `∃!`-statement characterising the morphisms `Sym^g C_{k'} ⟶ (tw σ).obj G'` which
intertwine the quotient map with `galProd σ ≫ (tw σ).map (quotMap ≫ AJSym)`. -/
theorem ajSymData (d : Inputs C P0) (σ : Work.Descent.Gal k d.k') :
    ∃! g : d.chart.Sym d.chart.g ⟶ (Gal.tw σ).obj d.toChunk.G,
      d.quotMapC d.chart.g ≫ g =
        d.galProd σ d.chart.g ≫
          (Gal.tw σ).map (d.quotMapC d.chart.g ≫ d.AJSymC) :=
  d.exports.desc d.chart.g _ (d.galProd_quotMap_AJSym_perm σ)

/-- **§1.4(c): `AJSym` is `Γ`-equivariant**, in the categorical form.  Its consequence in the
form used by `Work.JacFinal.Orbit` is `Inputs.AJSym_galAct_left`. -/
theorem AJSym_galAct_C (d : Inputs C P0) (σ : Work.Descent.Gal k d.k') :
    d.AJSymC ≫ d.psiC σ = d.symGal σ ≫ (Gal.tw σ).map d.AJSymC := by
  have h1 : d.quotMapC d.chart.g ≫ (d.symGal σ ≫ (Gal.tw σ).map d.AJSymC) =
      d.galProd σ d.chart.g ≫
        (Gal.tw σ).map (d.quotMapC d.chart.g ≫ d.AJSymC) := by
    rw [← Category.assoc, d.symGal_spec σ, Category.assoc, ← Functor.map_comp]
  have h2 : d.quotMapC d.chart.g ≫ (d.AJSymC ≫ d.psiC σ) =
      d.galProd σ d.chart.g ≫
        (Gal.tw σ).map (d.quotMapC d.chart.g ≫ d.AJSymC) := by
    rw [← Category.assoc, d.quotMapC_AJSym, d.galProd_sumTermC σ]
  exact ((d.ajSymData σ).unique h1 h2).symm

/-- **§1.4(c): the equivariance of `AJSym`** in the spelling in which the areas state their
morphisms. -/
theorem AJSym_galAct (d : Inputs C P0) (σ : Work.Descent.Gal k d.k') :
    d.exports.AJSym ≫ d.toChunk.psi σ =
      d.symGal σ ≫ (Gal.tw σ).map d.exports.AJSym :=
  d.AJSym_galAct_C σ

/-- **§1.4(c) in the form used downstream**: `AJSym.left ≫ galActHom σ = τ_σ ≫ AJSym.left`.
This is the `Γ`-equivariance of the Abel–Jacobi map `Sym^g C_{k'} ⟶ G'` on underlying schemes;
combined with the chart-translate formula §1.4(a) it gives the permutation of the
Brill–Noether charts by `Γ` (§1.4(e)). -/
theorem AJSym_galAct_left (d : Inputs C P0) (σ : Work.Descent.Gal k d.k') :
    d.exports.AJSym.left ≫ (d.toChunk.galAct σ).hom =
      (d.symGal σ).left ≫ d.exports.AJSym.left :=
  congrArg Over.Hom.left (d.AJSym_galAct σ)

end Inputs

end

end Work.JacFinal
