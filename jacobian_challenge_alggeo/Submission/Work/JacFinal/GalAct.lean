/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area JacFinal (the final assembly: `Work.DescentGeom.Input` from the areas)
-/
import Submission.Work.DescentGeom.Basic
import Submission.Work.DescentGeom.Kit
import Submission.Work.DescentGeom.geometricallyIrreducible_of_bc
import Submission.Work.AbVar.Hom.isMonHom_of_isPointedMap

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area `JacFinal` — the semilinear Galois action on the group chunk

`Work.DescentGeom.Input` (`Submission/Work/DescentGeom/Basic.lean`) asks for a semilinear action
of `Γ = Gal k k'` on the group chunk `G'` over `k'`:

* `galAct σ : G'.left ≅ G'.left` with `(galAct σ).hom ≫ G'.hom = G'.hom ≫ specGal σ`
  (semilinear over `Spec k'`), an action (`galAct_one`, `galAct_mul`), and compatibility with
  `μ`, `η`, `ι`;

Here it is **constructed**, not assumed: §1.2 of `Submission/Work/NOTES_LEAD_jacobian_final.md`.
The key point is that a semilinear map `φ` over `Spec σ` is the same thing as a `k'`-morphism
into the twist `(tw σ).obj G`, where `tw σ = Over.map (specGal σ⁻¹)`; the twist is an
autoequivalence (a monoidal one, preserving group objects and the geometry of the structure
morphism), so the universal property `univ'` of `AJ : bc k' C ⟶ G` applies to
`galActK k' C σ ≫ AJ.left : bc k' C ⟶ (tw σ).obj G` and produces `ψ σ : G ⟶ (tw σ).obj G`,
whose underlying morphism is `galAct σ`.

Everything here is generic in `G` (a group chunk over `k'` with the universal property of its
Abel–Jacobi map); the results are used in `Work.JacFinal.Assembly`.

The only mathematical input is the rigidity of pointed maps between abelian varieties
(`Work.AbVar.Hom.isMonHom_of_isPointedMap`).
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

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']

namespace Gal

open Work.DescentGeom

abbrev Sch (k : Type u) [Field k] : Type (u + 1) := Over (Spec (.of k))

/-! ## 1. The twist by `σ` -/

/-- `Spec σ` as an isomorphism of `k`-schemes (`specGal σ⁻¹` is its inverse). -/
def specGalIso (σ : Work.Descent.Gal k k') : Spec (.of k') ≅ Spec (.of k') where
  hom := Work.DescentGeom.specGal σ⁻¹
  inv := Work.DescentGeom.specGal σ
  hom_inv_id := by
    rw [← Work.DescentGeom.specGal_mul, inv_mul_cancel, Work.DescentGeom.specGal_one]
  inv_hom_id := by
    rw [← Work.DescentGeom.specGal_mul, mul_inv_cancel, Work.DescentGeom.specGal_one]

/-- **The twist of `Sch k'` by `σ`**: composition of the structure morphism with `Spec σ⁻¹`. -/
abbrev tw (σ : Work.Descent.Gal k k') : Sch k' ⥤ Sch k' :=
  Over.map (specGalIso σ).hom

/-- The twist is an equivalence of categories. -/
instance tw_isEquivalence (σ : Work.Descent.Gal k k') : (tw (k := k) (k' := k') σ).IsEquivalence :=
  (Over.mapIso (specGalIso σ)).isEquivalence_functor

/-- The twist is a monoidal functor (it preserves finite products). -/
instance tw_monoidal (σ : Work.Descent.Gal k k') : (tw (k := k) (k' := k') σ).Monoidal :=
  Functor.Monoidal.ofChosenFiniteProducts _

/-- The twist sends group objects to group objects. -/
instance tw_grpObj (σ : Work.Descent.Gal k k') (G : Sch k') [GrpObj G] :
    GrpObj ((tw (k := k) (k' := k') σ).obj G) :=
  Functor.grpObjObj

/-- The square with `𝟙` on top and an isomorphism at the bottom is a pullback. -/
theorem isPullback_comp_iso {X S : Scheme.{u}} (f : X ⟶ S) (e : S ≅ S) :
    IsPullback (𝟙 X) (f ≫ e.hom) f e.inv := by
  refine IsPullback.of_horiz_isIso ⟨?_⟩
  rw [Category.id_comp, Category.assoc, e.hom_inv_id, Category.comp_id]

/-- `geometrically P` is insensitive to composing with an isomorphism of the base. -/
theorem geometrically_comp_iso {P : ObjectProperty Scheme.{u}} {X S : Scheme.{u}} (f : X ⟶ S)
    (e : S ⟶ S) [IsIso e] (h : geometrically P f) : geometrically P (f ≫ e) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_comp_iso f (asIso e)) h

/-- The twist preserves geometric irreducibility. -/
instance tw_geometricallyIrreducible (σ : Work.Descent.Gal k k') (G : Sch k')
    [GeometricallyIrreducible G.hom] :
    GeometricallyIrreducible ((tw (k := k) (k' := k') σ).obj G).hom where
  geometrically_irreducibleSpace := by
    rw [Over.map_obj_hom]
    exact geometrically_comp_iso G.hom (specGalIso σ).hom
      (inferInstance : GeometricallyIrreducible G.hom).geometrically_irreducibleSpace

/-- The twist preserves geometric reducedness. -/
instance tw_geometricallyReduced (σ : Work.Descent.Gal k k') (G : Sch k')
    [GeometricallyReduced G.hom] :
    GeometricallyReduced ((tw (k := k) (k' := k') σ).obj G).hom where
  geometrically_isReduced := by
    rw [Over.map_obj_hom]
    exact geometrically_comp_iso G.hom (specGalIso σ).hom
      (inferInstance : GeometricallyReduced G.hom).geometrically_isReduced

/-- The twist preserves geometric integrality. -/
instance tw_geometricallyIntegral (σ : Work.Descent.Gal k k') (G : Sch k')
    [GeometricallyIntegral G.hom] :
    GeometricallyIntegral ((tw (k := k) (k' := k') σ).obj G).hom where
  geometrically_isIntegral := by
    rw [Over.map_obj_hom]
    exact geometrically_comp_iso G.hom (specGalIso σ).hom
      (inferInstance : GeometricallyIntegral G.hom).geometrically_isIntegral

/-- The twist preserves properness. -/
instance tw_isProper (σ : Work.Descent.Gal k k') (G : Sch k') [IsProper G.hom] :
    IsProper ((tw (k := k) (k' := k') σ).obj G).hom := by
  rw [Over.map_obj_hom]
  infer_instance

/-- The twist preserves smoothness. -/
instance tw_smooth (σ : Work.Descent.Gal k k') (G : Sch k') [Smooth G.hom] :
    Smooth ((tw (k := k) (k' := k') σ).obj G).hom := by
  rw [Over.map_obj_hom]
  infer_instance

/-- **A semilinear morphism is a morphism into the twist.**  If `φ : G.left ⟶ H.left` covers
`Spec σ`, then `φ` is a `k'`-morphism `G ⟶ (tw σ).obj H`. -/
def semilinOver (σ : Work.Descent.Gal k k') {G H : Sch k'} (φ : G.left ⟶ H.left)
    (hφ : φ ≫ H.hom = G.hom ≫ Work.DescentGeom.specGal σ) : G ⟶ (tw σ).obj H :=
  Over.homMk φ (by
    change φ ≫ H.hom ≫ (specGalIso σ).hom = G.hom
    rw [reassoc_of% hφ]
    change (G.hom ≫ Work.DescentGeom.specGal σ) ≫ Work.DescentGeom.specGal σ⁻¹ = G.hom
    rw [Category.assoc, ← Work.DescentGeom.specGal_mul, mul_inv_cancel,
      Work.DescentGeom.specGal_one, Category.comp_id])

@[simp]
theorem semilinOver_left (σ : Work.Descent.Gal k k') {G H : Sch k'} (φ : G.left ⟶ H.left)
    (hφ : φ ≫ H.hom = G.hom ≫ Work.DescentGeom.specGal σ) :
    (semilinOver σ φ hφ).left = φ := rfl

/-- The unit comparison of the twist, at the level of underlying schemes. -/
theorem tw_epsilon_left (σ : Work.Descent.Gal k k') :
    (Functor.LaxMonoidal.ε (tw (k := k) (k' := k') σ)).left =
      Work.DescentGeom.specGal σ := by
  have h := Over.w (Functor.LaxMonoidal.ε (tw (k := k) (k' := k') σ))
  have h1 : Over.hom ((tw (k := k) (k' := k') σ).obj (𝟙_ (Sch k'))) =
      Work.DescentGeom.specGal σ⁻¹ := by
    rw [Over.map_obj_hom]
    rfl
  rw [h1] at h
  have h2 := congrArg (fun t => t ≫ Work.DescentGeom.specGal σ) h
  simpa [Category.assoc, ← Work.DescentGeom.specGal_mul, inv_mul_cancel,
    Work.DescentGeom.specGal_one] using h2

/-- The unit of the twisted group, at the level of underlying schemes. -/
theorem tw_eta_left (σ : Work.Descent.Gal k k') (G : Sch k') [GrpObj G] :
    (η[(tw (k := k) (k' := k') σ).obj G]).left =
      Work.DescentGeom.specGal σ ≫ η[G].left := by
  have h := congrArg Over.Hom.left (Functor.obj.η_def (F := tw (k := k) (k' := k') σ) (X := G))
  rw [Over.comp_left, tw_epsilon_left] at h
  rw [h]
  rfl

/-- The inverse of the twisted group, at the level of underlying schemes. -/
theorem tw_inv_left (σ : Work.Descent.Gal k k') (G : Sch k') [GrpObj G] :
    (ι[(tw (k := k) (k' := k') σ).obj G]).left = ι[G].left := by
  have h := congrArg Over.Hom.left (Functor.obj.ι_def (F := tw (k := k) (k' := k') σ) (G := G))
  rw [h]
  rfl

/-- The multiplication of the twisted group, at the level of underlying schemes. -/
theorem tw_mul_left (σ : Work.Descent.Gal k k') (G : Sch k') [GrpObj G] :
    (μ[(tw (k := k) (k' := k') σ).obj G]).left =
      (Functor.LaxMonoidal.μ (tw (k := k) (k' := k') σ) G G).left ≫ μ[G].left := by
  have h := congrArg Over.Hom.left (Functor.obj.μ_def (F := tw (k := k) (k' := k') σ) (X := G))
  rw [h]
  rfl

/-- The comparison `μ` of the twist, against the first projection. -/
theorem tw_μ_fst (σ : Work.Descent.Gal k k') (G : Sch k') :
    (Functor.LaxMonoidal.μ (tw (k := k) (k' := k') σ) G G).left ≫ pullback.fst G.hom G.hom =
      pullback.fst (G.hom ≫ (specGalIso σ).hom) (G.hom ≫ (specGalIso σ).hom) :=
  congrArg Over.Hom.left (Functor.Monoidal.μ_fst (F := tw (k := k) (k' := k') σ) G G)

/-- The comparison `μ` of the twist, against the second projection. -/
theorem tw_μ_snd (σ : Work.Descent.Gal k k') (G : Sch k') :
    (Functor.LaxMonoidal.μ (tw (k := k) (k' := k') σ) G G).left ≫ pullback.snd G.hom G.hom =
      pullback.snd (G.hom ≫ (specGalIso σ).hom) (G.hom ≫ (specGalIso σ).hom) :=
  congrArg Over.Hom.left (Functor.Monoidal.μ_snd (F := tw (k := k) (k' := k') σ) G G)



/-! ## 2. The Galois action from the universal property

This is §1.2 of `NOTES_LEAD_jacobian_final.md`.  The hypotheses are bundled in the structure
`Chunk`: `G` is the glued group chunk of area `GC` (with its group law, properness, smoothness
and geometric integrality), `AJ` is its Abel–Jacobi map, `univ`/`epi` are the universal property
and the generation property of area `UP` over `k'`, and `AJ_pt` is the `GC` output `AJ₀_pt`.
Nothing else is assumed.
-/

/-- **A group chunk over `k'` with the Abel–Jacobi map and its universal property**: this is
exactly the data of areas `GC` and `UP` over the finite Galois extension `k'` which
`Work.DescentGeom.Input` consumes. -/
structure Chunk (C : Sch k) (P0 : 𝟙_ (Sch k) ⟶ C) where
  /-- the glued group chunk (area `GC`) -/
  G : Sch k'
  [grpObj : GrpObj G]
  [isProper : IsProper G.hom]
  [smooth : Smooth G.hom]
  [geomIntegral : GeometricallyIntegral G.hom]
  /-- the Abel–Jacobi map over `k'` (area `GC`) -/
  AJ : bc k' C ⟶ G
  /-- it sends the base point to the origin (area `GC`) -/
  AJ_pt : (bcFun k k').map P0 ≫ AJ =
    (CartesianMonoidalCategory.preservesTerminalIso (bcFun k k')).hom ≫ η[G]
  /-- the universal property of the Abel–Jacobi map over `k'` (area `UP`) -/
  univ : ∀ (A' : Sch k') [Smooth A'.hom] [IsProper A'.hom] [GeometricallyIrreducible A'.hom]
    [GrpObj A'] (f : bc k' C ⟶ A'),
    (bcFun k k').map P0 ≫ f =
      (CartesianMonoidalCategory.preservesTerminalIso (bcFun k k')).hom ≫ η[A'] →
    ∃! g : G ⟶ A', f = AJ ≫ g
  /-- the generation property over `k'` (area `UP`) -/
  epi : ∀ (A' : Sch k') [Smooth A'.hom] [IsProper A'.hom] [GeometricallyIrreducible A'.hom]
    [GrpObj A'] (u v : G ⟶ A'), AJ ≫ u = AJ ≫ v → u = v

namespace Chunk

variable {C : Sch k} {P0 : 𝟙_ (Sch k) ⟶ C}

instance (d : Chunk (k := k) (k' := k') C P0) : GrpObj d.G := d.grpObj
instance (d : Chunk (k := k) (k' := k') C P0) : IsProper d.G.hom := d.isProper
instance (d : Chunk (k := k) (k' := k') C P0) : Smooth d.G.hom := d.smooth
instance (d : Chunk (k := k) (k' := k') C P0) : GeometricallyIntegral d.G.hom :=
  d.geomIntegral

variable (d : Chunk (k := k) (k' := k') C P0)

/-- **The twisted Abel–Jacobi map.**  `galActK k' C σ ≫ AJ.left` is semilinear over `Spec σ`,
hence a `k'`-morphism `bc k' C ⟶ (tw σ).obj G`. -/
def fTw (σ : Work.Descent.Gal k k') : bc k' C ⟶ (tw (k := k) (k' := k') σ).obj d.G :=
  semilinOver σ (galActK k' C σ ≫ d.AJ.left)
    (by rw [Category.assoc, Over.w d.AJ]; exact galActK_hom C σ)

/-- The twisted Abel–Jacobi map sends the base point to the origin. -/
theorem fTw_pt (σ : Work.Descent.Gal k k') :
    (bcFun k k').map P0 ≫ d.fTw σ =
      (CartesianMonoidalCategory.preservesTerminalIso (bcFun k k')).hom ≫
        η[(tw (k := k) (k' := k') σ).obj d.G] := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, fTw, semilinOver_left]
  rw [show galActK k' C σ = Work.Descent.galAct C σ from rfl]
  rw [← Category.assoc, ← Work.DescentGeom.galAct_naturality (𝟙_ (Sch k)) C P0 σ]
  rw [Category.assoc, ← Over.comp_left, congrArg Over.Hom.left d.AJ_pt, Over.comp_left,
    ← Category.assoc, Work.DescentGeom.galAct_terminal, Category.assoc,
    ← tw_eta_left σ d.G]

/-- **The Galois action**, as a morphism of group chunks. -/
def psi (σ : Work.Descent.Gal k k') : d.G ⟶ (tw (k := k) (k' := k') σ).obj d.G :=
  (d.univ ((tw (k := k) (k' := k') σ).obj d.G) (d.fTw σ) (d.fTw_pt σ)).exists.choose

theorem psi_spec (σ : Work.Descent.Gal k k') : d.fTw σ = d.AJ ≫ d.psi σ :=
  (d.univ ((tw (k := k) (k' := k') σ).obj d.G) (d.fTw σ) (d.fTw_pt σ)).exists.choose_spec

/-- The underlying morphism of the Galois action. -/
def galActHom (σ : Work.Descent.Gal k k') : d.G.left ⟶ d.G.left := (d.psi σ).left

/-- The Galois action is semilinear over `Spec k'`. -/
theorem galActHom_hom (σ : Work.Descent.Gal k k') :
    d.galActHom σ ≫ d.G.hom = d.G.hom ≫ Work.DescentGeom.specGal σ := by
  have h := Over.w (d.psi σ)
  rw [show ((tw (k := k) (k' := k') σ).obj d.G).hom = d.G.hom ≫ (specGalIso σ).hom from
    Over.map_obj_hom] at h
  have h2 := congrArg (fun t => t ≫ Work.DescentGeom.specGal σ) h
  simpa [galActHom, Category.assoc, specGalIso, ← Work.DescentGeom.specGal_mul,
    mul_inv_cancel, Work.DescentGeom.specGal_one] using h2

/-- The semilinear action of `σ` on the chunk commutes with the Abel–Jacobi map. -/
theorem AJ'_compat (σ : Work.Descent.Gal k k') :
    galActK k' C σ ≫ d.AJ.left = d.AJ.left ≫ d.galActHom σ :=
  congrArg Over.Hom.left (d.psi_spec σ)

/-- **The uniqueness tool**: two semilinear endomorphisms of `G.left` agreeing after `AJ` are
equal. -/
theorem semilin_ext (σ : Work.Descent.Gal k k') {φ φ' : d.G.left ⟶ d.G.left}
    (hφ : φ ≫ d.G.hom = d.G.hom ≫ Work.DescentGeom.specGal σ)
    (hφ' : φ' ≫ d.G.hom = d.G.hom ≫ Work.DescentGeom.specGal σ)
    (h : d.AJ.left ≫ φ = d.AJ.left ≫ φ') : φ = φ' :=
  congrArg Over.Hom.left
    (d.epi ((tw (k := k) (k' := k') σ).obj d.G) (semilinOver σ φ hφ) (semilinOver σ φ' hφ')
      (Over.OverMorphism.ext h))

/-- The assignment `σ ↦ galActHom σ` is an action. -/
theorem galActHom_one : d.galActHom (1 : Work.Descent.Gal k k') = 𝟙 d.G.left := by
  refine d.semilin_ext 1 ?_ ?_ ?_
  · rw [galActHom_hom, Work.DescentGeom.specGal_one, Category.comp_id]
  · rw [Category.id_comp, Work.DescentGeom.specGal_one, Category.comp_id]
  · rw [← d.AJ'_compat 1]
    show Work.Descent.galAct C 1 ≫ d.AJ.left = d.AJ.left ≫ 𝟙 d.G.left
    rw [Work.Descent.galAct_one C, Category.id_comp, Category.comp_id]

theorem galActHom_mul (σ τ : Work.Descent.Gal k k') :
    d.galActHom (σ * τ) = d.galActHom σ ≫ d.galActHom τ := by
  refine d.semilin_ext (σ * τ) ?_ ?_ ?_
  · rw [galActHom_hom, Work.DescentGeom.specGal_mul]
  · rw [Category.assoc, d.galActHom_hom τ, ← Category.assoc, d.galActHom_hom σ,
      Category.assoc, ← Work.DescentGeom.specGal_mul]
  · rw [← Category.assoc, ← d.AJ'_compat σ, Category.assoc, ← d.AJ'_compat τ,
      ← Category.assoc, ← Work.Descent.galAct_mul C σ τ, d.AJ'_compat (σ * τ)]

/-- **The semilinear Galois action on the group chunk `G`.** -/
def galAct (σ : Work.Descent.Gal k k') : d.G.left ≅ d.G.left where
  hom := d.galActHom σ
  inv := d.galActHom σ⁻¹
  hom_inv_id := by rw [← galActHom_mul, mul_inv_cancel, galActHom_one]
  inv_hom_id := by rw [← galActHom_mul, inv_mul_cancel, galActHom_one]

theorem galAct_one :
    d.galAct (1 : Work.Descent.Gal k k') = Iso.refl d.G.left :=
  Iso.ext d.galActHom_one

theorem galAct_mul (σ τ : Work.Descent.Gal k k') :
    d.galAct (σ * τ) = (d.galAct σ).trans (d.galAct τ) :=
  Iso.ext (d.galActHom_mul σ τ)

theorem galAct_hom (σ : Work.Descent.Gal k k') :
    (d.galAct σ).hom ≫ d.G.hom = d.G.hom ≫ Work.DescentGeom.specGal σ :=
  d.galActHom_hom σ

/-- The unit of `G` is fixed by the Galois action. -/
theorem psi_pointed (σ : Work.Descent.Gal k k') :
    η[d.G] ≫ d.psi σ = η[(tw (k := k) (k' := k') σ).obj d.G] := by
  refine (cancel_epi (CartesianMonoidalCategory.preservesTerminalIso (bcFun k k')).hom).mp ?_
  rw [← Category.assoc, ← d.AJ_pt, Category.assoc, ← d.psi_spec]
  exact d.fTw_pt σ

/-- `psi σ` is a morphism of group objects (by rigidity: it is pointed). -/
instance psi_isMonHom (σ : Work.Descent.Gal k k') : IsMonHom (d.psi σ) :=
  Work.AbVar.Hom.isMonHom_of_isPointedMap _ (d.psi_pointed σ)

/-- The Galois action fixes the unit of the group law. -/
theorem galAct_one_compat (σ : Work.Descent.Gal k k') :
    Work.DescentGeom.specGal σ ≫ η[d.G].left = η[d.G].left ≫ (d.galAct σ).hom :=
  (tw_eta_left σ d.G).symm.trans (congrArg Over.Hom.left (d.psi_pointed σ)).symm

/-- The tensor square of `psi σ` composed with the multiplication of the twist is the twisted
diagonal action. -/
theorem tensor_psi_mul (σ : Work.Descent.Gal k k') :
    ((d.psi σ) ⊗ₘ (d.psi σ)).left ≫
        (Functor.LaxMonoidal.μ (tw (k := k) (k' := k') σ) d.G d.G).left =
      Work.DescentGeom.galActProd d.G d.galAct d.galAct_hom σ := by
  apply pullback.hom_ext
  · rw [Category.assoc, tw_μ_fst]
    rw [Over.tensorHom_left_fst (fS := Over.hom d.G ≫ (specGalIso σ).hom)
      (fU := Over.hom d.G ≫ (specGalIso σ).hom) (f := d.psi σ) (g := d.psi σ)]
    simp only [Work.DescentGeom.galActProd, Work.DescentGeom.galActProdMap,
      pullback.lift_fst]
    rfl
  · rw [Category.assoc, tw_μ_snd]
    rw [Over.tensorHom_left_snd (fS := Over.hom d.G ≫ (specGalIso σ).hom)
      (fU := Over.hom d.G ≫ (specGalIso σ).hom) (f := d.psi σ) (g := d.psi σ)]
    simp only [Work.DescentGeom.galActProd, Work.DescentGeom.galActProdMap,
      pullback.lift_snd]
    rfl

/-- The Galois action commutes with the group law. -/
theorem galAct_mul_compat (σ : Work.Descent.Gal k k') :
    Work.DescentGeom.galActProd d.G d.galAct d.galAct_hom σ ≫ μ[d.G].left =
      μ[d.G].left ≫ (d.galAct σ).hom := by
  have h := congrArg Over.Hom.left (IsMonHom.mul_hom (d.psi σ))
  simp only [Over.comp_left] at h
  rw [tw_mul_left] at h
  change Work.DescentGeom.galActProd d.G d.galAct d.galAct_hom σ ≫ μ[d.G].left =
    μ[d.G].left ≫ (d.psi σ).left
  rw [h, ← Category.assoc, d.tensor_psi_mul]

/-- The Galois action commutes with the inverse. -/
theorem galAct_inv_compat (σ : Work.Descent.Gal k k') :
    (d.galAct σ).hom ≫ ι[d.G].left = ι[d.G].left ≫ (d.galAct σ).hom := by
  have h := congrArg Over.Hom.left (GrpObj.inv_hom (d.psi σ))
  simp only [Over.comp_left] at h
  rw [tw_inv_left] at h
  exact h.symm

end Chunk

end Gal

end

end Work.JacFinal
