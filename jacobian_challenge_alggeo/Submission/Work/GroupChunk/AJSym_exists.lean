/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area GC — existence of the Abel–Jacobi morphism `AJSym : Sym^g C ⟶ G D`

For an arbitrary glued group chunk `X : Glued C P0` (the interface of `Glue.lean`) and the
chart datum `D : Input C P0`, this file constructs a morphism

`AJSymHom X : D.Sym D.g ⟶ X.G`

whose class map at every field point is the Abel–Jacobi class `D.picAJ`, i.e.
`X.cls (p ≫ AJSymHom X) = D.picAJ p`.

The construction is the gluing of the local chart maps `Wρ i ⟶ V ⟶ X.G` (where `ρ i` is the
Abel–Jacobi RESID map of `AbelJacobi.lean`) along the open cover of `Sym^g C` by the
transition domains `Wρ i`:

* `AJSym_exists_mem_Wρ`: the `Wρ i` cover `Sym^g C` (COV of area CH + DEFINED of the RESID
  map `ρ i` + `ℓ = 1` on the chart `V`);
* `AJSym_a`/`AJSym_local`: the local chart map on `Wρ i`, obtained by factoring `ρOnW i`
  through the chart `V` (`IsOpenImmersion.lift`), and its class computation
  `AJSym_local_cls`;
* `AJSym_overlap_compat`: the local maps agree on the overlaps `Wρ i ∩ Wρ j` (the two
  composites have the same class at every residue-field point, and the `V`-component of the
  second factors through the first chart, so `hom_ext_of_resPt` applies);
* `AJSym_left`/`AJSymHom`: the glued morphism (`Scheme.Cover.glueMorphisms`) and the
  verification that it is a morphism over `K`;
* `AJSymHom_cls`/`AJSym_exists`: the class of the glued morphism is `picAJ` at every field
  point, which is the statement requested of this file.
-/
import Mathlib
import Submission.Work.GroupChunk.Glue
import Submission.Work.GroupChunk.AbelJacobi
import Submission.Work.GroupChunk.landsIn_aux
import Submission.Work.GroupChunk.sigmaOnW_value

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

universe u

namespace Work.GroupChunk

noncomputable section

open Work.GCBasics

variable {K : Type u} [Field K] {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver}
  [SpecLin.DivBase C]

section AbelJacobiRho

variable [D : Input C P0]

/-- The range of `ρOnW i` is contained in the chart `V`. -/
theorem AJSym_range_ρOnW_le_V (i : D.Idx) :
    Set.range (ρOnW i).left ⊆ Set.range D.V.ι := by
  rw [Scheme.Opens.range_ι]
  have hpre : (Scheme.homOfLE (D.Sym D.g).left (Wρ_le_domain i)
      ≫ (ρPM i).hom) ⁻¹ᵁ D.V = ⊤ := by
    have hS : (ρPM i).hom ⁻¹ᵁ D.V = (ρPM i).domain.ι ⁻¹ᵁ Wρ i := by
      rw [Wρ]
      exact (Scheme.Hom.preimage_image_eq (ρPM i).domain.ι _).symm
    rw [Scheme.Hom.comp_preimage, hS, ← Scheme.Hom.comp_preimage, Scheme.homOfLE_ι,
      Scheme.Opens.ι_preimage_self]
  rintro z ⟨w, rfl⟩
  have h1 : w ∈ (Scheme.homOfLE (D.Sym D.g).left (Wρ_le_domain i)
      ≫ (ρPM i).hom) ⁻¹ᵁ D.V := by
    rw [hpre]; exact trivial
  exact h1

/-- **The value of `ρOnW i` at a field point is the RESID value `ρVal i`.** -/
theorem AJSym_ρOnW_value {F : Type u} [Field F] [Algebra K F]
    (i : D.Idx) (p : FPt (Opens.toOver (Wρ i)) F)
    (hp : RPt.LandsIn (p ≫ Opens.ιOver (Wρ i)) (ρ i).domain) :
    p ≫ ρOnW i = ρVal i (p ≫ Opens.ιOver (Wρ i)) hp := by
  let g : Opens.toOver (Wρ i) ⟶ Opens.toOver (ρ i).domain :=
    Over.homMk (Scheme.homOfLE (D.Sym D.g).left (Wρ_le_domain i)) (by
      change Scheme.homOfLE (D.Sym D.g).left (Wρ_le_domain i) ≫
        (ρPM i).domain.ι ≫ (D.Sym D.g).hom = (Wρ i).ι ≫ (D.Sym D.g).hom
      rw [← Category.assoc, Scheme.homOfLE_ι])
  let q : RPt (Opens.toOver (ρ i).domain) F := p ≫ g
  have hgs : g ≫ Opens.ιOver (ρ i).domain = Opens.ιOver (Wρ i) := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Opens.ιOver_left]
    change Scheme.homOfLE (D.Sym D.g).left (Wρ_le_domain i) ≫ (ρPM i).domain.ι = (Wρ i).ι
    rw [Scheme.homOfLE_ι]
  have hq : q ≫ Opens.ιOver (ρ i).domain = p ≫ Opens.ιOver (Wρ i) := by
    show p ≫ g ≫ Opens.ιOver (ρ i).domain = p ≫ Opens.ιOver (Wρ i)
    rw [hgs]
  have hval := value_left_eq (X := D.Sym D.g) (Y := D.Sym D.g) (hred := inferInstance)
    (hsep := inferInstance) (ρ i) (ρ_isOver i)
    (p ≫ Opens.ιOver (Wρ i)) hp q hq
  apply Over.OverMorphism.ext
  rw [Over.comp_left]
  rw [show (ρOnW i).left = Scheme.homOfLE (D.Sym D.g).left (Wρ_le_domain i)
      ≫ (ρ i).toPartialMap.hom from rfl]
  rw [show (ρVal i (p ≫ Opens.ιOver (Wρ i)) hp).left =
      (value (inferInstance : IsReduced (D.Sym D.g).left)
      (inferInstance : IsSeparated (D.Sym D.g).hom) (ρ i) (ρ_isOver i)
      (p ≫ Opens.ιOver (Wρ i)) hp).left from rfl]
  rw [hval]
  show p.left ≫ (Scheme.homOfLE (D.Sym D.g).left (Wρ_le_domain i) ≫ (ρ i).toPartialMap.hom)
    = (p.left ≫ Scheme.homOfLE (D.Sym D.g).left (Wρ_le_domain i)) ≫ (ρ i).toPartialMap.hom
  rw [Category.assoc]

/-- `x` lies in `Wρ i` if it lies in the domain of `ρ i` and the value of `ρ i` there is in
the chart. -/
theorem AJSym_mem_Wρ_of_domain (i : D.Idx) (x : (D.Sym D.g).left)
    (hx : x ∈ (ρPM i).domain)
    (hV : (ρPM i).hom (⟨x, hx⟩ : (ρPM i).domain) ∈ D.V) : x ∈ Wρ i :=
  (Scheme.Opens.mem_ι_image_iff (U := (ρPM i).domain)
    (V := (ρPM i).hom ⁻¹ᵁ D.V) (x := (⟨x, hx⟩ : (ρPM i).domain))).mpr
    ((Scheme.Hom.mem_preimage (f := (ρPM i).hom)
      (x := (⟨x, hx⟩ : (ρPM i).domain)) (U := D.V)).mpr hV)

/-- **The transition domains `Wρ i` cover `Sym^g C`.** -/
theorem AJSym_exists_mem_Wρ (x : (D.Sym D.g).left) : ∃ i : D.Idx, x ∈ Wρ i := by
  obtain ⟨i, y, hy, hcy⟩ := D.cov (D.picAJ (resPt (D.Sym D.g) x))
  refine ⟨i, ?_⟩
  have hc : D.picOf i y = D.picAJ (resPt (D.Sym D.g) x) := hcy
  have hA : LinEquiv C (D.divOf D.g y - D.divOf D.g (D.EF i))
      (D.divOf D.g (resPt (D.Sym D.g) x) - bcKF (resField (D.Sym D.g) x) D.P0g) := by
    rw [Input.picOf_def, Input.picAJ] at hc
    exact (Pic0.mk_eq_iff _ _).mp hc
  have h2 : LinEquiv C (D.divOf D.g y + bcKF (resField (D.Sym D.g) x) D.P0g)
      (D.divOf D.g (resPt (D.Sym D.g) x) + bcKF (resField (D.Sym D.g) x) (D.EDiv i)) := by
    have h := (linEquiv_add_iff_sub (D.divOf D.g y) (D.divOf D.g (resPt (D.Sym D.g) x))
      (bcKF (resField (D.Sym D.g) x) D.P0g) (D.divOf D.g (D.EF i))).mp hA
    simpa only [Input.EF_divOf] using h
  have hell_y : ell C (D.divOf D.g y) = 1 := ell_of_landsIn_V (D := D) y hy
  have hell : ell C (D.divOf D.g (resPt (D.Sym D.g) x)
      + bcKF (resField (D.Sym D.g) x) (D.EDiv i)
      - bcKF (resField (D.Sym D.g) x) D.P0g) = 1 := by
    have h3 : LinEquiv C (D.divOf D.g y) (D.divOf D.g (resPt (D.Sym D.g) x)
        + bcKF (resField (D.Sym D.g) x) (D.EDiv i)
        - bcKF (resField (D.Sym D.g) x) D.P0g) := by
      have h4 := (LinEquiv.sub_iff (D.divOf D.g y + bcKF (resField (D.Sym D.g) x) D.P0g)
        (D.divOf D.g (resPt (D.Sym D.g) x) + bcKF (resField (D.Sym D.g) x) (D.EDiv i))
        (bcKF (resField (D.Sym D.g) x) D.P0g)).mpr h2
      rw [show D.divOf D.g y + bcKF (resField (D.Sym D.g) x) D.P0g
          - bcKF (resField (D.Sym D.g) x) D.P0g = D.divOf D.g y from by abel] at h4
      exact h4
    rw [← ell_eq_of_linEquiv h3, hell_y]
  have hxdom : x ∈ (ρ i).domain := ρ_mem_domain i x hell
  have hp : RPt.LandsIn (resPt (D.Sym D.g) x) (ρ i).domain :=
    (resPt_landsIn_iff (D.Sym D.g) x (ρ i).domain).mpr hxdom
  have hval := ρ_value i (resPt (D.Sym D.g) x) hp
  have hlin : LinEquiv C (D.divOf D.g (ρVal i (resPt (D.Sym D.g) x) hp)) (D.divOf D.g y) := by
    have h5 : LinEquiv C (D.divOf D.g (ρVal i (resPt (D.Sym D.g) x) hp)
        + bcKF (resField (D.Sym D.g) x) D.P0g)
        (D.divOf D.g y + bcKF (resField (D.Sym D.g) x) D.P0g) := hval.trans h2.symm
    have h6 := (LinEquiv.sub_iff (D.divOf D.g (ρVal i (resPt (D.Sym D.g) x) hp)
        + bcKF (resField (D.Sym D.g) x) D.P0g)
        (D.divOf D.g y + bcKF (resField (D.Sym D.g) x) D.P0g)
        (bcKF (resField (D.Sym D.g) x) D.P0g)).mpr h5
    rw [show D.divOf D.g (ρVal i (resPt (D.Sym D.g) x) hp)
        + bcKF (resField (D.Sym D.g) x) D.P0g
        - bcKF (resField (D.Sym D.g) x) D.P0g
        = D.divOf D.g (ρVal i (resPt (D.Sym D.g) x) hp) from by abel,
      show D.divOf D.g y + bcKF (resField (D.Sym D.g) x) D.P0g
        - bcKF (resField (D.Sym D.g) x) D.P0g = D.divOf D.g y from by abel] at h6
    exact h6
  have hρy : ρVal i (resPt (D.Sym D.g) x) hp = y := by
    have h6 : D.divOf D.g y = D.divOf D.g (ρVal i (resPt (D.Sym D.g) x) hp) :=
      linEquiv_eq_of_ell_eq_one ((D.symGeom D.g).divOf_isEffective y) hell_y
        ((D.symGeom D.g).divOf_isEffective (ρVal i (resPt (D.Sym D.g) x) hp)) hlin.symm
    exact ((D.symGeom D.g).divOf_injective y (ρVal i (resPt (D.Sym D.g) x) hp) h6).symm
  obtain ⟨Q₀, hQ₀, -⟩ := FPt.factor_of_landsIn (ρ i).domain (resPt (D.Sym D.g) x) hp
  have hvl := value_left_eq (X := D.Sym D.g) (Y := D.Sym D.g) (hred := inferInstance)
    (hsep := inferInstance) (ρ i) (ρ_isOver i)
    (resPt (D.Sym D.g) x) hp Q₀ hQ₀
  have hpt : (ρPM i).hom (Q₀.left (IsLocalRing.closedPoint (resField (D.Sym D.g) x)))
      = (ρVal i (resPt (D.Sym D.g) x) hp).left
          (IsLocalRing.closedPoint (resField (D.Sym D.g) x)) := by
    rw [hvl]
    exact Scheme.Hom.comp_apply _ _ _
  have hV' : (ρPM i).hom (Q₀.left (IsLocalRing.closedPoint (resField (D.Sym D.g) x)))
      ∈ D.V := by
    rw [hpt, hρy]
    exact hy
  have hQι : (ρPM i).domain.ι (Q₀.left (IsLocalRing.closedPoint (resField (D.Sym D.g) x)))
      = (resPt (D.Sym D.g) x).left (IsLocalRing.closedPoint (resField (D.Sym D.g) x)) := by
    have h := congrArg (fun f : (specOf K (resField (D.Sym D.g) x)).left
        ⟶ (D.Sym D.g).left => f (IsLocalRing.closedPoint (resField (D.Sym D.g) x)))
      (congrArg Over.Hom.left hQ₀)
    rwa [Over.comp_left, Opens.ιOver_left] at h
  have hdom : Q₀.left (IsLocalRing.closedPoint (resField (D.Sym D.g) x))
      = (⟨x, hxdom⟩ : (ρPM i).domain) := by
    have hι_inj : Function.Injective (ρPM i).domain.ι := fun a b h => Subtype.val_injective h
    refine hι_inj ?_
    rw [hQι]
    exact resPt_apply (D.Sym D.g) x _
  rw [hdom] at hV'
  exact AJSym_mem_Wρ_of_domain i x hxdom hV'

/-- `Opens.toOver D.V` is separated over `K`. -/
instance AJSym_instIsSeparatedV : IsSeparated (Opens.toOver D.V).hom := by
  change IsSeparated (D.V.ι ≫ (D.Sym D.g).hom)
  exact MorphismProperty.IsStableUnderComposition.comp_mem _ _ (by infer_instance)
    (by haveI := D.isProper_Sym D.g; infer_instance)

/-- The open cover of `Sym^g C` by the transition domains `Wρ i`. -/
def AJSym_cover : (D.Sym D.g).left.OpenCover.{u} :=
  Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) D.Idx
    (fun i : D.Idx => (Wρ i : Scheme))
    (fun i => (Wρ i).ι) (fun x => by
      obtain ⟨i, hi⟩ := AJSym_exists_mem_Wρ (D := D) x
      exact ⟨i, ⟨x, hi⟩, rfl⟩)

/-- The pieces of `AJSym_cover` are the inclusions of the `Wρ i`. -/
theorem AJSym_cover_f (i : D.Idx) : (AJSym_cover (D := D)).f i = (Wρ i).ι := rfl

end AbelJacobiRho

section Overlap

variable [D : Input C P0]

/-- The overlap `Wρ i ×_{Sym^g C} Wρ j` as a `K`-scheme. -/
def AJSym_overlap (i j : D.Idx) : Sch K :=
  Over.mk (pullback.fst (Wρ i).ι (Wρ j).ι ≫ (Wρ i).ι ≫ (D.Sym D.g).hom)

/-- The first projection of the overlap. -/
def AJSym_overlapFst (i j : D.Idx) : AJSym_overlap (D := D) i j ⟶ Opens.toOver (Wρ i) :=
  Over.homMk (pullback.fst (Wρ i).ι (Wρ j).ι) rfl

/-- The second projection of the overlap. -/
def AJSym_overlapSnd (i j : D.Idx) : AJSym_overlap (D := D) i j ⟶ Opens.toOver (Wρ j) :=
  Over.homMk (pullback.snd (Wρ i).ι (Wρ j).ι) (by
    change pullback.snd (Wρ i).ι (Wρ j).ι ≫ ((Wρ j).ι ≫ (D.Sym D.g).hom)
      = pullback.fst (Wρ i).ι (Wρ j).ι ≫ (Wρ i).ι ≫ (D.Sym D.g).hom
    rw [← Category.assoc, ← Category.assoc, pullback.condition])

/-- The two projections of the overlap agree after inclusion into `Sym^g C`. -/
theorem AJSym_overlapFst_ι (i j : D.Idx) :
    AJSym_overlapFst (D := D) i j ≫ Opens.ιOver (Wρ i)
      = AJSym_overlapSnd (D := D) i j ≫ Opens.ιOver (Wρ j) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, Opens.ιOver_left, Opens.ιOver_left,
    show (AJSym_overlapFst (D := D) i j).left = pullback.fst (Wρ i).ι (Wρ j).ι from rfl,
    show (AJSym_overlapSnd (D := D) i j).left = pullback.snd (Wρ i).ι (Wρ j).ι from rfl]
  exact pullback.condition

/-- The overlap is reduced. -/
instance AJSym_instIsReducedOverlap (i j : D.Idx) :
    IsReduced (AJSym_overlap (D := D) i j).left := by
  haveI hred : IsReduced (Opens.toOver (Wρ i)).left := isReduced_of_isOpenImmersion (Wρ i).ι
  haveI hred' : IsReduced ((Wρ i).ι ⁻¹ᵁ (Wρ j)) := inferInstance
  exact ObjectProperty.prop_of_iso (fun X : Scheme => IsReduced X)
    (pullbackRestrictIsoRestrict (Wρ i).ι (Wρ j)).symm hred'

end Overlap

namespace Glued

variable [D : Input C P0]

/-- The chart map `Wρ i ⟶ V` underlying the local Abel–Jacobi morphism. -/
def AJSym_a (X : Glued (C := C) (P0 := P0)) (i : D.Idx) : Opens.toOver (Wρ i) ⟶ Opens.toOver D.V :=
  Over.homMk
    (IsOpenImmersion.lift D.V.ι (ρOnW i).left (AJSym_range_ρOnW_le_V (D := D) i)) (by
      change IsOpenImmersion.lift D.V.ι (ρOnW i).left _ ≫ D.V.ι ≫ (D.Sym D.g).hom
        = (Wρ i).ι ≫ (D.Sym D.g).hom
      rw [← Category.assoc, IsOpenImmersion.lift_fac]
      exact Over.w (ρOnW i))

/-- The defining property of `AJSym_a`. -/
theorem AJSym_a_ιOver (X : Glued (C := C) (P0 := P0)) (i : D.Idx) :
    AJSym_a X i ≫ Opens.ιOver D.V = ρOnW i := by
  apply Over.OverMorphism.ext
  simpa only [Over.comp_left, Opens.ιOver_left, AJSym_a, Over.homMk_left]
    using IsOpenImmersion.lift_fac D.V.ι (ρOnW i).left (AJSym_range_ρOnW_le_V (D := D) i)

/-- The local Abel–Jacobi chart morphism on `Wρ i`. -/
def AJSym_local (X : Glued (C := C) (P0 := P0)) (i : D.Idx) :
    Opens.toOver (Wρ i) ⟶ X.G :=
  AJSym_a X i ≫ X.chart i

/-- The class of the local Abel–Jacobi chart map is `picAJ`. -/
theorem AJSym_local_cls (X : Glued (C := C) (P0 := P0)) (i : D.Idx)
    {F : Type u} [Field F] [Algebra K F]
    (q : FPt (Opens.toOver (Wρ i)) F) :
    X.cls (D := D) (q ≫ AJSym_local X i) = D.picAJ (q ≫ Opens.ιOver (Wρ i)) := by
  have hq : (q ≫ AJSym_a X i) ≫ Opens.ιOver D.V = q ≫ ρOnW i := by
    rw [Category.assoc, AJSym_a_ιOver]
  have hcls := X.cls_eq_picOf (D := D)
    (p := (q ≫ AJSym_a X i) ≫ X.chart i) (i := i) (q := q ≫ AJSym_a X i) rfl
  rw [show q ≫ AJSym_local X i = (q ≫ AJSym_a X i) ≫ X.chart i from rfl, hcls, hq]
  have hland : RPt.LandsIn (q ≫ Opens.ιOver (Wρ i)) (Wρ i) := by
    show (q ≫ Opens.ιOver (Wρ i)).left (IsLocalRing.closedPoint F) ∈ Wρ i
    exact (q.left (IsLocalRing.closedPoint F)).property
  have hp : RPt.LandsIn (q ≫ Opens.ιOver (Wρ i)) (ρ i).domain := Wρ_le_domain i hland
  rw [AJSym_ρOnW_value (D := D) i q hp]
  rw [Input.picOf_def, Input.picAJ]
  refine (Pic0.mk_eq_iff _ _).mpr ?_
  rw [Input.EF_divOf]
  exact (linEquiv_add_iff_sub (D.divOf D.g (ρVal i (q ≫ Opens.ιOver (Wρ i)) hp))
    (D.divOf D.g (q ≫ Opens.ιOver (Wρ i))) (bcKF F D.P0g)
    (bcKF F (D.EDiv i))).mpr (ρ_value i (q ≫ Opens.ιOver (Wρ i)) hp)

end Glued

namespace Glued

variable [D : Input C P0]

/-- The two ways of associating `Fst ≫ (a ≫ chart)`. -/
theorem AJSym_assoc (X : Glued (C := C) (P0 := P0)) (i j : D.Idx) :
    AJSym_overlapFst (D := D) i j ≫ AJSym_local X i
      = (AJSym_overlapFst (D := D) i j ≫ AJSym_a X i) ≫ X.chart i := by
  rw [show AJSym_local X i = AJSym_a X i ≫ X.chart i from rfl, Category.assoc]

/-- The classes of the two composites on the overlap agree at every residue-field point. -/
theorem AJSym_overlap_cls (X : Glued (C := C) (P0 := P0)) (i j : D.Idx) (y : (AJSym_overlap (D := D) i j).left) :
    resPt (AJSym_overlap (D := D) i j) y
        ≫ (AJSym_overlapFst (D := D) i j ≫ AJSym_local X i)
      = resPt (AJSym_overlap (D := D) i j) y
        ≫ (AJSym_overlapSnd (D := D) i j ≫ AJSym_local X j) := by
  refine X.cls_injective (D := D) ?_
  simp only [← Category.assoc]
  rw [AJSym_local_cls X i, AJSym_local_cls X j]
  simp only [Category.assoc, AJSym_overlapFst_ι]

/-- The range of the second composite lies in the image of the `i`-th chart. -/
theorem AJSym_overlap_range (X : Glued (C := C) (P0 := P0)) (i j : D.Idx) :
    Set.range (AJSym_overlapSnd (D := D) i j ≫ AJSym_local X j).left
      ⊆ Set.range (X.chart i).left := by
  rintro _ ⟨y, rfl⟩
  have h1 : (AJSym_overlapFst (D := D) i j ≫ AJSym_local X i).left y
      = (AJSym_overlapSnd (D := D) i j ≫ AJSym_local X j).left y := by
    have h := congrArg Over.Hom.left (AJSym_overlap_cls X i j y)
    rw [Over.comp_left, Over.comp_left] at h
    have h2 := congrArg (fun g : (specOf K (resField (AJSym_overlap (D := D) i j) y)).left
        ⟶ X.G.left => g (IsLocalRing.closedPoint (resField (AJSym_overlap (D := D) i j) y))) h
    have h3 : (Over.Hom.left (resPt (AJSym_overlap (D := D) i j) y))
        (IsLocalRing.closedPoint (resField (AJSym_overlap (D := D) i j) y)) = y :=
      resPt_apply (AJSym_overlap (D := D) i j) y _
    calc (AJSym_overlapFst (D := D) i j ≫ AJSym_local X i).left y
        = ((Over.Hom.left (resPt (AJSym_overlap (D := D) i j) y)) ≫
            (AJSym_overlapFst (D := D) i j ≫ AJSym_local X i).left)
            (IsLocalRing.closedPoint (resField (AJSym_overlap (D := D) i j) y)) :=
          ((Scheme.Hom.comp_apply _ _ _).trans (congrArg _ h3)).symm
      _ = ((Over.Hom.left (resPt (AJSym_overlap (D := D) i j) y)) ≫
            (AJSym_overlapSnd (D := D) i j ≫ AJSym_local X j).left)
            (IsLocalRing.closedPoint (resField (AJSym_overlap (D := D) i j) y)) := h2
      _ = (AJSym_overlapSnd (D := D) i j ≫ AJSym_local X j).left y :=
          (Scheme.Hom.comp_apply _ _ _).trans (congrArg _ h3)
  rw [← h1]
  refine ⟨(AJSym_a X i).left ((AJSym_overlapFst (D := D) i j).left y), ?_⟩
  exact (Scheme.Hom.comp_apply (AJSym_a X i).left (X.chart i).left
      ((AJSym_overlapFst (D := D) i j).left y)).symm.trans
    ((Scheme.Hom.comp_apply (AJSym_overlapFst (D := D) i j).left
      (AJSym_local X i).left y).symm)

/-- **The local Abel–Jacobi morphisms agree on the overlaps.** -/
theorem AJSym_overlap_compat (X : Glued (C := C) (P0 := P0)) (i j : D.Idx) :
    AJSym_overlapFst (D := D) i j ≫ AJSym_local X i
      = AJSym_overlapSnd (D := D) i j ≫ AJSym_local X j := by
  haveI : IsOpenImmersion (X.chart i).left := X.isOpenImmersion i
  have hrange := AJSym_overlap_range (D := D) X i j
  let b₀ : (AJSym_overlap (D := D) i j).left ⟶ (Opens.toOver D.V).left :=
    IsOpenImmersion.lift (X.chart i).left
      (AJSym_overlapSnd (D := D) i j ≫ AJSym_local X j).left hrange
  have hb₀ : b₀ ≫ (X.chart i).left
      = (AJSym_overlapSnd (D := D) i j ≫ AJSym_local X j).left :=
    IsOpenImmersion.lift_fac _ _ hrange
  let b : AJSym_overlap (D := D) i j ⟶ Opens.toOver D.V :=
    Over.homMk b₀ (by
      rw [← Over.w (X.chart i), ← Category.assoc, hb₀]
      exact Over.w (AJSym_overlapSnd (D := D) i j ≫ AJSym_local X j))
  have hbv : b ≫ X.chart i = AJSym_overlapSnd (D := D) i j ≫ AJSym_local X j := by
    apply Over.OverMorphism.ext
    exact hb₀
  haveI : Mono (X.chart i) := Over.mono_of_mono_left (X.chart i)
  have key : b = AJSym_overlapFst (D := D) i j ≫ AJSym_a X i := by
    apply hom_ext_of_resPt (K := K)
    intro y
    have h := AJSym_overlap_cls X i j y
    rw [AJSym_assoc X i j] at h
    rw [← hbv] at h
    simp only [← Category.assoc] at h ⊢
    exact ((cancel_mono (X.chart i)).mp h).symm
  rw [AJSym_assoc X i j, ← key, hbv]

end Glued

section Assembly

open Glued

variable [D : Input C P0] (X : Glued (C := C) (P0 := P0))

/-- The compatibility condition for the gluing of the local Abel–Jacobi charts. -/
theorem AJSym_compat (i j : D.Idx) :
    pullback.fst ((AJSym_cover (D := D)).f i) ((AJSym_cover (D := D)).f j)
        ≫ (AJSym_local X i).left
      = pullback.snd ((AJSym_cover (D := D)).f i) ((AJSym_cover (D := D)).f j)
        ≫ (AJSym_local X j).left := by
  have h := congrArg Over.Hom.left (AJSym_overlap_compat X i j)
  show pullback.fst ((AJSym_cover (D := D)).f i) ((AJSym_cover (D := D)).f j)
      ≫ (AJSym_local X i).left
    = pullback.snd ((AJSym_cover (D := D)).f i) ((AJSym_cover (D := D)).f j)
      ≫ (AJSym_local X j).left
  rw [AJSym_cover_f, AJSym_cover_f]
  rw [Over.comp_left, Over.comp_left] at h
  rw [show (AJSym_overlapFst (D := D) i j).left = pullback.fst (Wρ i).ι (Wρ j).ι from rfl,
    show (AJSym_overlapSnd (D := D) i j).left = pullback.snd (Wρ i).ι (Wρ j).ι from rfl] at h
  exact h

/-- The pieces of the cover, as morphisms into `X.G`. -/
noncomputable def AJSym_pieces (i : D.Idx) : (Wρ i : Scheme) ⟶ X.G.left :=
  (AJSym_local X i).left

/-- The compatibility of the pieces. -/
theorem AJSym_pieces_compat : ∀ i j,
    pullback.fst ((AJSym_cover (D := D)).f i) ((AJSym_cover (D := D)).f j) ≫ AJSym_pieces X i
      = pullback.snd ((AJSym_cover (D := D)).f i) ((AJSym_cover (D := D)).f j)
        ≫ AJSym_pieces X j :=
  fun i j => AJSym_compat X i j

/-- The underlying morphism of schemes of the Abel–Jacobi morphism. -/
def AJSym_left : (D.Sym D.g).left ⟶ X.G.left :=
  Scheme.Cover.glueMorphisms (AJSym_cover (D := D)) (AJSym_pieces X) (AJSym_pieces_compat X)

theorem AJSym_left_ι (i : D.Idx) :
    (AJSym_cover (D := D)).f i ≫ AJSym_left X = (AJSym_local X i).left :=
  (Scheme.Cover.ι_glueMorphisms (AJSym_cover (D := D)) (AJSym_pieces X)
    (AJSym_pieces_compat X) i).trans rfl

/-- probe A: associativity by rfl -/
example {A B C D : Sch K} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) :
    (f ≫ g) ≫ h = f ≫ (g ≫ h) := rfl

/-- probe B: AJSym_left_ι as a rewrite -/
example (i : D.Idx) :
    (AJSym_cover (D := D)).f i ≫ AJSym_left X = (AJSym_local X i).left := by
  rw [AJSym_left_ι]

/-- probe C: the assoc step -/
example (i : D.Idx) :
    (AJSym_cover (D := D)).f i ≫ (AJSym_left X ≫ X.G.hom)
      = ((AJSym_cover (D := D)).f i ≫ AJSym_left X) ≫ X.G.hom := rfl

/-- probe D: Category.assoc with parens -/
example (i : D.Idx) :
    (AJSym_cover (D := D)).f i ≫ (AJSym_left X ≫ X.G.hom)
      = ((AJSym_cover (D := D)).f i ≫ AJSym_left X) ≫ X.G.hom :=
  (Category.assoc ((AJSym_cover (D := D)).f i) (AJSym_left X) X.G.hom).symm

/-- The composite of the pieces of the cover with `AJSym_left`. -/
theorem AJSym_left_comp (i : D.Idx) :
    (AJSym_cover (D := D)).f i ≫ (AJSym_left X ≫ X.G.hom)
      = (AJSym_local X i).left ≫ X.G.hom := by
  show ((AJSym_cover (D := D)).f i ≫ AJSym_left X) ≫ X.G.hom
    = (AJSym_local X i).left ≫ X.G.hom
  rw [AJSym_left_ι]
  rfl

/-- The Abel–Jacobi morphism `Sym^g C ⟶ G`. -/
def AJSymHom : D.Sym D.g ⟶ X.G :=
  Over.homMk (AJSym_left X) (by
    refine Scheme.Cover.hom_ext (AJSym_cover (D := D)) _ _ (fun i => ?_)
    exact ((AJSym_left_comp X i).trans (Over.w (AJSym_local X i))).trans
      (congrArg (fun k : (Wρ i : Scheme) ⟶ (D.Sym D.g).left => k ≫ (D.Sym D.g).hom)
        (AJSym_cover_f (D := D) i)).symm)

/-- The Abel–Jacobi morphism restricted to the transition domains. -/
theorem ιOver_AJSymHom (i : D.Idx) :
    Opens.ιOver (Wρ i) ≫ AJSymHom X = AJSym_local X i := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Opens.ιOver_left,
    show (AJSymHom X).left = AJSym_left X from rfl, ← AJSym_cover_f]
  exact AJSym_left_ι X i

/-- The class of `AJSymHom` at a field point is `picAJ`. -/
theorem AJSymHom_cls {F : Type u} [Field F] [Algebra K F] (p : FPt (D.Sym D.g) F) :
    X.cls (D := D) (p ≫ AJSymHom X) = D.picAJ p := by
  obtain ⟨i, hi⟩ := AJSym_exists_mem_Wρ (D := D) (p.left (IsLocalRing.closedPoint F))
  obtain ⟨q, hq, -⟩ := FPt.factor_of_landsIn (Wρ i) p hi
  rw [← hq, Category.assoc, ιOver_AJSymHom]
  exact AJSym_local_cls X i q

end Assembly

theorem AJSym_exists {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : 𝟙_ (Work.GCBasics.Sch K) ⟶ C.toOver} [Work.SpecLin.DivBase C]
    [D : Work.GroupChunk.Input C P0] (X : Work.GroupChunk.Glued (C := C) (P0 := P0)) :
    ∃ AJ : D.Sym D.g ⟶ X.G,
      ∀ {F : Type u} [Field F] [Algebra K F] (p : Work.GCBasics.FPt (D.Sym D.g) F),
        X.cls (D := D) (p ≫ AJ) = D.picAJ p := by
  exact ⟨AJSymHom X, fun p => AJSymHom_cls X p⟩

end

end Work.GroupChunk
