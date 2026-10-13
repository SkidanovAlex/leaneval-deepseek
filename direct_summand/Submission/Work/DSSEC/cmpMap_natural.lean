import Mathlib
import Submission.Work.DSSEC.Defs

namespace Work.DSSEC

universe u

open CategoryTheory AlgebraicGeometry Limits Opposite
open DSMap DSMap.Mix2

section Aux

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {f : X ⟶ Spec (.of A)} {N : ℕ}
  {i : X ⟶ DSMap.PSpace A N} {W : Type u} [CommRing W] {ψ : A →+* W} {t : Idx.{(u)} N → W}

/-- The comparison at a single index set `S`: the map `Γ(X, ⋂_{m∈S} U_m) → W[J/t_S]` given by
`D.toFun`, as a morphism of `A`-modules (`Work.DSSEC.cmpMap` is this composed with the transport
along `ROpen = IOpen`). -/
noncomputable def cmpNatural_mkOf (D : SecData A X f N i W ψ t) (S : Finset (Idx.{(u)} N))
    (hS : S.Nonempty) :
    (DSMap.cechPresheaf A X f).obj (op (⨅ m ∈ S, DSMap.Mix2.chartCover i m)) ⟶
      (ModuleCat.restrictScalars ψ).obj (ModuleCat.of W (DSMap.Mix2.chartRing t S)) :=
  letI : Algebra A Γ(X, ⨅ m ∈ S, DSMap.Mix2.chartCover i m) :=
    (DSMap.phiU A X f (⨅ m ∈ S, DSMap.Mix2.chartCover i m)).toAlgebra
  letI : Module A (DSMap.Mix2.chartRing t S) := Module.compHom (DSMap.Mix2.chartRing t S) ψ
  ModuleCat.ofHom
    { toFun := fun x => D.toFun S hS x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun a x => by
        show D.toFun S hS ((DSMap.phiU A X f (⨅ m ∈ S, DSMap.Mix2.chartCover i m)) a * x)
          = ψ a • (D.toFun S hS x)
        rw [D.toFun_smul, Algebra.smul_def] }

/-- `Work.DSSEC.cmpMap` is `cmpNatural_mkOf` preceded by the transport along `ROpen = IOpen`. -/
lemma cmpNatural_cmpMap_eq (D : SecData A X f N i W ψ t) (n : ℕ)
    (y : Fin (n + 1) → Idx.{(u)} N) :
    cmpMap D n y = (DSMap.cechPresheaf A X f).map
        (eqToHom (congrArg op (ROpen_eq_IOpen i n y))) ≫
      cmpNatural_mkOf D (SIdx N n y) (SIdx_nonempty N n y) := rfl

/-- The chart restriction `W[J/t_S] → W[J/t_T]` (`S ⊆ T`) as a morphism of `W`-modules. -/
noncomputable abbrev cmpNatural_chartResMod (t : Idx.{(u)} N → W) {S T : Finset (Idx.{(u)} N)}
    (h : S ⊆ T) :
    ModuleCat.of W (DSMap.Mix2.chartRing t S) ⟶ ModuleCat.of W (DSMap.Mix2.chartRing t T) :=
  ModuleCat.ofHom (chartRes t h).toLinearMap

/-- The simplex-level projection `∏ᶜ_{a} chartIdx (y a) → ∏ᶜ_{b} chartIdx (y (g b))` of the
nerve of the chart cover `i ↦ {i}`: the component `φ y` of the `(n+1)`-st coface of the Čech
nerve of the family `chartIdx`. -/
noncomputable def cmpNatural_chartNerve {N : ℕ} {n : ℕ} (g : Fin (n + 1) → Fin (n + 2))
    (y : Fin (n + 2) → Idx.{(u)} N) :
    (∏ᶜ (DSMap.Mix2.chartIdx (Idx.{(u)} N) ∘ y)) ⟶
      (∏ᶜ (DSMap.Mix2.chartIdx (Idx.{(u)} N) ∘ (y ∘ g))) :=
  Pi.lift (fun b => Pi.π (DSMap.Mix2.chartIdx (Idx.{(u)} N) ∘ y) (g b))

/-- The simplex-level projection `∏ᶜ_{a} U_{y a} → ∏ᶜ_{b} U_{y (g b)}` of the nerve of the
chart cover `i ↦ U_i` of `X`. -/
noncomputable def cmpNatural_coverNerve {A : Type u} [CommRing A] {X : Scheme.{u}} {N : ℕ}
    {n : ℕ} (i : X ⟶ DSMap.PSpace A N) (g : Fin (n + 1) → Fin (n + 2))
    (y : Fin (n + 2) → Idx.{(u)} N) :
    (∏ᶜ (DSMap.Mix2.chartCover i ∘ y)) ⟶
      (∏ᶜ (DSMap.Mix2.chartCover i ∘ (y ∘ g))) :=
  Pi.lift (fun b => Pi.π (DSMap.Mix2.chartCover i ∘ y) (g b))

/-- Naturality of the comparison maps with respect to the restriction maps: the comparison at
`S` followed by the chart restriction `W[J/t_S] → W[J/t_T]` (`S ⊆ T`) is the restriction of
sections `Γ(X, U_S) → Γ(X, U_T)` followed by the comparison at `T`.  This is the pointwise
statement `Work.DSSEC.SecData.natural`, packaged as an identity of morphisms of `A`-modules. -/
lemma cmpNatural_mkOf_natural (D : SecData A X f N i W ψ t) (S T : Finset (Idx.{(u)} N))
    (hS : S.Nonempty) (hT : T.Nonempty) (hST : S ⊆ T) :
    cmpNatural_mkOf D S hS ≫ (ModuleCat.restrictScalars ψ).map (cmpNatural_chartResMod t hST) =
      (DSMap.cechPresheaf A X f).map (homOfLE (iInf_chartCover_le i hST)).op ≫
        cmpNatural_mkOf D T hT := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  show (chartRes t hST) (D.toFun S hS x) =
    D.toFun T hT ((X.presheaf.map (homOfLE (iInf_chartCover_le i hST)).op).hom x)
  rw [show hT = (hS.imp fun _ hm => hST hm) from Subsingleton.elim _ _]
  exact (D.natural S T hS hST x).symm

end Aux

/-- Naturality of the comparison maps `Work.DSSEC.cmpMap` with respect to the Čech
differentials: for a simplex `y` of degree `n+1` and a coface `δ a`, the comparison at the
deleted simplex followed by the chart restriction agrees with the restriction of sections
followed by the comparison at `y`. -/
theorem cmpMap_natural {A : Type u} [CommRing A] {X : Scheme.{u}} {f : X ⟶ Spec (.of A)} {N : ℕ}
    {i : X ⟶ DSMap.PSpace A N} {W : Type u} [CommRing W] {ψ : A →+* W} {t : Idx.{(u)} N → W}
    (D : SecData A X f N i W ψ t) (n : ℕ) (a : Fin (n + 2)) (y : Fin (n + 2) → Idx.{(u)} N) :
    cmpMap D n (((FormalCoproduct.mk (Idx.{(u)} N) (DSMap.Mix2.chartIdx (Idx.{(u)} N))).cech.map
        (SimplexCategory.δ a).op).f y) ≫
      (ModuleCat.restrictScalars ψ).map
        ((DSMap.Mix2.chartPresheaf t).map
          (((FormalCoproduct.mk (Idx.{(u)} N) (DSMap.Mix2.chartIdx (Idx.{(u)} N))).cech.map
            (SimplexCategory.δ a).op).φ y).op) =
      (DSMap.cechPresheaf A X f).map
        (((FormalCoproduct.mk (Idx.{(u)} N) (DSMap.Mix2.chartCover i)).cech.map
          (SimplexCategory.δ a).op).φ y).op ≫ cmpMap D (n + 1) y := by
  -- `g` is the underlying map of the coface `δ a : ⦋n⦌ ⟶ ⦋n+1⦌`, so that the deleted simplex is
  -- `y ∘ g` and the nerve projections are the `Pi.lift`s of the projections onto the `g b`.
  set g := (SimplexCategory.Hom.toOrderHom ((SimplexCategory.δ a).op.unop)).toFun with hg
  -- Rewrite the goal into a form in which all the induced maps are written out: `cmpMap` as the
  -- transport `ROpen = IOpen` followed by `cmpNatural_mkOf`, and the nerve projections as
  -- `Pi.lift`s.
  show (DSMap.cechPresheaf A X f).map (eqToHom (congrArg op (ROpen_eq_IOpen i n (y ∘ g))))
        ≫ cmpNatural_mkOf D (SIdx N n (y ∘ g)) (SIdx_nonempty N n (y ∘ g))
        ≫ (ModuleCat.restrictScalars ψ).map
            (cmpNatural_chartResMod t (leOfHom (cmpNatural_chartNerve g y).unop)) =
      (DSMap.cechPresheaf A X f).map (cmpNatural_coverNerve i g y).op
        ≫ (DSMap.cechPresheaf A X f).map (eqToHom (congrArg op (ROpen_eq_IOpen i (n + 1) y)))
        ≫ cmpNatural_mkOf D (SIdx N (n + 1) y) (SIdx_nonempty N (n + 1) y)
  -- naturality of the comparison with respect to `SIdx N n (y ∘ g) ⊆ SIdx N (n+1) y`
  rw [cmpNatural_mkOf_natural D (SIdx N n (y ∘ g)) (SIdx N (n + 1) y)
        (SIdx_nonempty N n (y ∘ g)) (SIdx_nonempty N (n + 1) y)
        (leOfHom (cmpNatural_chartNerve g y).unop)]
  -- regroup: both sides become `F.map (restriction) ≫ cmpNatural_mkOf D (SIdx N (n+1) y) _`
  rw [← Category.assoc, ← Category.assoc]
  rw [← Functor.map_comp, ← Functor.map_comp]
  -- the two restrictions of sections coincide (morphisms in `X.Opens` are subsingleton)
  have h : (eqToHom (congrArg op (ROpen_eq_IOpen i n (y ∘ g))) ≫
      (homOfLE (iInf_chartCover_le i
        (leOfHom (cmpNatural_chartNerve g y).unop))).op) =
      (cmpNatural_coverNerve i g y).op ≫
        eqToHom (congrArg op (ROpen_eq_IOpen i (n + 1) y)) :=
    Subsingleton.elim _ _
  rw [h]

end Work.DSSEC
