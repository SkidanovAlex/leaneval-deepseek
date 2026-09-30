import Mathlib
import Submission.Work.SymQuot.DivOf.powMapAux
import Submission.Work.SymQuot.DivOf.mem_placeIdeal_valAt_sub

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot.DivOf

/-- **A morphism `Spec F ⟶ X` whose image lies in an affine open `W` is recovered from its
pullback of sections.**

If `σ : Spec F ⟶ X` maps into the affine open `W` and `ρ : Γ(X,W) →+* F` denotes the ring map
"pull back a section along `σ`, then read the result in `F`", then composing `Spec.map ρ` with
the canonical morphism `Spec Γ(X,W) ⟶ X` recovers `σ`.  (Equivalently `Γ(X,W) →+* F` determines
the morphism `Spec F ⟶ Spec Γ(X,W) ≅ W`, hence `σ`.) -/
theorem spec_map_ofHom_appLE_eq {F : Type u} [Field F] {X : Scheme.{u}} (W : X.Opens)
    (hW : IsAffineOpen W) (σ : Spec (CommRingCat.of F) ⟶ X) (hsle : ⊤ ≤ σ ⁻¹ᵁ W) :
    Spec.map (CommRingCat.ofHom ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.comp
      ((Scheme.Hom.appLE σ W ⊤ hsle).hom))) ≫ hW.fromSpec = σ := by
  have h1 : CommRingCat.ofHom ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.comp
      ((Scheme.Hom.appLE σ W ⊤ hsle).hom))
      = Scheme.Hom.appLE σ W ⊤ hsle ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom := by
    first | rfl | (erw [CommRingCat.ofHom_hom]; rfl)
  rw [h1, Spec.map_comp, Category.assoc,
    IsAffineOpen.SpecMap_appLE_fromSpec σ hW (isAffineOpen_top _) hsle]
  have h2 : Spec.map (Scheme.ΓSpecIso (CommRingCat.of F)).hom
      = (Spec (CommRingCat.of F)).isoSpec.hom := (Scheme.isoSpec_Spec_hom _).symm
  rw [← Category.assoc, IsAffineOpen.fromSpec_top, h2, Iso.hom_inv_id, Category.id_comp]

theorem exists_valAt_ne {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    [NeZero n] [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F}
    (d : Work.SymQuot.DivOf.ChartPt C n p) (x : Fin n → Work.SpecLin.CurveFPt C F)
    (h : Work.SymQuot.DivOf.LandsInChart d x)
    (hs : ∀ m : Fin n, Set.range (x m).left.base ⊆ (d.V : Set C.left))
    {m m' : Fin n} (hm : x m ≠ x m') :
    ∃ b : C.left.presheaf.obj (Opposite.op d.V),
      Work.SymQuot.DivOf.valAt d x h m b ≠ Work.SymQuot.DivOf.valAt d x h m' b := by
  classical
  -- Suppose no section separates the two points: then `valAt` agrees at `m` and `m'`.
  by_contra hcon
  have hcon' : ∀ b, valAt d x h m b = valAt d x h m' b := fun b => by
    by_contra hb
    exact hcon ⟨b, hb⟩
  -- Each point of `x` has its image in the affine chart `d.V`.
  have hsle : ∀ m : Fin n, ⊤ ≤ Over.Hom.left (x m) ⁻¹ᵁ d.V :=
    fun m y _ => hs m ⟨y, rfl⟩
  -- The value map `valAt` at `m` is the pullback of chart sections along the `F`-point `x m`.
  let ρ : Fin n → C.left.presheaf.obj (Opposite.op d.V) →+* F := fun m =>
    (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.comp
      ((Scheme.Hom.appLE (Over.Hom.left (x m)) d.V ⊤ (hsle m)).hom)
  have hval : ∀ m, valAt d x h m = ρ m := fun m => RingHom.ext (fun b =>
    valAt_eq_GammaSpecIso_apply d x h m (hsle m) b)
  -- The ring map `ρ m` recovers the morphism `x m` through the chart.
  have hfac : ∀ m, Spec.map (CommRingCat.ofHom (ρ m)) ≫ d.isAffineOpen_V.fromSpec
      = Over.Hom.left (x m) :=
    fun m => spec_map_ofHom_appLE_eq d.V d.isAffineOpen_V (Over.Hom.left (x m)) (hsle m)
  -- Hence the two ring maps agree, so the two morphisms do.
  have hρeq : ρ m = ρ m' := by
    rw [← hval m, ← hval m']
    exact RingHom.ext hcon'
  have hleft : Over.Hom.left (x m) = Over.Hom.left (x m') := by
    rw [← hfac m, ← hfac m', hρeq]
  exact hm (Over.OverMorphism.ext hleft)

end Work.SymQuot.DivOf
