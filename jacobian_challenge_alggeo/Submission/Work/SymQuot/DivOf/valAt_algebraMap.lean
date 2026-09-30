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

namespace Work.SymQuot.DivOf

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

open Work.CurveBasics

/-- **The value of a structure constant at an `F`-point.**  For an `F`-point `s : Spec F ⟶ C` of a
curve `C` over `K`, an open `U ⊆ C` containing its image and `c : K`, pulling back the structure
constant `algebraMap K Γ(C,U) c` along `s` and reading the result in `F` through `Γ(Spec F) ≅ F`
returns `algebraMap K F c`.

This is the compatibility, on sections, of the pullback along the `K`-morphism `s` with the
structure maps `K ⟶ Γ(C,U)` and `K ⟶ F`. -/
lemma appLE_algebraMap_sections {K : Type u} [Field K] {C : Curve K}
    {F : Type u} [Field F] [Algebra K F] (s : Work.SpecLin.CurveFPt C F) (U : C.left.Opens)
    (hU : ⊤ ≤ s.left ⁻¹ᵁ U) (c : K) :
    (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom
      ((Scheme.Hom.appLE s.left U ⊤ hU).hom (algebraMap K Γ(C.left, U) c)) =
      algebraMap K F c := by
  -- Combine `C.hom.appLE ⊤ U` with `s.left.appLE U ⊤` into a single `appLE` of
  -- `s.left ≫ C.hom`, using functoriality of `appLE`.
  have hmid : C.hom.appLE (⊤ : (Spec (CommRingCat.of K)).Opens) U le_top ≫
      Scheme.Hom.appLE s.left U ⊤ hU
      = Scheme.Hom.appLE (s.left ≫ C.hom) ⊤ ⊤ (le_top : ⊤ ≤ (s.left ≫ C.hom) ⁻¹ᵁ ⊤) :=
    Scheme.Hom.appLE_comp_appLE (f := s.left) (g := C.hom) (U := ⊤) (V := U) (W := ⊤)
      le_top hU
  -- The whole composite, as a map `K ⟶ F`, is `algebraMap K F`.
  have hkey : (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
      C.hom.appLE (⊤ : (Spec (CommRingCat.of K)).Opens) U le_top ≫
      (Scheme.Hom.appLE s.left U ⊤ hU) ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom =
      CommRingCat.ofHom (algebraMap K F) := by
    rw [← Category.assoc (Scheme.Hom.appLE C.hom ⊤ U le_top)
        (Scheme.Hom.appLE s.left U ⊤ hU) (Scheme.ΓSpecIso (CommRingCat.of F)).hom]
    rw [hmid]
    -- `s` is a morphism over `Spec K`
    rw [Over.w s]
    -- on global sections, `appLE` of the structure morphism is `appTop`
    rw [show Scheme.Hom.appLE ((Work.SpecLin.specOf (K := K) F).hom) ⊤ ⊤ _ =
        Scheme.Hom.appTop ((Work.SpecLin.specOf (K := K) F).hom) from
      Scheme.Hom.appLE_eq_app _]
    -- the structure morphism of `specOf F` is `Spec.map (algebraMap K F)`
    rw [show (Work.SpecLin.specOf (K := K) F).hom =
        Spec.map (CommRingCat.ofHom (algebraMap K F)) from rfl]
    -- `ΓSpecIso` naturality
    rw [← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap K F))]
    simp
  have h := congrArg (fun (m : CommRingCat.of K ⟶ CommRingCat.of F) => m.hom c) hkey
  rw [RingHom.algebraMap_toAlgebra, CommRingCat.comp_apply]
  exact h

theorem valAt_algebraMap {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    [NeZero n] [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F}
    (d : Work.SymQuot.DivOf.ChartPt C n p) (x : Fin n → Work.SpecLin.CurveFPt C F)
    (h : Work.SymQuot.DivOf.LandsInChart d x) (m : Fin n) (k : K) :
    Work.SymQuot.DivOf.valAt d x h m
      (algebraMap K (C.left.presheaf.obj (Opposite.op d.V)) k) = algebraMap K F k := by
  -- The `m`-th point `x m` lands in `d.V`, since the lift lands in `d.openOf = piOpen C.toOver d.V n`.
  have hsle : ⊤ ≤ (x m).left ⁻¹ᵁ d.V := by
    intro z _
    have hfac : Over.Hom.left (Limits.Pi.lift x) ≫
        Over.Hom.left (Work.SymQuot.proj C.toOver n m) = Over.Hom.left (x m) := by
      simpa only [Over.comp_left] using congrArg Over.Hom.left (Limits.Pi.lift_comp_π x m)
    have hz : (Limits.Pi.lift x).left z ∈ d.openOf := h trivial
    have hz' : (Work.SymQuot.proj C.toOver n m).left ((Limits.Pi.lift x).left z) ∈ d.V :=
      Work.SymQuot.mem_piOpen.mp hz m
    have hcomp : (Work.SymQuot.proj C.toOver n m).left ((Limits.Pi.lift x).left z) =
        (x m).left z := by
      rw [← hfac, Scheme.Hom.comp_apply]
      rfl
    rwa [hcomp] at hz'
  rw [valAt_eq_GammaSpecIso_apply d x h m hsle
      (algebraMap K (C.left.presheaf.obj (Opposite.op d.V)) k)]
  exact appLE_algebraMap_sections (x m) d.V hsle k

end Work.SymQuot.DivOf
