import Mathlib
import Submission.Work.Charts.Step3Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.Charts

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical MonoidalCategory
open Work.CurveBasics Work.GCBasics

universe u

noncomputable section

/-- **Base change of the point divisor `[p]`.**

For an `F`-point `q` of the curve `C` over `K` and a `K`-algebra map `e : K →ₐ[K] F`, the
point divisor of the base-changed point `RPt.map e q` is the base change of `ptDiv q`.  The
proof goes through `Sym^1 C`: `ptDiv` is `divOf ∘ powMap` (`SymGeom.divOf_powMap` at `n = 1`),
`divOf` commutes with base change (`SymGeom.divOf_map`) and `powMap` is natural
(`SymGeom.powMap_comp`). -/
theorem ptDiv_map_bc {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    [Work.SpecLin.DivBase C] (symGeom : ∀ n, Work.SpecLin.SymGeom C n)
    {F : Type u} [Field F] [Algebra K F] (e : K →ₐ[K] F)
    (q : Work.SpecLin.CurveFPt C K) :
    Work.SpecLin.ptDiv (Work.SpecLin.RPt.map e q)
      = Work.SpecLin.DivBase.bc e (Work.SpecLin.ptDiv q) := by
  have hq : Work.SpecLin.ptDiv q
      = (symGeom 1).divOf ((symGeom 1).powMap (fun _ : Fin 1 => q)) := by
    rw [(symGeom 1).divOf_powMap (fun _ : Fin 1 => q), Fin.sum_univ_one]
  rw [hq]
  rw [← (symGeom 1).divOf_map e ((symGeom 1).powMap (fun _ : Fin 1 => q))]
  rw [show Work.SpecLin.RPt.map e ((symGeom 1).powMap (fun _ : Fin 1 => q))
        = (symGeom 1).powMap (fun _ : Fin 1 => Work.SpecLin.RPt.map e q) from ?_]
  · rw [(symGeom 1).divOf_powMap (fun _ : Fin 1 => Work.SpecLin.RPt.map e q),
      Fin.sum_univ_one]
  · show Work.SpecLin.specOfMap (K := K) e ≫ (symGeom 1).powMap (fun _ : Fin 1 => q)
      = (symGeom 1).powMap (fun _ : Fin 1 => Work.SpecLin.specOfMap (K := K) e ≫ q)
    rw [← (symGeom 1).powMap_comp (Work.SpecLin.specOfMap (K := K) e) (fun _ : Fin 1 => q)]

/-- **The base change of the base point is the constant point.**

The base point `toCurveFPt P0 = toUnit (specOf K K) ≫ P0` of `C` over `K`, base changed
along `e : K →ₐ[K] F`, is the composite of the structure map `Spec F ⟶ 𝟙_ (Sch K)` with
`P0`: the two differ only by the (unique) map from `Spec F` to the terminal object. -/
theorem RPt_map_toCurveFPt {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    (P0 : Work.Charts.unitSch K ⟶ C.toOver) {F : Type u} [Field F] [Algebra K F]
    (e : K →ₐ[K] F) :
    Work.SpecLin.RPt.map e (Work.Charts.toCurveFPt P0)
      = Work.Charts.toUnit (Work.GCBasics.specOf K F) ≫ P0 := by
  show Work.SpecLin.specOfMap (K := K) e ≫
      (Work.Charts.toUnit (Work.GCBasics.specOf K K) ≫ P0) = _
  rw [← Category.assoc]
  rw [Work.Charts.toUnit_unique
        (Work.SpecLin.specOfMap (K := K) e ≫ Work.Charts.toUnit (Work.GCBasics.specOf K K))
        (Work.Charts.toUnit (Work.GCBasics.specOf K F))]

theorem divOf_constMap {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    [Work.SpecLin.DivBase C] (symGeom : ∀ n, Work.SpecLin.SymGeom C n) (n : ℕ)
    (P0 : Work.Charts.unitSch K ⟶ C.toOver) {T : Work.GCBasics.Sch K}
    {F : Type u} [Field F] [Algebra K F] (p : Work.GCBasics.FPt T F) :
    (symGeom n).divOf (Work.Charts.ptComp p (Work.Charts.constMap symGeom n P0 T)) =
      (n : ℤ) • Work.Charts.pullK C (Work.Charts.P0DivOf P0) := by
  have hpow : Work.Charts.ptComp p (Work.Charts.constMap symGeom n P0 T)
      = (symGeom n).powMap (fun _ : Fin n =>
          Work.Charts.toUnit (Work.GCBasics.specOf K F) ≫ P0) := by
    show p ≫ (symGeom n).powMap (fun _ : Fin n => Work.Charts.toUnit T ≫ P0) = _
    rw [← (symGeom n).powMap_comp p (fun _ : Fin n => Work.Charts.toUnit T ≫ P0)]
    congr 1
    funext m
    rw [← Category.assoc, Work.Charts.comp_toUnit p]
  have hP0 : Work.Charts.pullK C (Work.Charts.P0DivOf P0)
      = Work.SpecLin.ptDiv (Work.Charts.toUnit (Work.GCBasics.specOf K F) ≫ P0) := by
    show Work.SpecLin.DivBase.bc (IsScalarTower.toAlgHom K K F)
        (Work.Charts.P0DivOf P0) = _
    rw [show Work.Charts.P0DivOf P0
        = Work.SpecLin.ptDiv (Work.Charts.toCurveFPt P0) from rfl]
    rw [← ptDiv_map_bc (C := C) symGeom (IsScalarTower.toAlgHom K K F)
        (Work.Charts.toCurveFPt P0)]
    rw [RPt_map_toCurveFPt (C := C) P0 (IsScalarTower.toAlgHom K K F)]
  rw [hpow, (symGeom n).divOf_powMap
      (fun _ : Fin n => Work.Charts.toUnit (Work.GCBasics.specOf K F) ≫ P0)]
  rw [hP0]
  rw [show ∑ m : Fin n,
        Work.SpecLin.ptDiv (Work.Charts.toUnit (Work.GCBasics.specOf K F) ≫ P0)
      = n • Work.SpecLin.ptDiv
          (Work.Charts.toUnit (Work.GCBasics.specOf K F) ≫ P0) from by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]]
  rw [← Nat.cast_smul_eq_nsmul ℤ n
      (Work.SpecLin.ptDiv (Work.Charts.toUnit (Work.GCBasics.specOf K F) ≫ P0))]

end

end Work.Charts
