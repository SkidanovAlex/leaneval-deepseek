import Mathlib
import Submission.Work.Charts.Step3Defs
import Submission.Work.Charts.mem_basicOpen_iff_evalSection_ne_zero
import Submission.Work.Charts.eval_bnDelta
import Submission.Work.Charts.surjective_quotMap
import Submission.Work.GCBasics.fpt_exists_factor
import Submission.Work.GCBasics.map_landsIn
import Submission.Work.GroupChunk.exists_factor_resPt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 1000000

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.Charts

open Work.CurveBasics
open Work.GCBasics

noncomputable section

variable {K : Type u} [Field K]

/-- **`iOf` is invariant under base change of the field of definition.**

If `p` is an `F`-point of `Sym^g C` and `e : F →ₐ[K] F'` an extension of the field, then
`iOf (divOf p) = iOf (divOf (RPt.map e p))`: the divisor of the base-changed point is the base
change of the divisor (`SymGeom.divOf_map`), `pullK W` is compatible with the base change
(`bc_comp`), and base change of divisors preserves `ℓ` (`hell_bc`). -/
theorem iOf_divOf_map_eq {C : CurveBasics.Curve K} [Work.SpecLin.DivBase C]
    (R : RochData C) [Work.SpecLin.SymGeom C R.g]
    (hell_bc : ∀ {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F']
      (e : F →ₐ[K] F') (D : Work.GCBasics.Dv C F),
      Work.GCBasics.ell C (Work.SpecLin.DivBase.bc e D) = Work.GCBasics.ell C D)
    {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F'] (e : F →ₐ[K] F')
    (p : Work.SpecLin.FPt (Sym C R.g) F) :
    iOf C R.W (Work.SpecLin.SymGeom.divOf (Work.SpecLin.RPt.map e p))
      = iOf C R.W (Work.SpecLin.SymGeom.divOf p) := by
  have hcomp : e.comp (IsScalarTower.toAlgHom K K F) = IsScalarTower.toAlgHom K K F' :=
    AlgHom.ext fun k => by simp
  have hbc : Work.SpecLin.DivBase.bc e
      (Work.SpecLin.DivBase.bc (IsScalarTower.toAlgHom K K F) R.W)
      = Work.SpecLin.DivBase.bc (IsScalarTower.toAlgHom K K F') R.W := by
    rw [← Work.SpecLin.DivBase.bc_comp (IsScalarTower.toAlgHom K K F) e R.W, hcomp]
  have hsub : ∀ (A D : Work.GCBasics.Dv C F),
      Work.SpecLin.DivBase.bc e (A - D)
        = Work.SpecLin.DivBase.bc e A - Work.SpecLin.DivBase.bc e D := by
    intro A D
    rw [sub_eq_add_neg, Work.SpecLin.DivBase.bc_add, Work.SpecLin.DivBase.bc_neg, sub_eq_add_neg]
  show Work.GCBasics.ell C
      (Work.SpecLin.DivBase.bc (IsScalarTower.toAlgHom K K F') R.W
        - Work.SpecLin.SymGeom.divOf (Work.SpecLin.RPt.map e p))
    = Work.GCBasics.ell C
      (Work.SpecLin.DivBase.bc (IsScalarTower.toAlgHom K K F) R.W
        - Work.SpecLin.SymGeom.divOf p)
  rw [Work.SpecLin.SymGeom.divOf_map e p, ← hbc, ← hsub]
  exact hell_bc e _

/-- **Lifting a field point of `Sym^n C` to the product `C^n` over an algebraically closed
field.**  If `F'` is an algebraically closed extension of `F`, every point of `Sym^n C` which
is the base change of an `F`-point is the sum of `n` points of `C`, i.e. the image of an
`F'`-point of `C^n` under the quotient map `quotMap`.

The point `p`'s divisor is an effective divisor of degree `n`, which splits over the
algebraically closed field `F'` into `n` point divisors; the point of `C^n` with those `n`
coordinates has the same divisor as `p`, hence (by `divOf_injective`) the same image. -/
theorem exists_lift_quotMap_of_isAlgClosed {C : CurveBasics.Curve K} (n : ℕ)
    [Work.SpecLin.DivBase C] [Work.SpecLin.SymGeom C n]
    {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [Algebra F F'] [IsScalarTower K F F'] [IsAlgClosed F']
    (p : Work.SpecLin.FPt (Sym C n) F) :
    ∃ q : Work.SpecLin.FPt (Cprod C n) F',
      ptComp q (quotMap C n) = Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K F F') p := by
  obtain ⟨y, hy⟩ := Work.SpecLin.SymGeom.split (C := C) (n := n) (F := F) (F' := F')
    (D := Work.SpecLin.SymGeom.divOf p) (Work.SpecLin.SymGeom.divOf_isEffective p)
    (Work.SpecLin.SymGeom.divOf_deg p)
  let q : Work.SpecLin.FPt (Cprod C n) F' := Limits.Pi.lift (f := fun _ : Fin n => C.toOver) y
  have hcoord : ∀ m : Fin n, coord q m = y m := fun m =>
    Limits.Pi.lift_comp_π (f := fun _ : Fin n => C.toOver) y m
  have hq : ptComp q (quotMap C n) = Work.SpecLin.SymGeom.powMap y := by
    rw [ptComp_apply, quotMap,
      ← Work.SpecLin.SymGeom.powMap_comp q (fun m => Work.SymQuot.proj C.toOver n m)]
    congr 1
    funext m
    exact hcoord m
  refine ⟨q, ?_⟩
  refine Work.SpecLin.SymGeom.divOf_injective _ _ ?_
  rw [hq, Work.SpecLin.SymGeom.divOf_powMap, Work.SpecLin.SymGeom.divOf_map]
  exact hy.symm

/-- **The points of the Brill–Noether chart have `i (divOf p) = 0`.**

Let `g` be the genus, `U ⊆ C` an open, `s_1, …, s_g ∈ Γ(C,U)` sections and
`chartOpen C g U s ⊆ Sym^g C` the Brill–Noether chart of `ChartCg.lean` (the complement of the
image of `C^g ∖ D(δ)`, where `δ = det (s_j(x_m))²`).  Assume the Brill–Noether criterion
`hcrit`: at every field point of `C^g` landing in `U^g` whose evaluation matrix is invertible,
the divisor of the image point in `Sym^g C` has `i = 0`.  Then every field point of `Sym^g C`
landing in the chart has `i (divOf p) = 0`.

The proof never compares two divisors at different fields by hand.  Passing to the algebraic
closure `Ω` of the field of definition `F` — which changes neither `iOf` nor `ℓ`, by
`hell_bc` — the point `p_Ω` lifts to a point `q` of `C^g` (`exists_lift_quotMap_of_isAlgClosed`).
The underlying point of `q` is a lift of the point of the chart, hence lies in `D(δ)`, and the
canonical residue-field point of `C^g` at it has an invertible evaluation matrix
(`eval_bnDelta`, `mem_basicOpen_iff_evalSection_ne_zero`); the criterion `hcrit` gives
`i (divOf (q₀ ≫ quotMap)) = 0` over the residue field `κ(x₀)`, and `iOf_divOf_map_eq` — applied
once along `κ(x₀) ↪ Ω` (the canonical point of `C^g` at `x₀` is a base change of `q`,
`exists_factor_resPt`) and once along `F ↪ Ω` — transports this back to `F`. -/
theorem iOf_eq_zero_of_landsIn_chartOpen {K : Type u} [Field K]
    {C : Work.CurveBasics.Curve K} [Work.SpecLin.DivBase C] (R : Work.Charts.RochData C)
    [Work.SpecLin.SymGeom C R.g] (U : C.left.Opens)
    (s : Fin R.g → (C.left.presheaf.obj (Opposite.op U)))
    (hell_bc : ∀ {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F']
      (e : F →ₐ[K] F') (D : Work.GCBasics.Dv C F),
      Work.GCBasics.ell C (Work.SpecLin.DivBase.bc e D) = Work.GCBasics.ell C D)
    (hcrit : ∀ {F : Type u} [Field F] [Algebra K F]
      (p : Work.GCBasics.FPt (Work.Charts.Cprod C R.g) F)
      (hp : Work.GCBasics.RPt.LandsIn p (Work.Charts.cgOpen C U R.g)),
      (Matrix.det (Matrix.of (fun j m => Work.Charts.evalSection
        (Work.Charts.coord p m).left (Work.Charts.coord_landsIn hp m) (s j)))) ≠ 0 →
        Work.Charts.iOf C R.W (Work.SpecLin.SymGeom.divOf
          (Work.Charts.ptComp p (Work.Charts.quotMap C R.g))) = 0)
    (hclosed : IsClosedMap (Work.Charts.quotMap C R.g).left.base)
    {F : Type u} [Field F] [Algebra K F]
    (p : Work.GCBasics.FPt (Work.Charts.Sym C R.g) F)
    (hp : Work.GCBasics.RPt.LandsIn p (Work.Charts.chartOpen C R.g U s hclosed)) :
    Work.Charts.iOf C R.W (Work.SpecLin.SymGeom.divOf p) = 0 := by
  -- work over the algebraic closure `Ω` of `F`
  let Ω := AlgebraicClosure F
  have hST : IsScalarTower K F Ω := inferInstance
  obtain ⟨q, hq⟩ := exists_lift_quotMap_of_isAlgClosed (C := C) (F' := Ω) R.g p
  -- the underlying point of `q` is a lift of the point of the chart
  let x₀ : (Cprod C R.g).left := (Over.Hom.left q) (IsLocalRing.closedPoint Ω)
  have hx₀ : (Over.Hom.left (quotMap C R.g)) x₀ = (Over.Hom.left p) (IsLocalRing.closedPoint F) := by
    have h := congrArg (fun f : Work.GCBasics.FPt (Sym C R.g) Ω =>
      (Over.Hom.left f) (IsLocalRing.closedPoint Ω)) hq
    have h1 : (Over.Hom.left (ptComp q (quotMap C R.g))) (IsLocalRing.closedPoint Ω)
        = (Over.Hom.left (quotMap C R.g)) x₀ := by
      rw [ptComp_apply, Over.comp_left, Scheme.Hom.comp_apply]
    have h2 : (Over.Hom.left (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K F Ω) p))
          (IsLocalRing.closedPoint Ω)
        = (Over.Hom.left p) (IsLocalRing.closedPoint F) := by
      rw [Work.SpecLin.RPt.map, Over.comp_left, Scheme.Hom.comp_apply]
      exact congrArg (Over.Hom.left p)
        (Work.GCBasics.specOfMap_closedPoint (IsScalarTower.toAlgHom K F Ω))
    exact h1.symm.trans (h.trans h2)
  have hxbn : x₀ ∈ bnOpen C U R.g s := (mem_chartOpen.mp hp) x₀ hx₀
  -- the canonical residue-field point of `C^g` at `x₀` lands in `U^g`
  have h₀ : Work.GCBasics.RPt.LandsIn (Work.GCBasics.resPt (Cprod C R.g) x₀)
      (cgOpen C U R.g) := by
    rw [Work.GCBasics.RPt.landsIn_iff, Work.GCBasics.resPt_apply]
    exact (bnOpen_le (C := C) (U := U) (n := R.g) s) hxbn
  -- its Brill–Noether determinant is invertible
  have hδ : evalSection (Work.GCBasics.resPt (Cprod C R.g) x₀).left h₀ (bnDelta C U R.g s) ≠ 0 :=
    (mem_basicOpen_iff_evalSection_ne_zero x₀ (cgOpen C U R.g) (bnDelta C U R.g s) h₀).mp hxbn
  have hdetsq : (Matrix.det (Matrix.of (fun j m => evalSection
      (coord (Work.GCBasics.resPt (Cprod C R.g) x₀) m).left (coord_landsIn h₀ m) (s j)))) ^ 2
      ≠ 0 := by
    rw [← eval_bnDelta U s (Work.GCBasics.resPt (Cprod C R.g) x₀) h₀]
    exact hδ
  have hdet : (Matrix.det (Matrix.of (fun j m => evalSection
      (coord (Work.GCBasics.resPt (Cprod C R.g) x₀) m).left (coord_landsIn h₀ m) (s j)))) ≠ 0 :=
    fun h => hdetsq (by rw [h]; simp)
  -- the Brill–Noether criterion at the residue-field point
  have hc := hcrit (Work.GCBasics.resPt (Cprod C R.g) x₀) h₀ hdet
  -- the canonical point of `C^g` at `x₀` is a base change of `q`
  obtain ⟨e, he⟩ := Work.GroupChunk.exists_factor_resPt (K := K) (X := Cprod C R.g) q
  have h1 : ptComp q (quotMap C R.g)
      = Work.GCBasics.RPt.map e
          (ptComp (Work.GCBasics.resPt (Cprod C R.g) x₀) (quotMap C R.g)) := by
    simp only [ptComp_apply, Work.GCBasics.RPt.map, he, Category.assoc]
    rfl
  calc iOf C R.W (Work.SpecLin.SymGeom.divOf p)
      = iOf C R.W (Work.SpecLin.SymGeom.divOf
          (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K F Ω) p)) :=
        (iOf_divOf_map_eq R hell_bc (IsScalarTower.toAlgHom K F Ω) p).symm
    _ = iOf C R.W (Work.SpecLin.SymGeom.divOf (ptComp q (quotMap C R.g))) := by rw [hq]
    _ = iOf C R.W (Work.SpecLin.SymGeom.divOf (Work.GCBasics.RPt.map e
          (ptComp (Work.GCBasics.resPt (Cprod C R.g) x₀) (quotMap C R.g)))) := by rw [h1]
    _ = iOf C R.W (Work.SpecLin.SymGeom.divOf
          (ptComp (Work.GCBasics.resPt (Cprod C R.g) x₀) (quotMap C R.g))) :=
        iOf_divOf_map_eq R hell_bc e _
    _ = 0 := hc

end

end Work.Charts
