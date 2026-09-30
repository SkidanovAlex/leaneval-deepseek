import Mathlib
import Submission.Work.SymQuot.DivOf.DivOf
import Submission.Work.SymQuot.DivOf.divMap_divOfChart
import Submission.Work.SymQuot.Sym.exists_powMap_eq
import Submission.Work.RiemannRoch.ExportCB
import Submission.Work.SpecLin.Points.ptDiv_deg

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SymQuot.DivOf

universe u
open CategoryTheory Limits AlgebraicGeometry
open scoped Classical
namespace Work.SymQuot.DivOf

set_option linter.style.haveILetI false

/-- **The divisor of a point of `Symⁿ C` has degree `n`.**

Choose a finite extension `F' ⊇ F` over which `p` becomes a sum `powMap x` of `n` points of `C`
(`Sym.exists_finite_lift`).  By the hub lemma C1′ (`divMap_divOfChart`) the base change of the
chart divisor `divOfChart F d` to `F'` is `∑ m, ptDiv (x m)`, and base change of divisors
preserves the degree (`deg_divMap`).  Hence
`deg (divOf F p) = deg (∑ m, ptDiv (x m)) = ∑ m 1 = n`. -/
theorem divOf_deg {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    [NeZero n] [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    (p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F) :
    (C.baseChange F).deg (divOf F p) = n := by
  obtain ⟨F', hF', hAlgK, hAlgF, hTower, _hFin, x, hx⟩ :=
    Work.SymQuot.Sym.exists_finite_lift (K := K) C n p
  letI : Field F' := hF'
  letI : Algebra K F' := hAlgK
  letI : Algebra F F' := hAlgF
  letI : IsScalarTower K F F' := hTower
  haveI hne : Nonempty (Classical.choose
      (exists_chartPt_nonempty (C := C) (n := n) p)).V :=
    Classical.choose_spec (exists_chartPt_nonempty (C := C) (n := n) p)
  have hdiv : divOf F p =
      divOfChart F (Classical.choose (exists_chartPt_nonempty (C := C) (n := n) p)) := by
    rw [divOf]
  rw [hdiv]
  have hsum := divMap_divOfChart (C := C) (F := F) (p := p)
    (Classical.choose (exists_chartPt_nonempty (C := C) (n := n) p)) x hx
  have hdeg := Work.RiemannRoch.Curve.deg_divMap (C := C.baseChange F) (F := F')
    (C' := C.baseChange F') (bcSquareTower (C := C) F F')
    (divOfChart F (Classical.choose (exists_chartPt_nonempty (C := C) (n := n) p)))
  rw [hsum] at hdeg
  have hL : (C.baseChange F').deg (∑ m : Fin n, Work.SpecLin.ptDiv (x m)) = (n : ℤ) := by
    simp only [Work.CurveBasics.Curve.deg, map_sum]
    have : ∀ m : Fin n, (C.baseChange F').degHom (Work.SpecLin.ptDiv (x m)) = 1 :=
      fun m => Work.SpecLin.Points.ptDiv_deg (x m)
    rw [Finset.sum_congr rfl (fun m _ => this m)]
    simp
  rw [hL] at hdeg
  exact hdeg.symm

end Work.SymQuot.DivOf

/-- The statement as requested at the path of this file: the single-namespace form of
`Work.SymQuot.DivOf.Work.SymQuot.DivOf.divOf_deg` (the declaration above, which sits in the
doubly opened namespace inherited from this file's original skeleton). -/
theorem divOf_deg {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    [NeZero n] [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    (p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F) :
    (C.baseChange F).deg (divOf F p) = n :=
  Work.SymQuot.DivOf.Work.SymQuot.DivOf.divOf_deg p

end Work.SymQuot.DivOf
