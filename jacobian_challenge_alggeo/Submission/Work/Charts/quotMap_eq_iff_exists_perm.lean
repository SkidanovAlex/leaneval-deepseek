import Mathlib
import Submission.Work.Charts.Step3Defs
import Submission.Work.SymQuot.ProdOpen
import Submission.Work.SymQuot.Sym.powMap_eq_iff_exists_perm
import Submission.Work.Charts.section_eq_of_closedPoint_eq
import Submission.Work.Charts.sum_single_eq_iff_exists_perm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

set_option maxHeartbeats 1000000

namespace Work.Charts

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

/-- **`ptPlace` is injective on field points of a curve.**

An `F`-point `p : Spec F ⟶ C` of the curve gives the section `ptLeft p : Spec F ⟶ C_F`
of `C_F ⟶ Spec F` and the place `ptPlace p` (a closed point of `C_F`).  Two points with the
same place are equal: both `ptLeft p` and `ptLeft q` are sections of the separated morphism
`C_F ⟶ Spec F` through the same point, and for a section of `X ⟶ Spec F` the residue field
map `κ(x) → F` is forced (`section_eq_of_closedPoint_eq`). -/
theorem ptPlace_injective {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {F : Type u} [Field F]
    [Algebra K F] : Function.Injective (Work.SpecLin.ptPlace (C := C) (F := F)) := by
  intro p q h
  have hx : Work.SpecLin.ptToPoint p = Work.SpecLin.ptToPoint q :=
    congrArg Work.CurveBasics.Curve.Place.point h
  have hleft : Work.SpecLin.ptLeft p = Work.SpecLin.ptLeft q :=
    section_eq_of_closedPoint_eq ((C.baseChange F).hom) (Work.SpecLin.ptLeft p)
      (Work.SpecLin.ptLeft q) (Work.SpecLin.Points.ptLeft_comp_hom p)
      (Work.SpecLin.Points.ptLeft_comp_hom q) (by simpa [Work.SpecLin.ptToPoint] using hx)
  apply Over.OverMorphism.ext
  rw [← Work.SpecLin.ptLeft_fst p, ← Work.SpecLin.ptLeft_fst q, hleft]

/-- **`ptDiv` is injective on field points of a curve**: an `F`-point of `C` is determined by
the point divisor `[p]` of `C_F`. -/
theorem ptDiv_injective {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {F : Type u} [Field F]
    [Algebra K F] : Function.Injective (Work.SpecLin.ptDiv (C := C) (F := F)) :=
  fun p q h => ptPlace_injective (Work.SpecLin.ptPlace_eq_of_ptDiv_eq h)

/-- **The fibres of the quotient map `C^n ⟶ Sym^n C` are the `S_n`-orbits.**

Two `F`-points `x`, `y` of the `n`-fold product `C^n` of a curve have the same image under the
quotient map `quotMap C n : C^n ⟶ Sym^n C` if and only if they differ by a permutation of the
coordinates.

Since `divOf` is injective, the hypothesis is equivalent to the equality of the divisors
`∑_m [coord x m] = ∑_m [coord y m]`; comparing multiplicities of places turns this into the
existence of a permutation `σ` with `ptPlace (coord y m) = ptPlace (coord x (σ m))`, and
`ptPlace_injective` upgrades this to `coord y m = coord x (σ m)`.  The converse is the
invariance of the quotient map under the permutation of the factors. -/
theorem quotMap_eq_iff_exists_perm {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    (n : ℕ) [Work.SpecLin.DivBase C] [Work.SpecLin.SymGeom C n]
    {F : Type u} [Field F] [Algebra K F] (x y : Work.GCBasics.FPt (Work.Charts.Cprod C n) F) :
    Work.Charts.ptComp x (Work.Charts.quotMap C n) =
        Work.Charts.ptComp y (Work.Charts.quotMap C n) ↔
      ∃ σ : Equiv.Perm (Fin n),
        y = Work.Charts.ptComp x (Work.SymQuot.permIso C.toOver σ).hom := by
  constructor
  · intro h
    -- the two divisor sums agree
    have hdiv : (∑ m : Fin n, Work.SpecLin.ptDiv (Work.Charts.coord x m)) =
        ∑ m : Fin n, Work.SpecLin.ptDiv (Work.Charts.coord y m) := by
      rw [← Work.Charts.divOf_quotMap x, ← Work.Charts.divOf_quotMap y]
      simp only [Work.Charts.ptComp_apply] at h
      rw [h]
    -- hence the multisets of places agree
    have hdiv' : (∑ m : Fin n,
          (Finsupp.single (Work.SpecLin.ptPlace (Work.Charts.coord x m)) (1 : ℤ) :
            (C.baseChange F).Place →₀ ℤ)) =
        ∑ m : Fin n,
          (Finsupp.single (Work.SpecLin.ptPlace (Work.Charts.coord y m)) (1 : ℤ) :
            (C.baseChange F).Place →₀ ℤ) := by
      simpa only [Work.SpecLin.ptDiv, Work.CurveBasics.Curve.Div.place] using hdiv
    obtain ⟨σ, hσ⟩ := (sum_single_eq_iff_exists_perm
      (fun m => Work.SpecLin.ptPlace (Work.Charts.coord x m))
      (fun m => Work.SpecLin.ptPlace (Work.Charts.coord y m))).mp hdiv'
    -- and the coordinates themselves agree up to `σ`
    have hcoord : ∀ m, Work.Charts.coord y m = Work.Charts.coord x (σ m) := fun m =>
      ptPlace_injective (hσ m)
    refine ⟨σ.symm, ?_⟩
    apply Limits.Pi.hom_ext
    intro m
    show y ≫ Work.SymQuot.proj C.toOver n m =
      (x ≫ (Work.SymQuot.permIso C.toOver σ.symm).hom) ≫ Work.SymQuot.proj C.toOver n m
    rw [Category.assoc, Work.SymQuot.Product.permIso_hom_proj]
    exact hcoord m
  · rintro ⟨σ, rfl⟩
    -- the quotient map is invariant under the permutation of the coordinates
    show x ≫ Work.Charts.quotMap C n =
      (x ≫ (Work.SymQuot.permIso C.toOver σ).hom) ≫ Work.Charts.quotMap C n
    apply Work.SpecLin.SymGeom.divOf_injective
    show Work.Charts.divOf (x ≫ Work.Charts.quotMap C n) =
      Work.Charts.divOf ((x ≫ (Work.SymQuot.permIso C.toOver σ).hom) ≫
        Work.Charts.quotMap C n)
    rw [Work.Charts.divOf_quotMap, Work.Charts.divOf_quotMap]
    have hcoord : ∀ m, Work.Charts.coord (x ≫ (Work.SymQuot.permIso C.toOver σ).hom) m =
        Work.Charts.coord x (σ.symm m) := by
      intro m
      rw [Work.Charts.coord, Work.Charts.coord, Category.assoc,
        Work.SymQuot.Product.permIso_hom_proj]
    simp only [hcoord]
    exact (Equiv.sum_comp σ.symm
      (fun m => Work.SpecLin.ptDiv (Work.Charts.coord x m))).symm

end Work.Charts
