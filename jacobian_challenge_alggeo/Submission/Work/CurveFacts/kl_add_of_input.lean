import Mathlib
import Submission.Work.Universal.Basic
import Submission.Work.Universal.sumMap_powMap
import Submission.Work.SymQuot.SymGeomInst
import Submission.Work.SymQuot.DivBaseInst
import Submission.Work.SymQuot.AddMap
import Submission.Work.GroupChunk.Interface
import Submission.Work.CurveFacts.AddCompat

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.CurveFacts

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical MonObj
open scoped Work.GCBasics

/-- **Item A6 of the closure design, second half: additivity of `Σ f`.**  The conclusion

  `Σ f(E + E') = Σ f(E) · Σ f(E')`

is exactly the type of `Work.Universal.Input.kl_add`; but that type is *not* derivable from the
fields of `Work.GroupChunk.Input` and `Work.Universal.SymQuotData`, so the missing datum is taken
as the explicit hypothesis `hadd`.

**The missing datum.**  The proof needs the morphism identity
`lift p q ≫ D.addMap m n ≫ sumMap D f (m+n) = (p ≫ sumMap D f m) * (q ≫ sumMap D f n)`, which is
invisible to `divOf` and hence is not implied by the only field of `Work.GroupChunk.Input` about
`addMap`, namely `addMap_divOf`.  `hadd` is `Work.CurveFacts.IsAddSumMap` (defined in
`Submission/Work/CurveFacts/AddCompat.lean`), i.e. exactly that identity, uniformly in `m`, `n`,
`f` and the target.  For the concrete symmetric powers of area `SY` it *is* available: the
`powMap`-level form `Work.SymQuot.addMap_spec` (`Submission/Work/SymQuot/AddMap.lean`) together
with `Work.Universal.sumMap_powMap` gives it (`Work.CurveFacts.IsAddSumMapPow`, also in
`AddCompat.lean`).  The corresponding interface repair is to add a field `addMap_powMap` (namely
`Work.SymQuot.addMap_spec`) to `Work.GroupChunk.Input`, or to restate `Input.kl_add` with `hadd`
as an extra hypothesis.

Proof route, given `hadd`.  Let `p : FPt (Sym^n C) F` and `q : FPt (Sym^m C) F` be points with
`divOf p = E` and `divOf q = E'` (`SymGeom.divOf_complete`).  By `D.addMap_divOf` the divisor of
`lift p q ≫ D.addMap n m` is `E + E'`, and `SymGeom.divOf_injective` identifies that point with
the point chosen inside `Work.Universal.sumDiv` by `Classical.choose`; hence
`Work.Universal.sumDiv_eq_of_divOf` gives
`sumDiv D f (E+E') ... = (lift p q ≫ D.addMap n m) ≫ sumMap D f (n+m)`, and `hadd f n m` turns
this into the product `sumDiv D f E ... * sumDiv D f E' ...`. -/
theorem kl_add_of_input {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : 𝟙_ (Work.GCBasics.Sch K) ⟶ C.toOver} [Work.SpecLin.DivBase C]
    (D : Work.GroupChunk.Input C P0) [Work.Universal.SymQuotData C P0 D]
    (hadd : ∀ {A : Work.GCBasics.Sch K} [GrpObj A] [IsCommMonObj A] (f : C.toOver ⟶ A)
      (m n : ℕ), Work.CurveFacts.IsAddSumMap D f m n) :
    ∀ {A : Work.GCBasics.Sch K} [GrpObj A] [IsCommMonObj A] (f : C.toOver ⟶ A) {F : Type u}
      [Field F] [Algebra K F] (E E' : Work.GCBasics.Dv C F) (hE : E.IsEffective)
      (hE' : E'.IsEffective) (n m : ℕ) (hn : Work.GCBasics.Ddeg C F E = (n : ℤ))
      (hm : Work.GCBasics.Ddeg C F E' = (m : ℤ)) (hEE' : (E + E').IsEffective),
      Work.Universal.sumDiv D f (E + E') hEE' (n + m) (Work.Universal.ddeg_add hn hm) =
        Work.Universal.sumDiv D f E hE n hn * Work.Universal.sumDiv D f E' hE' m hm := by
  intro A instGrp instComm f F instField instAlg E E' hE hE' n m hn hm hEE'
  -- Points of `Sym^n C` and `Sym^m C` whose divisors are `E` and `E'`.
  obtain ⟨p, hp⟩ := (D.symGeom n).divOf_complete E hE hn
  obtain ⟨q, hq⟩ := (D.symGeom m).divOf_complete E' hE' hm
  -- `D.addMap_divOf` computes the divisor of `lift p q ≫ D.addMap n m` as `E + E'`.
  have hdiv : (D.symGeom (n + m)).divOf
      (CartesianMonoidalCategory.lift p q ≫ D.addMap n m) = E + E' := by
    have h := D.addMap_divOf n m p q (𝟙 (Work.GCBasics.specOf K F))
    simp only [Category.id_comp, CartesianMonoidalCategory.liftEquiv_apply] at h
    rw [hp, hq] at h
    exact h
  -- Hence each of the three sums is the value of the corresponding `sumMap`.
  have h1 : Work.Universal.sumDiv D f (E + E') hEE' (n + m)
        (Work.Universal.ddeg_add hn hm)
      = (CartesianMonoidalCategory.lift p q ≫ D.addMap n m) ≫
        Work.Universal.sumMap D f (n + m) :=
    Work.Universal.sumDiv_eq_of_divOf D f hEE' (Work.Universal.ddeg_add hn hm) hdiv
  have h3 : Work.Universal.sumDiv D f E hE n hn = p ≫ Work.Universal.sumMap D f n :=
    Work.Universal.sumDiv_eq_of_divOf D f hE hn hp
  have h4 : Work.Universal.sumDiv D f E' hE' m hm = q ≫ Work.Universal.sumMap D f m :=
    Work.Universal.sumDiv_eq_of_divOf D f hE' hm hq
  rw [h1, h3, h4]
  exact hadd f n m p q

end Work.CurveFacts
