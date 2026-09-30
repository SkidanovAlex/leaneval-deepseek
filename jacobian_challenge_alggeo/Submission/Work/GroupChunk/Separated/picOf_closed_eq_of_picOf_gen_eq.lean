import Mathlib
import Submission.Work.GroupChunk.Defs
import Submission.Work.GroupChunk.landsIn_aux
import Submission.Work.SpecLin.All
import Submission.Work.GroupChunk.Glue

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.GroupChunk.Separated

universe u
open CategoryTheory in
theorem picOf_closed_eq_of_picOf_gen_eq {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : MonoidalCategoryStruct.tensorUnit (Work.GCBasics.Sch K) ⟶ C.toOver}
    [Work.SpecLin.DivBase C]
    (D : Work.GroupChunk.Input C P0) {R : Type u} [CommRing R] [IsDomain R]
    [ValuationRing R] [Algebra K R] {A C' : Work.GCBasics.RPt (D.Sym D.g) R} {i j : D.Idx}
    (h : D.picOf i (Work.GCBasics.genPt (K := K) R ≫ A)
       = D.picOf j (Work.GCBasics.genPt (K := K) R ≫ C')) :
    D.picOf i (Work.GCBasics.closedPt (K := K) R ≫ A)
      = D.picOf j (Work.GCBasics.closedPt (K := K) R ≫ C') := by
  -- The generic fibre, as a linear equivalence of divisors of degree `2g` on `Sym^{2g} C`.
  have hF : Work.SpecLin.LinEquiv C
      ((D.symGeom (D.g + D.g)).divOf
        (Work.SpecLin.genPt (K := K) R ≫ (A ≫ Work.GroupChunk.addE (D := D) j)))
      ((D.symGeom (D.g + D.g)).divOf
        (Work.SpecLin.genPt (K := K) R ≫ (C' ≫ Work.GroupChunk.addE (D := D) i))) := by
    have h1 := (Work.GroupChunk.picOf_eq_iff' (D := D) i j
      (Work.GCBasics.genPt (K := K) R ≫ A)
      (Work.GCBasics.genPt (K := K) R ≫ C')).mp h
    rw [Work.GroupChunk.Input.EF_divOf (D := D) j,
        Work.GroupChunk.Input.EF_divOf (D := D) i] at h1
    rw [← Work.GroupChunk.divOf_addE (D := D) j (Work.GCBasics.genPt (K := K) R ≫ A),
        ← Work.GroupChunk.divOf_addE (D := D) i (Work.GCBasics.genPt (K := K) R ≫ C')] at h1
    rw [← Category.assoc]
    exact h1
  -- Specialisation of linear equivalence (SPEC-LIN) applied to `Sym^{2g} C`.
  have hG := Work.SpecLin.specLin (K := K) (C := C) (n := D.g + D.g)
    (D.symGeom (D.g + D.g)) R
    (A ≫ Work.GroupChunk.addE (D := D) j) (C' ≫ Work.GroupChunk.addE (D := D) i) hF
  -- Back to the fibre over the residue field.
  refine (Work.GroupChunk.picOf_eq_iff' (D := D) i j
    (Work.GCBasics.closedPt (K := K) R ≫ A)
    (Work.GCBasics.closedPt (K := K) R ≫ C')).mpr ?_
  have hcp : Work.SpecLin.closedPt (K := K) R = Work.GCBasics.closedPt (K := K) R := rfl
  rw [hcp] at hG
  rw [← Category.assoc, ← Category.assoc] at hG
  rw [Work.GroupChunk.divOf_addE (D := D) j (Work.GCBasics.closedPt (K := K) R ≫ A),
      Work.GroupChunk.divOf_addE (D := D) i (Work.GCBasics.closedPt (K := K) R ≫ C')] at hG
  rw [← Work.GroupChunk.Input.EF_divOf (D := D) j,
      ← Work.GroupChunk.Input.EF_divOf (D := D) i] at hG
  exact hG

end Work.GroupChunk.Separated
