import Mathlib
import Submission.Work.KeyLemma.Sum
import Submission.Work.KeyLemma.Place.placeOfPoint_degree

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.KeyLemma.Sum

/-- The residue degree of the place attached to a `k`-point of a curve is `1`: the residue
field of a `k`-rational point is `k` itself.  This is
`Work.KeyLemma.Place.placeOfPoint_degree`, restated with the `abbrev`
`Work.CurveBasics.Place.degree` unfolded. -/
lemma residueDegree_placeOfPoint {k : Type*} [Field k] (C : Work.CurveBasics.Curve k)
    (p : Work.KeyLemma.Curve.Point C) :
    C.hom.residueDegree (Work.KeyLemma.Curve.placeOfPoint C p).point = 1 :=
  Work.KeyLemma.Place.placeOfPoint_degree C p

theorem deg_toDiv {k : Type*} [Field k] (C : Work.CurveBasics.Curve k)
    (s : Work.KeyLemma.Curve.SumDiv C) :
    C.deg (Work.KeyLemma.Curve.SumDiv.toDiv C s) =
      (Work.KeyLemma.Curve.SumDiv.deg s : ℤ) := by
  rw [Work.KeyLemma.Curve.SumDiv.deg]
  -- `deg` is additive, so it commutes with the `Finsupp.sum` defining `toDiv`.
  have h1 : C.deg (Work.KeyLemma.Curve.SumDiv.toDiv C s)
      = s.sum (fun p m => C.deg
          (Finsupp.single (Work.KeyLemma.Curve.placeOfPoint C p) (m : ℤ) : C.Div)) := by
    rw [Work.KeyLemma.Curve.SumDiv.toDiv, Finsupp.sum]
    exact map_sum C.degHom _ _
  -- Each summand is `m · [κ(Q) : k] = m`, since `Q` is the image of a `k`-point.
  have h2 : s.sum (fun p m => C.deg
        (Finsupp.single (Work.KeyLemma.Curve.placeOfPoint C p) (m : ℤ) : C.Div))
      = s.sum (fun p m => (m : ℤ)) := by
    refine Finsupp.sum_congr ?_
    intro p _
    rw [show (Finsupp.single (Work.KeyLemma.Curve.placeOfPoint C p) ((s p : ℕ) : ℤ) : C.Div)
        = Work.CurveBasics.Curve.Div.single (Work.KeyLemma.Curve.placeOfPoint C p)
            ((s p : ℕ) : ℤ) from rfl]
    rw [Work.CurveBasics.Curve.deg_single, residueDegree_placeOfPoint C p]
    simp
  have h3 : s.sum (fun p m => (m : ℤ)) = ((s.sum fun _ m => m : ℕ) : ℤ) :=
    (Nat.cast_finsupp_sum s (fun _ m => m)).symm
  rw [h1, h2, h3]

end Work.KeyLemma.Sum
