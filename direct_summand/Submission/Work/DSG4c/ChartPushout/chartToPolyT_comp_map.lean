import Mathlib
import Submission.Work.DSG4c.ChartPushout.DefsT

/-!
# Chart pushout (area DSG4c): functoriality in the coefficients of the chart identification

The identification of the `i`-th standard chart of `ℙᴺ_A` with the polynomial ring
`A[x_j : j ≠ i]` (file `Defs.lean`) and its counterpart over `A'` (file `DefsT.lean`) are
compatible with coefficient extension: the square

```
A[x_j : j ≠ i]   --chartToPolyT-->   Away (PGr A' N) (coeffExt ψ (X i))
      |                                        ^
    map ψ                                      | awayMapChart
      v                                        |
A'[x_j : j ≠ i]  --chartToPoly---->  Away (PGr A N) (X i)
```

commutes.  This is the ring-theoretic statement underlying the compatibility of the chart
identifications of `ℙᴺ_A` and `ℙᴺ_{A'}` with the base change morphism.
-/

open CategoryTheory AlgebraicGeometry Limits MvPolynomial

namespace Work.DSG4c.ChartPushout

universe u

section

variable (A A' : Type u) [CommRing A] [CommRing A'] (ψ : A →+* A') (N : ℕ) (i : Fin (N+1))

/-- Values of the induced map of chart rings on the structure homomorphisms: the square of
structure maps of the two charts commutes. -/
lemma awayMapChart_chartMap (a : A) :
    (Work.DSG4c.awayMapChart A A' ψ N i) (Work.DSG4c.chartMap A N i a) =
      Work.DSG4c.chartMapT A A' ψ N i (ψ a) := by
  -- Both sides, evaluated on a constant, land in degree `0`; the only substantive input is that
  -- coefficient extension commutes with the structure maps of the two graded polynomial rings.
  have key : (Work.DSG4c.coeffExt A A' ψ N)
        (((algebraMap A (DSMap.PGr A N 0) a : DSMap.PGr A N 0) :
            MvPolynomial (Fin (N+1)) A))
      = ((algebraMap A' (DSMap.PGr A' N 0) (ψ a) : DSMap.PGr A' N 0) :
            MvPolynomial (Fin (N+1)) A') := by
    rw [SetLike.GradeZero.coe_algebraMap (DSMap.PGr A N),
      SetLike.GradeZero.coe_algebraMap (DSMap.PGr A' N),
      MvPolynomial.algebraMap_eq, MvPolynomial.algebraMap_eq,
      Work.DSG4c.coeffExt_apply, MvPolynomial.map_C]
  have h1 : Work.DSG4c.chartMap A N i a
      = HomogeneousLocalization.Away.mk (DSMap.PGr A N) (X_mem A N i) 0
          (algebraMap A (DSMap.PGr A N 0) a) (algebraMap A (DSMap.PGr A N 0) a).2 := rfl
  have h2 : Work.DSG4c.chartMapT A A' ψ N i (ψ a)
      = HomogeneousLocalization.Away.mk (DSMap.PGr A' N)
          ((Work.DSG4c.coeffExt A A' ψ N).map_mem (X_mem A N i)) 0
          (algebraMap A' (DSMap.PGr A' N 0) (ψ a))
          (algebraMap A' (DSMap.PGr A' N 0) (ψ a)).2 := rfl
  rw [h1, h2, Work.DSG4c.awayMapChart, HomogeneousLocalization.Away.map_mk]
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk]
  simp only [pow_zero]
  rw [key]

end

theorem chartToPolyT_comp_map (A A' : Type u) [CommRing A] [CommRing A'] (ψ : A →+* A')
    (N : ℕ) (i : Fin (N+1)) :
    (Work.DSG4c.ChartPushout.chartToPolyT A A' ψ N i).comp (MvPolynomial.map ψ) =
      (Work.DSG4c.awayMapChart A A' ψ N i).comp (Work.DSG4c.ChartPushout.chartToPoly A N i) := by
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
  · rw [RingHom.comp_apply, RingHom.comp_apply, MvPolynomial.map_C,
      Work.DSG4c.ChartPushout.chartToPolyT_C, Work.DSG4c.ChartPushout.chartToPoly_C,
      awayMapChart_chartMap]
  · rw [RingHom.comp_apply, RingHom.comp_apply, MvPolynomial.map_X,
      Work.DSG4c.ChartPushout.chartToPolyT_X, Work.DSG4c.ChartPushout.chartToPoly_X,
      awayMapChart_chartElem]

end Work.DSG4c.ChartPushout
