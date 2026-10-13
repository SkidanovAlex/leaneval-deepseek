import Mathlib

/-!
# DSREG — basic API for "regular local rings are domains"

This file collects the small pieces of vocabulary/API on which the area DSREG is built:

* `Work.DSREG.quotientIsLocalRing`: a quotient of a local ring by a proper ideal is local
  (Mathlib has `IsLocalRing.of_surjective'` but no instance for quotients).
* `Work.DSREG.nontrivial_quotient_span_singleton`: `R ⧸ (x)` is nontrivial for `x` in the
  maximal ideal of the local ring `R`; this is the side condition needed to get `IsLocalRing`
  on the quotient out of the instance above.
* `Work.DSREG.maximalIdeal_quotient_span_singleton`: the maximal ideal of `R ⧸ (x)` is the image
  of the maximal ideal of `R`.

The main theorem of the area is `DSMap.area_REG_proved` in `Submission/Work/DSREG/Main.lean`.
-/

namespace Work.DSREG

universe u

/-- A quotient of a (commutative) local ring by a proper ideal is a local ring. -/
instance quotientIsLocalRing (R : Type u) [CommRing R] [IsLocalRing R] (I : Ideal R)
    [Nontrivial (R ⧸ I)] : IsLocalRing (R ⧸ I) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

/-- If `x` lies in the maximal ideal of a local ring then `(x)` is a proper ideal. -/
theorem span_singleton_ne_top_of_mem_maximalIdeal {R : Type u} [CommRing R] [IsLocalRing R]
    {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R) : Ideal.span {x} ≠ ⊤ := by
  intro h
  exact (IsLocalRing.notMem_maximalIdeal.mpr (Ideal.span_singleton_eq_top.mp h)) hx

/-- The quotient of a local ring by `(x)`, `x` in the maximal ideal, is nontrivial. -/
theorem nontrivial_quotient_span_singleton {R : Type u} [CommRing R] [IsLocalRing R]
    {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R) : Nontrivial (R ⧸ Ideal.span {x}) :=
  Ideal.Quotient.nontrivial_iff.mpr (span_singleton_ne_top_of_mem_maximalIdeal hx)

/-- The maximal ideal of `R ⧸ (x)` is the image of the maximal ideal of `R`
(the quotient is a local ring by `Work.DSREG.quotientIsLocalRing`, which needs it to be
nontrivial; for `x` in the maximal ideal this is `nontrivial_quotient_span_singleton`). -/
theorem maximalIdeal_quotient_span_singleton (R : Type u) [CommRing R] [IsLocalRing R]
    (x : R) [Nontrivial (R ⧸ Ideal.span {x})] :
    IsLocalRing.maximalIdeal (R ⧸ Ideal.span {x})
      = (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {x})) :=
  (IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk (Ideal.span {x}))
    Ideal.Quotient.mk_surjective).symm

end Work.DSREG
