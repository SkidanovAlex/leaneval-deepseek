import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.NumberTheory.NumberField

theorem natDegree_minpoly_int_eq_finrank_adjoin_simple (z : ℂ) (hz : IsIntegral ℤ z) :
    (minpoly ℤ z).natDegree = Module.finrank ℚ ↥(IntermediateField.adjoin ℚ ({z} : Set ℂ)) := by
  -- `z` is, in particular, integral (hence algebraic) over `ℚ`.
  have hzQ : IsIntegral ℚ z := hz.tower_top
  -- The minimal polynomial over `ℤ` maps to the one over `ℚ`.
  have hmin : minpoly ℚ z = (minpoly ℤ z).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' (K := ℚ) hz
  -- Hence the two minimal polynomials have the same degree.
  have hdeg : (minpoly ℚ z).natDegree = (minpoly ℤ z).natDegree := by
    rw [hmin, Polynomial.natDegree_map_eq_of_injective (f := algebraMap ℤ ℚ) Int.cast_injective]
  -- The degree of the minimal polynomial over `ℚ` is `[ℚ(z) : ℚ]`.
  have hfr : Module.finrank ℚ ↥(IntermediateField.adjoin ℚ ({z} : Set ℂ)) =
      (minpoly ℚ z).natDegree :=
    IntermediateField.adjoin.finrank hzQ
  rw [← hdeg, ← hfr]

end Commons.NumberTheory.NumberField