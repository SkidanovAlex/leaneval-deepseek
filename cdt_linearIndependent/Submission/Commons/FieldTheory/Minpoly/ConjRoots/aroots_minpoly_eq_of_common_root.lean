import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.FieldTheory.Minpoly.ConjRoots

/-- If `z` and `w` are algebraic over `ℚ` and their minimal polynomials share
a common complex root `u`, then the two minimal polynomials are equal (up to
their multisets of complex roots).  Indeed a common root means `u` is a
conjugate of both `z` and `w` over `ℚ`, so `minpoly ℚ z = minpoly ℚ u =
minpoly ℚ w`. -/
lemma aroots_minpoly_eq_of_common_root {z w u : ℂ} (hz : IsAlgebraic ℚ z) (hw : IsAlgebraic ℚ w)
    (huz : u ∈ (minpoly ℚ z).aroots ℂ) (huw : u ∈ (minpoly ℚ w).aroots ℂ) :
    (minpoly ℚ z).aroots ℂ = (minpoly ℚ w).aroots ℂ := by
  have huz_root : Polynomial.aeval u (minpoly ℚ z) = 0 :=
    ((Polynomial.mem_aroots' (T := ℚ) (S := ℂ) (p := minpoly ℚ z) (a := u)).mp huz).2
  have huw_root : Polynomial.aeval u (minpoly ℚ w) = 0 :=
    ((Polynomial.mem_aroots' (T := ℚ) (S := ℂ) (p := minpoly ℚ w) (a := u)).mp huw).2
  have hzI : IsIntegral ℚ z := hz.isIntegral
  have hwI : IsIntegral ℚ w := hw.isIntegral
  have hzu : minpoly ℚ z = minpoly ℚ u :=
    (minpoly.eq_iff_aeval_minpoly_eq_zero (A := ℚ) (B := ℂ) (C := ℂ) (b := z) hzI (c := u)).mpr
      huz_root
  have hwu : minpoly ℚ w = minpoly ℚ u :=
    (minpoly.eq_iff_aeval_minpoly_eq_zero (A := ℚ) (B := ℂ) (C := ℂ) (b := w) hwI (c := u)).mpr
      huw_root
  rw [hzu, hwu]

end Commons.FieldTheory.Minpoly.ConjRoots