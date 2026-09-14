import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.FieldTheory.Polynomial

open IntermediateField

/-- For `L / K` a finite separable field extension and `x : L` a primitive element
(`K[x] = ⊤`), the field norm of `x` is `(-1) ^ [L : K]` times the constant term of the
minimal polynomial of `x`.

This is the "generating element" case of `Norm(x) = (-1)^n * charpoly.coeff 0`: since `x`
generates `L`, the minimal polynomial of `x` equals the characteristic polynomial of
multiplication by `x` on `L`, whose constant term is `(-1)^n · Norm(x)`. -/
theorem norm_eq_neg_one_pow_mul_coeff_zero {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (x : L)
    (hx : Algebra.adjoin K ({x} : Set L) = ⊤) :
    Algebra.norm K x = (-1) ^ Module.finrank K L * (minpoly K x).coeff 0 := by
  have hx_int : IsIntegral K x := Algebra.IsSeparable.isIntegral K x
  have hxa : IsAlgebraic K x := hx_int.isAlgebraic
  -- `x` is a primitive element, so the intermediate field it generates is everything.
  have hF : K⟮x⟯ = ⊤ :=
    (IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic hxa).mpr hx
  -- consequently `deg (minpoly K x) = [L : K]`
  have hfin : (minpoly K x).natDegree = Module.finrank K L := by
    rw [← IntermediateField.adjoin.finrank hx_int, hF, IntermediateField.finrank_top']
  -- and `[K⟮x⟯ : L] = 1`
  have hfinL : Module.finrank K⟮x⟯ L = 1 := by
    rw [hF]; exact IntermediateField.finrank_top
  -- The norm of the generator of the simple extension, via the power basis.
  have hgen : Algebra.norm K (AdjoinSimple.gen K x)
      = (-1) ^ Module.finrank K L * (minpoly K x).coeff 0 := by
    have h := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly
      (IntermediateField.adjoin.powerBasis hx_int)
    rw [IntermediateField.adjoin.powerBasis_gen] at h
    rw [IntermediateField.minpoly_gen] at h
    rw [IntermediateField.adjoin.powerBasis_dim, hfin] at h
    exact h
  rw [Algebra.norm_eq_norm_adjoin K x, hfinL, pow_one]
  exact hgen

end Commons.FieldTheory.Polynomial