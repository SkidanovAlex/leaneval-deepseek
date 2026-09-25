import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Norm.Defs

namespace Commons.RingTheory.Norm

open Module IsLocalRing
open scoped Matrix

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]
  [Module.Free R S] [Module.Finite R S]

attribute [local instance] Ideal.Quotient.field

/-- For a finite free `R`-algebra `S` over a local ring `R` and `x : S`, the norm of the image of
`x` in `S ⧸ 𝔪 S` over `R ⧸ 𝔪` is the image of `Algebra.norm R x`.  (Norm analogue of
Mathlib's `Algebra.trace_quotient_mk`.) -/
lemma norm_quotient_mk (x : S) :
    Algebra.norm (R ⧸ IsLocalRing.maximalIdeal R)
        (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)) x) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (Algebra.norm R x) := by
  let ι := Module.Free.ChooseBasisIndex R S
  let b : Module.Basis ι R S := Module.Free.chooseBasis R S
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det (basisQuotient b),
    RingHom.map_det]
  congr 1
  ext i j
  simp only [Algebra.leftMulMatrix_eq_repr_mul, RingHom.mapMatrix_apply, Matrix.map_apply,
    basisQuotient_apply, ← map_mul]
  exact basisQuotient_repr b (x * b j) i

end Commons.RingTheory.Norm