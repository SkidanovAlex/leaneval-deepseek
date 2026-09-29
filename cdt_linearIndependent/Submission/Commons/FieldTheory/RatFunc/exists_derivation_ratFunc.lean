import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Submission.Commons.FieldTheory.RatFunc.exists_differential_ratFunc

set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

/-!
# A `K`-derivation on `RatFunc K` extending the polynomial derivative

The `K`-algebra `K(X) = RatFunc K` of rational functions carries the standard derivation
`(p/q)' = (p'q - pq')/q²`, which restricts on the image of `K[X]` to the formal derivative
`Polynomial.derivative`.

Such a derivation is packaged in the commons as a `Differential (RatFunc K)`
(`Commons.FieldTheory.RatFunc.exists_differential_ratFunc`), but a `Differential` only gives a
`ℤ`-derivation.  Here we upgrade it to a genuine `K`-derivation
`Derivation K (RatFunc K) (RatFunc K)`, which is what the arithmetic-holonomy / Picard–Vessiot
layer needs: the underlying map is `K`-linear because it kills the constants `K`, and everything
else is inherited from the `ℤ`-derivation.
-/

namespace Commons.FieldTheory.RatFunc

open Polynomial

/-- **There is a `K`-derivation of `K(X) = RatFunc K` extending the polynomial derivative.**

Take the standard derivation `dR` of the commons `Differential` on `RatFunc K` — a `ℤ`-derivation
satisfying the quotient rule — and regard it as `K`-linear.  Concretely, on constants
`algebraMap K (RatFunc K) c = algebraMap (Polynomial K) (RatFunc K) (Polynomial.C c)` and the
derivative of a constant polynomial vanishes, so by the Leibniz rule `dR (c • x) = c • dR x`.
Packaging the result through `Derivation.mk'` gives the claim. -/
theorem exists_derivation_ratFunc {K : Type*} [Field K] :
    ∃ D : Derivation K (RatFunc K) (RatFunc K), ∀ p : Polynomial K,
      D (algebraMap (Polynomial K) (RatFunc K) p)
        = algebraMap (Polynomial K) (RatFunc K) p.derivative := by
  -- Fix the `ℤ`-algebra structure on `RatFunc K` to the canonical `Ring.toIntAlgebra`, the one
  -- used in the statement of `exists_differential_ratFunc` (the polynomial-induced instance is
  -- not syntactically the same).
  letI : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra (RatFunc K)
  obtain ⟨d, hd⟩ := exists_differential_ratFunc (K := K)
  -- Constants: `algebraMap K K(X) c` is the image of the constant polynomial `C c`.
  have hcompat : ∀ c : K, algebraMap K (RatFunc K) c
      = algebraMap (Polynomial K) (RatFunc K) (Polynomial.C c) := by
    intro c; rw [RatFunc.algebraMap_eq_C, RatFunc.algebraMap_C]
  -- Hence the derivation kills `K`.
  have hC : ∀ c : K, d.deriv (algebraMap K (RatFunc K) c) = 0 := by
    intro c
    rw [hcompat c, hd (Polynomial.C c)]
    simp
  -- `dR` is `K`-linear.
  let L : RatFunc K →ₗ[K] RatFunc K :=
    { toFun := fun x => d.deriv x
      map_add' := fun a b => map_add d.deriv a b
      map_smul' := fun c x => by
        rw [Algebra.smul_def, Derivation.leibniz, hC c, smul_zero, add_zero]
        rw [smul_eq_mul, Algebra.smul_def]
        rfl }
  refine ⟨Derivation.mk' L ?_, ?_⟩
  · intro a b
    exact d.deriv.leibniz a b
  · intro p
    exact hd p

end Commons.FieldTheory.RatFunc