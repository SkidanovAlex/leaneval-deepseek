import Mathlib.Algebra.Polynomial.Basis
import Mathlib.RingTheory.Algebraic.Basic

namespace Commons.FieldTheory.Transcendental

theorem linearIndependent_powers {K L : Type*} [Field K] [Field L] [Algebra K L] {x : L}
    (hx : Transcendental K x) (n : ℕ) :
    LinearIndependent K (fun i : Fin n => x ^ (i : ℕ)) := by
  have hinj : Function.Injective (Polynomial.aeval x : Polynomial K →ₐ[K] L) :=
    transcendental_iff_injective.mp hx
  have hX : LinearIndependent K (fun i : ℕ => (Polynomial.X : Polynomial K) ^ i) := by
    simpa only [Polynomial.coe_basisMonomials, Polynomial.X_pow_eq_monomial] using
      (Polynomial.basisMonomials K).linearIndependent
  have hmap : LinearIndependent K
      (fun i : ℕ => Polynomial.aeval x ((Polynomial.X : Polynomial K) ^ i)) :=
    hX.map' (Polynomial.aeval x).toLinearMap (LinearMap.ker_eq_bot.mpr hinj)
  have hmap' : LinearIndependent K (fun i : ℕ => x ^ i) := by
    simpa [Polynomial.aeval_X] using hmap
  exact hmap'.comp Fin.val Fin.val_injective

end Commons.FieldTheory.Transcendental