import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.FieldTheory.AlgebraicClosure

/-!
# Real and imaginary parts of an algebraic complex number are algebraic

If `z : ℂ` is algebraic over `ℚ`, then so are its real and imaginary parts.  This is
because conjugation is a `ℚ`-algebra automorphism of `ℂ`, so `z + conj z = 2 * z.re`
and `z - conj z = 2 * I * z.im` express `z.re` and `z.im` as polynomials (over `ℚ`)
in the algebraic numbers `z`, `conj z` and `I`.
-/

open Polynomial

namespace Commons.NumberTheory.Algebraic

theorem complex_re_im_isAlgebraic {z : ℂ} (hz : IsAlgebraic ℚ z) :
    IsAlgebraic ℚ z.re ∧ IsAlgebraic ℚ z.im := by
  -- `I` is algebraic over `ℚ`, being a root of `X ^ 2 + 1`.
  have hI : IsAlgebraic ℚ Complex.I := by
    refine ⟨X ^ 2 + 1, ?_, ?_⟩
    · intro h
      have := congrArg (Polynomial.eval (0 : ℚ)) h
      simp at this
    · rw [map_add, map_pow, aeval_X, map_one]
      simp [pow_two, Complex.I_mul_I]
  -- The set of elements of `ℂ` algebraic over `ℚ`, viewed as a subfield.
  have hzA : z ∈ algebraicClosure ℚ ℂ := mem_algebraicClosure_iff.mpr hz
  -- Conjugation is a `ℚ`-algebra automorphism of `ℂ`, so it preserves algebraicity.
  have hconj : star z ∈ algebraicClosure ℚ ℂ := by
    have := (map_mem_algebraicClosure_iff
      (AlgEquiv.restrictScalars ℚ Complex.conjAe).toAlgHom).mpr hzA
    simpa using this
  have hIA : Complex.I ∈ algebraicClosure ℚ ℂ := mem_algebraicClosure_iff.mpr hI
  have h2 : (2 : ℂ) ∈ algebraicClosure ℚ ℂ := by norm_num
  -- `z.re = (z + conj z) / 2` and `z.im = (z - conj z) / (2 * I)`.
  have hre : (z.re : ℂ) ∈ algebraicClosure ℚ ℂ := by
    rw [Complex.re_eq_add_conj]
    exact div_mem (add_mem hzA hconj) h2
  have him : (z.im : ℂ) ∈ algebraicClosure ℚ ℂ := by
    rw [Complex.im_eq_sub_conj]
    exact div_mem (sub_mem hzA hconj) (mul_mem h2 hIA)
  -- Descend from `ℂ` to `ℝ`: an element of `ℝ` is algebraic over `ℚ` iff its image in
  -- `ℂ` is (the inclusion `ℝ → ℂ` is an injective `ℚ`-algebra map).
  have key : ∀ x : ℝ, IsAlgebraic ℚ (x : ℂ) → IsAlgebraic ℚ x := fun x hx =>
    (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom ℚ ℝ ℂ) Complex.ofReal_injective).mp hx
  exact ⟨key z.re (mem_algebraicClosure_iff.mp hre),
         key z.im (mem_algebraicClosure_iff.mp him)⟩

end Commons.NumberTheory.Algebraic