import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.SimpleRing.Principal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.HeckeL.Product

open Polynomial

/-- **Product over the `d`-th roots of unity.**
For `d > 0` and any `x : ℂ`,
`∏_{z^d = 1} (1 - z * x) = 1 - x ^ d`,
the `d`-th roots of unity being `Polynomial.nthRootsFinset d (1 : ℂ)`.

This is the `d = 1` variable form of `X ^ d - 1 = ∏_{z^d = 1} (X - z)`, obtained by
evaluating the factorisation `X ^ d - C (x ^ d) = ∏_{i < d} (X - C (ζ ^ i * x))`
(at `X = 1`) and reindexing the roots via a primitive `d`-th root of unity `ζ`. -/
theorem prod_nthRootsFinset_one_sub_mul (d : ℕ) (hd : 0 < d) (x : ℂ) :
    ∏ z ∈ Polynomial.nthRootsFinset d (1 : ℂ), (1 - z * x) = 1 - x ^ d := by
  -- a primitive `d`-th root of unity in `ℂ`
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ d := ⟨_, Complex.isPrimitiveRoot_exp d hd.ne'⟩
  -- factorisation of `X ^ d - x ^ d` over the `ζ ^ i`, `i < d`
  have hpoly : (X ^ d - C (x ^ d) : ℂ[X]) = ∏ i ∈ Finset.range d, (X - C (ζ ^ i * x)) :=
    X_pow_sub_C_eq_prod hζ hd rfl
  -- evaluate at `1`
  have h1 : ∏ i ∈ Finset.range d, (1 - ζ ^ i * x) = 1 - x ^ d := by
    have h := congrArg (Polynomial.eval (1 : ℂ)) hpoly
    simpa [Polynomial.eval_prod] using h.symm
  have hne : NeZero d := NeZero.of_pos hd
  -- reindex the product over `nthRootsFinset d 1` by `i ↦ ζ ^ i`
  have h2 : ∏ i ∈ Finset.range d, (1 - ζ ^ i * x)
      = ∏ z ∈ Polynomial.nthRootsFinset d (1 : ℂ), (1 - z * x) := by
    refine Finset.prod_bij (fun i _ => ζ ^ i)
      (fun i hi => ?_) (fun i hi j hj hij => ?_) (fun z hz => ?_) (fun i hi => ?_)
    · rw [Polynomial.mem_nthRootsFinset hd]
      rw [← pow_mul, mul_comm i d, pow_mul, hζ.pow_eq_one, one_pow]
    · exact hζ.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij
    · rw [Polynomial.mem_nthRootsFinset hd] at hz
      obtain ⟨i, hi, hiz⟩ := hζ.eq_pow_of_pow_eq_one hz
      exact ⟨i, Finset.mem_range.mpr hi, hiz⟩
    · rfl
  rw [← h2, h1]

end NK.HeckeL.Product
