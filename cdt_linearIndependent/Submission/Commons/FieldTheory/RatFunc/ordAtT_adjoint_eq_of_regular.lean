import Mathlib
import Submission.Commons.FieldTheory.RatFunc.ordAtT_adjoint_eq_of_indicial_le
import Submission.Commons.Algebra.Polynomial.fallFact_cast_ne_zero

namespace Commons.FieldTheory.RatFunc

open Classical
open Commons.Algebra.Polynomial
open Commons.FieldTheory.RatFunc

set_option maxHeartbeats 800000

/-- **Indicial exactness at a regular (non-singular) point.**  Suppose that the coefficients `γᵢ` of the eliminated fourth-order expression `Σᵢ (−1)ⁱ Dⁱ(γᵢ·b)` are all *regular* at `α` (`0 ≤ ordAtT α (γ i)`), that `γ₄ = 1`, and that `b ≠ 0` has *negative* order `N = ordAt α b < 0` at `α` (with leading coefficient `r ≠ 0`).  Then the expression has order *exactly* `N − 4`: the term `D⁴(γ₄·b) = b⁗` has order `N − 4` while every other term `Dⁱ(γᵢ·b)` has order at least `N − i ≥ N − 3`.  The indicial value at such a point is the falling factorial `(N)₄ = N(N−1)(N−2)(N−3)`, which is non-zero for every negative integer `N`.

This is the "non-singular point" (generic) case of the local/indicial analysis of the CDT systems (arXiv:2408.15403, `(onceagain)` and the Theorem-A analogue): it shows that a solution of the eliminated equation has no poles at any point where all the `γᵢ = cᵢ/c₄` are regular, so that the divisor of `b` is supported on the singular points of the operator, where the bounds `N₀ ≥ 0, N₄ ≥ 2, N_β ≥ 1, N_γ ≥ −1, N_∞ ≤ 5` apply.  It is proved from `ordAtT_adjoint_eq_of_indicial_le` with the constant data `e i = 0`, `m = −4`, `λ₄ = 1`. -/
theorem ordAtT_adjoint_eq_of_regular {K : Type*} [Field K] [CharZero K]
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hd : ∀ p : Polynomial K, D (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative)
    (α : K) (b : RatFunc K) (hb : b ≠ 0) (r : K) (hr : r ≠ 0)
    (hb' : (((ordAt α b) + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
      (b - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C r)
        * linFactor (K := K) α ^ (ordAt α b)))
    (γ : Fin 5 → RatFunc K) (hγ4 : γ 4 = 1)
    (hγ : ∀ i : Fin 5, (0 : WithTop ℤ) ≤ ordAtT α (γ i))
    (hNneg : ordAt α b < 0) :
    ordAtT α (∑ i : Fin 5, (-1 : ℤ) ^ (i : ℕ) •
      ((fun x : RatFunc K => D x)^[i]) (γ i * b))
      = (((ordAt α b) - 4 : ℤ) : WithTop ℤ) := by
  classical
  set N : ℤ := ordAt α b with hNdef
  have hN : ordAt α b = N := hNdef.symm
  have hm : ∀ i : Fin 5, (-4 : ℤ) ≤ (0 : ℤ) - ((i : ℕ) : ℤ) := by
    intro i; have := i.isLt; omega
  have hfilter : Finset.univ.filter (fun i : Fin 5 => (0 : ℤ) - ((i : ℕ) : ℤ) = (-4 : ℤ))
      = {4} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h; exact Fin.ext (by omega)
    · intro h; rw [h]; norm_num
  have hsum : (∑ i ∈ Finset.univ.filter (fun i : Fin 5 => (0 : ℤ) - ((i : ℕ) : ℤ) = (-4 : ℤ)),
      (-1 : ℤ) ^ (i : ℕ) • ((1 : K) * ∏ j ∈ Finset.range (i : ℕ),
        ((N + 0 - (j : ℤ) : ℤ) : K)))
      = ((fallFact N 4 : ℤ) : K) := by
    rw [hfilter]
    simp only [Finset.sum_singleton]
    rw [fallFact, Int.cast_prod]
    norm_num
  have hP : (∑ i ∈ Finset.univ.filter (fun i : Fin 5 => (0 : ℤ) - ((i : ℕ) : ℤ) = (-4 : ℤ)),
      (-1 : ℤ) ^ (i : ℕ) • ((1 : K) * ∏ j ∈ Finset.range (i : ℕ),
        ((N + 0 - (j : ℤ) : ℤ) : K))) ≠ 0 := by
    rw [hsum]
    exact fallFact_cast_ne_zero (fun k hk => by omega)
  have he : ∀ i : Fin 5, (0 : ℤ) - ((i : ℕ) : ℤ) ≠ (-4 : ℤ) →
      (((0 : ℤ)) : WithTop ℤ) ≤ ordAtT α (γ i) := by
    intro i _; simpa using hγ i
  have hlam : ∀ i : Fin 5, (0 : ℤ) - ((i : ℕ) : ℤ) = (-4 : ℤ) →
      ((((0 : ℤ) + 1 : ℤ)) : WithTop ℤ) ≤ ordAtT α
        (γ i - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C ((1 : K)))
          * linFactor (K := K) α ^ (0 : ℤ)) := by
    intro i hi
    have hi4 : i = 4 := Fin.ext (by omega)
    rw [hi4, hγ4]
    simp [ordAtT]
  have hmain := ordAtT_adjoint_eq_of_indicial_le (K := K) D hd α b hb N hN r hr hb'
    γ (fun _ => (0 : ℤ)) (fun _ => (1 : K)) (-4) he hm hlam hP
  convert hmain using 2
  ring

end Commons.FieldTheory.RatFunc
