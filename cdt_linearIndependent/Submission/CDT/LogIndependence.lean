import Mathlib
import Submission.CDT.LogRelation
import Submission.CDT.LogProduct

/-!
# Function-field Lindemann–Weierstrass: independence statements

`Submission.CDT.LogRelation` proves the *dependence* form of the function-field
Lindemann–Weierstrass theorem: a nonzero `K`-linear relation `Σᵢ cᵢ·ℓᵢ ∈ K(X)` among logarithms
forces a nontrivial multiplicative relation `∏ᵢ fᵢ^{mᵢ} ∈ K` among the functions.  This file draws
the immediate *independence* consequences, in the form in which they are used:

* `transcendental_notMem_range` — a transcendental element of a differential extension of `K(X)` is
  not a rational function;
* `transcendental_pow_notMem_range` — nor is any positive power of it;
* **`not_exists_sum_eq_algebraMap`** — if the nonzero `fᵢ ∈ K(X)` admit no nontrivial
  multiplicative relation with constant value, then no nonzero `K`-linear combination of the
  logarithms `ℓᵢ` (with `ℓᵢ' = (dRat fᵢ)/fᵢ`) is a rational function.

Together with `Submission.CDT.LogProduct.not_exists_mul_eq_algebraMap` (weight two) and
`Submission.CDT.LogTranscendence.linearIndependent_powers_of_deriv_eq_dRat_div` (powers of a single
logarithm), this is the part of the function-field Lindemann–Weierstrass theorem that is available
without any arithmetic input.
-/

noncomputable section

namespace Submission.CDT

open Polynomial

variable {K : Type*} [Field K]
variable {L : Type*} [Field L] [Algebra (RatFunc K) L]

/-- **A transcendental element is not a rational function.** -/
theorem transcendental_notMem_range (v : L) (hv : Transcendental (RatFunc K) v) :
    ¬ ∃ r₀ : RatFunc K, v = algebraMap (RatFunc K) L r₀ := by
  rintro ⟨r₀, h⟩
  refine hv ⟨Polynomial.X - Polynomial.C r₀, ?_, ?_⟩
  · simpa using Polynomial.X_sub_C_ne_zero r₀
  · simp only [Polynomial.aeval_def, Polynomial.eval₂_sub, Polynomial.eval₂_X,
      Polynomial.eval₂_C]
    rw [h, sub_self]

/-- **A positive power of a transcendental element is not a rational function.** -/
theorem transcendental_pow_notMem_range (v : L) (hv : Transcendental (RatFunc K) v)
    {n : ℕ} (hn : n ≠ 0) (r₀ : RatFunc K) : v ^ n ≠ algebraMap (RatFunc K) L r₀ := by
  intro h
  refine hv ⟨Polynomial.X ^ n - Polynomial.C r₀, ?_, ?_⟩
  · intro hzero
    have h2 := congrArg (fun p : Polynomial (RatFunc K) => p.coeff n) hzero
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C, if_neg hn,
      Polynomial.coeff_zero, sub_zero] at h2
    exact one_ne_zero h2
  · simp only [Polynomial.aeval_def, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    rw [h, sub_self]

section LW

variable [CharZero K] [IsAlgClosed K] [Differential (RatFunc K)]
  [Differential L] [DifferentialAlgebra (RatFunc K) L]

/-- **Independence form of the logarithmic Lindemann–Weierstrass theorem.**  Let `f : ι → K(X)`
be a family of nonzero rational functions admitting no nontrivial multiplicative relation with
constant value, and let `ℓ : ι → L` have `ℓᵢ' = (dRat fᵢ)/fᵢ` in a differential field extension
`L` of `K(X)`.  Then no nonzero `K`-linear combination of the `ℓᵢ` is a rational function. -/
theorem not_exists_sum_eq_algebraMap
    (hderiv : ∀ r : RatFunc K, Differential.deriv r = dRat r)
    {ι : Type*} [Fintype ι] (f : ι → RatFunc K) (hf : ∀ i, f i ≠ 0)
    (hindep : ∀ m : ι → ℤ, m ≠ 0 → ∀ C : K, C ≠ 0 →
      (∏ i, f i ^ (m i)) ≠ algebraMap K (RatFunc K) C)
    (c : ι → K) (hc : c ≠ 0) (l : ι → L)
    (hl : ∀ i, Differential.deriv (l i) = algebraMap (RatFunc K) L (dRat (f i) / f i)) :
    ¬ ∃ g : RatFunc K,
      ∑ i, algebraMap (RatFunc K) L (algebraMap K (RatFunc K) (c i)) * l i
        = algebraMap (RatFunc K) L g := by
  rintro ⟨g, hg⟩
  obtain ⟨m, hm, C, hC, hprod⟩ :=
    exists_int_prod_zpow_const_of_logRelation hderiv f hf c hc l hl g hg
  exact hindep m hm C hC hprod

/-- **Two logarithms**: the independence form for a pair.  If `f, g ∈ K(X)` are nonzero with no
nontrivial multiplicative relation of the form `f ^ m * g ^ n = const` (`(m,n) ≠ 0`), then the sum
`ℓ₁ + ℓ₂` of their logarithms (elements of a differential extension with `ℓ₁' = (dRat f)/f`,
`ℓ₂' = (dRat g)/g`) is not a rational function. -/
theorem not_exists_add_eq_algebraMap
    (hderiv : ∀ r : RatFunc K, Differential.deriv r = dRat r)
    {f g : RatFunc K} (hf : f ≠ 0) (hg : g ≠ 0)
    (hindep : ∀ m n : ℤ, (m ≠ 0 ∨ n ≠ 0) → ∀ C : K, C ≠ 0 →
      f ^ m * g ^ n ≠ algebraMap K (RatFunc K) C)
    (u v : L) (hu : Differential.deriv u = algebraMap (RatFunc K) L (dRat f / f))
    (hv : Differential.deriv v = algebraMap (RatFunc K) L (dRat g / g)) :
    ¬ ∃ r₀ : RatFunc K, u + v = algebraMap (RatFunc K) L r₀ := by
  set F : Fin 2 → RatFunc K := ![f, g] with hF
  set c : Fin 2 → K := ![1, 1] with hc
  set l : Fin 2 → L := ![u, v] with hl
  have hF0 : ∀ i, F i ≠ 0 := by
    intro i; fin_cases i
    · simpa [hF] using hf
    · simpa [hF] using hg
  have hc0 : c ≠ 0 := by
    intro h
    have h0 : c 0 = 0 := congrFun h 0
    have h1 : c 0 = 1 := by simp [hc]
    rw [h1] at h0
    exact one_ne_zero h0
  have hl' : ∀ i, Differential.deriv (l i) = algebraMap (RatFunc K) L (dRat (F i) / F i) := by
    intro i; fin_cases i
    · simpa [hl, hF] using hu
    · simpa [hl, hF] using hv
  have hind : ∀ m : Fin 2 → ℤ, m ≠ 0 → ∀ C : K, C ≠ 0 →
      (∏ i, F i ^ (m i)) ≠ algebraMap K (RatFunc K) C := by
    intro m hm C hC hcontra
    refine hindep (m 0) (m 1) ?_ C hC ?_
    · by_contra hmn
      push Not at hmn
      exact hm (funext (fun i => by fin_cases i <;> simp [hmn.1, hmn.2]))
    · simpa [hF, Fin.prod_univ_two] using hcontra
  intro h
  refine not_exists_sum_eq_algebraMap (K := K) (L := L) hderiv F hF0 hind c hc0 l hl' ?_
  obtain ⟨r₀, hr₀⟩ := h
  refine ⟨r₀, ?_⟩
  have : ∑ i : Fin 2, algebraMap (RatFunc K) L (algebraMap K (RatFunc K) (c i)) * l i = u + v := by
    rw [Fin.sum_univ_two]
    simp [hc, hl]
  rw [this, hr₀]

end LW

end Submission.CDT
