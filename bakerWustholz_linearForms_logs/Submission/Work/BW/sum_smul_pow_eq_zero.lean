import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Polynomial

/-- If a `ℂ`-algebra integral domain `K` satisfies the polynomial-type relation
`∑ a ∈ s, (algebraMap ℂ K t) ^ (n a) * c a = 0` for all nonzero complex `t`,
where the exponents `n a` are pairwise distinct on `s`, then every coefficient
`c a` is zero.

The proof evaluates the polynomial `P = ∑ a ∈ s, C (c a) * X ^ (n a) ∈ K[X]`
at the infinitely many points `algebraMap ℂ K t`, `t ≠ 0`.  Since `algebraMap ℂ K`
is injective (a ring map from a field to a nontrivial ring) these give infinitely
many distinct roots of `P`, forcing `P = 0`; reading off the coefficient of
`X ^ (n a)` (nonzero terms are separated by the injectivity hypothesis on `n`)
gives `c a = 0`. -/
theorem sum_smul_pow_eq_zero {ι K : Type*} [CommRing K] [IsDomain K] [Algebra ℂ K]
    (s : Finset ι) (c : ι → K) (n : ι → ℕ)
    (hinj : ∀ a ∈ s, ∀ b ∈ s, n a = n b → a = b)
    (h : ∀ t : ℂ, t ≠ 0 → ∑ a ∈ s, (algebraMap ℂ K t) ^ (n a) * c a = 0) :
    ∀ a ∈ s, c a = 0 := by
  -- The structure map `ℂ → K` is injective since `ℂ` is a field and `K` is nontrivial.
  have halg_inj : Function.Injective (algebraMap ℂ K) := by
    intro x y hxy
    have hsub : algebraMap ℂ K (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    by_contra hne
    have hz : x - y ≠ 0 := sub_ne_zero.mpr hne
    have h2 : algebraMap ℂ K ((x - y) * (x - y)⁻¹) = (1 : K) := by
      rw [mul_inv_cancel₀ hz, map_one]
    rw [map_mul, hsub, zero_mul] at h2
    exact one_ne_zero h2.symm
  -- The polynomial whose values are given by the hypothesis.
  set P : K[X] := ∑ a ∈ s, Polynomial.C (c a) * Polynomial.X ^ (n a) with hP
  -- Every `algebraMap ℂ K t`, `t ≠ 0`, is a root of `P`.
  have hroot : ∀ t : ℂ, t ≠ 0 → P.IsRoot (algebraMap ℂ K t) := by
    intro t ht
    show P.eval (algebraMap ℂ K t) = 0
    rw [hP, Polynomial.eval_finsetSum]
    have heq : (∑ a ∈ s, (Polynomial.C (c a) * Polynomial.X ^ (n a)).eval (algebraMap ℂ K t))
        = ∑ a ∈ s, (algebraMap ℂ K t) ^ (n a) * c a := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      exact mul_comm _ _
    rw [heq]
    exact h t ht
  -- Infinitely many roots: the numbers `algebraMap ℂ K ((m : ℂ) + 1)` are distinct.
  have hInf : Set.Infinite {x : K | Polynomial.IsRoot P x} := by
    refine Set.infinite_of_injective_forall_mem
      (f := fun m : ℕ => algebraMap ℂ K ((m : ℂ) + 1)) ?_ ?_
    · intro m1 m2 hmm
      have hcast : (m1 : ℂ) + 1 = (m2 : ℂ) + 1 := halg_inj hmm
      have : (m1 : ℂ) = (m2 : ℂ) := by simpa using hcast
      exact Nat.cast_injective this
    · intro m
      have hm1 : ((m : ℂ) + 1) ≠ 0 := by
        have : ((m : ℂ) + 1) = ((m + 1 : ℕ) : ℂ) := by push_cast; ring
        rw [this, Nat.cast_ne_zero]
        exact Nat.succ_ne_zero m
      exact hroot _ hm1
  have hP0 : P = 0 := Polynomial.eq_zero_of_infinite_isRoot P hInf
  intro a ha
  have hcoeff : P.coeff (n a) = 0 := by rw [hP0, Polynomial.coeff_zero]
  -- The coefficient of `X ^ (n a)` in `P` is exactly `c a`.
  have hcoeff' : P.coeff (n a) = c a := by
    rw [hP, ← Polynomial.lcoeff_apply, map_sum]
    simp only [Polynomial.lcoeff_apply]
    rw [Finset.sum_eq_single_of_mem a ha (fun b hb hba => by
      rw [Polynomial.coeff_C_mul_X_pow,
          ite_eq_right (fun hnab => hba (hinj a ha b hb hnab).symm)])]
    rw [Polynomial.coeff_C_mul_X_pow]
    exact ite_eq_left rfl
  rw [hcoeff'] at hcoeff
  exact hcoeff

end Work.BW
