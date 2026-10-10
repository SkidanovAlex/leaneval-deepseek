import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Twist

open MvPolynomial Polynomial

/-- The "set `X₀ = 1`" substitution `𝕜[X₀,…,Xₙ] →+* 𝕜[X₁,…,Xₙ]` is the composite of the
dehomogenisation `finSuccEquiv` with evaluation of the resulting univariate polynomial at `1`. -/
private lemma eval_one_finSuccEquiv (𝕜 : Type) [Field 𝕜] (n : ℕ)
    (y : MvPolynomial (Fin (n + 1)) 𝕜) :
    Polynomial.eval 1 (MvPolynomial.finSuccEquiv 𝕜 n y) =
      MvPolynomial.eval₂Hom (algebraMap 𝕜 (MvPolynomial (Fin n) 𝕜))
        (Fin.cases 1 (fun j => MvPolynomial.X j)) y := by
  have key : (Polynomial.evalRingHom (1 : MvPolynomial (Fin n) 𝕜)).comp
      (MvPolynomial.finSuccEquiv 𝕜 n : MvPolynomial (Fin (n+1)) 𝕜 →+*
        Polynomial (MvPolynomial (Fin n) 𝕜))
      = MvPolynomial.eval₂Hom (algebraMap 𝕜 (MvPolynomial (Fin n) 𝕜))
        (Fin.cases 1 (fun j => MvPolynomial.X j)) := by
    refine MvPolynomial.ringHom_ext ?_ ?_
    · intro r
      simp [MvPolynomial.finSuccEquiv_apply, MvPolynomial.algebraMap_eq]
    · intro i
      induction i using Fin.cases with
      | zero => simp [MvPolynomial.finSuccEquiv_X_zero]
      | succ j => simp [MvPolynomial.finSuccEquiv_X_succ]
  exact congrFun (congrArg DFunLike.coe key) y

/-- A homogeneous polynomial of degree `N` which is killed by the "set `X₀ = 1`" substitution is
zero. -/
private lemma eq_zero_of_eval_one_finSuccEquiv (𝕜 : Type) [Field 𝕜] (n N : ℕ)
    (y : MvPolynomial (Fin (n + 1)) 𝕜) (hy : y.IsHomogeneous N)
    (hy0 : Polynomial.eval 1 (MvPolynomial.finSuccEquiv 𝕜 n y) = 0) : y = 0 := by
  classical
  set P : Polynomial (MvPolynomial (Fin n) 𝕜) := MvPolynomial.finSuccEquiv 𝕜 n y with hP
  -- Coefficients of `P` above the degree bound `N` vanish.
  have hlarge : ∀ i, N < i → P.coeff i = 0 := by
    intro i hi
    by_contra hne
    have hle := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le y i (by rwa [hP] at hne)
    have := hy.totalDegree_le
    omega
  -- Each coefficient of degree `i ≤ N` is homogeneous of degree `N - i`.
  have hhom : ∀ i, i ≤ N → (P.coeff i).IsHomogeneous (N - i) := by
    intro i hi
    have hh := hy.finSuccEquiv_coeff_isHomogeneous i (N - i) (by omega)
    rw [hP]; exact hh
  -- Isolate the graded pieces of `∑ᵢ P.coeff i = P.eval 1 = 0`.
  have hsum : ∀ k, k ≤ N → P.coeff k = 0 := by
    intro k hk
    have h0 : MvPolynomial.homogeneousComponent (N - k) (P.eval 1) = 0 := by
      rw [hy0, map_zero]
    have hsupp : P.support ⊆ Finset.range (N + 1) := by
      intro i hi
      rw [Polynomial.mem_support_iff] at hi
      rw [Finset.mem_range]
      by_contra h
      exact hi (hlarge i (by omega))
    have hsum_eq : P.eval 1 = ∑ i ∈ Finset.range (N + 1), P.coeff i := by
      rw [Polynomial.eval_eq_sum,
        Polynomial.sum_eq_of_subset (fun i a => a * (1: MvPolynomial (Fin n) 𝕜) ^ i) ?_ hsupp]
      · simp
      · intro i; simp
    rw [hsum_eq, map_sum] at h0
    have hsingle : ∑ i ∈ Finset.range (N + 1),
        MvPolynomial.homogeneousComponent (N - k) (P.coeff i)
          = MvPolynomial.homogeneousComponent (N - k) (P.coeff k) := by
      refine Finset.sum_eq_single k ?_ ?_
      · intro i hi hik
        have hiN : i ≤ N := by rw [Finset.mem_range] at hi; omega
        rw [MvPolynomial.homogeneousComponent_of_mem
          ((MvPolynomial.mem_homogeneousSubmodule (N - i) (P.coeff i)).2 (hhom i hiN))]
        have hne : N - k ≠ N - i := by omega
        simp [hne]
      · intro hknot
        exact absurd (Finset.mem_range.mpr (by omega)) hknot
    rw [hsingle, MvPolynomial.homogeneousComponent_eq_self (hhom k hk)] at h0
    exact h0
  have hPzero : P = 0 := by
    apply Polynomial.ext
    intro i
    by_cases hi : i ≤ N
    · simpa using hsum i hi
    · simpa using hlarge i (by omega)
  rw [hP] at hPzero
  exact (MvPolynomial.finSuccEquiv 𝕜 n).injective (by rw [hPzero, map_zero])

/-- **Dehomogenisation at `X₀ = 1` is injective on each graded piece of the standard grading of
`𝕜[X₀,…,Xₙ]`.**  The ring homomorphism `MvPolynomial.eval₂Hom` below substitutes `X₀ ↦ 1` and
`X_{i+1} ↦ X_i`, i.e. it is the "set `X₀ = 1`" map `𝕜[X₀,…,Xₙ] →+* 𝕜[X₁,…,Xₙ]`.

If a polynomial which is homogeneous of degree `N` (all monomials of total degree `N`) is killed by
this substitution then it is zero: on a fixed graded piece the substitution is injective, since a
monomial `X₀^{d₀}·∏_{i≥1} X_i^{d_i}` of degree `N` is recovered from its image
`∏_{i≥1} X_i^{d_i}` together with `N` (indeed `d₀ = N - ∑_{i≥1} d_i`).

Route: write `x` as the sum of its monomials (`MvPolynomial.support_sum_monomial_coeff`), use
`MvPolynomial.eval₂Hom_monomial` to see that the image is the sum of the monomials
`monomial (d ∘ Fin.succ) (x.coeff d)` over `d ∈ x.support` (all of which have degree `N`), and
observe that `d ↦ d ∘ Fin.succ` is injective on the multi-indices of degree `N` because
`d 0 = N - ∑_{i≥1} d i` is determined.  Equivalently use `MvPolynomial.finSuccEquiv` (which sends
`X₀ ↦ Polynomial.X` and `X_{i+1} ↦ Polynomial.C (X i)`): the hypothesis says that the polynomial
`finSuccEquiv x` evaluates to `0` at `1`, so `∑ᵢ (finSuccEquiv x).coeff i = 0`, and applying
`MvPolynomial.homogeneousComponent k` (the coefficient `(finSuccEquiv x).coeff i` is homogeneous of
degree `N - i`, by `MvPolynomial.IsHomogeneous.finSuccEquiv_coeff_isHomogeneous`) isolates the
single term `(finSuccEquiv x).coeff (N - k)`; hence every coefficient vanishes. -/
theorem chartDhom_eq_zero (𝕜 : Type) [Field 𝕜] (n : ℕ) {N : ℕ}
    {x : MvPolynomial (Fin (n + 1)) 𝕜} (hx : x.IsHomogeneous N)
    (h : MvPolynomial.eval₂Hom (algebraMap 𝕜 (MvPolynomial (Fin n) 𝕜))
      (Fin.cases 1 (fun j => MvPolynomial.X j)) x = 0) : x = 0 := by
  have h1 : Polynomial.eval 1 (MvPolynomial.finSuccEquiv 𝕜 n x) = 0 := by
    rw [eval_one_finSuccEquiv]; exact h
  exact eq_zero_of_eval_one_finSuccEquiv 𝕜 n N x hx h1

end Work.Twist
