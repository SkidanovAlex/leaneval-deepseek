import Mathlib
import Submission.Work.FunctionalEquations.Basic
import Submission.Work.FunctionalEquations.PeriodicAddSmul
import Submission.Work.FunctionalEquations.EqZeroOfTsumExp
import Submission.Work.FunctionalEquations.SummableExpansionTerms
import Submission.Work.FunctionalEquations.FourierInversionRadial

/-!
# Auxiliary material for the Kronecker-delta pattern of the interpolation basis

This file collects the general-purpose lemmas used in
`Submission.Work.FunctionalEquations.BasisCoeffsDelta` to deduce the Kronecker-delta
pattern for the samples of the coefficient families `a_n, ã_n, b_n, b̃_n` of an
`InterpolationSolution`.

The mathematics is the elementary part of CKMRV Section 8:

* the Dirichlet kernel `dirichletTerm m τ = e^{2 π i m τ}` is `1`-periodic in `τ`, hence
  so is any Dirichlet series `τ ↦ ∑' m, c m * dirichletTerm m τ`;
* splitting off the `τ`-linear part of such a series (`PeriodicAddSmulUHP`) identifies
  both the periodic and the linear coefficient series;
* uniqueness of Dirichlet coefficients (`DirichletCoeffUnique`), proved by integrating
  against characters (`EqZeroOfTsumExp`), turns the resulting identity of series into an
  identity of coefficients;
* polynomial growth of the coefficient families at a sample point
  (`basis_sample_bound`, `radialDeriv_basis_sample_bound`) supplies the absolute
  convergence needed for the uniqueness step.
-/

namespace Work.FunctionalEquations.BasisDelta

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

/-- The Dirichlet kernel is periodic of period `1` in `τ`. -/
lemma dirichletTerm_add_one (m : ℕ) (τ : ℂ) : dirichletTerm m (τ + 1) = dirichletTerm m τ := by
  rw [dirichletTerm, dirichletTerm]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (τ + 1)
      = 2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * τ
        + (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) from by ring]
  rw [Complex.exp_add, Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow, mul_one]

/-- The Dirichlet kernel in terms of the real index, the form in which it appears in
`EqZeroOfTsumExp`. -/
lemma dirichletTerm_eq_exp (m : ℕ) (τ : ℂ) :
    dirichletTerm m τ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℝ) * τ) := rfl

/-- Any Dirichlet series is periodic of period `1` in `τ` (no convergence needed: the
terms are literally the same). -/
lemma tsum_dirichletTerm_add_one (c : Set.Ici (1 : ℕ) → ℂ) (τ : ℂ) :
    (∑' m : Set.Ici (1 : ℕ), c m * dirichletTerm m.1 (τ + 1))
      = ∑' m : Set.Ici (1 : ℕ), c m * dirichletTerm m.1 τ :=
  tsum_congr fun m => by rw [dirichletTerm_add_one]

/-- **Splitting off the linear part of a periodic decomposition.**  If two
decompositions `τ ↦ A τ + τ * B τ` agree on the upper half plane, and all four functions
are `1`-periodic, then the decompositions coincide on the upper half plane. -/
lemma PeriodicAddSmulUHP {A₁ B₁ A₂ B₂ : ℂ → ℂ}
    (hA₁ : ∀ τ : ℂ, A₁ (τ + 1) = A₁ τ) (hA₂ : ∀ τ : ℂ, A₂ (τ + 1) = A₂ τ)
    (hB₁ : ∀ τ : ℂ, B₁ (τ + 1) = B₁ τ) (hB₂ : ∀ τ : ℂ, B₂ (τ + 1) = B₂ τ)
    (h : ∀ τ : ℂ, 0 < τ.im → A₁ τ + τ * B₁ τ = A₂ τ + τ * B₂ τ) :
    (∀ τ : ℂ, 0 < τ.im → A₁ τ = A₂ τ) ∧ (∀ τ : ℂ, 0 < τ.im → B₁ τ = B₂ τ) := by
  have hB : ∀ τ : ℂ, 0 < τ.im → B₁ τ = B₂ τ := by
    intro τ hτ
    have hτ1 : 0 < (τ + 1).im := by simpa using hτ
    have h1 := h τ hτ
    have h2 := h (τ + 1) hτ1
    rw [hA₁ τ, hA₂ τ, hB₁ τ, hB₂ τ] at h2
    have e3 : τ * (B₂ τ - B₁ τ) = (τ + 1) * (B₂ τ - B₁ τ) := by
      have e1 : A₁ τ - A₂ τ = τ * (B₂ τ - B₁ τ) := by linear_combination h1
      have e2 : A₁ τ - A₂ τ = (τ + 1) * (B₂ τ - B₁ τ) := by linear_combination h2
      exact e1 ▸ e2
    linear_combination e3
  refine ⟨?_, hB⟩
  intro τ hτ
  have h1 := h τ hτ
  rw [hB τ hτ] at h1
  exact add_right_cancel h1

/-- The radial derivative of order `1` along the axis is the ordinary derivative of the
radial profile. -/
lemma radialDeriv_one_of_nonneg {n : ℕ} [NeZero n] (g : E n → ℂ) {r : ℝ} (hr : 0 ≤ r) :
    radialDeriv 1 g (realIncl (n := n) r) = deriv (g ∘ realIncl (n := n)) r := by
  rw [radialDeriv, iteratedDeriv_one, Work.Sampling.realIncl_norm, abs_of_nonneg hr]
  rfl

/-- The radial derivative of order `0` at a sample point is evaluation. -/
lemma radialDeriv_zero_eq {n : ℕ} [NeZero n] (g : E n → ℂ) (k : Set.Ici (1 : ℕ)) :
    radialDeriv 0 g (samplePoint (n := n) (k.1 : ℝ)) = g (samplePoint (n := n) (k.1 : ℝ)) := by
  rw [radialDeriv, iteratedDeriv_zero]
  rw [show samplePoint (n := n) (k.1 : ℝ) = realIncl (Real.sqrt (2 * (k.1 : ℝ))) from rfl]
  rw [Work.Sampling.realIncl_norm, abs_of_nonneg (Real.sqrt_nonneg _)]

/-- The norm of `exp (-(2 π y m))` for real `y`, `m`. -/
lemma norm_exp_neg_real (y : ℝ) (m : ℕ) :
    ‖Complex.exp (-(2 * (Real.pi : ℂ) * (y : ℂ) * (m : ℝ)))‖
      = Real.exp (-(2 * Real.pi * (m : ℝ) * y)) := by
  have harg : -(2 * (Real.pi : ℂ) * (y : ℂ) * (m : ℝ))
      = -(((2 * Real.pi * y * (m : ℝ) : ℝ)) : ℂ) := by
    push_cast; ring
  rw [harg, Complex.norm_exp, Complex.neg_re, Complex.ofReal_re]
  congr 1
  ring

/-- Absolute convergence of a Dirichlet series on a horizontal line, from the absolute
convergence of the corresponding sequence of coefficients against the exponential decay
`e^{-2 π y m}`. -/
lemma summable_mul_dirichletTerm_of {c : Set.Ici (1 : ℕ) → ℂ} {y : ℝ}
    (hc : Summable fun m : Set.Ici (1 : ℕ) =>
      c m * Complex.exp (-(2 * (Real.pi : ℂ) * (y : ℂ) * (m.1 : ℝ))))
    {τ : ℂ} (hτ : τ.im = y) :
    Summable fun m : Set.Ici (1 : ℕ) => c m * dirichletTerm m.1 τ := by
  refine Summable.of_norm ?_
  refine hc.norm.congr fun m => ?_
  rw [norm_mul, norm_mul, normDirichletTermAux, hτ, norm_exp_neg_real]

/-- **Uniqueness of Dirichlet coefficients.**  If a Dirichlet series vanishes on a
horizontal line in the upper half plane, all its coefficients vanish. -/
theorem eqZeroOfTsumDirichletTerm {c : Set.Ici (1 : ℕ) → ℂ} {y : ℝ} (hy : 0 < y)
    (hsum : Summable fun m : Set.Ici (1 : ℕ) =>
      c m * Complex.exp (-(2 * (Real.pi : ℂ) * (y : ℂ) * (m.1 : ℝ))))
    (hzero : ∀ t : ℝ, ∑' m : Set.Ici (1 : ℕ),
      c m * dirichletTerm m.1 ((t : ℂ) + (y : ℂ) * Complex.I) = 0) :
    ∀ m, c m = 0 := by
  refine EqZeroOfTsumExp (c := c) (y := y) hy hsum fun t => ?_
  rw [← hzero t]
  apply tsum_congr
  intro m
  exact congrArg (fun z => c m * z)
    (dirichletTerm_eq_exp m.1 ((t : ℂ) + (y : ℂ) * Complex.I))

/-- **Two Dirichlet series agreeing on a horizontal line have equal coefficients.** -/
theorem DirichletCoeffUnique {c d : Set.Ici (1 : ℕ) → ℂ} {y : ℝ} (hy : 0 < y)
    (hc : Summable fun m : Set.Ici (1 : ℕ) =>
      c m * Complex.exp (-(2 * (Real.pi : ℂ) * (y : ℂ) * (m.1 : ℝ))))
    (hd : Summable fun m : Set.Ici (1 : ℕ) =>
      d m * Complex.exp (-(2 * (Real.pi : ℂ) * (y : ℂ) * (m.1 : ℝ))))
    (h : ∀ t : ℝ, (∑' m : Set.Ici (1 : ℕ),
        c m * dirichletTerm m.1 ((t : ℂ) + (y : ℂ) * Complex.I))
      = ∑' m : Set.Ici (1 : ℕ),
        d m * dirichletTerm m.1 ((t : ℂ) + (y : ℂ) * Complex.I)) :
    ∀ m : Set.Ici (1 : ℕ), c m = d m := by
  have hsub : Summable fun m : Set.Ici (1 : ℕ) =>
      (c m - d m) * Complex.exp (-(2 * (Real.pi : ℂ) * (y : ℂ) * (m.1 : ℝ))) :=
    (hc.sub hd).congr fun m => by ring
  have key := eqZeroOfTsumDirichletTerm (c := fun m => c m - d m) hy hsub ?_
  · intro m
    have hm := key m
    rwa [sub_eq_zero] at hm
  · intro t
    have hτ : (((t : ℂ) + (y : ℂ) * Complex.I)).im = y := by simp
    have hs1 : Summable fun m : Set.Ici (1 : ℕ) =>
        c m * dirichletTerm m.1 ((t : ℂ) + (y : ℂ) * Complex.I) :=
      summable_mul_dirichletTerm_of hc hτ
    have hs2 : Summable fun m : Set.Ici (1 : ℕ) =>
        d m * dirichletTerm m.1 ((t : ℂ) + (y : ℂ) * Complex.I) :=
      summable_mul_dirichletTerm_of hd hτ
    rw [show (fun m : Set.Ici (1 : ℕ) => (c m - d m) *
          dirichletTerm m.1 ((t : ℂ) + (y : ℂ) * Complex.I))
        = fun m : Set.Ici (1 : ℕ) => (c m * dirichletTerm m.1 ((t : ℂ) + (y : ℂ) * Complex.I)
            - d m * dirichletTerm m.1 ((t : ℂ) + (y : ℂ) * Complex.I))
        from funext fun m => by ring]
    rw [Summable.tsum_sub hs1 hs2, h t, sub_self]

/-- Polynomial growth of the coefficient families at the sample point of index `k`. -/
lemma basis_sample_bound {n : ℕ} [NeZero n] (S : InterpolationSolution n) (j : Fin 4)
    (k : Set.Ici (1 : ℕ)) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ m : Set.Ici (1 : ℕ),
      ‖(S.basis (m, j)).1 (samplePoint (n := n) (k.1 : ℝ))‖ ≤ C * ((m.1 : ℝ) + 1) ^ N := by
  obtain ⟨C, N, hC, h⟩ := S.growth_radial 0 0
  refine ⟨C, N, hC, fun m => ?_⟩
  have h1 := h m j (samplePoint (n := n) (k.1 : ℝ))
  rw [pow_zero, one_mul, radialDeriv_zero_eq] at h1
  exact h1

/-- Polynomial growth of the radial derivatives of the coefficient families at the
sample point of index `k`. -/
lemma radialDeriv_basis_sample_bound {n : ℕ} [NeZero n] (S : InterpolationSolution n)
    (j : Fin 4) (k : Set.Ici (1 : ℕ)) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ m : Set.Ici (1 : ℕ),
      ‖radialDeriv 1 (⇑(S.basis (m, j)).1) (samplePoint (n := n) (k.1 : ℝ))‖
        ≤ C * ((m.1 : ℝ) + 1) ^ N := by
  obtain ⟨C, N, hC, h⟩ := S.growth_radial 0 1
  refine ⟨C, N, hC, fun m => ?_⟩
  have h1 := h m j (samplePoint (n := n) (k.1 : ℝ))
  rw [pow_zero, one_mul] at h1
  exact h1

/-- The polynomial growth bound is preserved on multiplying by the rate `√(2 m)`. -/
lemma rate_mul_bound {c : Set.Ici (1 : ℕ) → ℂ} {C : ℝ} {N : ℕ} (hC : 0 ≤ C)
    (h : ∀ m : Set.Ici (1 : ℕ), ‖c m‖ ≤ C * ((m.1 : ℝ) + 1) ^ N) :
    ∃ C' : ℝ, ∃ N' : ℕ, 0 ≤ C' ∧ ∀ m : Set.Ici (1 : ℕ),
      ‖(rate m.1 : ℂ) * c m‖ ≤ C' * ((m.1 : ℝ) + 1) ^ N' := by
  refine ⟨C, N + 1, hC, fun m => ?_⟩
  have hm0 : (0 : ℝ) ≤ (m.1 : ℝ) + 1 := by positivity
  have hr : ‖(rate m.1 : ℂ)‖ = rate m.1 := by
    rw [rate, Complex.norm_of_nonneg (Real.sqrt_nonneg _)]
  rw [norm_mul, hr]
  calc rate m.1 * ‖c m‖ ≤ ((m.1 : ℝ) + 1) * (C * ((m.1 : ℝ) + 1) ^ N) :=
        mul_le_mul (rate_le_add_one m.1) (h m) (norm_nonneg _) hm0
    _ = C * ((m.1 : ℝ) + 1) ^ (N + 1) := by rw [pow_succ]; ring

/-- The rate `√(2 m)` is nonzero for `m ≥ 1`. -/
lemma rate_ne_zero (m : ℕ) (hm : 1 ≤ m) : (rate m : ℂ) ≠ 0 := by
  rw [Complex.ofReal_ne_zero]
  intro h
  have hpos : 0 < rate m := by
    rw [rate, Real.sqrt_pos]
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  exact absurd h (ne_of_gt hpos)

/-- `2 π i ≠ 0`. -/
lemma two_pi_I_ne_zero : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero
  exact_mod_cast Real.pi_ne_zero

end Work.FunctionalEquations.BasisDelta
