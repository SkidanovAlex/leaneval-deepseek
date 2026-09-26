import Mathlib

/-!
# Auxiliary estimates for `Work.FunctionalEquations.SeminormCompare`

Two elementary analytic facts are collected here.

* `exists_extraction_coeffs`: the `b`-th coefficient of a polynomial of degree `< Q`
  is a fixed linear combination of its values at the nodes `0, 1, …, Q - 1`.

* `taylor_remainder_bound_V`: Taylor's theorem with the Lagrange form of the remainder
  for `V`-valued functions on an interval, with the remainder bounded by the supremum
  of the `Q`-th derivative.
-/

open scoped ContDiff
open Polynomial

set_option linter.unusedVariables false

namespace Work.FunctionalEquations

/-- For every `Q` and every `b` there are real coefficients `α j` such that for all
`i : Fin Q` one has `∑ j, α j * (j : ℝ) ^ i = if i = b then 1 else 0`.  (For `b ≥ Q`
the right hand side vanishes identically and the coefficients given by the Lagrange
basis at `0, …, Q - 1` are all zero.) -/
theorem exists_extraction_coeffs (Q b : ℕ) :
    ∃ α : Fin Q → ℝ, ∀ i : Fin Q,
      ∑ j : Fin Q, α j * (j : ℝ) ^ (i : ℕ) = if (i : ℕ) = b then 1 else 0 := by
  classical
  refine ⟨fun j => (Lagrange.basis Finset.univ (fun j : Fin Q => (j : ℝ)) j).coeff b, ?_⟩
  intro i
  have hvs : Set.InjOn (fun j : Fin Q => (j : ℝ)) (↑(Finset.univ : Finset (Fin Q))) := by
    intro a _ c _ h
    exact Fin.ext (Nat.cast_injective h)
  have hdeg : (X ^ (i : ℕ) : Polynomial ℝ).degree <
      ((Finset.univ : Finset (Fin Q)).card : WithBot ℕ) := by
    rw [Finset.card_univ, Fintype.card_fin, degree_X_pow]
    exact_mod_cast i.isLt
  have hf := Lagrange.eq_interpolate (s := (Finset.univ : Finset (Fin Q)))
    (v := fun j : Fin Q => (j : ℝ)) (f := (X ^ (i : ℕ) : Polynomial ℝ)) hvs hdeg
  have h2 := congrArg (fun p : Polynomial ℝ => p.coeff b) hf
  rw [Lagrange.interpolate_apply] at h2
  simp only [finsetSum_coeff, coeff_C_mul, coeff_X_pow, eval_pow, eval_X] at h2
  have h2b : (∑ x : Fin Q,
        (x : ℝ) ^ (i : ℕ) * (Lagrange.basis Finset.univ (fun j : Fin Q => (j : ℝ)) x).coeff b)
      = if (i : ℕ) = b then 1 else 0 := by
    rw [h2.symm]
    by_cases h : b = (i : ℕ)
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hh => h hh.symm)]
  rw [← h2b]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- Taylor's theorem with the Lagrange remainder on an interval, for functions with
values in a normed space: if `‖g⁽Q⁾‖` is bounded by `N` on `Icc x₀ t` then the
difference of `g t` from its Taylor polynomial of degree `Q - 1` at `x₀` is at most
`N * (t - x₀)^Q / (Q - 1)!`. -/
theorem taylor_remainder_bound_V {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {g : ℝ → V} {Q : ℕ} (hQ : 1 ≤ Q) (hg : ContDiff ℝ (Q : ℕ∞ω) g)
    {x₀ t N : ℝ} (hxt : x₀ ≤ t) (hN : 0 ≤ N)
    (hgb : ∀ s ∈ Set.Icc x₀ t, ‖iteratedDeriv Q g s‖ ≤ N) :
    ‖g t - ∑ k ∈ Finset.range Q,
        ((Nat.factorial k : ℝ)⁻¹ * (t - x₀) ^ k) • iteratedDeriv k g x₀‖
      ≤ N * (t - x₀) ^ Q / ((Q - 1).factorial : ℝ) := by
  rcases eq_or_lt_of_le hxt with h | hlt
  · subst h
    have hsum : (∑ k ∈ Finset.range Q,
        ((Nat.factorial k : ℝ)⁻¹ * (x₀ - x₀) ^ k) • iteratedDeriv k g x₀) = g x₀ := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro k _ hk0
        rw [sub_self, zero_pow hk0]
        simp
      · intro h0
        exact absurd (Finset.mem_range.mpr (by omega)) h0
    rw [hsum, sub_self, norm_zero, sub_self, zero_pow (by omega : Q ≠ 0)]
    simp
  · have hdiff : ContDiffOn ℝ (((Q - 1 + 1 : ℕ)) : ℕ∞ω) g (Set.Icc x₀ t) := by
      rw [show ((Q - 1 + 1 : ℕ) : ℕ∞ω) = (Q : ℕ∞ω) from by
        rw [show Q - 1 + 1 = Q from by omega]]
      exact hg.contDiffOn
    have hC : ∀ y ∈ Set.Icc x₀ t,
        ‖iteratedDerivWithin (Q - 1 + 1) g (Set.Icc x₀ t) y‖ ≤ N := by
      intro y hy
      rw [show Q - 1 + 1 = Q from by omega]
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hlt) hg.contDiffAt hy]
      exact hgb y hy
    have hmain := taylor_mean_remainder_bound (f := g) (a := x₀) (b := t) (C := N)
      (n := Q - 1) hxt hdiff (Set.right_mem_Icc.mpr hxt) hC
    rw [taylor_within_apply] at hmain
    rw [show Q - 1 + 1 = Q from by omega] at hmain
    have hconv : (∑ k ∈ Finset.range Q,
          ((Nat.factorial k : ℝ)⁻¹ * (t - x₀) ^ k) • iteratedDerivWithin k g (Set.Icc x₀ t) x₀)
        = ∑ k ∈ Finset.range Q,
          ((Nat.factorial k : ℝ)⁻¹ * (t - x₀) ^ k) • iteratedDeriv k g x₀ := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hlt)
        ((hg.contDiffAt).of_le (by
          rw [Finset.mem_range] at hk
          exact_mod_cast hk.le)) (Set.left_mem_Icc.mpr hxt)]
    rw [hconv] at hmain
    exact hmain

end Work.FunctionalEquations
