import Mathlib
import Submission.Transcendence.LindemannC

/-!
# The powers of `log(1 − x)` are `ℚ(x)`-linearly independent (first step of
CDT Lemma `seven`)

The Calegari–Dimitrov–Tang paper (arXiv:2408.15403) proves its "pure
functions" `Bᵢ(y)` to be linearly independent over `ℂ(y)` (Lemma `seven`) by
reducing to the linear independence, over `ℚ(x)`, of the five functions
`1, log(1−x), log²(1−x), Li₂(x), J(x)`.  Of those, the first three are
independent "since `log(1−x)` is transcendental over `ℚ(x)`" — a statement
that rests on Lindemann–Weierstrass (the logarithm of a positive rational
`≠ 1` is transcendental), which is formalized in this repository
(`Submission.Transcendence.transcendental_log_rat`).

This module formalizes that first step: if a `ℚ[x]`-linear combination of
the functions `x ↦ log(1−x)^i` vanishes at the rational points
`x = 1 − 1/n` (all `n ≥ 2`) — where `log(1/n)` is transcendental — then all
coefficients vanish identically.

All declarations are fully proved (no axioms, no `sorry`).
-/

open scoped BigOperators

noncomputable section

namespace Submission.CDT

/-- **The powers of `log(1 − x)` are `ℚ(x)`-linearly independent.**
If `Σ_i pᵢ(1 − 1/n)·log(1/n)^i = 0` (in `ℂ`) for every `n ≥ 2`, with
`pᵢ ∈ ℚ[x]`, then every `pᵢ = 0`. -/
theorem log_powers_linearIndependent (K : ℕ) (p : Fin K → Polynomial ℚ)
    (h : ∀ n : ℕ, 2 ≤ n →
      ∑ i : Fin K, (((p i).eval (1 - ((n : ℚ))⁻¹) : ℚ) : ℂ)
        * (((Real.log ((((n : ℚ))⁻¹ : ℚ) : ℝ)) : ℝ) : ℂ) ^ (i : ℕ) = 0) :
    ∀ i, p i = 0 := by
  have hroot : ∀ n : ℕ, 2 ≤ n → ∀ j : Fin K, (p j).eval (1 - ((n : ℚ))⁻¹) = 0 := by
    intro n hn j
    have hn0 : (0 : ℚ) < (n : ℚ) := by exact_mod_cast (by omega : 0 < n)
    have hn1 : ((n : ℚ)) ≠ 1 := by
      intro hc
      have : (n : ℕ) = 1 := by exact_mod_cast hc
      omega
    have hqpos : 0 < ((n : ℚ))⁻¹ := inv_pos.mpr hn0
    have hqne : ((n : ℚ))⁻¹ ≠ 1 := by
      intro hc
      have : ((n : ℚ)) = 1 := by
        have h' := congrArg (fun x : ℚ => x⁻¹) hc
        rwa [inv_inv, inv_one] at h'
      exact hn1 this
    have hL : Transcendental ℚ (((Real.log ((((n : ℚ))⁻¹ : ℚ) : ℝ)) : ℝ) : ℂ) :=
      Submission.Transcendence.transcendental_log_rat hqpos hqne
    set P : Polynomial ℚ :=
      ∑ i : Fin K, Polynomial.C ((p i).eval (1 - ((n : ℚ))⁻¹)) * Polynomial.X ^ (i : ℕ) with hP
    have hzero :
        Polynomial.aeval (((Real.log ((((n : ℚ))⁻¹ : ℚ) : ℝ)) : ℝ) : ℂ) P = 0 := by
      have hterm : ∀ i : Fin K,
          Polynomial.aeval (((Real.log ((((n : ℚ))⁻¹ : ℚ) : ℝ)) : ℝ) : ℂ)
              (Polynomial.C ((p i).eval (1 - ((n : ℚ))⁻¹)) * Polynomial.X ^ (i : ℕ))
            = (((p i).eval (1 - ((n : ℚ))⁻¹) : ℚ) : ℂ)
              * (((Real.log ((((n : ℚ))⁻¹ : ℚ) : ℝ)) : ℝ) : ℂ) ^ (i : ℕ) := by
        intro i
        rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
        rfl
      rw [hP, map_sum, Finset.sum_congr rfl (fun i _ => hterm i), h n hn]
    have hP0 : P = 0 := (transcendental_iff.mp hL) P hzero
    have hcoeffval : P.coeff (j : ℕ) = (p j).eval (1 - ((n : ℚ))⁻¹) := by
      rw [hP]
      simp only [Polynomial.finsetSum_coeff]
      have hterm2 : ∀ i : Fin K,
          (Polynomial.C ((p i).eval (1 - ((n : ℚ))⁻¹)) * Polynomial.X ^ (i : ℕ)).coeff (j : ℕ)
            = if ((j : ℕ) = (i : ℕ)) then (p i).eval (1 - ((n : ℚ))⁻¹) else 0 := by
        intro i
        rw [Polynomial.coeff_C_mul_X_pow]
      rw [Finset.sum_congr rfl (fun i _ => hterm2 i)]
      have hsingle : (∑ i : Fin K,
            (if ((j : ℕ) = (i : ℕ)) then (p i).eval (1 - ((n : ℚ))⁻¹) else 0))
          = (if ((j : ℕ) = (j : ℕ)) then (p j).eval (1 - ((n : ℚ))⁻¹) else 0) :=
        Finset.sum_eq_single j
          (fun b _ hb => by
            rw [if_neg]
            rintro h
            exact hb (Fin.ext h.symm))
          (fun hj => absurd (Finset.mem_univ j) hj)
      rw [hsingle, if_pos rfl]
    have hcoeff := congrArg (fun Q : Polynomial ℚ => Q.coeff (j : ℕ)) hP0
    rw [hcoeffval, Polynomial.coeff_zero] at hcoeff
    exact hcoeff
  intro j
  refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero (p j)
    (f := fun i : Fin ((p j).natDegree + 3) => (1 - ((((i : ℕ) + 2 : ℕ)) : ℚ)⁻¹)) ?_ ?_ ?_
  · intro a b hab
    have h1 : (1 - ((((a : ℕ) + 2 : ℕ)) : ℚ)⁻¹ : ℚ) = 1 - ((((b : ℕ) + 2 : ℕ)) : ℚ)⁻¹ := hab
    have h2 : ((((a : ℕ) + 2 : ℕ)) : ℚ)⁻¹ = ((((b : ℕ) + 2 : ℕ)) : ℚ)⁻¹ := by linarith
    have h3 : ((((a : ℕ) + 2 : ℕ)) : ℚ) = ((((b : ℕ) + 2 : ℕ)) : ℚ) := by
      have := congrArg (fun x : ℚ => x⁻¹) h2
      rwa [inv_inv, inv_inv] at this
    have h4 : (a : ℕ) + 2 = (b : ℕ) + 2 := by exact_mod_cast h3
    exact Fin.ext (by omega)
  · intro i
    exact hroot ((i : ℕ) + 2) (by omega) j
  · simp only [Fintype.card_fin]
    omega

end Submission.CDT
