import Mathlib
import Submission.Work.A3.Defs

/-!
# `𝓕(A_N f) = m_N · f̂` (the Fourier multiplier identity for the polynomial average)

For a finitely supported `f : ℤ → ℂ` and the polynomial average

`A_N f(x) = N⁻¹ ∑_{n ∈ [1,N]} f(x - Q(n))`

one has `𝓕(A_N f)(θ) = m_N(θ) · f̂(θ)` for every frequency `θ`, where

`m_N(θ) = N⁻¹ ∑_{n ∈ [1,N]} e(-θ Q(n))`  (`Work.A3.kmtMul`)

is the multiplier of `A_N` and `f̂(θ) = ∑_x f(x) e(-θ x)` (`Work.A3.kmtFhat`).

This is the identity that converts the `ℓ²`-estimate for `A_N` (Plancherel) into the pointwise
bound `|m_N f̂|`, and hence -- with `Work.A3.moment_identity` and `Work.A3.hausdorffYoung` --
into the `ℓ^p`-improving estimate of Area A3.

The proof is the standard one: since `f` is finitely supported, both sides are finite sums.  The
inner reindexing `y ↦ y - Q(n)` uses that `e(-θ(x + c)) = e(-θx)·e(-θc)`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.A3

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- The Fourier character `e(-θx) = exp(-2πi x θ)` of `ℤ` at frequency `θ`. -/
private def kmtE (θ : ℝ) (x : ℤ) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℝ) * θ)))

/-- The character is multiplicative in the position: `e(-θ(x+c)) = e(-θx) e(-θc)`. -/
private lemma kmtE_add (θ : ℝ) (x c : ℤ) : kmtE θ (x + c) = kmtE θ x * kmtE θ c := by
  simp only [kmtE]
  rw [show -(2 * Real.pi * Complex.I * (((x + c : ℤ) : ℝ) * θ))
      = -(2 * Real.pi * Complex.I * ((x : ℝ) * θ))
        + -(2 * Real.pi * Complex.I * ((c : ℝ) * θ)) by
    push_cast
    ring]
  rw [Complex.exp_add]

/-- For a function supported in a finite set `s`, `kmtFhat` is the finite sum over `s`. -/
private lemma kmtFhat_eq_sum (f : ℤ → ℂ) (s : Finset ℤ) (h : ∀ x ∉ s, f x = 0) (θ : ℝ) :
    kmtFhat f θ = ∑ x ∈ s, f x * kmtE θ x := by
  simp only [kmtFhat, kmtE]
  exact tsum_eq_sum (fun x hx => by rw [h x hx, zero_mul])

/-- Reindexing the `θ`-sum of a translate of a finitely supported `f`. -/
private lemma sum_shift_eq (f : ℤ → ℂ) (s : Finset ℤ) (h : ∀ x ∉ s, f x = 0) (θ : ℝ)
    (c : ℤ) (T : Finset ℤ) (hA : s.image (fun x => x + c) ⊆ T) :
    ∑ y ∈ T, f (y - c) * kmtE θ y = (∑ x ∈ s, f x * kmtE θ x) * kmtE θ c := by
  have h1 : ∑ y ∈ T, f (y - c) * kmtE θ y
      = ∑ y ∈ s.image (fun x => x + c), f (y - c) * kmtE θ y := by
    refine (Finset.sum_subset hA ?_).symm
    intro y hyT hyA
    have hyc : y - c ∉ s := fun hmem =>
      hyA (Finset.mem_image.mpr ⟨y - c, hmem, by ring⟩)
    rw [h _ hyc, zero_mul]
  rw [h1, Finset.sum_image (fun x _ y _ hxy => add_right_cancel hxy), Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [show x + c - c = x by ring, kmtE_add, mul_assoc]

/-- **Fourier multiplier identity for the polynomial average.**  The Fourier transform of the
averaging operator `A_N f(x) = N⁻¹ ∑_{n ∈ [1,N]} f(x - Q(n))` is multiplication of `f̂` by the
symbol `m_N(θ) = N⁻¹ ∑_{n ∈ [1,N]} e(-θ Q(n))`. -/
theorem fhat_conv (Q : Polynomial ℤ) (N : ℕ) (f : ℤ → ℂ) (hf : ∃ s : Finset ℤ, ∀ x ∉ s, f x = 0)
    (hN : 1 ≤ N) (θ : ℝ) : Work.A3.kmtFhat (fun x : ℤ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, f (x - Polynomial.eval (n : ℤ) Q)) θ = Work.A3.kmtMul Q N θ * Work.A3.kmtFhat f θ := by
  obtain ⟨s, hs⟩ := hf
  -- The averaging operator is supported in `T := ⋃_{n ∈ [1,N]} (s + Q(n))`.
  set T : Finset ℤ := (Finset.Icc 1 N).biUnion
      (fun n => s.image (fun x => x + Polynomial.eval (n : ℤ) Q)) with hT
  have hsupp : ∀ y ∉ T, (N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N,
      f (y - Polynomial.eval (n : ℤ) Q) = 0 := by
    intro y hy
    have hzero : ∑ n ∈ Finset.Icc 1 N, f (y - Polynomial.eval (n : ℤ) Q) = 0 := by
      refine Finset.sum_eq_zero (fun n hn => ?_)
      refine hs _ (fun hmem => hy ?_)
      rw [hT, Finset.mem_biUnion]
      exact ⟨n, hn, Finset.mem_image.mpr ⟨y - Polynomial.eval (n : ℤ) Q, hmem, by ring⟩⟩
    rw [hzero, mul_zero]
  -- Both sides are finite sums now.
  rw [kmtFhat_eq_sum _ T hsupp θ, kmtFhat_eq_sum f s hs θ]
  -- Pull the factor `N⁻¹` and the character out of the inner sum, then exchange the sums.
  have step1 : ∑ y ∈ T, ((N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N,
        f (y - Polynomial.eval (n : ℤ) Q)) * kmtE θ y
      = (N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N,
          ∑ y ∈ T, f (y - Polynomial.eval (n : ℤ) Q) * kmtE θ y := by
    calc ∑ y ∈ T, ((N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N,
            f (y - Polynomial.eval (n : ℤ) Q)) * kmtE θ y
        = ∑ y ∈ T, (N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N,
            f (y - Polynomial.eval (n : ℤ) Q) * kmtE θ y := by
          refine Finset.sum_congr rfl (fun y _ => ?_)
          rw [mul_assoc, Finset.sum_mul]
      _ = (N : ℂ)⁻¹ * ∑ y ∈ T, ∑ n ∈ Finset.Icc 1 N,
            f (y - Polynomial.eval (n : ℤ) Q) * kmtE θ y := by
          rw [Finset.mul_sum]
      _ = (N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, ∑ y ∈ T,
            f (y - Polynomial.eval (n : ℤ) Q) * kmtE θ y := by
          rw [Finset.sum_comm]
  -- Translate-invariance of the character sum: only `y = x + Q(n)` contributes.
  have step2 : ∀ n ∈ Finset.Icc 1 N,
      ∑ y ∈ T, f (y - Polynomial.eval (n : ℤ) Q) * kmtE θ y
        = kmtE θ (Polynomial.eval (n : ℤ) Q) * (∑ x ∈ s, f x * kmtE θ x) := by
    intro n hn
    have hA : s.image (fun x => x + Polynomial.eval (n : ℤ) Q) ⊆ T := by
      intro y hy
      rw [hT, Finset.mem_biUnion]
      exact ⟨n, hn, hy⟩
    rw [sum_shift_eq f s hs θ (Polynomial.eval (n : ℤ) Q) T hA, mul_comm]
  have step3 : ∑ n ∈ Finset.Icc 1 N, ∑ y ∈ T,
        f (y - Polynomial.eval (n : ℤ) Q) * kmtE θ y
      = (∑ n ∈ Finset.Icc 1 N, kmtE θ (Polynomial.eval (n : ℤ) Q))
        * (∑ x ∈ s, f x * kmtE θ x) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun n hn => step2 n hn)
  -- Identify the remaining exponential sum with the multiplier `kmtMul`.
  have hS : (∑ n ∈ Finset.Icc 1 N, kmtE θ (Polynomial.eval (n : ℤ) Q))
      = ∑ n ∈ Finset.Icc 1 N, Complex.exp
          (-(2 * Real.pi * Complex.I * (((Polynomial.eval (n : ℤ) Q : ℤ) : ℝ) * θ))) := by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [kmtE]
  rw [step1, step3, hS]
  unfold kmtMul
  ring

end

end Work.A3
