import Mathlib
import Submission.Commons.Combinatorics.Transference.poly_lemma_monomial
import Submission.Commons.Combinatorics.Transference.poly_lemma_abstract

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

/-- Pairing `f` with a multivariate polynomial in the dual functions `𝒟F_i` is bounded by
`‖f‖_{U^d}` times a weighted sum of the coefficients. -/
theorem poly_lemma_mvpoly {p : ℕ} [Fact p.Prime] {d K : ℕ} (hd : 1 ≤ d) (f : ZMod p → ℝ)
    (F : Fin K → ZMod p → ℝ) (P : MvPolynomial (Fin K) ℝ)
    {ν τ : ZMod p → ℝ} (hν : ∀ x, 0 ≤ ν x) (hτ : ∀ x, 0 ≤ τ x)
    (hF : ∀ (j : Fin K) (x : ZMod p), |F j x| ≤ ν x)
    (hcorr : ∀ h : Fin d → ZMod p,
      (Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ y : ZMod p,
          ∏ ω : Fin d → Bool, ν (y + ∑ i, (if ω i then h i else 0))
        ≤ ∑ ω : Fin d → Bool, ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'),
            τ ((∑ i, (if ω' i then h i else 0)) - (∑ i, (if ω i then h i else 0))))
    {Cm : ℕ → ℝ} (hmom : ∀ q : ℕ,
      (Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ y : ZMod p, τ y ^ q ≤ Cm q) :
    |((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x : ZMod p, f x *
        MvPolynomial.eval (fun i : Fin K => davg d (F i) x) P|
      ≤ Unorm d f * ∑ m ∈ P.support, (|P.coeff m| *
          (1 + ((2 ^ d * 2 ^ d : ℕ) : ℝ) ^ (m.sum (fun _ n => n)) * Cm (m.sum (fun _ n => n)))) := by
  classical
  have hexp : ∀ x : ZMod p, MvPolynomial.eval (fun i : Fin K => davg d (F i) x) P
      = ∑ m ∈ P.support, P.coeff m * ∏ i : Fin K, (davg d (F i) x) ^ (m i) := by
    intro x
    rw [MvPolynomial.eval_eq']
  have hsum : ∑ x : ZMod p, f x * MvPolynomial.eval (fun i : Fin K => davg d (F i) x) P
      = ∑ m ∈ P.support, P.coeff m *
          (∑ x : ZMod p, f x * ∏ i : Fin K, (davg d (F i) x) ^ (m i)) := by
    calc ∑ x : ZMod p, f x * MvPolynomial.eval (fun i : Fin K => davg d (F i) x) P
        = ∑ x : ZMod p, f x *
            (∑ m ∈ P.support, P.coeff m * ∏ i : Fin K, (davg d (F i) x) ^ (m i)) := by
          apply Finset.sum_congr rfl; intro x _; rw [hexp x]
      _ = ∑ x : ZMod p, ∑ m ∈ P.support,
            f x * (P.coeff m * ∏ i : Fin K, (davg d (F i) x) ^ (m i)) := by
          apply Finset.sum_congr rfl; intro x _
          rw [Finset.mul_sum]
      _ = ∑ m ∈ P.support, ∑ x : ZMod p,
            f x * (P.coeff m * ∏ i : Fin K, (davg d (F i) x) ^ (m i)) := by
          rw [Finset.sum_comm]
      _ = ∑ m ∈ P.support, P.coeff m *
            (∑ x : ZMod p, f x * ∏ i : Fin K, (davg d (F i) x) ^ (m i)) := by
          apply Finset.sum_congr rfl; intro m _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro x _; ring
  rw [hsum]
  have hmain : |((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ m ∈ P.support, P.coeff m *
        (∑ x : ZMod p, f x * ∏ i : Fin K, (davg d (F i) x) ^ (m i))|
      ≤ ∑ m ∈ P.support, |P.coeff m| * (Unorm d f *
          (1 + ((2 ^ d * 2 ^ d : ℕ) : ℝ) ^ (m.sum (fun _ n => n)) * Cm (m.sum (fun _ n => n)))) := by
    calc |((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ m ∈ P.support, P.coeff m *
            (∑ x : ZMod p, f x * ∏ i : Fin K, (davg d (F i) x) ^ (m i))|
        = |∑ m ∈ P.support, P.coeff m * (((Fintype.card (ZMod p) : ℝ))⁻¹ *
            (∑ x : ZMod p, f x * ∏ i : Fin K, (davg d (F i) x) ^ (m i)))| := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro m _; ring
      _ ≤ ∑ m ∈ P.support, |P.coeff m * (((Fintype.card (ZMod p) : ℝ))⁻¹ *
            (∑ x : ZMod p, f x * ∏ i : Fin K, (davg d (F i) x) ^ (m i)))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ m ∈ P.support, |P.coeff m| * |((Fintype.card (ZMod p) : ℝ))⁻¹ *
            (∑ x : ZMod p, f x * ∏ i : Fin K, (davg d (F i) x) ^ (m i))| := by
          apply Finset.sum_congr rfl; intro m _; rw [abs_mul]
      _ ≤ ∑ m ∈ P.support, |P.coeff m| * (Unorm d f *
            (1 + ((2 ^ d * 2 ^ d : ℕ) : ℝ) ^ (m.sum (fun _ n => n)) * Cm (m.sum (fun _ n => n)))) := by
          apply Finset.sum_le_sum; intro m _
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          have hm := poly_lemma_monomial (p := p) (d := d) (K := K) hd f F (fun i : Fin K => m i)
            hν hτ hF hcorr (hmom (∑ i : Fin K, m i))
          have hkey : m.sum (fun _ n => n) = ∑ i : Fin K, m i := by
            rw [Finsupp.sum_fintype]; intro i; rfl
          rw [hkey]
          exact hm
  refine le_trans hmain (le_of_eq ?_)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro m _
  ring

end Commons.Combinatorics.Transference
