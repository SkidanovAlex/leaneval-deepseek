import Mathlib
import Submission.Commons.Combinatorics.Transference.poly_lemma_mvpoly
import Submission.Commons.Combinatorics.Transference.Unorm_nonneg

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

theorem weier_poly_bound {p : ℕ} [Fact p.Prime] {d K : ℕ} (hd : 1 ≤ d) {M : ℝ} (hM : 0 ≤ M)
    {ν τ : ZMod p → ℝ} (hν : ∀ x, 0 ≤ ν x) (hτ : ∀ x, 0 ≤ τ x)
    (hcorr : ∀ h : Fin d → ZMod p,
      (Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ y : ZMod p,
          ∏ ω : Fin d → Bool, ν (y + ∑ i, (if ω i then h i else 0))
        ≤ ∑ ω : Fin d → Bool, ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'),
            τ ((∑ i, (if ω' i then h i else 0)) - (∑ i, (if ω i then h i else 0))))
    {Cm : ℕ → ℝ} (hmom : ∀ q : ℕ, (Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ y : ZMod p, τ y ^ q ≤ Cm q)
    (P : MvPolynomial (Fin K) ℝ) {Φ : (Fin K → ℝ) → ℝ} {η' : ℝ} (hη' : 0 ≤ η')
    (happrox : ∀ t ∈ Set.pi Set.univ (fun _ : Fin K => Set.Icc (-M) M),
      |Φ t - MvPolynomial.eval t P| ≤ η')
    (f : ZMod p → ℝ) (F : Fin K → ZMod p → ℝ)
    (hF : ∀ (j : Fin K) (x : ZMod p), |F j x| ≤ ν x)
    (hFd : ∀ (j : Fin K) (x : ZMod p), |davg d (F j) x| ≤ M) :
    |((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x : ZMod p, f x * Φ (fun j : Fin K => davg d (F j) x)|
      ≤ Unorm d f * (∑ m ∈ P.support, (|P.coeff m| *
            (1 + (((2 ^ d * 2 ^ d : ℕ)) : ℝ) ^ (m.sum (fun _ n => n)) *
              Cm (m.sum (fun _ n => n)))))
        + η' * (((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x : ZMod p, |f x|) := by
  classical
  set E : ℝ := ∑ m ∈ P.support, (|P.coeff m| *
      (1 + (((2 ^ d * 2 ^ d : ℕ)) : ℝ) ^ (m.sum (fun _ n => n)) *
        Cm (m.sum (fun _ n => n)))) with hE
  have hpt : ∀ x : ZMod p,
      |Φ (fun j : Fin K => davg d (F j) x)
        - MvPolynomial.eval (fun j : Fin K => davg d (F j) x) P| ≤ η' := by
    intro x
    apply happrox
    rw [Set.mem_pi]
    intro j _
    exact abs_le.mp (hFd j x)
  have hpoly := poly_lemma_mvpoly (p := p) (d := d) (K := K) hd f F P hν hτ hF hcorr hmom
  rw [← hE] at hpoly
  have hcpos : (0 : ℝ) < (Fintype.card (ZMod p) : ℝ) := by
    have h : 0 < Fintype.card (ZMod p) := Fintype.card_pos_iff.mpr ⟨(0 : ZMod p)⟩
    exact_mod_cast h
  have hinvnn : (0 : ℝ) ≤ ((Fintype.card (ZMod p) : ℝ))⁻¹ :=
    inv_nonneg.mpr (le_of_lt hcpos)
  have hsplit : ((Fintype.card (ZMod p) : ℝ))⁻¹ *
        ∑ x : ZMod p, f x * Φ (fun j : Fin K => davg d (F j) x)
      = ((Fintype.card (ZMod p) : ℝ))⁻¹ *
          (∑ x : ZMod p, f x * MvPolynomial.eval (fun j : Fin K => davg d (F j) x) P)
        + ((Fintype.card (ZMod p) : ℝ))⁻¹ *
          (∑ x : ZMod p, f x *
            (Φ (fun j : Fin K => davg d (F j) x)
              - MvPolynomial.eval (fun j : Fin K => davg d (F j) x) P)) := by
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl; intro x _
    ring
  have hsecond : |((Fintype.card (ZMod p) : ℝ))⁻¹ *
        ∑ x : ZMod p, f x *
          (Φ (fun j : Fin K => davg d (F j) x)
            - MvPolynomial.eval (fun j : Fin K => davg d (F j) x) P)|
      ≤ η' * (((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x : ZMod p, |f x|) := by
    rw [abs_mul, abs_of_nonneg hinvnn]
    calc ((Fintype.card (ZMod p) : ℝ))⁻¹ *
            |∑ x : ZMod p, f x *
              (Φ (fun j : Fin K => davg d (F j) x)
                - MvPolynomial.eval (fun j : Fin K => davg d (F j) x) P)|
        ≤ ((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x : ZMod p, |f x *
              (Φ (fun j : Fin K => davg d (F j) x)
                - MvPolynomial.eval (fun j : Fin K => davg d (F j) x) P)| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hinvnn
      _ ≤ ((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x : ZMod p, |f x| * η' := by
          apply mul_le_mul_of_nonneg_left _ hinvnn
          apply Finset.sum_le_sum; intro x _
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hpt x) (abs_nonneg _)
      _ = η' * (((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x : ZMod p, |f x|) := by
          rw [← Finset.sum_mul]; ring
  rw [hsplit]
  refine le_trans (abs_add_le _ _) ?_
  exact add_le_add hpoly hsecond

end Commons.Combinatorics.Transference
