import Mathlib
import Submission.Commons.Combinatorics.Transference.poly_lemma_mvpoly
import Submission.Commons.Analysis.Approximation.exists_mvpolynomial_near_of_continuousOn
import Submission.Commons.Combinatorics.Transference.Unorm_nonneg
import Submission.Commons.Combinatorics.Transference.poly_lemma_abstract

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

/-- **Green–Tao Proposition 6.5 (`weier`), quantitative form.**  For a continuous `Φ` on
the cube `[-M, M]^K` and any `η > 0` there is a constant `E` such that, for any `f` and any
`F_1, …, F_K` majored by `ν` whose dual functions take values in `[-M, M]`,
`|𝔼_x f(x) Φ(𝒟F_1 x, …, 𝒟F_K x)| ≤ ‖f‖_{U^d} · E + η · 𝔼|f|`. -/
theorem weier_bound {p : ℕ} [Fact p.Prime] {d K : ℕ} (hd : 1 ≤ d) {M : ℝ} (hM : 0 ≤ M)
    {ν τ : ZMod p → ℝ} (hν : ∀ x, 0 ≤ ν x) (hτ : ∀ x, 0 ≤ τ x)
    (hcorr : ∀ h : Fin d → ZMod p,
      (Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ y : ZMod p,
          ∏ ω : Fin d → Bool, ν (y + ∑ i, (if ω i then h i else 0))
        ≤ ∑ ω : Fin d → Bool, ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'),
            τ ((∑ i, (if ω' i then h i else 0)) - (∑ i, (if ω i then h i else 0))))
    {Cm : ℕ → ℝ} (hmom : ∀ q : ℕ,
      (Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ y : ZMod p, τ y ^ q ≤ Cm q)
    (Φ : (Fin K → ℝ) → ℝ)
    (hΦ : ContinuousOn Φ (Set.pi Set.univ (fun _ : Fin K => Set.Icc (-M) M)))
    {η : ℝ} (hη : 0 < η) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (f : ZMod p → ℝ) (F : Fin K → ZMod p → ℝ),
        (∀ (j : Fin K) (x : ZMod p), |F j x| ≤ ν x) →
        (∀ (j : Fin K) (x : ZMod p), |davg d (F j) x| ≤ M) →
      |((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x : ZMod p, f x * Φ (fun j : Fin K => davg d (F j) x)|
        ≤ Unorm d f * E + η * (((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x : ZMod p, |f x|) := by
  classical
  obtain ⟨P, hP⟩ :=
    Commons.Analysis.Approximation.exists_mvpolynomial_near_of_continuousOn M hM Φ hΦ hη
  let E : ℝ := ∑ m ∈ P.support, |P.coeff m| *
    (1 + ((2 ^ d * 2 ^ d : ℕ) : ℝ) ^ (m.sum (fun _ n => n)) * Cm (m.sum (fun _ n => n)))
  have hCm_nn : ∀ q : ℕ, 0 ≤ Cm q := by
    intro q
    refine le_trans ?_ (hmom q)
    refine mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) ?_
    exact Finset.sum_nonneg (fun y _ => pow_nonneg (hτ y) q)
  refine ⟨E, ?_, ?_⟩
  · dsimp only [E]
    exact Finset.sum_nonneg (fun m _ => mul_nonneg (abs_nonneg _)
      (add_nonneg zero_le_one (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (hCm_nn _))))
  · intro f F hF hD
    have hcpos : (0 : ℝ) < (Fintype.card (ZMod p) : ℝ) := by
      have h : 0 < Fintype.card (ZMod p) := Fintype.card_pos_iff.mpr ⟨(0 : ZMod p)⟩
      exact_mod_cast h
    have hinvnn : (0 : ℝ) ≤ ((Fintype.card (ZMod p) : ℝ))⁻¹ :=
      inv_nonneg.mpr (le_of_lt hcpos)
    have hpt : ∀ x : ZMod p,
        |Φ (fun j : Fin K => davg d (F j) x)
          - MvPolynomial.eval (fun j : Fin K => davg d (F j) x) P| ≤ η := by
      intro x
      apply hP
      rw [Set.mem_pi]
      intro j _
      exact abs_le.mp (hD j x)
    have hsplit : (∑ x : ZMod p, f x * Φ (fun j : Fin K => davg d (F j) x))
        = (∑ x : ZMod p, f x * MvPolynomial.eval (fun j : Fin K => davg d (F j) x) P)
          + ∑ x : ZMod p, f x * (Φ (fun j : Fin K => davg d (F j) x)
              - MvPolynomial.eval (fun j : Fin K => davg d (F j) x) P) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro x _; ring
    have hpoly := poly_lemma_mvpoly (p := p) (d := d) (K := K) hd f F P hν hτ hF hcorr hmom
    have hsecond : |((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x : ZMod p, f x *
          (Φ (fun j : Fin K => davg d (F j) x)
            - MvPolynomial.eval (fun j : Fin K => davg d (F j) x) P)|
        ≤ η * (((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x : ZMod p, |f x|) := by
      rw [abs_mul, abs_of_nonneg hinvnn]
      calc ((Fintype.card (ZMod p) : ℝ))⁻¹ * |∑ x : ZMod p, f x *
              (Φ (fun j : Fin K => davg d (F j) x)
                - MvPolynomial.eval (fun j : Fin K => davg d (F j) x) P)|
          ≤ ((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x : ZMod p, |f x *
              (Φ (fun j : Fin K => davg d (F j) x)
                - MvPolynomial.eval (fun j : Fin K => davg d (F j) x) P)| :=
            mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hinvnn
        _ ≤ ((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x : ZMod p, |f x| * η := by
            apply mul_le_mul_of_nonneg_left _ hinvnn
            apply Finset.sum_le_sum; intro x _
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hpt x) (abs_nonneg _)
        _ = η * (((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x : ZMod p, |f x|) := by
            rw [← Finset.sum_mul]; ring
    calc |((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x : ZMod p, f x *
            Φ (fun j : Fin K => davg d (F j) x)|
        = |((Fintype.card (ZMod p) : ℝ))⁻¹ *
              ((∑ x : ZMod p, f x * MvPolynomial.eval (fun j : Fin K => davg d (F j) x) P)
                + ∑ x : ZMod p, f x * (Φ (fun j : Fin K => davg d (F j) x)
                    - MvPolynomial.eval (fun j : Fin K => davg d (F j) x) P))| := by
            rw [hsplit]
      _ = |((Fintype.card (ZMod p) : ℝ))⁻¹ *
                (∑ x : ZMod p, f x * MvPolynomial.eval (fun j : Fin K => davg d (F j) x) P)
              + ((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x : ZMod p, f x *
                (Φ (fun j : Fin K => davg d (F j) x)
                  - MvPolynomial.eval (fun j : Fin K => davg d (F j) x) P)| := by
            rw [mul_add]
      _ ≤ |((Fintype.card (ZMod p) : ℝ))⁻¹ *
                (∑ x : ZMod p, f x * MvPolynomial.eval (fun j : Fin K => davg d (F j) x) P)|
              + |((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x : ZMod p, f x *
                (Φ (fun j : Fin K => davg d (F j) x)
                  - MvPolynomial.eval (fun j : Fin K => davg d (F j) x) P)| :=
            abs_add_le _ _
      _ ≤ Unorm d f * E + η * (((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x : ZMod p, |f x|) :=
            add_le_add hpoly hsecond

end Commons.Combinatorics.Transference
