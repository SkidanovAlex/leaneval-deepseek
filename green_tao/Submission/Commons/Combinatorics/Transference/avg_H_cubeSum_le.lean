import Mathlib
import Submission.Commons.Combinatorics.Transference.avg_H_nu_sum_eq
import Submission.Commons.Combinatorics.Transference.avg_H_pair_bound

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

/-- The `H`-average of the cube average of `g_{ω·H}(x) = ∏_j F_j (x + ω·H_j)` is bounded,
using the majorant `ν` and the correlation condition.  This is the "correlation condition"
step of the polynomial lemma (Green–Tao Lemma 6.6). -/
theorem avg_H_cubeSum_le {p : ℕ} [Fact p.Prime] {d K : ℕ} (hd : 1 ≤ d) {ν τ : ZMod p → ℝ}
    (F : Fin K → ZMod p → ℝ) (hν : ∀ x, 0 ≤ ν x) (hτ : ∀ x, 0 ≤ τ x)
    (hF : ∀ (j : Fin K) (x : ZMod p), |F j x| ≤ ν x) {Cm : ℝ}
    (hcorr : ∀ h : Fin d → ZMod p,
      (Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ y : ZMod p,
          ∏ ω : Fin d → Bool, ν (y + ∑ i, (if ω i then h i else 0))
        ≤ ∑ ω : Fin d → Bool, ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'),
            τ ((∑ i, (if ω' i then h i else 0)) - (∑ i, (if ω i then h i else 0))))
    (hmom : (Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ y : ZMod p, τ y ^ K ≤ Cm)
    (ω : Fin d → Bool) (hω : ω ≠ 0) :
    ((Fintype.card (ZMod p) : ℝ) ^ (d * K))⁻¹ * ((Fintype.card (ZMod p) : ℝ) ^ (d + 1))⁻¹ *
      (∑ H : Fin K → Fin d → ZMod p, ∑ h : Fin d → ZMod p, ∑ x : ZMod p,
        ∏ ω' : Fin d → Bool, ∏ j : Fin K,
          F j (x + (∑ i, (if ω' i then h i else 0)) + (∑ i, (if ω i then H j i else 0))))
    ≤ ((2 ^ d * 2 ^ d : ℕ) : ℝ) ^ K * Cm := by
  classical
  set n : ℝ := (Fintype.card (ZMod p) : ℝ) with hn
  have hnpos : 0 < n := by
    rw [hn]; exact_mod_cast (Fintype.card_pos_iff.mpr ⟨0⟩)
  -- pointwise domination `F ↦ ν`
  have hpoint : ∀ (H : Fin K → Fin d → ZMod p) (h : Fin d → ZMod p) (x : ZMod p),
      (∏ ω' : Fin d → Bool, ∏ j : Fin K,
          F j (x + (∑ i, (if ω' i then h i else 0)) + (∑ i, (if ω i then H j i else 0))))
      ≤ ∏ ω' : Fin d → Bool, ∏ j : Fin K,
          ν (x + (∑ i, (if ω' i then h i else 0)) + (∑ i, (if ω i then H j i else 0))) := by
    intro H h x
    calc (∏ ω' : Fin d → Bool, ∏ j : Fin K,
          F j (x + (∑ i, (if ω' i then h i else 0)) + (∑ i, (if ω i then H j i else 0))))
        ≤ |∏ ω' : Fin d → Bool, ∏ j : Fin K,
          F j (x + (∑ i, (if ω' i then h i else 0)) + (∑ i, (if ω i then H j i else 0)))| :=
            le_abs_self _
      _ = ∏ ω' : Fin d → Bool, |∏ j : Fin K,
          F j (x + (∑ i, (if ω' i then h i else 0)) + (∑ i, (if ω i then H j i else 0)))| :=
            Finset.abs_prod _ _
      _ = ∏ ω' : Fin d → Bool, ∏ j : Fin K,
          |F j (x + (∑ i, (if ω' i then h i else 0)) + (∑ i, (if ω i then H j i else 0)))| := by
            simp_rw [Finset.abs_prod]
      _ ≤ ∏ ω' : Fin d → Bool, ∏ j : Fin K,
          ν (x + (∑ i, (if ω' i then h i else 0)) + (∑ i, (if ω i then H j i else 0))) := by
            apply Finset.prod_le_prod
            · intro ω' _
              exact Finset.prod_nonneg (fun j _ => abs_nonneg _)
            · intro ω' _
              exact Finset.prod_le_prod (fun j _ => abs_nonneg _) (fun j _ => hF j _)
  have hAFν : (∑ H : Fin K → Fin d → ZMod p, ∑ h : Fin d → ZMod p, ∑ x : ZMod p,
        ∏ ω' : Fin d → Bool, ∏ j : Fin K,
          F j (x + (∑ i, (if ω' i then h i else 0)) + (∑ i, (if ω i then H j i else 0))))
      ≤ (∑ H : Fin K → Fin d → ZMod p, ∑ h : Fin d → ZMod p, ∑ x : ZMod p,
        ∏ ω' : Fin d → Bool, ∏ j : Fin K,
          ν (x + (∑ i, (if ω' i then h i else 0)) + (∑ i, (if ω i then H j i else 0)))) := by
    apply Finset.sum_le_sum; intro H _
    apply Finset.sum_le_sum; intro h _
    apply Finset.sum_le_sum; intro x _
    exact hpoint H h x
  have hνeq := avg_H_nu_sum_eq (p := p) (K := K) hd (ν := ν) hν ω hω
  have hpt2 : ∀ h : Fin d → ZMod p,
      (n⁻¹ * (∑ y : ZMod p, ∏ ω' : Fin d → Bool,
          ν (y + ∑ i, (if ω' i then h i else 0)))) ^ K
      ≤ (∑ ω : Fin d → Bool, ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'),
          τ ((∑ i, (if ω' i then h i else 0)) - (∑ i, (if ω i then h i else 0)))) ^ K := by
    intro h
    refine pow_le_pow_left₀ ?_ (hcorr h) K
    exact mul_nonneg (inv_nonneg.mpr (le_of_lt hnpos))
      (Finset.sum_nonneg (fun y _ => Finset.prod_nonneg (fun ω' _ => hν _)))
  have hpair := avg_H_pair_bound (p := p) hd (τ := τ) hτ hmom
  have harith : ∀ X : ℝ,
      (n ^ (d * K))⁻¹ * (n ^ (d + 1))⁻¹ * (n ^ (d * K + 1) * X) = (n ^ d)⁻¹ * X := by
    intro X
    rw [pow_succ n (d * K), show n ^ (d + 1) = n ^ d * n from by rw [pow_succ]]
    field_simp
  calc (n ^ (d * K))⁻¹ * (n ^ (d + 1))⁻¹ *
        (∑ H : Fin K → Fin d → ZMod p, ∑ h : Fin d → ZMod p, ∑ x : ZMod p,
          ∏ ω' : Fin d → Bool, ∏ j : Fin K,
            F j (x + (∑ i, (if ω' i then h i else 0)) + (∑ i, (if ω i then H j i else 0))))
      ≤ (n ^ (d * K))⁻¹ * (n ^ (d + 1))⁻¹ *
        (∑ H : Fin K → Fin d → ZMod p, ∑ h : Fin d → ZMod p, ∑ x : ZMod p,
          ∏ ω' : Fin d → Bool, ∏ j : Fin K,
            ν (x + (∑ i, (if ω' i then h i else 0)) + (∑ i, (if ω i then H j i else 0)))) := by
        apply mul_le_mul_of_nonneg_left hAFν
        exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (le_of_lt hnpos) _))
          (inv_nonneg.mpr (pow_nonneg (le_of_lt hnpos) _))
    _ = (n ^ (d * K))⁻¹ * (n ^ (d + 1))⁻¹ *
          (n ^ (d * K + 1) * ∑ h : Fin d → ZMod p,
            (n⁻¹ * (∑ y : ZMod p, ∏ ω' : Fin d → Bool,
              ν (y + ∑ i, (if ω' i then h i else 0)))) ^ K) := by rw [hνeq]
    _ = (n ^ d)⁻¹ * ∑ h : Fin d → ZMod p,
            (n⁻¹ * (∑ y : ZMod p, ∏ ω' : Fin d → Bool,
              ν (y + ∑ i, (if ω' i then h i else 0)))) ^ K := by
        rw [harith]
    _ ≤ (n ^ d)⁻¹ * ∑ h : Fin d → ZMod p,
            (∑ ω : Fin d → Bool, ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'),
              τ ((∑ i, (if ω' i then h i else 0)) - (∑ i, (if ω i then h i else 0)))) ^ K := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (pow_nonneg (le_of_lt hnpos) d))
        apply Finset.sum_le_sum; intro h _
        exact hpt2 h
    _ ≤ ((2 ^ d * 2 ^ d : ℕ) : ℝ) ^ K * Cm := hpair

end Commons.Combinatorics.Transference
