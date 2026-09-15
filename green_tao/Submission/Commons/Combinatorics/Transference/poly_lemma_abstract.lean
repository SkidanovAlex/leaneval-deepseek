import Mathlib
import Submission.Commons.Combinatorics.Transference.Unorm_pow
import Submission.Commons.Combinatorics.Transference.Unorm_nonneg
import Submission.Commons.Combinatorics.Transference.Kfold_dual_eq
import Submission.Commons.Combinatorics.Transference.gcs_fold_Unorm
import Submission.Commons.Combinatorics.Transference.sum_prod_Unorm_le
import Submission.Commons.Combinatorics.Transference.cubeSum_nonneg

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

/-- The dual function `𝒟F(x) = |G|^{-d} ∑_h ∏_{ω ≠ 0} F (x + ω·h)`. -/
noncomputable def davg {G : Type*} [AddCommGroup G] [Fintype G] (d : ℕ) (F : G → ℝ) (x : G) : ℝ :=
  ((Fintype.card (Fin d → G) : ℝ))⁻¹ * (∑ h : Fin d → G,
    ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)), F (x + ∑ i, (if ω i then h i else 0)))

private lemma pow_inv_mul_arith (N U B : ℝ) (d K : ℕ) (hN : N ≠ 0) :
    (N ^ d)⁻¹ * (N ^ (d + 1) * U * (N ^ (d * K) * (1 + B))) = N ^ (1 + d * K) * U * (1 + B) := by
  have h1 : N ^ d ≠ 0 := pow_ne_zero _ hN
  have e1 : N ^ (d + 1) = N ^ d * N := pow_succ _ _
  have e2 : N ^ (1 + d * K) = N * N ^ (d * K) := by rw [pow_add, pow_one]
  rw [e1, e2,
      show (N ^ d)⁻¹ * (N ^ d * N * U * (N ^ (d * K) * (1 + B)))
        = ((N ^ d)⁻¹ * N ^ d) * (N * U * (N ^ (d * K) * (1 + B))) by ring,
      inv_mul_cancel₀ h1, one_mul,
      show N * U * (N ^ (d * K) * (1 + B)) = N * N ^ (d * K) * U * (1 + B) by ring]

private lemma pow_inv_mul_arith2 (N U B : ℝ) (d K : ℕ) (hN : N ≠ 0) :
    N⁻¹ * ((N ^ d)⁻¹) ^ K * (N ^ (1 + d * K) * U * (1 + B)) = U * (1 + B) := by
  have e : ((N ^ d)⁻¹) ^ K = (N ^ (d * K))⁻¹ := by rw [inv_pow, pow_mul]
  have e2 : N ^ (1 + d * K) = N * N ^ (d * K) := by rw [pow_add, pow_one]
  calc N⁻¹ * ((N ^ d)⁻¹) ^ K * (N ^ (1 + d * K) * U * (1 + B))
      = (N⁻¹ * N) * ((N ^ (d * K))⁻¹ * N ^ (d * K)) * (U * (1 + B)) := by rw [e, e2]; ring
    _ = U * (1 + B) := by
        rw [inv_mul_cancel₀ hN, inv_mul_cancel₀ (pow_ne_zero _ hN)]; ring

/-- **Green–Tao Lemma 6.6 (polynomial lemma), abstract core.**  If the `H`-averages of the
cube sums of `g_{ω·H}(x) = ∏_j F_j (x + ω·H_j)` are bounded by `Bm`, then the pairing of `f`
with the product of the `K` dual functions is bounded by `‖f‖_{U^d} (1 + Bm)`. -/
theorem poly_lemma_abstract {G : Type*} [AddCommGroup G] [Fintype G] (d : ℕ) (hd : 1 ≤ d)
    {K : ℕ} (f : G → ℝ) (F : Fin K → G → ℝ) {Bm : ℝ}
    (hB : ∀ ω : Fin d → Bool, ω ≠ 0 →
      ((Fintype.card G : ℝ) ^ (d * K))⁻¹ * ((Fintype.card G : ℝ) ^ (d+1))⁻¹ *
        (∑ H : Fin K → Fin d → G, ∑ h : Fin d → G, ∑ x : G,
          ∏ ω' : Fin d → Bool, ∏ j : Fin K,
            F j (x + (∑ i, if ω' i then h i else 0) + (∑ i, if ω i then H j i else 0))) ≤ Bm) :
    |((Fintype.card G : ℝ))⁻¹ * ∑ x : G, f x * ∏ j : Fin K, davg d (F j) x|
      ≤ Unorm d f * (1 + Bm) := by
  classical
  set N : ℝ := (Fintype.card G : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast Fintype.card_pos_iff.mpr ⟨(0 : G)⟩
  have hNne : N ≠ 0 := ne_of_gt hNpos
  have hNd : ((Fintype.card (Fin d → G) : ℝ)) = N ^ d := by
    rw [Fintype.card_fun, Fintype.card_fin]; push_cast; rw [hN]
  have hB' : ∀ ω : Fin d → Bool, ω ≠ 0 →
      (N ^ (d * K))⁻¹ * (N ^ (d+1))⁻¹ *
        (∑ H : Fin K → Fin d → G, ∑ h : Fin d → G, ∑ x : G,
          ∏ ω' : Fin d → Bool, ∏ j : Fin K,
            F j (x + (∑ i, if ω' i then h i else 0) + (∑ i, if ω i then H j i else 0))) ≤ Bm := by
    intro ω hω; exact hB ω hω
  have hID := Kfold_dual_eq d K f F
  rw [← hN] at hID
  set Ssum := ∑ x : G, f x * ∏ j : Fin K, (∑ h : Fin d → G,
        ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)), F j (x + ∑ i, (if ω i then h i else 0))) with hSsum
  set T := ∑ (H : Fin K → Fin d → G) (h : Fin d → G) (x : G),
          f x * ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)), ∏ j : Fin K,
            F j (x + (∑ i, (if ω i then h i else 0)) + (∑ i, (if ω i then H j i else 0))) with hT
  have hID' : Ssum = (N ^ d)⁻¹ * T := by
    rw [hSsum, hT]; exact hID
  have hbracket : ∀ H : Fin K → Fin d → G,
      |∑ h : Fin d → G, ∑ x : G, f x * ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)),
        ∏ j : Fin K, F j (x + (∑ i, (if ω i then h i else 0)) + (∑ i, (if ω i then H j i else 0)))|
      ≤ N ^ (d+1) * Unorm d f *
          ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)),
            Unorm d (fun x => ∏ j : Fin K, F j (x + ∑ i, (if ω i then H j i else 0))) := by
    intro H
    have h := gcs_fold_Unorm d hd f F H
    rw [← hN] at h
    exact h
  have hTnested : T = ∑ H : Fin K → Fin d → G, ∑ h : Fin d → G, ∑ x : G,
          f x * ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)), ∏ j : Fin K,
            F j (x + (∑ i, (if ω i then h i else 0)) + (∑ i, (if ω i then H j i else 0))) := by
    rw [hT]
    exact Kfold_sum_binder3
      (fun (H : Fin K → Fin d → G) (h : Fin d → G) (x : G) =>
        f x * ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)), ∏ j : Fin K,
          F j (x + (∑ i, (if ω i then h i else 0)) + (∑ i, (if ω i then H j i else 0))))
  have hTbound : |T| ≤ N ^ (d+1) * Unorm d f *
      (∑ H : Fin K → Fin d → G, ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)),
        Unorm d (fun x => ∏ j : Fin K, F j (x + ∑ i, (if ω i then H j i else 0)))) := by
    rw [hTnested]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro H _
    exact hbracket H
  have hsum := sum_prod_Unorm_le d hd (K := K) F hB'
  have hNdnn : (0:ℝ) ≤ N ^ d := pow_nonneg (le_of_lt hNpos) _
  have hTfinal : |T| ≤ N ^ (d+1) * Unorm d f * (N ^ (d*K) * (1 + Bm)) := by
    refine le_trans hTbound ?_
    exact mul_le_mul_of_nonneg_left hsum
      (mul_nonneg (pow_nonneg (le_of_lt hNpos) _) (Unorm_nonneg d hd f))
  have hSbound : |Ssum| ≤ N ^ (1 + d*K) * Unorm d f * (1 + Bm) := by
    rw [hID', abs_mul, abs_of_nonneg (inv_nonneg.mpr hNdnn)]
    calc (N ^ d)⁻¹ * |T|
        ≤ (N ^ d)⁻¹ * (N ^ (d+1) * Unorm d f * (N ^ (d*K) * (1 + Bm))) :=
          mul_le_mul_of_nonneg_left hTfinal (inv_nonneg.mpr hNdnn)
      _ = N ^ (1 + d*K) * Unorm d f * (1 + Bm) := pow_inv_mul_arith N (Unorm d f) Bm d K hNne
  have hstep : ∀ x : G, (∏ j : Fin K, davg d (F j) x)
      = ((N ^ d)⁻¹) ^ K * ∏ j : Fin K, (∑ h : Fin d → G,
          ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)), F j (x + ∑ i, (if ω i then h i else 0))) := by
    intro x
    rw [show (∏ j : Fin K, davg d (F j) x)
        = ∏ j : Fin K, ((N ^ d)⁻¹ * (∑ h : Fin d → G,
            ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)), F j (x + ∑ i, (if ω i then h i else 0)))) from by
      apply Finset.prod_congr rfl; intro j _
      rw [davg, hNd]]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hdav : (∑ x : G, f x * ∏ j : Fin K, davg d (F j) x) = ((N ^ d)⁻¹) ^ K * Ssum := by
    rw [hSsum]
    rw [show (∑ x : G, f x * ∏ j : Fin K, davg d (F j) x)
        = ∑ x : G, f x * (((N ^ d)⁻¹) ^ K * ∏ j : Fin K, (∑ h : Fin d → G,
            ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)), F j (x + ∑ i, (if ω i then h i else 0)))) from by
      apply Finset.sum_congr rfl; intro x _; rw [hstep x]]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro x _
    ring
  rw [hdav]
  have habs : |N⁻¹ * (((N ^ d)⁻¹) ^ K * Ssum)| = N⁻¹ * ((N ^ d)⁻¹) ^ K * |Ssum| := by
    rw [abs_mul, abs_mul, abs_of_nonneg (inv_nonneg.mpr (le_of_lt hNpos)),
        abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hNdnn) _), mul_assoc]
  rw [habs]
  calc N⁻¹ * ((N ^ d)⁻¹) ^ K * |Ssum|
      ≤ N⁻¹ * ((N ^ d)⁻¹) ^ K * (N ^ (1 + d*K) * Unorm d f * (1 + Bm)) :=
        mul_le_mul_of_nonneg_left hSbound
          (mul_nonneg (inv_nonneg.mpr (le_of_lt hNpos)) (pow_nonneg (inv_nonneg.mpr hNdnn) _))
    _ = Unorm d f * (1 + Bm) := pow_inv_mul_arith2 N (Unorm d f) Bm d K hNne

end Commons.Combinatorics.Transference
