import Mathlib
import Submission.Work.BW.mvdefs
import Submission.Work.BW.fejer_sum_cos_sq_ge
import Submission.Work.BW.fejer_cosFourier_tail_ge
import Submission.Work.BW.sum_double_mul_ge

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Finset

theorem logMoment_sq_ge_lin {n : ℕ} (ε θ : Fin n → ℝ) (K : ℕ) (hK : 1 ≤ K)
    (hε0 : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j < 1) :
    ((K:ℝ)+1)/4 * ∑ j, (ε j)^2 - (∑ j, ε j) * (∑ j, Real.log (1/(1-ε j)))
      ≤ ∑ k ∈ Finset.Icc 1 K,
          (1 - (k:ℝ)/((K:ℝ)+1)) *
            (∑ j, Real.log ‖(1:ℂ) - (ε j : ℂ) * Complex.exp (2*Real.pi*Complex.I*(k:ℂ)*(θ j:ℂ))‖)^2 := by
  classical
  set F : ℕ → ℝ := fun k => ∑ j, cosFourier (ε j) ((k:ℝ) * (θ j)) with hF
  set A : ℕ → ℝ := fun k => ∑ j, ε j * Real.cos (2*Real.pi*k*(θ j)) with hA
  have hFk : ∀ k : ℕ, F k = ∑ j, cosFourier (ε j) ((k:ℝ) * (θ j)) := fun k => by simp only [hF]
  have hAk : ∀ k : ℕ, A k = ∑ j, ε j * Real.cos (2*Real.pi*k*(θ j)) := fun k => by simp only [hA]
  have hBk : ∀ k : ℕ, F k - A k = ∑ j, (cosFourier (ε j) ((k:ℝ) * (θ j)) - ε j * Real.cos (2*Real.pi*k*(θ j))) := by
    intro k
    rw [hFk k, hAk k, ← Finset.sum_sub_distrib]
  -- rewrite sigma_k = - F k
  have hσ : ∀ k : ℕ, (∑ j, Real.log ‖(1:ℂ) - (ε j : ℂ) * Complex.exp (2*Real.pi*Complex.I*(k:ℂ)*(θ j:ℂ))‖) = - F k := by
    intro k
    rw [hFk k, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [cosFourier_eq_log (ε j) (le_of_lt (hε0 j)) (hε1 j) ((k:ℝ)*(θ j)), neg_neg]
    congr 1
    rw [norm_sub_rev]
    congr 1
    have hexp : Complex.exp (2*Real.pi*Complex.I*(k:ℂ)*(θ j:ℂ))
        = Complex.exp (Complex.I * ↑(2*Real.pi*((k:ℝ)*(θ j)))) := by
      congr 1
      push_cast
      ring
    rw [hexp]
  -- the weight is fejerW
  have hw : ∀ k : ℕ, (1 - (k:ℝ)/((K:ℝ)+1)) = fejerW K k := by
    intro k
    rw [fejerW]
  -- piece 1
  have hA2 : ((K:ℝ)+1)/4 * (∑ j, (ε j)^2) - (1/2) * (∑ j, ε j)^2
      ≤ ∑ k ∈ Finset.Icc 1 K, fejerW K k * (A k)^2 := by
    have h := fejer_sum_cos_sq_ge ε θ K (fun j => le_of_lt (hε0 j))
    have heq : ∑ k ∈ Finset.Icc 1 K, fejerW K k * (A k)^2
        = ∑ k ∈ Finset.Icc 1 K, fejerW K k * (∑ j, ε j * Real.cos (2*Real.pi*k*(θ j)))^2 := by
      apply Finset.sum_congr rfl; intro k hk; rw [hAk k]
    rw [heq]; exact h
  -- piece 2
  have hAB : -(1/2) * ((∑ j, ε j) * ((∑ j, Real.log (1/(1-ε j))) - ∑ j, ε j))
      ≤ ∑ k ∈ Finset.Icc 1 K, fejerW K k * (A k) * (F k - A k) := by
    have hpair : ∀ i j, -(1/2) * (ε i * (Real.log (1/(1-ε j)) - ε j))
        ≤ ∑ k ∈ Finset.Icc 1 K, fejerW K k *
            ((ε i * Real.cos (2*Real.pi*k*(θ i))) * (cosFourier (ε j) ((k:ℝ)*(θ j)) - ε j * Real.cos (2*Real.pi*k*(θ j)))) := by
      intro i j
      have hp := fejer_cosFourier_tail_ge (le_of_lt (hε0 j)) (hε1 j) K (θ i) (θ j)
      have hεi : 0 ≤ ε i := le_of_lt (hε0 i)
      calc -(1/2) * (ε i * (Real.log (1/(1-ε j)) - ε j))
          = ε i * (-(1/2) * (Real.log (1/(1-ε j)) - ε j)) := by ring
        _ ≤ ε i * (∑ k ∈ Finset.Icc 1 K, fejerW K k * Real.cos (2*Real.pi*k*(θ i)) *
              (cosFourier (ε j) ((k:ℝ)*(θ j)) - ε j * Real.cos (2*Real.pi*k*(θ j)))) :=
              mul_le_mul_of_nonneg_left hp hεi
        _ = ∑ k ∈ Finset.Icc 1 K, fejerW K k *
              ((ε i * Real.cos (2*Real.pi*k*(θ i))) * (cosFourier (ε j) ((k:ℝ)*(θ j)) - ε j * Real.cos (2*Real.pi*k*(θ j)))) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl; intro k hk; ring
    have hmain := sum_double_mul_ge (s := Finset.Icc 1 K) (w := fejerW K)
        (U := fun i k => ε i * Real.cos (2*Real.pi*k*(θ i)))
        (V := fun j k => cosFourier (ε j) ((k:ℝ)*(θ j)) - ε j * Real.cos (2*Real.pi*k*(θ j)))
        (C := fun i j => -(1/2) * (ε i * (Real.log (1/(1-ε j)) - ε j))) hpair
    have hR : ∑ k ∈ Finset.Icc 1 K, fejerW K k * (∑ i, ε i * Real.cos (2*Real.pi*k*(θ i))) *
          (∑ j, (cosFourier (ε j) ((k:ℝ)*(θ j)) - ε j * Real.cos (2*Real.pi*k*(θ j))))
        = ∑ k ∈ Finset.Icc 1 K, fejerW K k * (A k) * (F k - A k) := by
      apply Finset.sum_congr rfl; intro k hk
      rw [hAk k, hBk k]
    have h1 : (∑ j, (Real.log (1/(1-ε j)) - ε j)) = (∑ j, Real.log (1/(1-ε j))) - ∑ j, ε j :=
      Finset.sum_sub_distrib (fun j => Real.log (1/(1-ε j))) (fun j => ε j)
    have h2 : (∑ j, ε j) * (∑ j, (Real.log (1/(1-ε j)) - ε j))
        = ∑ i, ∑ j, ε i * (Real.log (1/(1-ε j)) - ε j) := by
      rw [Finset.sum_mul_sum]
    have hL : ∑ i, ∑ j, -(1/2) * (ε i * (Real.log (1/(1-ε j)) - ε j))
        = -(1/2) * ((∑ j, ε j) * ((∑ j, Real.log (1/(1-ε j))) - ∑ j, ε j)) := by
      rw [← h1, h2, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i hi
      rw [Finset.mul_sum]
    calc -(1/2) * ((∑ j, ε j) * ((∑ j, Real.log (1/(1-ε j))) - ∑ j, ε j))
        = ∑ i, ∑ j, -(1/2) * (ε i * (Real.log (1/(1-ε j)) - ε j)) := hL.symm
      _ ≤ ∑ k ∈ Finset.Icc 1 K, fejerW K k * (∑ i, ε i * Real.cos (2*Real.pi*k*(θ i))) *
            (∑ j, (cosFourier (ε j) ((k:ℝ)*(θ j)) - ε j * Real.cos (2*Real.pi*k*(θ j)))) := hmain
      _ = ∑ k ∈ Finset.Icc 1 K, fejerW K k * (A k) * (F k - A k) := hR
  -- drop the square
  have hconv : ∑ k ∈ Finset.Icc 1 K, fejerW K k * (A k)^2
        + 2 * (∑ k ∈ Finset.Icc 1 K, fejerW K k * (A k) * (F k - A k))
      ≤ ∑ k ∈ Finset.Icc 1 K, fejerW K k * (F k)^2 := by
    have hpt : ∀ k ∈ Finset.Icc 1 K,
        fejerW K k * (A k)^2 + 2 * (fejerW K k * (A k) * (F k - A k)) ≤ fejerW K k * (F k)^2 := by
      intro k hk
      have hk' : k ≤ K + 1 := by have := (Finset.mem_Icc.mp hk).2; omega
      have hw0 : 0 ≤ fejerW K k := fejerW_nonneg hk'
      have hid : fejerW K k * (F k)^2 - (fejerW K k * (A k)^2 + 2 * (fejerW K k * (A k) * (F k - A k)))
          = fejerW K k * (F k - A k)^2 := by ring
      nlinarith [hid, mul_nonneg hw0 (sq_nonneg (F k - A k))]
    have hs := Finset.sum_le_sum hpt
    have hs2 : ∑ k ∈ Finset.Icc 1 K, (fejerW K k * (A k)^2 + 2 * (fejerW K k * (A k) * (F k - A k)))
        = ∑ k ∈ Finset.Icc 1 K, fejerW K k * (A k)^2
          + 2 * (∑ k ∈ Finset.Icc 1 K, fejerW K k * (A k) * (F k - A k)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    linarith [hs, hs2]
  -- assemble
  simp_rw [hw, hσ, neg_sq]
  linarith [hconv, hA2, hAB, sq_nonneg (∑ j, ε j)]

end Work.BW
