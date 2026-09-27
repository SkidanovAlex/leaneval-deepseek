import Mathlib
import Submission.Work.KT.Psi.Basic

namespace Work.KT.Psi

theorem proj2_orth {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ}
    (K S : Matrix (Fin m) (Fin m) A) (hK : K * K = K) (hS : S * S = 1) (hKS : K * S = S * K) :
    (K * ((1 / 2 : ℂ) • (1 + S))) * (K * ((1 / 2 : ℂ) • (1 + S))) = K * ((1 / 2 : ℂ) • (1 + S)) ∧
    (K * ((1 / 2 : ℂ) • (1 - S))) * (K * ((1 / 2 : ℂ) • (1 - S))) = K * ((1 / 2 : ℂ) • (1 - S)) ∧
    K * ((1 / 2 : ℂ) • (1 + S)) + K * ((1 / 2 : ℂ) • (1 - S)) = K ∧
    (K * ((1 / 2 : ℂ) • (1 + S))) * (K * ((1 / 2 : ℂ) • (1 - S))) = 0 ∧
    (K * ((1 / 2 : ℂ) • (1 - S))) * (K * ((1 / 2 : ℂ) • (1 + S))) = 0 := by
  -- `K` commutes with the two scalar-multiplied factors.
  have hKT : K * ((1 / 2 : ℂ) • (1 + S)) = ((1 / 2 : ℂ) • (1 + S)) * K := by
    have h : K * (1 + S) = (1 + S) * K := by rw [mul_add, mul_one, add_mul, one_mul, hKS]
    rw [Matrix.mul_smul, Matrix.smul_mul, h]
  have hKU : K * ((1 / 2 : ℂ) • (1 - S)) = ((1 / 2 : ℂ) • (1 - S)) * K := by
    have h : K * (1 - S) = (1 - S) * K := by rw [mul_sub, mul_one, sub_mul, one_mul, hKS]
    rw [Matrix.mul_smul, Matrix.smul_mul, h]
  -- The two halves are idempotent.
  have hTT : ((1 / 2 : ℂ) • (1 + S)) * ((1 / 2 : ℂ) • (1 + S)) = (1 / 2 : ℂ) • (1 + S) := by
    have h : (1 + S) * (1 + S) = (2 : ℂ) • (1 + S) := by
      rw [mul_add, mul_one, add_mul, one_mul, hS, two_smul]; abel
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h, smul_smul]; norm_num
  have hUU : ((1 / 2 : ℂ) • (1 - S)) * ((1 / 2 : ℂ) • (1 - S)) = (1 / 2 : ℂ) • (1 - S) := by
    have h : (1 - S) * (1 - S) = (2 : ℂ) • (1 - S) := by
      rw [sub_mul, one_mul, mul_sub, mul_one, hS, two_smul]; abel
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h, smul_smul]; norm_num
  -- They are orthogonal.
  have hTU : ((1 / 2 : ℂ) • (1 + S)) * ((1 / 2 : ℂ) • (1 - S)) = 0 := by
    have h : (1 + S) * (1 - S) = 0 := by
      rw [mul_sub, mul_one, add_mul, one_mul, hS]; abel
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h, smul_zero]
  have hUT : ((1 / 2 : ℂ) • (1 - S)) * ((1 / 2 : ℂ) • (1 + S)) = 0 := by
    have h : (1 - S) * (1 + S) = 0 := by
      rw [sub_mul, one_mul, mul_add, mul_one, hS]; abel
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h, smul_zero]
  -- They sum to one.
  have hT1 : ((1 / 2 : ℂ) • (1 + S)) + ((1 / 2 : ℂ) • (1 - S)) = 1 := by
    rw [← smul_add]
    have h : (1 + S) + (1 - S) = (2 : ℂ) • (1 : Matrix (Fin m) (Fin m) A) := by
      rw [two_smul]; abel
    rw [h, smul_smul]; norm_num
  -- Now assemble with the elementary ring facts.
  have idem : ∀ {p q : Matrix (Fin m) (Fin m) A}, p * p = p → q * q = q → p * q = q * p →
      (p * q) * (p * q) = p * q := by
    intro p q hp hq h
    calc (p * q) * (p * q) = p * (q * p) * q := by noncomm_ring
      _ = p * (p * q) * q := by rw [← h]
      _ = (p * p) * (q * q) := by noncomm_ring
      _ = p * q := by rw [hp, hq]
  have orth : ∀ {k t u : Matrix (Fin m) (Fin m) A}, k * k = k → k * t = t * k → t * u = 0 →
      (k * t) * (k * u) = 0 := by
    intro k t u hk hkt htu
    calc (k * t) * (k * u) = k * (t * k) * u := by noncomm_ring
      _ = k * (k * t) * u := by rw [← hkt]
      _ = (k * k) * (t * u) := by noncomm_ring
      _ = 0 := by rw [hk, htu, mul_zero]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact idem hK hTT hKT
  · exact idem hK hUU hKU
  · rw [← mul_add, hT1, mul_one]
  · exact orth hK hKT hTU
  · exact orth hK hKU hUT

end Work.KT.Psi
