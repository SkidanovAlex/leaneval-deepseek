import Mathlib

namespace Work.Resample

/-- Auxiliary: for `p ≥ 3`, `(p+1)^4` is at least `3`. -/
private lemma three_le_pow (p : ℕ) (hp : 100 ≤ p) : (3 : ℕ) ≤ (p+1)^4 := by
  have h : (3 : ℕ) ≤ p + 1 := by omega
  exact le_trans (by norm_num) (Nat.pow_le_pow_left h 4)

theorem auWtLCostPoly (p : ℕ) (hp : 100 ≤ p) :
    (4*p+3)*(10*p+401) ≤ (p+1)^8 ∧
    (4*p+1)*(10*p+401) + (4*p+1)*(4*p+2) + 2 ≤ (p+1)^8 ∧
    (4*p+1)*(20*p+802) + 1 ≤ (p+1)^8 ∧
    4*p+1 ≤ (p+1)^2 := by
  have hpow : (p+1)^2 * (p+1)^2 = (p+1)^4 := by ring
  have h8 : (p+1)^4 * (p+1)^4 = (p+1)^8 := by ring
  have hle : (p+1)^4 ≤ (p+1)^8 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h3le : (3 : ℕ) ≤ (p+1)^4 := three_le_pow p hp
  have h2le : (2 : ℕ) ≤ (p+1)^4 := le_trans (by norm_num) h3le
  have h1le : (1 : ℕ) ≤ (p+1)^4 := Nat.one_le_pow 4 (p+1) (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hA : 4*p+3 ≤ (p+1)^2 := by nlinarith [hp]
    have hB : 10*p+401 ≤ (p+1)^2 := by nlinarith [hp]
    calc (4*p+3)*(10*p+401) ≤ (p+1)^2*(p+1)^2 := Nat.mul_le_mul hA hB
      _ = (p+1)^4 := hpow
      _ ≤ (p+1)^8 := hle
  · have hA1 : 4*p+1 ≤ (p+1)^2 := by nlinarith [hp]
    have hA2 : 4*p+2 ≤ (p+1)^2 := by nlinarith [hp]
    have hB : 10*p+401 ≤ (p+1)^2 := by nlinarith [hp]
    have e1 : (4*p+1)*(10*p+401) ≤ (p+1)^4 := by
      calc (4*p+1)*(10*p+401) ≤ (p+1)^2*(p+1)^2 := Nat.mul_le_mul hA1 hB
        _ = (p+1)^4 := hpow
    have e2 : (4*p+1)*(4*p+2) ≤ (p+1)^4 := by
      calc (4*p+1)*(4*p+2) ≤ (p+1)^2*(p+1)^2 := Nat.mul_le_mul hA1 hA2
        _ = (p+1)^4 := hpow
    calc (4*p+1)*(10*p+401) + (4*p+1)*(4*p+2) + 2
        ≤ (p+1)^4 + (p+1)^4 + (p+1)^4 := add_le_add (add_le_add e1 e2) h2le
      _ = 3*(p+1)^4 := by ring
      _ ≤ (p+1)^4*(p+1)^4 := Nat.mul_le_mul_right _ h3le
      _ = (p+1)^8 := h8
  · have hA1 : 4*p+1 ≤ (p+1)^2 := by nlinarith [hp]
    have hC : 20*p+802 ≤ 2*(p+1)^2 := by nlinarith [hp]
    have e1 : (4*p+1)*(20*p+802) ≤ 2*(p+1)^4 := by
      calc (4*p+1)*(20*p+802) ≤ (p+1)^2*(2*(p+1)^2) := Nat.mul_le_mul hA1 hC
        _ = 2*(p+1)^4 := by ring
    calc (4*p+1)*(20*p+802) + 1 ≤ 2*(p+1)^4 + (p+1)^4 := add_le_add e1 h1le
      _ = 3*(p+1)^4 := by ring
      _ ≤ (p+1)^4*(p+1)^4 := Nat.mul_le_mul_right _ h3le
      _ = (p+1)^8 := h8
  · nlinarith [hp]

end Work.Resample
