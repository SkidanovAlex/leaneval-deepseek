import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

lemma descFactorial_floor_mul_le {N r : ℕ} (hNr : N < r) (ρ : ℕ)
    (δ : Fin (N + 1) → ℝ) (hδnn : ∀ i, 0 ≤ δ i) (J : Finset (Fin N)) :
    ((N + 1).descFactorial (ρ + 1) : ℝ) * ((⌊δ 0⌋₊ : ℕ) : ℝ) *
        ∏ i ∈ J, ((⌊δ i.succ⌋₊ : ℕ) : ℝ) ≤
      ((r + 1).descFactorial (ρ + 1) : ℝ) * δ 0 * ∏ i ∈ J, δ i.succ := by
  have hmono : ((N + 1).descFactorial (ρ + 1) : ℝ) ≤ ((r + 1).descFactorial (ρ + 1) : ℝ) := by
    exact Nat.cast_le.mpr (Nat.descFactorial_le (ρ + 1) (by omega : N + 1 ≤ r + 1))
  have h0 : ((⌊δ 0⌋₊ : ℕ) : ℝ) ≤ δ 0 := Nat.floor_le (hδnn 0)
  have hp : ∏ i ∈ J, ((⌊δ i.succ⌋₊ : ℕ) : ℝ) ≤ ∏ i ∈ J, δ i.succ := by
    apply Finset.prod_le_prod₀
    · intro i _; exact Nat.cast_nonneg _
    · intro i _; exact Nat.floor_le (hδnn i.succ)
  have hp0 : 0 ≤ ∏ i ∈ J, ((⌊δ i.succ⌋₊ : ℕ) : ℝ) :=
    Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _)
  have hB : 0 ≤ δ 0 := hδnn 0
  have hpd : 0 ≤ ∏ i ∈ J, δ i.succ := Finset.prod_nonneg (fun i _ => hδnn i.succ)
  have hh : ((N + 1).descFactorial (ρ + 1) : ℝ) * ((⌊δ 0⌋₊ : ℕ) : ℝ) ≤
            ((N + 1).descFactorial (ρ + 1) : ℝ) * δ 0 :=
    mul_le_mul_of_nonneg_left h0 (Nat.cast_nonneg _)
  calc ((N + 1).descFactorial (ρ + 1) : ℝ) * ((⌊δ 0⌋₊ : ℕ) : ℝ)
        * ∏ i ∈ J, ((⌊δ i.succ⌋₊ : ℕ) : ℝ)
      ≤ ((N + 1).descFactorial (ρ + 1) : ℝ) * δ 0 * ∏ i ∈ J, δ i.succ :=
        mul_le_mul hh hp hp0 (mul_nonneg (Nat.cast_nonneg _) hB)
    _ ≤ ((r + 1).descFactorial (ρ + 1) : ℝ) * δ 0 * ∏ i ∈ J, δ i.succ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmono hB) hpd

end Work.BW
