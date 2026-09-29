import Mathlib

namespace Work.TMC16Core.Basic

theorem toNat_interval_facts {k : ℕ} {x₁ x₂ y : ℤ} (hx : x₂ = x₁ + (k : ℤ) - 1)
    (h1 : x₁ ≤ y) (h2 : y ≤ x₂) :
    (x₂ - x₁ + 1).toNat = k ∧ (x₂ - x₁).toNat = k - 1 ∧
    (y - x₁).toNat ≤ k ∧ (x₂ - y).toNat ≤ k ∧
    k - (y - x₁).toNat = (x₂ - y).toNat + 1 ∧
    ((y - x₁).toNat : ℝ) = ((y - x₁ : ℤ) : ℝ) ∧
    ((x₂ - y).toNat : ℝ) = ((x₂ - y : ℤ) : ℝ) ∧
    (x₁ - x₁).toNat = 0 := by
  -- A nonempty interval [x₁, x₂] with x₂ = x₁ + k - 1 forces k ≥ 1.
  have hk : 1 ≤ k := by omega
  have hx1 : x₂ - x₁ = (k : ℤ) - 1 := by omega
  have hkz : (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub hk]; ring
  have hy0 : 0 ≤ y - x₁ := by omega
  have hz0 : 0 ≤ x₂ - y := by omega
  have hyk : y - x₁ ≤ (k : ℤ) := by omega
  have hzk : x₂ - y ≤ (k : ℤ) := by omega
  -- On the nonnegative side, `Int.toNat` is the identity.
  have hA : (((y - x₁).toNat : ℤ)) = y - x₁ := Int.toNat_of_nonneg hy0
  have hB : (((x₂ - y).toNat : ℤ)) = x₂ - y := Int.toNat_of_nonneg hz0
  -- The two pieces (y - x₁) and (x₂ - y) sum to k - 1.
  have hAB : (y - x₁).toNat + (x₂ - y).toNat = k - 1 := by
    apply Int.ofNat_inj.mp
    rw [Nat.cast_add, hA, hB, ← hkz]
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : x₂ - x₁ + 1 = (k : ℤ) := by omega
    rw [this, Int.toNat_natCast]
  · rw [hx1, hkz, Int.toNat_natCast]
  · exact Int.toNat_le.mpr hyk
  · exact Int.toNat_le.mpr hzk
  · omega
  · have hh := congrArg (fun z : ℤ => (z : ℝ)) hA
    exact hh
  · have hh := congrArg (fun z : ℤ => (z : ℝ)) hB
    exact hh
  · simp

end Work.TMC16Core.Basic
