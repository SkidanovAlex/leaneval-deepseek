import Mathlib
import Submission.Work.Resample.lamDefs

namespace Work.Resample

/-- The absolute value of `Int.fmod a t` is strictly smaller than that of a positive `t`. -/
theorem fmod_natAbs_lt (a t : ℤ) (ht : 0 < t) : (Int.fmod a t).natAbs < t.natAbs := by
  have hf : Int.fmod a t = a % t := by rw [Int.fmod_eq_emod]; simp [le_of_lt ht]
  rw [hf]
  have h1 : 0 ≤ a % t := Int.emod_nonneg a (ne_of_gt ht)
  rw [← Nat.cast_lt (α := ℤ), Int.natAbs_of_nonneg h1, Int.natAbs_of_nonneg (le_of_lt ht)]
  exact Int.emod_lt_of_pos a ht

/-- Basic size bounds for `HvdH.isz z = z.natAbs.size + 2` (the size of the integer value `z`):
multiplicativity, `neg`, `fmod` against a positive modulus, the universal lower bound `2`,
and the value at `0`. -/
theorem sigSizes :
    (∀ a b : ℤ, HvdH.isz (a * b) ≤ HvdH.isz a + HvdH.isz b) ∧
    (∀ a : ℤ, HvdH.isz (-a) = HvdH.isz a) ∧
    (∀ a t : ℤ, 0 < t → HvdH.isz (Int.fmod a t) ≤ HvdH.isz t) ∧
    (∀ z : ℤ, 2 ≤ HvdH.isz z) ∧ HvdH.isz (0 : ℤ) = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    have h : (a * b).natAbs = a.natAbs * b.natAbs := Int.natAbs_mul a b
    have h2 : (a.natAbs * b.natAbs).size ≤ a.natAbs.size + b.natAbs.size := by
      rw [Nat.size_le, Nat.pow_add]
      exact Nat.mul_lt_mul'' (Nat.lt_size_self _) (Nat.lt_size_self _)
    simp only [HvdH.isz, h]
    omega
  · intro a
    simp [HvdH.isz]
  · intro a t ht
    have h : (Int.fmod a t).natAbs < t.natAbs := fmod_natAbs_lt a t ht
    have h2 : (Int.fmod a t).natAbs.size ≤ t.natAbs.size := Nat.size_le_size (le_of_lt h)
    simp only [HvdH.isz]
    omega
  · intro z
    simp [HvdH.isz]
  · simp [HvdH.isz]

end Work.Resample
