import Mathlib
import Submission.Work.WilC5.Values

namespace Work.WilC5

/-- The product identity `(N+1)(M+1) = (N*M + N + M) + 1`, which lets the composition of two
natural multipliers be written again with a natural multiplier. -/
private lemma cast_mul_succ {K : Type} [Field K] (N M : ℕ) :
    ((N : K) + 1) * ((M : K) + 1) = ((N * M + N + M : ℕ) : K) + 1 := by
  push_cast; ring

theorem ValuesAPI {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    (∀ x : K, WilkiesDesign.CG.IsUnitVal x ↔ Work.WilC5.SameArch x 1) ∧
    (∀ x : K, Work.WilC5.SameArch x x) ∧
    (∀ x y : K, Work.WilC5.SameArch x y → Work.WilC5.SameArch y x) ∧
    (∀ x y z : K, Work.WilC5.SameArch x y → Work.WilC5.SameArch y z →
      Work.WilC5.SameArch x z) ∧
    (∀ x : K, Work.WilC5.VLe x x) ∧
    (∀ x y z : K, Work.WilC5.VLe x y → Work.WilC5.VLe y z → Work.WilC5.VLe x z) ∧
    (∀ x y : K, Work.WilC5.SameArch x y ↔ Work.WilC5.VLe x y ∧ Work.WilC5.VLe y x) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `IsUnitVal x ↔ SameArch x 1`
    intro x
    unfold WilkiesDesign.CG.IsUnitVal SameArch
    simp only [abs_one, mul_one]
    constructor
    · rintro ⟨N, hN, hxN⟩
      refine ⟨N, hxN, ?_⟩
      rw [inv_le_iff_one_le_mul₀ (by positivity)] at hN
      rwa [mul_comm] at hN
    · rintro ⟨N, hxN, hN⟩
      refine ⟨N, ?_, hxN⟩
      rw [inv_le_iff_one_le_mul₀ (by positivity)]
      rwa [mul_comm]
  · -- reflexivity of `SameArch`
    intro x
    exact ⟨0, by simp, by simp⟩
  · -- symmetry of `SameArch`
    rintro x y ⟨N, h1, h2⟩
    exact ⟨N, h2, h1⟩
  · -- transitivity of `SameArch`
    rintro x y z ⟨N1, a1, b1⟩ ⟨N2, a2, b2⟩
    refine ⟨N1 * N2 + N1 + N2, ?_, ?_⟩
    · calc |x| ≤ ((N1 : K) + 1) * |y| := a1
        _ ≤ ((N1 : K) + 1) * (((N2 : K) + 1) * |z|) :=
              mul_le_mul_of_nonneg_left a2 (by positivity)
        _ = (((N1 * N2 + N1 + N2 : ℕ) : K) + 1) * |z| := by
              rw [← cast_mul_succ N1 N2]; ring
    · calc |z| ≤ ((N2 : K) + 1) * |y| := b2
        _ ≤ ((N2 : K) + 1) * (((N1 : K) + 1) * |x|) :=
              mul_le_mul_of_nonneg_left b1 (by positivity)
        _ = (((N1 * N2 + N1 + N2 : ℕ) : K) + 1) * |x| := by
              rw [← cast_mul_succ N1 N2]; ring
  · -- reflexivity of `VLe`
    intro x
    exact ⟨0, by simp⟩
  · -- transitivity of `VLe`
    rintro x y z ⟨N1, a1⟩ ⟨N2, a2⟩
    refine ⟨N1 * N2 + N1 + N2, ?_⟩
    calc |z| ≤ ((N2 : K) + 1) * |y| := a2
      _ ≤ ((N2 : K) + 1) * (((N1 : K) + 1) * |x|) :=
            mul_le_mul_of_nonneg_left a1 (by positivity)
      _ = (((N1 * N2 + N1 + N2 : ℕ) : K) + 1) * |x| := by
            rw [← cast_mul_succ N1 N2]; ring
  · -- `SameArch x y ↔ VLe x y ∧ VLe y x`
    intro x y
    unfold SameArch VLe
    constructor
    · rintro ⟨N, a, b⟩
      exact ⟨⟨N, b⟩, ⟨N, a⟩⟩
    · rintro ⟨⟨N1, a1⟩, ⟨N2, b2⟩⟩
      refine ⟨max N1 N2, ?_, ?_⟩
      · apply le_trans b2
        have h : ((N2 : K) + 1) ≤ ((max N1 N2 : ℕ) : K) + 1 := by
          have := Nat.cast_le (α := K).mpr (le_max_right N1 N2); linarith
        exact mul_le_mul_of_nonneg_right h (abs_nonneg y)
      · apply le_trans a1
        have h : ((N1 : K) + 1) ≤ ((max N1 N2 : ℕ) : K) + 1 := by
          have := Nat.cast_le (α := K).mpr (le_max_left N1 N2); linarith
        exact mul_le_mul_of_nonneg_right h (abs_nonneg x)

end Work.WilC5
