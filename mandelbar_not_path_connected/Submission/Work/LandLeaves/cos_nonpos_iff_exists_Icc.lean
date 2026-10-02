import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

/-- `sin` is nonnegative exactly on the union of the intervals `[2πk, π + 2πk]`. -/
lemma sin_nonneg_iff_exists_Icc (y : ℝ) :
    0 ≤ Real.sin y ↔
      ∃ k : ℤ, y ∈ Set.Icc ((k : ℝ) * (2 * Real.pi))
        (Real.pi + (k : ℝ) * (2 * Real.pi)) := by
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  constructor
  · intro hy
    set k : ℤ := ⌊y / (2 * Real.pi)⌋ with hk
    have hk_le : (k : ℝ) ≤ y / (2 * Real.pi) := by
      rw [hk]; exact Int.floor_le _
    have hk_lt : y / (2 * Real.pi) < (k : ℝ) + 1 := by
      rw [hk]; exact Int.lt_floor_add_one _
    have h1 : (k : ℝ) * (2 * Real.pi) ≤ y := (le_div_iff₀ h2pi).mp hk_le
    have h2 : y < (k : ℝ) * (2 * Real.pi) + 2 * Real.pi := by
      have h := (div_lt_iff₀ h2pi).mp hk_lt
      have : ((k : ℝ) + 1) * (2 * Real.pi) = (k : ℝ) * (2 * Real.pi) + 2 * Real.pi := by
        ring
      rwa [this] at h
    have hz0 : 0 ≤ y - (k : ℝ) * (2 * Real.pi) := by linarith
    have hz2pi : y - (k : ℝ) * (2 * Real.pi) < 2 * Real.pi := by linarith
    have hsinz : 0 ≤ Real.sin (y - (k : ℝ) * (2 * Real.pi)) := by
      rw [Real.sin_sub_int_mul_two_pi y k]; exact hy
    have hzle : y - (k : ℝ) * (2 * Real.pi) ≤ Real.pi := by
      by_contra hz
      have hz' : Real.pi < y - (k : ℝ) * (2 * Real.pi) := not_le.mp hz
      have hneg : Real.sin (y - (k : ℝ) * (2 * Real.pi) - 2 * Real.pi) < 0 :=
        Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
      have heq : Real.sin (y - (k : ℝ) * (2 * Real.pi) - 2 * Real.pi) =
          Real.sin (y - (k : ℝ) * (2 * Real.pi)) := by
        have := Real.sin_sub_int_mul_two_pi (y - (k : ℝ) * (2 * Real.pi)) 1
        simpa only [Int.cast_one, one_mul] using this
      linarith [hneg, heq, hsinz]
    exact ⟨k, by constructor <;> linarith⟩
  · rintro ⟨k, hk1, hk2⟩
    have hsin : Real.sin y = Real.sin (y - (k : ℝ) * (2 * Real.pi)) :=
      (Real.sin_sub_int_mul_two_pi y k).symm
    rw [hsin]
    exact Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩

theorem cos_nonpos_iff_exists_Icc (x : ℝ) :
    Real.cos x ≤ 0 ↔
      ∃ k : ℤ, x ∈ Set.Icc (Real.pi / 2 + (k : ℝ) * (2 * Real.pi))
        (3 * Real.pi / 2 + (k : ℝ) * (2 * Real.pi)) := by
  have hiff : (Real.cos x ≤ 0) ↔ 0 ≤ Real.sin (x - Real.pi / 2) := by
    rw [Real.sin_sub_pi_div_two]
    constructor <;> intro h <;> linarith
  rw [hiff, sin_nonneg_iff_exists_Icc]
  constructor
  · rintro ⟨k, hk1, hk2⟩
    exact ⟨k, by constructor <;> linarith⟩
  · rintro ⟨k, hk1, hk2⟩
    exact ⟨k, by constructor <;> linarith⟩

end Work.LandLeaves
