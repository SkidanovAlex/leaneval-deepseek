import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

theorem grid_iUnion_Ico (h : ℝ) (hh : 0 < h) (N : ℕ) :
    (⋃ l : Fin N, Set.Ico ((l : ℝ) * h) (((l : ℝ) + 1) * h)) = Set.Ico 0 ((N : ℝ) * h) := by
  ext x
  rw [Set.mem_iUnion, Set.mem_Ico]
  constructor
  · rintro ⟨l, hl0, hl1⟩
    refine ⟨mul_nonneg (Nat.cast_nonneg _) hh.le |>.trans hl0, ?_⟩
    have hlt : (l : ℝ) + 1 ≤ (N : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt l.isLt
    linarith [hl1, mul_le_mul_of_nonneg_right hlt hh.le]
  · rintro ⟨hx0, hxN⟩
    have hd0 : 0 ≤ x / h := div_nonneg hx0 hh.le
    have hlt : x / h < (N : ℝ) := by rw [div_lt_iff₀ hh]; linarith
    refine ⟨⟨⌊x / h⌋₊, (Nat.floor_lt hd0).mpr hlt⟩, ?_, ?_⟩
    · have h1 : ((⌊x / h⌋₊ : ℝ)) * h ≤ (x / h) * h :=
        mul_le_mul_of_nonneg_right (Nat.floor_le hd0) hh.le
      rwa [div_mul_cancel₀ x hh.ne'] at h1
    · have h1 : (x / h) * h < ((⌊x / h⌋₊ : ℝ) + 1) * h :=
        mul_lt_mul_of_pos_right (Nat.lt_floor_add_one (x / h)) hh
      rwa [div_mul_cancel₀ x hh.ne'] at h1

end Work.BMF
