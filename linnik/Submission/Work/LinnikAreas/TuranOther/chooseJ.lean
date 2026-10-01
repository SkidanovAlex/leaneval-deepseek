import Mathlib

namespace Work.LinnikAreas.TuranOther

theorem chooseJ {C JB L M x : ℝ} (hC : 0 < C) (hJB : JB = 9 * 16 * C + 1) (hL : 1 ≤ L)
    (hM : 0 ≤ M) (hMle : M ≤ 16 * C * (L + 1)) (hx : 0 < x)
    (hxL : x * L ≤ min (1 / 2) (3 / ((32 + 4 * 1) * 4 * Real.exp 1 * JB))) :
    ∃ J : ℕ, 1 ≤ J ∧ (J : ℝ) * x ≤ 1 / 24 ∧ (J : ℝ) ≤ 2 * JB * L ∧
      ∀ j : ℕ, (j : ℝ) ≤ 9 * M → (j : ℝ) ≤ (J : ℝ) := by
  have hJBpos : 0 < JB := by rw [hJB]; positivity
  have hJB1 : 1 ≤ JB := by rw [hJB]; linarith [hC]
  have hE1 : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr one_pos
  -- Bound on the ceiling of 9*M
  have hbound : 9 * M + 1 ≤ 2 * JB * L := by
    have hmul9 : 9 * M ≤ 9 * (16 * C * (L + 1)) :=
      mul_le_mul_of_nonneg_left hMle (by norm_num)
    have h9M : 9 * M ≤ 144 * C * (L + 1) := by
      have hh : (9 : ℝ) * (16 * C * (L + 1)) = 144 * C * (L + 1) := by ring
      rwa [hh] at hmul9
    have h2 : 144 * C * (L + 1) ≤ 288 * C * L := by nlinarith [hC, hL]
    have h3 : 2 * JB * L = 288 * C * L + 2 * L := by rw [hJB]; ring
    have h4 : (2 : ℝ) ≤ 2 * L := by linarith
    linarith [h9M, h2, h3, h4]
  have hceil : (Nat.ceil (9 * M) : ℝ) ≤ 2 * JB * L := by
    have h := Nat.ceil_lt_add_one (mul_nonneg (by norm_num : (0 : ℝ) ≤ 9) hM)
    linarith
  have h1le : (1 : ℝ) ≤ 2 * JB * L := by nlinarith [hJB1, hL]
  have hJle : ((max 1 (Nat.ceil (9 * M)) : ℕ) : ℝ) ≤ 2 * JB * L := by
    have hJcast : (((max 1 (Nat.ceil (9 * M)) : ℕ)) : ℝ) =
        max (1 : ℝ) ((Nat.ceil (9 * M) : ℕ) : ℝ) := by
      rw [Nat.cast_max]; norm_num
    rw [hJcast]; exact max_le h1le hceil
  have hJge : 9 * M ≤ ((max 1 (Nat.ceil (9 * M)) : ℕ) : ℝ) := by
    have h1 : 9 * M ≤ (Nat.ceil (9 * M) : ℝ) := Nat.le_ceil (9 * M)
    have h2 : (Nat.ceil (9 * M) : ℝ) ≤ ((max 1 (Nat.ceil (9 * M)) : ℕ) : ℝ) := by
      exact_mod_cast (le_max_right 1 (Nat.ceil (9 * M)))
    linarith
  -- Bound on x*L
  have hxL2 : x * L ≤ 3 / (144 * Real.exp 1 * JB) := by
    have h := le_trans hxL (min_le_right (1 / 2) _)
    have hden : (32 + 4 * 1) * 4 * Real.exp 1 * JB = 144 * Real.exp 1 * JB := by ring
    rwa [hden] at h
  have hJBne : JB ≠ 0 := ne_of_gt hJBpos
  refine ⟨max 1 (Nat.ceil (9 * M)), le_max_left 1 _, ?_, hJle, ?_⟩
  · calc (((max 1 (Nat.ceil (9 * M)) : ℕ)) : ℝ) * x
        ≤ (2 * JB * L) * x := mul_le_mul_of_nonneg_right hJle (le_of_lt hx)
      _ = 2 * JB * (x * L) := by ring
      _ ≤ 2 * JB * (3 / (144 * Real.exp 1 * JB)) :=
          mul_le_mul_of_nonneg_left hxL2 (by linarith [hJBpos])
      _ = 1 / (24 * Real.exp 1) := by
          field_simp
          ring
      _ ≤ 1 / 24 := by
          apply le_of_lt
          apply one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 24)
          nlinarith [hE1]
  · intro j hj
    exact le_trans hj hJge

end Work.LinnikAreas.TuranOther
