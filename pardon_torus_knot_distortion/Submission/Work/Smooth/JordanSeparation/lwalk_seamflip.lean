import Mathlib
import Submission.Work.Smooth.JordanSeparation.lwalk_peel
import Submission.Work.Smooth.JordanSeparation.lwalk_lexmin

/-!
# The seam flip of a closed lattice walk

For a simple closed lattice walk whose lex-max vertex is the *seam* `W.v 0 = W.v W.n`, the corner
move at the seam moves both ends to `W.v 0 - (1,1)`: this is `LWalk.seamFlip`.  Its loop is freely
homotopic to the loop of `W` (the corner move happens at the base point, so the base point moves).
-/

namespace Work.Smooth.JordanSeparation

open Set Metric

noncomputable section

namespace LWalk

variable (W : LWalk)

/-- The walk with the seam vertex moved to `W.v 0 - (1,1)` at both ends. -/
def seamFlip (h2 : 2 ≤ W.n)
    (ha : W.v (W.n - 1) = W.v 0 - (1, 0) ∨ W.v (W.n - 1) = W.v 0 - (0, 1))
    (hb : W.v 1 = W.v 0 - (1, 0) ∨ W.v 1 = W.v 0 - (0, 1)) : LWalk where
  n := W.n
  c := W.c
  cpos := W.cpos
  v := fun j => if j = 0 ∨ j = W.n then W.v 0 - (1, 1) else W.v j
  step := by
    intro j hj
    have hn0 : W.n ≠ 0 := by omega
    by_cases h0 : j = 0
    · subst h0
      have h1n : ¬ ((1 : ℕ) = 0 ∨ 1 = W.n) := by omega
      show GridStep (if (0 : ℕ) = 0 ∨ 0 = W.n then W.v 0 - (1, 1) else W.v 0)
        (if (0 : ℕ) + 1 = 0 ∨ (0 : ℕ) + 1 = W.n then W.v 0 - (1, 1) else W.v 1)
      rw [if_pos (Or.inl rfl), if_neg (by omega)]
      rcases hb with hb | hb
      · rw [hb]; exact gridStep_11_10 (W.v 0)
      · rw [hb]; exact gridStep_11_01 (W.v 0)
    · by_cases hlast : j + 1 = W.n
      · have hj' : j = W.n - 1 := by omega
        show GridStep (if j = 0 ∨ j = W.n then W.v 0 - (1, 1) else W.v j)
          (if j + 1 = 0 ∨ j + 1 = W.n then W.v 0 - (1, 1) else W.v (j + 1))
        rw [if_neg (by omega), if_pos (Or.inr hlast), hj']
        rcases ha with ha | ha
        · rw [ha]; exact gridStep_10_11 (W.v 0)
        · rw [ha]; exact gridStep_01_11 (W.v 0)
      · show GridStep (if j = 0 ∨ j = W.n then W.v 0 - (1, 1) else W.v j)
          (if j + 1 = 0 ∨ j + 1 = W.n then W.v 0 - (1, 1) else W.v (j + 1))
        rw [if_neg (by omega), if_neg (by omega)]
        exact W.step j hj
  closed := by
    have hn0 : W.n ≠ 0 := by omega
    show (if W.n = 0 ∨ W.n = W.n then W.v 0 - (1, 1) else W.v W.n) =
      (if (0 : ℕ) = 0 ∨ 0 = W.n then W.v 0 - (1, 1) else W.v 0)
    rw [if_pos (Or.inr rfl), if_pos (Or.inl rfl)]

theorem seamFlip_n (h2 : 2 ≤ W.n)
    (ha : W.v (W.n - 1) = W.v 0 - (1, 0) ∨ W.v (W.n - 1) = W.v 0 - (0, 1))
    (hb : W.v 1 = W.v 0 - (1, 0) ∨ W.v 1 = W.v 0 - (0, 1)) :
    (W.seamFlip h2 ha hb).n = W.n := rfl

theorem seamFlip_c (h2 : 2 ≤ W.n)
    (ha : W.v (W.n - 1) = W.v 0 - (1, 0) ∨ W.v (W.n - 1) = W.v 0 - (0, 1))
    (hb : W.v 1 = W.v 0 - (1, 0) ∨ W.v 1 = W.v 0 - (0, 1)) :
    (W.seamFlip h2 ha hb).c = W.c := rfl

theorem seamFlip_v (h2 : 2 ≤ W.n)
    (ha : W.v (W.n - 1) = W.v 0 - (1, 0) ∨ W.v (W.n - 1) = W.v 0 - (0, 1))
    (hb : W.v 1 = W.v 0 - (1, 0) ∨ W.v 1 = W.v 0 - (0, 1)) (j : ℕ) :
    (W.seamFlip h2 ha hb).v j = if j = 0 ∨ j = W.n then W.v 0 - (1, 1) else W.v j := rfl

theorem seamFlip_v_zero (h2 : 2 ≤ W.n)
    (ha : W.v (W.n - 1) = W.v 0 - (1, 0) ∨ W.v (W.n - 1) = W.v 0 - (0, 1))
    (hb : W.v 1 = W.v 0 - (1, 0) ∨ W.v 1 = W.v 0 - (0, 1)) :
    (W.seamFlip h2 ha hb).v 0 = W.v 0 - (1, 1) := by
  rw [seamFlip_v]; simp

theorem seamFlip_v_last (h2 : 2 ≤ W.n)
    (ha : W.v (W.n - 1) = W.v 0 - (1, 0) ∨ W.v (W.n - 1) = W.v 0 - (0, 1))
    (hb : W.v 1 = W.v 0 - (1, 0) ∨ W.v 1 = W.v 0 - (0, 1)) :
    (W.seamFlip h2 ha hb).v W.n = W.v 0 - (1, 1) := by
  rw [seamFlip_v]; simp

theorem seamFlip_v_of_ne (h2 : 2 ≤ W.n)
    (ha : W.v (W.n - 1) = W.v 0 - (1, 0) ∨ W.v (W.n - 1) = W.v 0 - (0, 1))
    (hb : W.v 1 = W.v 0 - (1, 0) ∨ W.v 1 = W.v 0 - (0, 1)) {j : ℕ}
    (h0 : j ≠ 0) (hn : j ≠ W.n) :
    (W.seamFlip h2 ha hb).v j = W.v j := by
  rw [seamFlip_v]; simp [h0, hn]

end LWalk

open LWalk in
/-- **The seam flip preserves the lex-min vertex.** -/
theorem seamFlip_vmin_eq {W : LWalk} (hW : W.IsSimple) (hn : 4 ≤ W.n) (h2 : 2 ≤ W.n)
    (ha : W.v (W.n - 1) = W.v 0 - (1, 0) ∨ W.v (W.n - 1) = W.v 0 - (0, 1))
    (hb : W.v 1 = W.v 0 - (1, 0) ∨ W.v 1 = W.v 0 - (0, 1))
    (hp : W.v 0 = vmax W) :
    vmin (W.seamFlip h2 ha hb) = vmin W := by
  have hn' : (W.seamFlip h2 ha hb).n = W.n := LWalk.seamFlip_n W h2 ha hb
  apply lexLe_antisymm
  · obtain ⟨j, hj, hj'⟩ := exists_vmin W
    have hjW : j ≤ (W.seamFlip h2 ha hb).n := by rw [hn']; exact hj
    have h1 := vmin_le (W.seamFlip h2 ha hb) hjW
    rcases eq_or_ne j 0 with h | h
    · rw [h] at hj' h1
      rw [LWalk.seamFlip_v_zero W h2 ha hb] at h1
      exact lexLe_trans h1
        (lexLe_of_lexLt (by rw [← hj']; exact lexLt_sub_one_self (W.v 0)))
    · rcases eq_or_ne j W.n with h' | h'
      · rw [h', W.closed] at hj'
        rw [h'] at h1
        rw [LWalk.seamFlip_v_last W h2 ha hb] at h1
        exact lexLe_trans h1
          (lexLe_of_lexLt (by rw [← hj']; exact lexLt_sub_one_self (W.v 0)))
      · rw [LWalk.seamFlip_v_of_ne W h2 ha hb h h', hj'] at h1
        exact h1
  · obtain ⟨j, hj, hj'⟩ := exists_vmin (W.seamFlip h2 ha hb)
    have hjW : j ≤ W.n := by rw [← hn']; exact hj
    rcases eq_or_ne j 0 with h | h
    · rw [← hj', h, LWalk.seamFlip_v_zero W h2 ha hb, hp]
      exact lexmin_le_vmax_sub_one hW hn
    · rcases eq_or_ne j W.n with h' | h'
      · rw [← hj', h', LWalk.seamFlip_v_last W h2 ha hb, hp]
        exact lexmin_le_vmax_sub_one hW hn
      · simpa only [← LWalk.seamFlip_v_of_ne W h2 ha hb h h', hj'] using vmin_le W hjW

open LWalk in
/-- **The seam flip strictly decreases the lex-max vertex.** -/
theorem seamFlip_vmax_lt {W : LWalk} (hW : W.IsSimple) (h2 : 2 ≤ W.n)
    (ha : W.v (W.n - 1) = W.v 0 - (1, 0) ∨ W.v (W.n - 1) = W.v 0 - (0, 1))
    (hb : W.v 1 = W.v 0 - (1, 0) ∨ W.v 1 = W.v 0 - (0, 1))
    (hp : W.v 0 = vmax W) :
    LexLt (vmax (W.seamFlip h2 ha hb)) (vmax W) := by
  have hn' : (W.seamFlip h2 ha hb).n = W.n := LWalk.seamFlip_n W h2 ha hb
  have hupper : ∀ j, j ≤ (W.seamFlip h2 ha hb).n →
      LexLe ((W.seamFlip h2 ha hb).v j) (vmax W) := by
    intro j hj
    have hjW : j ≤ W.n := by rw [hn'] at hj; exact hj
    rcases eq_or_ne j 0 with h | h
    · rw [h, LWalk.seamFlip_v_zero W h2 ha hb, hp]
      exact lexLe_of_lexLt (lexLt_sub_one_self (vmax W))
    · rcases eq_or_ne j W.n with h' | h'
      · rw [h', LWalk.seamFlip_v_last W h2 ha hb, hp]
        exact lexLe_of_lexLt (lexLt_sub_one_self (vmax W))
      · rw [LWalk.seamFlip_v_of_ne W h2 ha hb h h']
        exact le_vmax W hjW
  refine lexLt_of_lexLe_of_ne (vmax_upper _ hupper) ?_
  intro hcon
  obtain ⟨j, hj, hj'⟩ := exists_vmax (W.seamFlip h2 ha hb)
  have hjW : j ≤ W.n := by rw [hn'] at hj; exact hj
  rcases eq_or_ne j 0 with h | h
  · rw [h, LWalk.seamFlip_v_zero W h2 ha hb, hcon, ← hp] at hj'
    have hthis := lexLt_sub_one_self (W.v 0)
    rw [hj'] at hthis
    exact lexLt_irrefl (W.v 0) hthis
  · rcases eq_or_ne j W.n with h' | h'
    · rw [h', LWalk.seamFlip_v_last W h2 ha hb, hcon, ← hp] at hj'
      have hthis := lexLt_sub_one_self (W.v 0)
      rw [hj'] at hthis
      exact lexLt_irrefl (W.v 0) hthis
    · rw [LWalk.seamFlip_v_of_ne W h2 ha hb h h', hcon, ← hp] at hj'
      have hne : W.v j ≠ W.v 0 := by
        intro hc
        have hlt : 0 < j := by omega
        exact hW 0 j hlt hjW (by intro hh; have h2' := (Prod.ext_iff.mp hh).2; omega) hc.symm
      exact hne hj'

end

end Work.Smooth.JordanSeparation
