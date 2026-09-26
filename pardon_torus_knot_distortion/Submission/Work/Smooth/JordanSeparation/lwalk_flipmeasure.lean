import Mathlib
import Submission.Work.Smooth.JordanSeparation.lwalk_lexmin
import Submission.Work.Smooth.JordanSeparation.lwalk_measure
import Submission.Work.Smooth.JordanSeparation.lwalk_peel

/-!
# The corner move does not change the lex-min vertex, and strictly decreases the lex-max one
-/

namespace Work.Smooth.JordanSeparation

open Set Metric

noncomputable section

attribute [local instance] Classical.propDecidable

/-- **The corner move preserves the lex-min vertex** (the new vertex `vmax W - (1,1)` is still
lexicographically above the lex-min one, by `lexmin_le_vmax_sub_one`). -/
theorem vmin_flip_eq {W : LWalk} (hW : W.IsSimple) (hn : 4 ≤ W.n) {k : ℕ} (hk1 : 1 ≤ k)
    (hk2 : k + 1 ≤ W.n)
    (ha : W.v (k - 1) = W.v k - (1, 0) ∨ W.v (k - 1) = W.v k - (0, 1))
    (hb : W.v (k + 1) = W.v k - (1, 0) ∨ W.v (k + 1) = W.v k - (0, 1))
    (hp : W.v k = vmax W) :
    vmin (W.flip hk1 hk2 ha hb) = vmin W := by
  have hn' : (W.flip hk1 hk2 ha hb).n = W.n := LWalk.flip_n W hk1 hk2 ha hb
  apply lexLe_antisymm
  · obtain ⟨j, hj, hj'⟩ := exists_vmin W
    have hjW : j ≤ (W.flip hk1 hk2 ha hb).n := by rw [hn']; exact hj
    have h1 := vmin_le (W.flip hk1 hk2 ha hb) hjW
    rcases eq_or_ne j k with h | h
    · rw [h] at hj' h1
      rw [LWalk.flip_v_self W hk1 hk2 ha hb] at h1
      exact lexLe_trans h1 (lexLe_of_lexLt (by rw [← hj']; exact lexLt_sub_one_self (W.v k)))
    · rw [LWalk.flip_v_of_ne W hk1 hk2 ha hb h, hj'] at h1
      exact h1
  · obtain ⟨j, hj, hj'⟩ := exists_vmin (W.flip hk1 hk2 ha hb)
    have hjW : j ≤ W.n := by rw [← hn']; exact hj
    rcases eq_or_ne j k with h | h
    · rw [h] at hj'
      rw [← hj', LWalk.flip_v_self W hk1 hk2 ha hb, hp]
      exact lexmin_le_vmax_sub_one hW hn
    · simpa only [← LWalk.flip_v_of_ne W hk1 hk2 ha hb h, hj'] using vmin_le W hjW

/-- **The corner move strictly decreases the lex-max vertex.** -/
theorem vmax_flip_lt {W : LWalk} (hW : W.IsSimple) {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ W.n)
    (ha : W.v (k - 1) = W.v k - (1, 0) ∨ W.v (k - 1) = W.v k - (0, 1))
    (hb : W.v (k + 1) = W.v k - (1, 0) ∨ W.v (k + 1) = W.v k - (0, 1))
    (hp : W.v k = vmax W) :
    LexLt (vmax (W.flip hk1 hk2 ha hb)) (vmax W) := by
  have hn' : (W.flip hk1 hk2 ha hb).n = W.n := LWalk.flip_n W hk1 hk2 ha hb
  have hupper : ∀ j, j ≤ (W.flip hk1 hk2 ha hb).n →
      LexLe ((W.flip hk1 hk2 ha hb).v j) (vmax W) := by
    intro j hj
    have hjW : j ≤ W.n := by rw [hn'] at hj; exact hj
    rcases eq_or_ne j k with h | h
    · rw [h, LWalk.flip_v_self W hk1 hk2 ha hb, hp]
      exact lexLe_of_lexLt (lexLt_sub_one_self (vmax W))
    · rw [LWalk.flip_v_of_ne W hk1 hk2 ha hb h]
      exact le_vmax W hjW
  refine lexLt_of_lexLe_of_ne (vmax_upper _ hupper) ?_
  intro hcon
  obtain ⟨j, hj, hj'⟩ := exists_vmax (W.flip hk1 hk2 ha hb)
  have hjW : j ≤ W.n := by rw [hn'] at hj; exact hj
  rcases eq_or_ne j k with h | h
  · rw [h] at hj'
    rw [LWalk.flip_v_self W hk1 hk2 ha hb, hcon, ← hp] at hj'
    have hthis := lexLt_sub_one_self (W.v k)
    rw [hj'] at hthis
    exact lexLt_irrefl (W.v k) hthis
  · rw [LWalk.flip_v_of_ne W hk1 hk2 ha hb h] at hj'
    have hne : W.v j ≠ W.v k := by
      intro hc
      rcases lt_or_gt_of_ne h with hlt | hlt
      · exact hW j k hlt (by omega) (by intro hh; have h2 := (Prod.ext_iff.mp hh).2; omega) hc
      · exact hW k j hlt (by omega) (by intro hh; have h1 := (Prod.ext_iff.mp hh).1; omega)
          hc.symm
    rw [hcon, ← hp] at hj'
    exact hne hj'

end

end Work.Smooth.JordanSeparation
