import Mathlib
import Submission.Work.WilC4aCS.Defs

namespace Work.WilC4aCS

/-- The sign `±1` of a nonzero real number equals `sign` in the sense that
`posSign c` is `1` when `c > 0` and `-1` when `c < 0`, matching `SignType.sign`,
and `posSign c` orients the real line as `sign c` does. -/
theorem posSign_spec {c : ℝ} (hc : c ≠ 0) :
    Work.WilC4aCS.posSign c ≠ 0 ∧ SignType.sign (Work.WilC4aCS.posSign c) = SignType.sign c ∧
      (∀ y : ℝ, 0 < Work.WilC4aCS.posSign c * y ↔ SignType.sign y = SignType.sign c) := by
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · -- `c < 0`, so `posSign c = -1`
    have hps : Work.WilC4aCS.posSign c = -1 := by
      unfold Work.WilC4aCS.posSign
      rw [if_neg (not_lt.mpr hneg.le)]
    refine ⟨by rw [hps]; norm_num, ?_, ?_⟩
    · rw [hps, sign_neg (show (-1 : ℝ) < 0 by norm_num), sign_neg hneg]
    · intro y
      rw [hps, sign_neg hneg, sign_eq_neg_one_iff]
      constructor <;> intro h <;> linarith
  · -- `0 < c`, so `posSign c = 1`
    have hps : Work.WilC4aCS.posSign c = 1 := by
      unfold Work.WilC4aCS.posSign
      rw [if_pos hpos]
    refine ⟨by rw [hps]; norm_num, ?_, ?_⟩
    · rw [hps, sign_pos zero_lt_one, sign_pos hpos]
    · intro y
      rw [hps, sign_pos hpos, sign_eq_one_iff]
      constructor <;> intro h <;> linarith

end Work.WilC4aCS
