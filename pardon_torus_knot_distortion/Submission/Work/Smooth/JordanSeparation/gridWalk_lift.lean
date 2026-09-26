import Mathlib
import Submission.Work.Smooth.JordanSeparation.GridWalkDefs
import Submission.Work.Smooth.JordanSeparation.gridWalk_basic

namespace Work.Smooth.JordanSeparation

open Set

noncomputable section

lemma Path.liftU_trans {U : Set ℂ} {a b c : ℂ} (ha : a ∈ U) (hb : b ∈ U) (hc : c ∈ U)
    (p : Path a b) (q : Path b c) (hp : ∀ t, p t ∈ U) (hq : ∀ t, q t ∈ U)
    (hpq : ∀ t, (p.trans q) t ∈ U) :
    Path.liftU ha hc (p.trans q) hpq = (Path.liftU ha hb p hp).trans (Path.liftU hb hc q hq) := by
  ext s
  have hs0 : (0:ℝ) ≤ (s:ℝ) := s.2.1
  have hs1 : (s:ℝ) ≤ 1 := s.2.2
  rw [Path.trans_apply]
  by_cases h : (s : ℝ) ≤ 1 / 2
  · have hmem : (2 * (s:ℝ) : ℝ) ∈ unitInterval := by
      rw [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
    rw [dif_pos h]
    show (p.trans q) s = p ⟨2 * (s:ℝ), hmem⟩
    rw [Path.trans_apply]
    rw [dif_pos h]
  · have hmem : (2 * (s:ℝ) - 1 : ℝ) ∈ unitInterval := by
      rw [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
    rw [dif_neg h]
    show (p.trans q) s = q ⟨2 * (s:ℝ) - 1, hmem⟩
    rw [Path.trans_apply]
    rw [dif_neg h]

end

end Work.Smooth.JordanSeparation
