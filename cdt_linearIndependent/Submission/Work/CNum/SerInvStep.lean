import Mathlib
import Submission.Work.CNum.SerUpDefs
import Submission.Work.CNum.LgInfra
import Submission.Work.CNum.SerStepArith
import Submission.Work.CNum.SerStepScale
import Submission.Work.CNum.SerStepErr
import Submission.Work.CNum.SerStepSize

namespace Work.CNum

open Work.ANum

theorem SerInvStep {x y e σ : ℤ} (he : 0 ≤ e) (hσlt : Work.ANum.m2r σ < 1) (hRσ : Work.CNum.srad x y e ≤ Work.ANum.m2r σ) {k : ℕ} {px py pe sg : ℤ} (h : Work.CNum.SerInv x y e σ k px py pe sg) : Work.CNum.SerInv x y e σ (k + 1) (Work.CNum.snx x y px py) (Work.CNum.sny x y px py) (Work.CNum.snpe σ pe) (Work.CNum.snsg σ sg) := by
  have hσ0 : 0 ≤ σ := (m2r_nonneg_iff σ).mp (le_trans (srad_nonneg he) hRσ)
  obtain ⟨hpe, hpe3, hk, hsg2, hp5, hx34, hy34⟩ := h
  obtain ⟨h1, h2⟩ := SerStepArith hpe hpe3 hσlt hσ0
  obtain ⟨h3, h4⟩ := SerStepScale he hσlt hRσ hk hsg2
  have h5 := SerStepErr he hσlt hRσ hpe hp5
  obtain ⟨h6, h7⟩ := SerStepSize he hσlt hRσ hpe3 hp5
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

end Work.CNum
