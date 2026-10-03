import Mathlib
import Submission.Work.Peluse.UControl.histPhase1Inv
import Submission.Work.Peluse.UControl.histCloseLinkWin
import Submission.Work.Peluse.UControl.level1Compare
import Submission.Work.Peluse.UControl.petCornerZero
import Submission.Work.Peluse.UControl.peluseProp34Defs2
import Submission.Work.Peluse.UControl.petQuad5Aux
import Submission.Work.Peluse.UControl.petInitSym_hw

set_option autoImplicit false
set_option maxHeartbeats 16000000
open scoped BigOperators
open Polynomial

namespace Work.Peluse.UControl

noncomputable section

/-! ## Bookkeeping lemmas -/

/-- From `2 ≤ ⌊x⌋.toNat` one gets `2 ≤ x`. -/
lemma two_le_of_toNat_le {x : ℝ} (h : 2 ≤ ⌊x⌋.toNat) : (2 : ℝ) ≤ x := by
  have h1 : (2 : ℤ) ≤ ⌊x⌋ := by
    by_contra hlt
    have hle : ⌊x⌋ ≤ 0 := by omega
    rw [Int.toNat_of_nonpos hle] at h
    omega
  have h2 : (2 : ℝ) ≤ ((⌊x⌋ : ℤ) : ℝ) := by exact_mod_cast h1
  have h3 : ((⌊x⌋ : ℤ) : ℝ) ≤ x := Int.floor_le x
  linarith

/-- From `2 ≤ x` one gets `2 ≤ ⌊x⌋.toNat`. -/
lemma toNat_floor_two_le {x : ℝ} (h : (2 : ℝ) ≤ x) : 2 ≤ ⌊x⌋.toNat := by
  have h1 : (2 : ℤ) ≤ ⌊x⌋ := Int.le_floor.mpr h
  have h2 : (0 : ℤ) ≤ ⌊x⌋ := by omega
  have h3 : ((⌊x⌋.toNat : ℕ) : ℤ) = ⌊x⌋ := Int.toNat_of_nonneg h2
  omega

/-! ## The sharp evaluation bound of the terminal slot of the quadratic chain -/

/-! ## The chapter -/

end

end Work.Peluse.UControl
