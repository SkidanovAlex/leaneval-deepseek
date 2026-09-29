import Mathlib
import Submission.Work.IntLib.Defs
import Submission.Work.IntLib.Shift.Defs

namespace Work.IntLib.Shift

/-- Auxiliary: the value of the Horner fold is monotone in the initial value
(`natOfMSB p R ≤ natOfMSB p' R` when `p ≤ p'`). -/
theorem natOfMSB_mono : ∀ (R : List Bool) {p p' : ℕ}, p ≤ p' → natOfMSB p R ≤ natOfMSB p' R := by
  intro R
  induction R with
  | nil => intro p p' h; simpa using h
  | cons b bs ih =>
      intro p p' h
      simp only [natOfMSB_cons]
      exact ih (by omega)

/-- Cost bound of the `shl` main loop: with block length `p` and remaining bits `R`, the loop cost
plus `p` is at most `2 * natOfMSB p R + |R| + 2`.  (One unit of extra slack per step absorbs the
doubling `p ↦ 2p + b`.) -/
theorem shlCostBound : ∀ (p : ℕ) (R : List Bool), Work.IntLib.Shift.shlCost p R + p ≤ 2 * Work.IntLib.Shift.natOfMSB p R + R.length + 2 := by
  intro p R
  induction R generalizing p with
  | nil => simp only [shlCost_nil, natOfMSB_nil, List.length_nil]; omega
  | cons b bs ih =>
      have h := ih (2 * p + b.toNat)
      simp only [shlCost_cons, natOfMSB_cons, List.length_cons] at h ⊢
      omega

end Work.IntLib.Shift
