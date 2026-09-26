import Mathlib
import Submission.Work.Smooth.JordanSeparation.lwalk_corner
import Submission.Work.Smooth.JordanSeparation.lwalk_peel_base

/-!
# The corner step in the form used by `joinNat_replace`

`edgeUNat_pair_corner_homotopic` is the `hQ` hypothesis of `joinNat_replace` at a lex-max vertex:
the two clamped lifted edges that meet at `W.pt (j+1)` are homotopic *in `↥U`* to the two-step path
through the opposite corner `s` of the corner cell.
-/

namespace Work.Smooth.JordanSeparation

open Set Metric

noncomputable section

/-- **The corner step, clamped form.**  The two consecutive clamped lifted edges `j`, `j + 1` are
homotopic in `↥U` to the two-step path through `s` (the two-step path being cast back to the
clamped endpoints). -/
theorem edgeUNat_pair_corner_homotopic {U B : Set ℂ} {W : LWalk} {hval : ∀ t, W.path t ∈ U}
    {j : ℕ} (hj1 : j < W.n) (hj2 : j + 1 < W.n) {hB : Convex ℝ B} {hBU : B ⊆ U}
    (hBne : B.Nonempty) {s : ℂ} (ha : W.pt j ∈ B) (hp : W.pt (j + 1) ∈ B)
    (hb : W.pt ((j + 1) + 1) ∈ B) (hs : s ∈ B) :
    Path.Homotopic ((W.edgeUNat hval j).trans (W.edgeUNat hval (j + 1)))
      (((segIn hB hBU ha hs).trans (segIn hB hBU hs hb)).cast
        (W.ptMin_eq_ptU hval j (le_of_lt hj1))
        (W.ptMin_eq_ptU hval ((j + 1) + 1) (Nat.succ_le_of_lt hj2))) := by
  have h := Path.Homotopic.pathCast
    (corner_step (hval := hval) (hB := hB) (hBU := hBU) hj1 hj2 hBne ha hp hb hs)
    (W.ptMin_eq_ptU hval j (le_of_lt hj1))
    (W.ptMin_eq_ptU hval ((j + 1) + 1) (Nat.succ_le_of_lt hj2))
  rwa [← edgeUNat_trans_eq (hval := hval) (hB := hB) (hBU := hBU) hj1 hj2 ha hp hb] at h

end

end Work.Smooth.JordanSeparation
