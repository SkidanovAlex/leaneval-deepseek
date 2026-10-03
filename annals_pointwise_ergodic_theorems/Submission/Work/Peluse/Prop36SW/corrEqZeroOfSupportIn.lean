import Mathlib
import Submission.Work.Peluse.TransferUp.boxNormPow_transfer_up

namespace Work.Peluse.Prop36SW

theorem corrEqZeroOfSupportIn {M : ℕ} {h : ℤ → ℂ} (hsup : Work.Peluse.SupportIn h M)
    {m : ℤ} (hm : 2 * M + 1 ≤ m.natAbs) : Work.Peluse.TransferUp.corr h m = 0 := by
  unfold Work.Peluse.TransferUp.corr
  have hzero : ∀ x : ℤ, h x * star (h (x + m)) = 0 := by
    intro x
    by_cases hx : h x = 0
    · simp [hx]
    · have hxM : x.natAbs ≤ M := Nat.not_lt.mp (fun hlt => hx (hsup x hlt))
      by_cases hy : h (x + m) = 0
      · simp [hy]
      · have hyM : (x + m).natAbs ≤ M := Nat.not_lt.mp (fun hlt => hy (hsup (x + m) hlt))
        have h2 : m.natAbs = ((x + m) - x).natAbs :=
          congrArg Int.natAbs (show m = (x + m) - x by ring)
        have hle : m.natAbs ≤ 2 * M := by
          rw [h2]
          calc ((x + m) - x).natAbs ≤ (x + m).natAbs + x.natAbs := Int.natAbs_sub_le _ _
            _ ≤ M + M := Nat.add_le_add hyM hxM
            _ = 2 * M := by ring
        omega
  simpa using tsum_congr hzero

end Work.Peluse.Prop36SW
