import Mathlib
import Submission.Work.Main.defs
import Submission.Work.Main.crt.Pinv_spec
import Submission.Work.Main.crt.Pcr_inj
import Submission.Work.Main.crt.Pcr_lt

namespace Work.Main.crt

/-- `Pinv ss` is a left inverse of the CRT reindexing `Pcr ss` on the range `[0, ∏ss)`:
`Pinv ss` chooses (via `Pinv_spec`) a preimage `m < ∏ss` of `Pcr ss k`, and `Pcr_inj` shows
that preimage must be `k` itself. -/
theorem Pinv_Pcr {ss : List ℕ} (hcop : ss.Pairwise Nat.Coprime) (hpos : ∀ s ∈ ss, 0 < s)
    {k : ℕ} (hk : k < ss.prod) : Work.Main.Pinv ss (Work.Main.Pcr ss k) = k := by
  have hq : Pcr ss k < ss.prod := Pcr_lt hpos k
  obtain ⟨hlt, hPcr⟩ := Pinv_spec hcop hpos hq
  exact Pcr_inj hcop hpos hlt hk hPcr

end Work.Main.crt
