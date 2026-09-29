import Mathlib
import Submission.Work.Params.defs
import Submission.Work.Params.basic
import Submission.Work.Params.rparbig

namespace Work.Params

/-- `F·Q ≤ 2^{n.size+2}` as soon as `n` is at least the area threshold `n₁`
(through its consequence `2^{65755586} ≤ n`, i.e. `65755586 ≤ n.size`).

We use the elementary symbolic bounds of `rparbig`:
`F ≤ 2^19008` and `Q ≤ 2^{19021·3456} = 2^65736576`, so `F·Q ≤ 2^65755584 ≤ 2^{n.size+2}`. -/
theorem QallPowNr (n : ℕ) (hsz : 65755586 ≤ n.size) :
    Work.Params.Ffac * Work.Params.Qall ≤ 2 ^ (n.size + 2) := by
  have hF : Ffac ≤ 2 ^ 19008 := Ffac_le_two_pow
  have hQ : Qall ≤ 2 ^ (19021 * 3456) := Qall_le_pow (19021 * 3456) le_rfl
  have hsum : 19008 + 19021 * 3456 ≤ n.size + 2 := by omega
  calc Ffac * Qall ≤ 2 ^ 19008 * 2 ^ (19021 * 3456) := Nat.mul_le_mul hF hQ
    _ = 2 ^ (19008 + 19021 * 3456) := (pow_add 2 19008 (19021 * 3456)).symm
    _ ≤ 2 ^ (n.size + 2) := pow_two_mono hsum

end Work.Params
