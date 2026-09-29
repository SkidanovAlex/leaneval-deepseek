import Mathlib
import Submission.Work.IntLib.evArith

/-!
# The empty-chain arithmetic of the `evalPoly` budget

`evArithNil` is the `hs = []` case of the pure arithmetic behind the assembled
`evalPoly` word: if the cost `n1` of the zero-chain program is bounded by
`KZ * (b.size + 4)` (its output is the value `0`, whose encoding is `b`-independent
up to the size of `b` itself), then `n1 + 2` is absorbed by `polyK * polyBudget [] b`.

Concretely `polyBudget [] b = b.size + 3` and `polyK` is `1000 * S` with
`S ≥ KZ + 21`, so the claim reduces to `KZ * (b.size + 4) + 2 ≤ 1000 * S * (b.size + 3)`.
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH

theorem evArithNil (KP KCM KR KEP KE KC KA KZ n1 b : ℕ)
    (hn1 : n1 ≤ KZ * (b.size + 4)) :
    n1 + 2 ≤ Work.IntLib.polyK KP KCM KR KEP KE KC KA KZ * Work.IntLib.polyBudget ([] : List ℕ) b := by
  have hbud : Work.IntLib.polyBudget ([] : List ℕ) b = b.size + 3 := by
    simp [Work.IntLib.polyBudget, Work.IntLib.isz_nat]
  set S := KP * (KCM + KR + 1) + KEP * (KE + 40) + (KR + KC + KA + KZ + 20) + 1 with hSdef
  have hS : KZ + 21 ≤ S := by
    have h1 : 0 ≤ KP * (KCM + KR + 1) := Nat.zero_le _
    have h2 : 0 ≤ KEP * (KE + 40) := Nat.zero_le _
    rw [hSdef]; omega
  have hK : Work.IntLib.polyK KP KCM KR KEP KE KC KA KZ = 1000 * S := by
    rw [Work.IntLib.polyK, ← hSdef]
  rw [hbud, hK]
  have hKZle : KZ ≤ S := by omega
  have hn1' : n1 ≤ S * (b.size + 4) := le_trans hn1 (Nat.mul_le_mul_right _ hKZle)
  have hS1 : 1 ≤ S := by omega
  nlinarith [hn1', hS1, Nat.zero_le b.size]

end Work.IntLib
