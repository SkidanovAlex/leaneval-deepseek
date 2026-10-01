
import Mathlib
import Submission.Work.LinnikBurgess.frame_step_defs
import Submission.Work.LinnikBurgess.frameSum_eq_zero
import Submission.Work.LinnikBurgess.frame_count
open scoped BigOperators

namespace Work.ZeroFreeTables.P9F

theorem frame_stub_aux {H : ℕ} (i : Fin 6) {m d g : ℕ} (hm : Squarefree m)
    (hmd : Nat.Coprime m d) (hmg : Nat.Coprime m g) (hd : 0 < d) (hg : 0 < g) :
    Work.LinnikBurgess.frameSum H m d g i ≤ 10 ^ 5 * (3 : ℝ) ^ d.primeFactors.card
        * ((m * d * g).divisors.card : ℝ) ^ 8
        * ((H : ℝ) ^ 6 / ((d : ℝ) * (g : ℝ)) + (H : ℝ) ^ 5 / (g : ℝ)) :=
  Work.LinnikBurgess.frame_count i hm hmd hmg hd hg

end Work.ZeroFreeTables.P9F
