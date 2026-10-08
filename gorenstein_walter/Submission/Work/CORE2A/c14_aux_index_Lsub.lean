/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CORE2A area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.CORE2A.TorusDefs
import Submission.Work.CORE2A.c14_mul_mem_layer

/-!
# CORE2A, pass 14, aux: `[PGL₂(q) : L₂(q)] = 2`

The subgroup `L₂(q) = Lsub p k = toPGL '' PSL(2,q) ≤ PGL₂(q)` has index `2`
(`Work.CORE2A.index_Lsub_eq_two`, from `Submission.Work.CORE2A.c14_mul_mem_layer`), and the
hypothesis `5 ≤ p ^ k` is only used to deduce `k ≠ 0` (otherwise `p ^ 0 = 1 < 5`).
-/

namespace Work.CORE2A

theorem c14_aux_index_Lsub (p k : ℕ) [Fact p.Prime] (hp : Odd p) (hk : 5 ≤ p ^ k) :
    (Work.GW2.Lsub p k).index = 2 := by
  -- `5 ≤ p ^ k` forces `k ≠ 0`.
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    omega
  exact index_Lsub_eq_two hp hk0

end Work.CORE2A
