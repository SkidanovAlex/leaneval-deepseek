import Mathlib
import Submission.Work.BMF.mr_direct.badDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

theorem badQ_bounds {a Y : ℝ} (ha : a ≤ 1) (h1 : 1 ≤ Real.log Y)
    (h2 : 1 ≤ Real.log (Real.log Y)) :
    (1 : ℝ) ≤ Work.BMF.mr_direct.badQ Y ∧
    Work.BMF.mr_direct.badP a Y ≤ Work.BMF.mr_direct.badQ Y ∧
    Real.log (Work.BMF.mr_direct.badQ Y) ≤ Real.log Y := by
  have hLpos : 0 < Real.log Y := lt_of_lt_of_le zero_lt_one h1
  have hlpos : 0 < Real.log (Real.log Y) := lt_of_lt_of_le zero_lt_one h2
  have hQ1 : (1 : ℝ) ≤ Work.BMF.mr_direct.badQ Y := by
    rw [Work.BMF.mr_direct.badQ]
    exact Real.one_le_exp (div_nonneg hLpos.le hlpos.le)
  refine ⟨hQ1, ?_, ?_⟩
  · rw [Work.BMF.mr_direct.badP]
    calc Work.BMF.mr_direct.badQ Y ^ a
        ≤ Work.BMF.mr_direct.badQ Y ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hQ1 ha
      _ = Work.BMF.mr_direct.badQ Y := Real.rpow_one _
  · rw [Work.BMF.mr_direct.badQ, Real.log_exp]
    rw [div_le_iff₀ hlpos]
    nlinarith [hLpos, h2]

end Work.BMF.mr_direct
