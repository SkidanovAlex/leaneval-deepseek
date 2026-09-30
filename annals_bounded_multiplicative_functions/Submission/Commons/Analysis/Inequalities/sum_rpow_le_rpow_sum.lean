import Mathlib.Analysis.MeanInequalitiesPow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.Inequalities

theorem sum_rpow_le_rpow_sum {ι : Type*} (s : Finset ι) (x : ι → ENNReal) {r : ℝ} (hr : 1 ≤ r) :
    s.sum (fun i => x i ^ r) ≤ (s.sum x) ^ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    rw [Finset.sum_insert has, Finset.sum_insert has]
    calc x a ^ r + s.sum (fun i => x i ^ r)
        ≤ x a ^ r + (s.sum x) ^ r := add_le_add_right ih _
      _ ≤ (x a + s.sum x) ^ r := ENNReal.add_rpow_le_rpow_add _ _ hr

end Commons.Analysis.Inequalities