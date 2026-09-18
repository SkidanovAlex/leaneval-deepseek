import Mathlib.NumberTheory.WellApproximable

namespace Commons.NumberTheory.DuffinSchaeffer

open Set Filter
open scoped Topology

theorem addWellApproximable_eq_limsup_piecewise (δ : ℕ → ℝ) :
    addWellApproximable UnitAddCircle δ =
      limsup (fun n : ℕ => if 0 < n then approxAddOrderOf UnitAddCircle n (δ n) else
        (∅ : Set UnitAddCircle)) atTop := by
  change blimsup (fun n : ℕ => approxAddOrderOf UnitAddCircle n (δ n)) atTop (fun n => 0 < n) =
      limsup (fun n : ℕ => if 0 < n then approxAddOrderOf UnitAddCircle n (δ n) else
        (∅ : Set UnitAddCircle)) atTop
  rw [← Nat.cofinite_eq_atTop]
  rw [Filter.cofinite.blimsup_set_eq, Filter.cofinite.limsup_set_eq]
  congr 1
  funext x
  apply congrArg Set.Infinite
  ext n
  by_cases hn : 0 < n <;> simp [hn]

end Commons.NumberTheory.DuffinSchaeffer