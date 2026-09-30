import Mathlib
import Submission.Commons.NumberTheory.Mertens.second_mertens_converges

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Filter Real
open scoped Topology

namespace Commons.NumberTheory.Mertens

/-!
# `∑_{p ≤ x} 1/p − log log x` is eventually bounded

Since `second_mertens_converges` provides the limit
`M := lim_{x → ∞} (primeRecips x − log log x)`, the function
`x ↦ primeRecips x − Real.log (Real.log x)` tends to `M` at `+∞`, hence it is
eventually bounded: take any point beyond which it stays within distance `1` of
`M` and absorb the tail into the constant `C := |M| + 1`.
-/

lemma primeRecips_sub_loglog_eventually_bounded :
    ∃ (C : ℝ) (_hC : 0 < C) (X₀ : ℝ), 3 ≤ X₀ ∧
      ∀ x : ℝ, X₀ ≤ x → |primeRecips x - Real.log (Real.log x)| ≤ C := by
  rcases second_mertens_converges with ⟨M, hM⟩
  let f : ℝ → ℝ := fun x => primeRecips x - Real.log (Real.log x)
  have hMf : Tendsto f atTop (nhds M) := by
    simpa [f] using hM
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hMf) 1 zero_lt_one
  refine ⟨|M| + 1, ?_, max N 3, le_max_right N 3, ?_⟩
  · have hMnonneg : 0 ≤ |M| := abs_nonneg M
    linarith
  · intro x hx
    have hxN : N ≤ x := le_trans (le_max_left N 3) hx
    have hlt : |f x - M| < 1 := hN x hxN
    have hle1 : |f x - M| ≤ 1 := le_of_lt hlt
    have htri : |f x| ≤ |f x - M| + |M| := by
      calc
        |f x| = |(f x - M) + M| := by congr 1; ring
        _ ≤ |f x - M| + |M| := abs_add_le (f x - M) M
    linarith

end Commons.NumberTheory.Mertens
