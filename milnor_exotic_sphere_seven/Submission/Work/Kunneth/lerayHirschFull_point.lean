import Mathlib
import Submission.Work.LerayHirsch.Chapter
import Submission.Work.Projective.cpn_cohomology
import Submission.Work.Gen.ChernGenerator
import Submission.Work.Kunneth.PointMain

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Kunneth

/-- **Leray–Hirsch for the trivial bundle `ε^m` over the point.**  The projectivisation is
`P(ε^m) = ℂP^{m-1}` (`m = 0`: empty), so `H^*(P(ε^m))` is free over `H^*(pt) = ℤ` on
`1, ζ, …, ζ^{m-1}`: the assembly is

* `m = 0`: `P(ε⁰)` is empty, so both sides vanish;
* `m = n+1`, `k ≤ n`: the Leray–Hirsch map is `a ↦ a • ζ^k` on the single non-vanishing
  coefficient (`Work.Kunneth.PointSumCollapse`, `Work.Kunneth.PointTopValue`), and `ζ^k` generates
  `H^{2k}(ℂPⁿ;ℤ)` with infinite order (`Work.Kunneth.keyLH`, `Work.Kunneth.PointFunctional`);
* `m = n+1`, `k > n`: `H^{2k}(ℂPⁿ;ℤ) = 0` and all coefficients are in positive degree;
* odd degrees and `m = 0`: both sides are subsingletons (`H^{2k+1}(ℂPⁿ;ℤ) = 0`,
  `Work.Projective.cpn_cohomology`). -/
theorem lerayHirschFull_point (m : ℕ) :
    Work.LerayHirsch.LerayHirschFull (Work.LerayHirsch.trivCore m) := by
  cases m with
  | zero => exact ⟨lerayHirsch_trivCore_zero, lerayHirschOdd_trivCore_zero⟩
  | succ n =>
    refine ⟨fun k => ?_, fun k => ?_⟩
    · by_cases hk : k ≤ n
      · exact lerayHirsch_trivCore_succ_le n k hk
      · exact lerayHirsch_trivCore_succ_high n k (by omega)
    · exact lerayHirschOdd_trivCore_succ n k

end Work.Kunneth
