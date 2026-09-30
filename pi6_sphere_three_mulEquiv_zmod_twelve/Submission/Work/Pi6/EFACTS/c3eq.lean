import Mathlib
import Submission.Work.Pi6.EFACTS.Coeff
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The cube coefficient `c₃ = 3 c₁` of the Wang transgression of the cover

For the cover `E = Ecov g3` of a Postnikov section `g3 : S³ → P₃` (`b = 3`, `p = proj g3`,
`F = fib g3`, `θ_n = wangTheta 3 … n : H^{n+3}(F) → H^{n+1}(F)`, `θ_{-1} = wangThetaLow`), the
cube contractibility of the transgression gives

  `θ₃(x ⌣ x ⌣ x) = 3 • (x ⌣ x ⌣ θ_{-1}(x))`.

This is the `k = 3` instance of the integral multiplicativity
`Work.Pi6.EFACTS.CollarZ.wangTheta_cup_three` (`θ(x³) = 3 x² θ(x)` for odd `b`), with the degree
transports `transT` (which are the transports `eqToIso …` of the proof terms in the general
statement) stripped by `transT_self`, so that the conclusion lives in the literal degrees
`2 + 4 = 6 = 3 + 3` and `4 + 0 = 4 = 2 + 2` requested by the consumer.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Work.Pi6.EFACTS

noncomputable section

theorem c3eq {P3 : Type} [TopologicalSpace P3] (g3 : C(Work.Pi6.S3, P3)) (x : Work.Pi6.Coh ℤ (Work.Pi6.EFACTS.fib g3) 2) : Work.StemsB.wangTheta 3 (by norm_num) (Work.Pi6.EFACTS.proj g3) Work.Pi6.EFACTS.shellPt (Work.Pi6.EFACTS.hTG g3) (Work.Pi6.EFACTS.hTO g3) 3 (Work.StemsB.cupT ↥((Work.Pi6.EFACTS.proj g3) ⁻¹' {OnePoint.infty}) 2 4 x (Work.StemsB.cupT ↥((Work.Pi6.EFACTS.proj g3) ⁻¹' {OnePoint.infty}) 2 2 x x)) = 3 • Work.StemsB.cupT ↥((Work.Pi6.EFACTS.proj g3) ⁻¹' {OnePoint.infty}) 4 0 (Work.StemsB.cupT ↥((Work.Pi6.EFACTS.proj g3) ⁻¹' {OnePoint.infty}) 2 2 x x) (Work.Pi6.EFACTS.wangThetaLow 3 (by norm_num) (Work.Pi6.Ecov g3) (Work.Pi6.EFACTS.proj g3) (Work.Pi6.EFACTS.isHurewiczFibration_proj g3) (Work.Pi6.EFACTS.hTO g3) Work.Pi6.EFACTS.shellPt (Work.Pi6.EFACTS.hTG g3) x) := by
  have h := CollarZ.wangTheta_cup_three 3 (by norm_num) (by norm_num) (Ecov g3) (proj g3)
    shellPt (hTG g3) (hTO g3) x
  simp only [Work.StemsB.transT_self] at h
  exact h

end

end Work.Pi6.EFACTS
