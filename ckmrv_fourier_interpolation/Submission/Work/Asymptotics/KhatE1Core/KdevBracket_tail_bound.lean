import Mathlib
import Submission.Work.Asymptotics.KhatE1.KdevE2Defs
import Submission.Work.Asymptotics.KhatE1Core.Kdev8_matching_bridge
import Submission.Work.Asymptotics.KhatE1.KdevBracket_rest
import Submission.Work.Asymptotics.KhatE1Core.KdevBracket_cleared_core

namespace Work.Asymptotics.KhatE1Core

/-- **Tail bound for the `E(z)²`-free funnel bracket.**

This is the specialisation to the unit strip `0 ≤ Re z ≤ 1` of the `-1 ≤ Re z ≤ 2`
statement `KhatE1.KdevBracket_rest`; the latter is obtained from the *cleared* bound
`KhatE1Core.KdevBracket_cleared_core` through the (proved) reduction
`KhatE1.KdevBracket_rest_of_cleared`, which divides by the uniform lower bound
`‖Δ(τ)·Sh τ z‖ ≥ (1/32)‖q(τ)‖`. -/
theorem KdevBracket_tail_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z
            - 2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(2 * Real.pi * t)) := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ :=
    Work.Asymptotics.KhatE1.KdevBracket_rest_of_cleared ℓ
      (KdevBracket_cleared_core ℓ)
  exact ⟨C, N, M, hC, hN, hM,
    fun τ z t hF ht hz0 hz1 hzim => hb τ z t hF ht (by linarith) (by linarith) hzim⟩

end Work.Asymptotics.KhatE1Core
