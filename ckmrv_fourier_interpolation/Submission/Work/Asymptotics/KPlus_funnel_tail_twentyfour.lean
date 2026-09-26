import Mathlib
import Submission.Work.Asymptotics.K24FAssembly
import Submission.Work.Asymptotics.K24F_sm_sum_bound

namespace Work.Asymptotics

open UpperHalfPlane

/-- **Funnel tail expansion of `K₊^{(24)}`.**

For `τ` in the funnel `{τ ∈ 𝒟 : 2 ≤ Im τ}` and `z = i t`, `t ≥ Im τ + 1`, the kernel
`K₊^{(24)}` differs from `Compact.Gplus 24` (`Compact/tailDefs.lean`) by
`O((scale τ)^N (1+t)^M e^{-π(t - Im τ)})`. -/
theorem KPlus_funnel_tail_twentyfour :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        (z : ℂ) = (t : ℂ) * Complex.I →
        ‖Work.Kernels.KPlus 24 τ z - Work.Asymptotics.Compact.Gplus 24 τ z‖
          ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(Real.pi * (t - τ.im))) :=
  KPlus_funnel_tail_twentyfour_of_sm K24F_sm_sum_bound

end Work.Asymptotics
