import Mathlib
import Submission.Work.Asymptotics.KhatE1Defs
import Submission.Work.Asymptotics.KhatE1.Kdev_cusp0_strip_sharp
import Submission.Work.Asymptotics.KhatE1.Kdev_strip_of_cusp0

namespace Work.Asymptotics.KhatE1

/-- **The sharp strip bound for the deviation `Kdev = K̂ - (𝒢₊ - 𝒢₋)/2` on the funnel.**

The deviation transforms under `τ ↦ S • τ` into the cusp-`0` deviation of the kernel
`Kfun = (K₊ + K₋)/2`:

  `Kdev τ z = -τ^{-d/2} (Kfun (S • τ) z - (𝒢₊(S•τ,z) + 𝒢₋(S•τ,z))/2)`,

which is the content of `Khat_eq_neg_slash_pointwise` combined with the `S`-law of the cusp
model `Gfun = (𝒢₊ + 𝒢₋)/2`.  Since `S` maps the funnel `𝓕 = {τ ∈ 𝒟 : Im τ ≥ 2}` onto the
cusp-`0` tile `E = KEpsilon`, and `scale (S • τ) ≤ 3 (scale τ)^2` there, the sharp strip bound
on `E` (the statement `Kdev_cusp0_strip_sharp`) transports to the funnel bound above.  The
transport itself is `Work.Asymptotics.KhatE1.strip_sharp_of_cusp0`. -/
theorem Kdev_strip_sharp (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖Work.Asymptotics.Kdev ℓ d τ z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(Real.pi * t)) :=
  strip_sharp_of_cusp0 ℓ d hd (Kdev_cusp0_strip_sharp ℓ d hd)

end Work.Asymptotics.KhatE1
