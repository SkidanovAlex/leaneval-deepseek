/-
# The cusp expansion of the CKMRV kernel on a compact subset of `𝒟`

The tail statement `Work.Asymptotics.Compact.tail_on_compact` is the `Compact`-namespace
specialisation of the cusp-`i∞` expansion of the CKMRV kernel `z ↦ K^{(d)}(τ,z)`.  The full
statement, together with the explicit coefficient functions `𝒢_{k,j}` of the non-decaying part
and their moderate growth, is proved in `Work.Asymptotics.Kaxis_local_tail` (built on the
atom-wise cusp expansions `cuspExpansionKernel`, `GcuspDefs`, `GcuspInP`).

This file records that specialisation: the quantifier order, the compactness hypothesis and the
`Aexp` bound are literally those of `Kaxis_local_tail`.
-/
import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Kernels.ModerateGrowth
import Submission.Work.HFN.Kaxis_local_tail

noncomputable section

open UpperHalfPlane

namespace Work.HFN.Compact
open Work.Asymptotics  -- ck-hfn-fix: fork moved out of Work.Asymptotics

/-- **Tail control of the cusp expansion of the CKMRV kernel on a compact `K ⊆ 𝒟`.**

There is a `2 × 2` family `G` of coefficient functions of moderate growth on the CKMRV
fundamental domain `𝒟` — with `G 1 j = 0` in dimension `8`, where the kernel grows only
polynomially along the contour — such that, uniformly for `τ ∈ K` and `t ≥ 1`,

  `K^{(d)}(τ,it) - (G 0 0 τ + it·G 0 1 τ + e^{2πt}(G 1 0 τ + it·G 1 1 τ)) = O((1+t)^M e^{-π(t-T₀)})`.

This is `Work.Asymptotics.Kaxis_local_tail`, i.e. the paper's
`K^{(d)}_±(τ,it) = 𝒢^{(d)}_±(τ,it) + O(t²e^{-πt})` (§4.5). -/
theorem tail_on_compact (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (hsub : K ⊆ Work.Asymptotics.DomainD) :
    ∃ G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ,
      (∀ i j : Fin 2, Work.Kernels.ModerateGrowthOn Work.Asymptotics.DomainD (G i j)) ∧
      (d = 8 → ∀ j : Fin 2, G 1 j = 0) ∧
      ∃ C M T₀ : ℝ, 0 < C ∧ 0 ≤ M ∧ 0 ≤ T₀ ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
        τ ∈ K → 1 ≤ t →
          ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp G τ t‖
            ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀))) :=
  Work.HFN.Kaxis_local_tail ℓ d hd hK hsub

end Work.HFN.Compact
