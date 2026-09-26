import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.Asymptotics.LogLambdaData_L_eq_Lfun
import Submission.Work.Asymptotics.cusp_L_second
import Submission.Work.Residues.theta_E6_identity
import Submission.Work.Kernels.Classical
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.Gcusp_one_exp_small_funnel

namespace Work.Asymptotics.HalfFunnel

/-
# The `i = 1` row of the cusp coefficients `Gcusp` is exponentially small on the funnel

`Gcusp ℓ d 1 j τ` is the coefficient of `e^{2πt}` (resp. `i t e^{2πt}`) in the non-decaying part
`Aexp (Gcusp ℓ d) τ t` of the cusp expansion of the CKMRV kernel.  Both entries decay like
`e^{-2π Im τ}` times a polynomial in `scale τ`, uniformly on the funnel `{τ ∈ 𝒟 : 2 ≤ Im τ}`.
This is what makes `Aexp` polynomially bounded *below* the pole, and it is used in
`Work.Asymptotics.HalfFunnel.funnelLayerTrunc` (the window `1 ≤ t ≤ Im τ - 1` carries the factor
`e^{2πt}`, so the coefficient must beat `e^{-2π Im τ}`).

## Why it is true (and how to prove it)

`Gcusp8 1 j = 0` identically (its definition is `if i = 1 then 0`), so only `d = 24` matters.  The
explicit `Gcusp24 1 j` is a combination of the atoms `τ = phiNeg2`, `phi0 = τE₂ - 3i/π`,
`phi2 = τE₂² - (6i/π)E₂`, `E₄, E₆, E₈, E₁₀, E₁₄, Δ, ψ₂, ψ₄` and `cuspL`; the *polynomial/q⁰* parts
cancel identically:

* `Gcusp24 1 0 = [-(i/288)(p0E14 + p2E10) + (i/144)p1 E4³ - 7i p1 Δ + Δ(cuspL-1)/π
   + (ψ2E10 - ψ4E8)/(1152π)]/2`: at `E2 = E4 = E6 = 1`, `p0 = p1 = p2 = τ`, the first two terms
   cancel (`-(i/288)(2τ) + (i/144)τ = 0`); the remainders are `O(q poly)` (`q = e^{2πiτ}`,
   `|q| = e^{-2π Im τ}`) — e.g. the `Δ`-terms, and the `ψ`-terms via the weight-8 identity
   `ξ₂E₆ - ξ₄E₄ = O(q)` for the cuspidal combination (`ξ₂ = U+W`, `ξ₄ = U²+W²-2V²`; the `q`-parts
   of the two `𝓛`-, `𝓛_S`-contributions cancel against each other below the pole);
* `Gcusp24 1 1 = [(π/864)(p0E14 + p2E10 + 1728p1Δ - 2p1E4³) + iΔ]/2`: the bracket is `O(q poly)`
   (`p0 + p2 - 2p1 = O(q)` since `E₂ = 1 + O(q)` and `E₁₄, E₁₀, E₄³` differ from `1` by `O(q)`).

Numerically (high precision, with the standard theta conventions
`θ00(z) = 1 + 2Σ_{n≥1} e^{πin²z}`, `θ10(z) = 2Σ_{n≥0} e^{πi(n+1/2)²z}`, and the *canonical*
`𝓛_S τ = ℓ.L(S•τ) = Lfun(-1/τ)`, which is forced by `LogLambdaData.slash_S` and
`Work.Asymptotics.LogLambdaData_L_eq_Lfun`): `|Gcusp24 1 0(iT)| = T·e^{-2πT}` and
`|Gcusp24 1 1(iT)| = e^{-2πT}` to 10 digits for `T = 3,4,5,6,8,10,12`.
Beware: the script `_mine/chk_gcusp.py` uses the `θ(0|2τ)` conventions (its `λ` is `λ(2τ)`),
which produces a spurious `e^{-π T}` rate; do not use it to judge this statement.

Suggested formalisation: bound each atom by `C (scale τ)^N e^{-2π Im τ}` or `C (scale τ)^N`
(using `Work.Kernels.KernelGrowth`/`ClassicalFacts` and
`Work.Asymptotics.LogLambdaData_L_eq_Lfun` for `𝓛`), so that the terms without a `Δ`/`q`/`𝓛`
factor cancel exactly; the `T`-law/quasi-periodicity of `L` is not needed.
-/
theorem GcuspRow11Small (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ : UpperHalfPlane) (j : Fin 2), τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im → ‖Work.Asymptotics.Gcusp ℓ d 1 j τ‖ ≤ C * (Work.Kernels.scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) := by
  obtain ⟨C, N, hC, hN, hb⟩ := Work.Asymptotics.Gcusp_one_exp_small_funnel ℓ d hd
  exact ⟨C, N, hC, hN, fun τ j hD h2 => hb τ j (show Work.Asymptotics.Funnel τ from ⟨hD, h2⟩)⟩

end Work.Asymptotics.HalfFunnel
