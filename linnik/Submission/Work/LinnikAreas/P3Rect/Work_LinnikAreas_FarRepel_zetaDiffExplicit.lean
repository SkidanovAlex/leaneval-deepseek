import Submission.Work.ZeroFreeTables.P9.XiChain
import Submission.Work.LinnikAreas.DhK.Defs
import Submission.Work.LinnikAreas.FarRepel.zetaDiffExplicit_of_ballPF

open scoped Classical BigOperators Topology
open Filter

namespace Work.LinnikAreas.FarRepel

noncomputable section

/-- **Differentiated explicit formula for the Riemann zeta factor, tsum form (unconditional).**
(module `Submission.Work.LinnikAreas.FarRepel.zetaDiffExplicit`; declare in
`namespace Work.LinnikAreas.FarRepel`.)

For `k ≥ 1` odd and `1 < Re s`, with `Λ = completedRiemannZeta` and `ord_u(Λ) = analyticOrderNatAt Λ u`
the multiplicity of `u` as a non-trivial zero of `ζ`:

`(∑' u, ord_u(Λ)·(1/(s-u))^{k+1}) + (∑' n, (1/(s+2n+2))^{k+1}) = 1/(s-1)^{k+1} - (1/k!)·((logDeriv ζ)^{(k)})(s)`

and in particular the first family is summable.  This is the `ζ`-half of the identity
(Lagarias–Montgomery–Odlyzko p. 289; Kadiri–Ng–Wong arXiv:1902.08640 (2.5)).

This is `zetaDiffExplicit_of_ballPF` with its ball-limit partial-fraction hypothesis `hPF`, the
classical Hadamard partial fraction for the entire completion `Ξ = DhK.Xi`, discharged by
`Work.LinnikAreas.FarRepel.xiDerivPF` (the ball divisor sums of `Ξ` converge to the `k`-th
derivative of `logDeriv Ξ`). -/
theorem zetaDiffExplicit (k : ℕ) (hk : 1 ≤ k) (hodd : k % 2 = 1) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun u : ℂ => (analyticOrderNatAt completedRiemannZeta u : ℂ) * (1 / (s - u)) ^ (k + 1)) ∧
    (∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℂ) * (1 / (s - u)) ^ (k + 1))
      + (∑' n : ℕ, (1 / (s + ((2 * (n + 1) : ℕ) : ℂ))) ^ (k + 1))
      = 1 / (s - 1) ^ (k + 1)
        - (1 / (k.factorial : ℂ)) * iteratedDeriv k (logDeriv riemannZeta) s :=
  zetaDiffExplicit_of_ballPF k hk hodd (fun s h => xiDerivPF k hk s h) hs

end

end Work.LinnikAreas.FarRepel
