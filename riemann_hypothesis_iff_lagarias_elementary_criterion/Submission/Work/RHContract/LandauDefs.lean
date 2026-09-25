import Submission.Work.RHContract.Defs
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# `Work.RHContract.LandauDefs` — the Mellin objects of the Landau step (ROUTE_LEAD §3.3)

* `Phi s = ∫_2^∞ (ψ t − t) k(t) t^{−s} dt`  (the Mellin transform of `J` with the extra
  factor `k`; ROUTE_LEAD's `Φ`);
* `h2 s = ∫_2^∞ (ψ t − t) t^{−s−2} dt` (the Mellin transform of `ψ − id`, whose closed form
  follows from `Commons.NumberTheory.Zeta.logDeriv_zeta_eq_mellin_psi_sub_id` with `w = s+1`);
* `h2Closed` is that closed form, `[−ζ′(s+1)/ζ(s+1) − (s+1)/s]/(s+1) + (1 − 2^{−s})/s`
  (equivalently `(−ζ₁′(s+1)/ζ₁(s+1) − 1)/(s+1) + (1 − 2^{−s})/s`, since `ζ = ζ₁/(s−1)`);
* `h2Minus s = h2Closed s − (deriv h2Closed) s` is `h₂ − h₂′`, the function whose double pole
  at `ρ − 1` is the obstruction in ROUTE_LEAD's B6.
-/

open MeasureTheory

namespace Work.RHContract

noncomputable section

namespace Landau

/-- `Φ(s) = ∫_2^∞ (ψ t − t) k(t) t^{−s} dt`. -/
def Phi (s : ℂ) : ℂ := ∫ t in Set.Ioi 2, ((Chebyshev.psi t - t) * kW t : ℂ) * (t : ℂ) ^ (-s)

/-- `h₂(s) = ∫_2^∞ (ψ t − t) t^{−s−2} dt`. -/
def h2 (s : ℂ) : ℂ := ∫ t in Set.Ioi 2, ((Chebyshev.psi t - t) : ℂ) * (t : ℂ) ^ (-s - 2)

/-- The closed form of `h₂` (ROUTE_LEAD §3.3):
`[−ζ′(s+1)/ζ(s+1) − (s+1)/s]/(s+1) + (1 − 2^{−s})/s`. -/
def h2Closed (s : ℂ) : ℂ :=
  (-(deriv riemannZeta (s + 1)) / riemannZeta (s + 1) - (s + 1) / s) / (s + 1)
    + (1 - (2 : ℂ) ^ (-s)) / s

/-- `h₂ − h₂′` (the derivative being taken in the closed form), the double-pole carrier. -/
def h2Minus (s : ℂ) : ℂ := h2Closed s - deriv h2Closed s

end Landau

end

end Work.RHContract
