import Mathlib
import Submission.Work.WilG4c.Defs

namespace Work.WilG4c

/-- `ContDiffAt` is a *local* condition at a point: if `g` is `C^k` at `z₀`, then `g` is `C^k`
at every point of a neighbourhood of `z₀` (Mathlib's `ContDiffAt.eventually`). Consequently the
same holds along any curve which is continuous at `x` and passes through `pt t₀ y₀` at `x`.

This is the "eventual smoothness along the curve" statement used in the Cdp (piecewise
`C^k`-gluing) reduction. -/
theorem CdpEventuallyCurveSmooth {n k : ℕ} {g : (Fin (n + 1) → ℝ) → ℝ} {ψ : ℝ → ℝ}
    {γ : ℝ → Fin n → ℝ} {x t₀ : ℝ} {y₀ : Fin n → ℝ}
    (hF : ContDiffAt ℝ k g (Work.WilkG4c.pt t₀ y₀))
    (hψ : ContinuousAt ψ x) (hψx : ψ x = t₀) (hγ : ContinuousAt γ x) (hγx : γ x = y₀) :
    Filter.Eventually (fun u : ℝ => ContDiffAt ℝ k g (Work.WilkG4c.pt (ψ u) (γ u))) (nhds x) := by
  -- `ContDiffAt ℝ k g` holds on a neighbourhood of `pt t₀ y₀` (`k` is finite).
  have hloc : ∀ᶠ z in nhds (Work.WilkG4c.pt t₀ y₀), ContDiffAt ℝ k g z :=
    hF.eventually (by simp)
  -- The curve `u ↦ pt (ψ u) (γ u) = Fin.cons (ψ u) (γ u)` is continuous at `x`.
  have hcurve : ContinuousAt (fun u : ℝ => Work.WilkG4c.pt (ψ u) (γ u)) x := hψ.finCons hγ
  have htend : Filter.Tendsto (fun u : ℝ => Work.WilkG4c.pt (ψ u) (γ u)) (nhds x)
      (nhds (Work.WilkG4c.pt t₀ y₀)) := by
    simpa [hψx, hγx] using hcurve.tendsto
  -- Pull the neighbourhood back through the continuous curve.
  simpa using htend.eventually hloc

end Work.WilG4c
