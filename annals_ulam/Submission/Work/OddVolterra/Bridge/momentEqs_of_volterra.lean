import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Assembly
import Submission.Work.OddVolterra.Ball
import Submission.Work.OddVolterra.Bridge.momentEqs_of_volterra_tail

namespace Work.OddVolterra.Bridge

/-- **The bridge `momentEqs_of_volterra`.**

The requested statement carries, besides the Abel inversion `harik` and the two row
identities `hrow`, `hrowH`, the hypothesis that `h` is supported in the transition
window `[1 - 2τ, 1 - τ]`.  That support condition is exactly what supplies the tail
vanishing `∀ s, 1 - τ ≤ s → h s = 0` which the constant-of-integration step of the
argument requires: `h` vanishes on `(1 - τ, ∞)` by the support condition and at the
endpoint `1 - τ` by continuity.  With it the perturbed data coincide with the ball
data on `[1 - τ, 1]` (`moment_identities_on_tail`), so `momentF - momentRHS` and
`momentH` vanish there; their `(n+1)`-st resp. `n`-th derivatives vanish on `(0,1)`
by `harik` together with the row identities; hence they vanish identically.  This is
`Work.OddVolterra.Bridge.momentEqs_of_volterra_of_support`. -/
theorem momentEqs_of_volterra (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hhsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hdata : Work.OddVolterra.CurveData n h x y)
    (harik : ∀ a c : ℝ, 0 < a → a ≤ c → c < 1 → ∀ s ∈ Set.Icc a c,
      (∫ σ in s..1,
          (Work.OddVolterra.Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 0 /
            Real.sqrt (σ - s)) = (Work.OddVolterra.Q n h s) 0 ∧
      (∫ σ in s..1,
          (Work.OddVolterra.Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 1 /
            Real.sqrt (σ - s)) = (Work.OddVolterra.Q n h s) 1)
    (hrow : ∀ a c : ℝ, 0 < a → a ≤ c → c < 1 → ∀ s ∈ Set.Icc a c,
      iteratedDeriv (n + 1)
          (fun u : ℝ => Work.OddVolterra.momentF n h x y
            (Work.OddEnvelope.envelopeProfile h x y) u) s =
        Work.OddVolterra.E1 n h s + ∫ σ in s..1,
          (Work.OddVolterra.Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 0 /
            Real.sqrt (σ - s))
    (hrowH : ∀ a c : ℝ, 0 < a → a ≤ c → c < 1 → ∀ s ∈ Set.Icc a c,
      iteratedDeriv n
          (fun u : ℝ => Work.OddVolterra.momentH n h x y
            (Work.OddEnvelope.envelopeProfile h x y) u) s =
        Work.OddVolterra.E2 n h s + ∫ σ in s..1,
          (Work.OddVolterra.Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 1 /
            Real.sqrt (σ - s))
    (hcontF : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun u : ℝ => Work.OddVolterra.momentF n h x y
        (Work.OddEnvelope.envelopeProfile h x y) u - Work.OddVolterra.momentRHS n u)
      (Set.Ioo 0 1))
    (hcontH : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun u : ℝ => Work.OddVolterra.momentH n h x y
        (Work.OddEnvelope.envelopeProfile h x y) u) (Set.Ioo 0 1)) :
    Work.OddVolterra.MomentEqsOn n (Commons.Geometry.Ulam.oddSemicircleMomentConstant n) h x y
      (Work.OddEnvelope.envelopeProfile h x y) (Set.Ioc 0 1) :=
  momentEqs_of_volterra_of_support n hn hh hdata hhsupp harik hrow hrowH hcontF hcontH

end Work.OddVolterra.Bridge
