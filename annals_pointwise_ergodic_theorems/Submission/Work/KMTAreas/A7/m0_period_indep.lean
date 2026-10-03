import Mathlib
import Submission.Work.KMTAreas.A7.spikeDefs
import Submission.Work.KMTPlan.A6.mZ_period_eq

namespace Work.KMTAreas.A7

/-- **`M₀` does not depend on the choice of modulus, as long as that modulus kills both
frequencies `α₁, α₂`.**

`M0 P N q α₁ α₂ ξ₁ ξ₂ = weylAvg P N α₁ α₂ ξ₁ ξ₂ − mZ P q α₁ α₂ * mTilde P N ξ₁ ξ₂`; the discrete
average `weylAvg` and the oscillatory integral `mTilde` do not involve `q` at all, and the
arithmetic symbol `mZ P q α₁ α₂` is independent of `q` among the moduli with `q • α₁ = q • α₂ = 0`
by `Work.KMTPlan.A6.mZ_period_eq` (the character `n ↦ e(α₁n + α₂P(n))` is `q`-periodic). -/
theorem m0_period_indep (P : Polynomial ℤ) (N : ℕ) {q q' : ℕ}
    {α₁ α₂ : Work.Analysis.IonescuWainger.Circle}
    (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (h₁ : q • α₁ = 0) (h₂ : q • α₂ = 0) (h₁' : q' • α₁ = 0) (h₂' : q' • α₂ = 0)
    (ξ₁ ξ₂ : ℝ) :
    Work.KMTAreas.A7.M0 P N q α₁ α₂ ξ₁ ξ₂ = Work.KMTAreas.A7.M0 P N q' α₁ α₂ ξ₁ ξ₂ := by
  have hmZ : mZ P q α₁ α₂ = mZ P q' α₁ α₂ :=
    Work.KMTPlan.A6.mZ_period_eq P (by omega) (by omega) h₁ h₂ h₁' h₂'
  simp only [M0, hmZ]

end Work.KMTAreas.A7
