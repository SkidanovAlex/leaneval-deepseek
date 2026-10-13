/-
# `exists_cptQ_approx`: the cutoff families and the moment profile (definitions)

This module fixes the vocabulary for the approximation
`Work.FTS.PhiStar.Honesty.exists_cptQ_approx`: for `n : ℕ`, `n ≥ 1`,

* `chiR n : ℝ → ℝ` is a smooth radial cutoff equal to `1` on `[2/n, n]` and vanishing
  outside `(1/n, 2n)`;
* `zetaR n : ℝ → ℝ` is a smooth angular cutoff equal to `1` on `[2/n, π/2 - 2/n]` and
  vanishing outside `(1/n, π/2 - 1/n)`;
* `rho : ℝ → ℝ` is a fixed smooth profile supported in `(1, 3/2) ⊂ (0, π/2)` with
  `∫_0^{π/2} rho θ · sinθ cos²θ dθ = 1`, used to neutralise the angular moment
  `F_* G z = ∫_θ G z θ sinθcos²θ dθ`.

The approximation is `G n z θ = chiR n z · (zetaR n θ · F z θ - lam n F z · rho θ)` where
`lam n F z = ∫_θ zetaR n θ · F z θ · sinθcos²θ dθ`; the key identity used in the estimate is
`chiR n z · lam n F z = ∫_θ (chiR n z · zetaR n θ - 1) · F z θ · sinθcos²θ dθ`, which holds
because `F_* F ≡ 0`.
-/
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.PhiStar.Honesty.CptDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp

set_option autoImplicit false

/-- The smooth step: `0` for `t ≤ 0`, `1` for `1 ≤ t`. -/
def cut01 (t : ℝ) : ℝ := Real.smoothTransition t

/-- The radial cutoff at scale `n`: `1` on `[2/n, n]`, `0` outside `(1/n, 2n)`. -/
def chiR (n : ℕ) (z : ℝ) : ℝ := cut01 ((n : ℝ) * z - 1) * cut01 (2 - z / (n : ℝ))

/-- The angular cutoff at scale `n`: `1` on `[2/n, π/2 - 2/n]`, `0` outside
`(1/n, π/2 - 1/n)`. -/
def zetaR (n : ℕ) (θ : ℝ) : ℝ :=
  cut01 ((n : ℝ) * θ - 1) * cut01 ((n : ℝ) * (Real.pi / 2 - θ) - 1)

/-- A fixed smooth profile supported in `(1, 3/2) ⊂ (0, π/2)`. -/
def rhoAux (θ : ℝ) : ℝ := cut01 (2 * θ - 2) * cut01 (3 - 2 * θ)

/-- The normalisation of the moment profile. -/
def crho : ℝ := ∫ θ in Work.Spaces.Iθ, rhoAux θ * Work.Elliptic.sinCos2 θ

/-- The normalised moment profile with `∫_0^{π/2} rho θ sinθcos²θ dθ = 1`. -/
def rho (θ : ℝ) : ℝ := (crho)⁻¹ * rhoAux θ

/-- The `z`-dependent moment of the truncated source:
`lam n F z = ∫_θ zetaR n θ · F z θ · sinθcos²θ dθ`. -/
def lam (n : ℕ) (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, zetaR n θ * F z θ * Work.Elliptic.sinCos2 θ

/-- The moment of the truncated source, put inside the radial cutoff. -/
def mu (n : ℕ) (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ := chiR n z * lam n F z

/-- **The approximation of `F` at scale `n`.** -/
def approx (n : ℕ) (F : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => chiR n z * (zetaR n θ * F z θ - lam n F z * rho θ)

/-- The error of the approximation at scale `n`. -/
def err (n : ℕ) (F : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => approx n F z θ - F z θ

/-- The shrinking region where the two cutoffs are not simultaneously equal to `1`:
`Ω_n = {z < 2/n} ∪ {n < z} ∪ {θ < 2/n} ∪ {π/2 - 2/n < θ}`. -/
def Omega (n : ℕ) : Set (ℝ × ℝ) :=
  {p | p.1 < 2 / (n : ℝ) ∨ (n : ℝ) < p.1 ∨ p.2 < 2 / (n : ℝ)
    ∨ Real.pi / 2 - 2 / (n : ℝ) < p.2}

theorem Omega_measurable (n : ℕ) : MeasurableSet (Omega n) := by
  refine MeasurableSet.union ?_ ?_
  · exact measurableSet_lt measurable_fst measurable_const
  · refine MeasurableSet.union ?_ ?_
    · exact measurableSet_lt measurable_const measurable_fst
    · refine MeasurableSet.union ?_ ?_
      · exact measurableSet_lt measurable_snd measurable_const
      · exact measurableSet_lt measurable_const measurable_snd

end Work.FTS.PhiStar.Honesty.CptApp
