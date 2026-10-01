import Mathlib
import Submission.Work.LinnikAreas.SiegelBase
import Submission.Commons.NumberTheory.Linnik.tentMellin_bridge_scale
/-!
# Definitions for the principal-character (`ζ`) side of the Siegel expansion

This small module holds the notation in which the two `ζ`-lemmas
(`Work.LinnikAreas.zetaTentExplicit`, `Work.LinnikAreas.zetaBoxComparison`) are stated, so that
those statements can be read without any decidability/`open` gymnastics, and so that the file
proving `Work.LinnikAreas.siegelExpansion` can import them without a cycle.

With `L = 11/2`, `K = 3/10`, `𝓛 = log q`:

* `zetaBallSum q ρ` is the ball-restricted sum of the divisor of the completed Riemann zeta
  function against Heath-Brown's tent kernel `tentK L K ((1-u)𝓛)`;
* `farSumP q R` is the (multiplicity weighted) mass of the zeros of `ζ` outside the box
  `InBox q R`, weighted by `‖Hk L K ((1-ρ)𝓛)‖` — i.e. the `χ = 1` summand of
  `Work.LinnikAreas.Siegel.farZeroSum`.
-/

open DirichletCharacter Complex Filter
open scoped Classical

namespace Work.LinnikAreas

/-- The ball-restricted sum of the divisor of the completed Riemann zeta function against the
tent kernel, as a function of the ball radius `ρ`. -/
noncomputable def zetaBallSum (q : ℕ) (ρ : ℝ) : ℂ :=
  ∑ᶠ u : ℂ, (((MeromorphicOn.divisor completedRiemannZeta (Metric.closedBall 0 ρ)) u : ℤ) : ℂ) *
    Commons.NumberTheory.Linnik.tentK (11/2) (3/10) ((1 - u) * (Real.log (q : ℝ) : ℂ))

/-- The `χ = 1` summand of `Siegel.farZeroSum`: the mass of the non-trivial zeros of `ζ`
lying outside the box, weighted by the kernel. -/
noncomputable def farSumP (q : ℕ) [NeZero q] (R : ℝ) : ℝ :=
  ∑' ρ : ℂ, if Work.LinnikContract.InBox q R ρ then 0
    else (Work.LinnikContract.zeroMult (1 : DirichletCharacter ℂ q) ρ : ℝ) *
      ‖Work.LinnikContract.Hk (11/2) (3/10) ((1 - ρ) * (Real.log (q : ℝ) : ℂ))‖

/-- The tent kernel of `Submission.Commons` and Heath-Brown's kernel `Hk` agree away from `0`
(they only differ at `z = 0`, where `Hk` is `0` by the division convention and `tentK` is `K²`,
the value of the Laplace transform). -/
lemma Hk_eq_tentK {L K : ℝ} {z : ℂ} (hz : z ≠ 0) :
    Work.LinnikContract.Hk L K z = Commons.NumberTheory.Linnik.tentK L K z := by
  have h1 : Commons.NumberTheory.Linnik.tentH K z = (1 - Complex.exp (-(K : ℂ) * z)) / z := by
    simpa only [neg_mul] using Commons.NumberTheory.Linnik.tentH_eq K z hz
  simp only [Commons.NumberTheory.Linnik.tentK, h1, Work.LinnikContract.Hk,
    Work.LinnikContract.F2]
  ring_nf

end Work.LinnikAreas
