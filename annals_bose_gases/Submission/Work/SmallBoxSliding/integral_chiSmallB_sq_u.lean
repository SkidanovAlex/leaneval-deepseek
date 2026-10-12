import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxSliding.nBox_integral_u
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `u`-integral of the squared two-factor cutoff `χ_{B(u)}`

For `χ_{B(u)}(x) = χ_M(x/ℓ)·χ_M(x/(ℓd) − u)` (`Submission.BoseGases.chiSmallB`,
FS `eq:chiBdefinition`) we compute, for every centre `y`,

    ∫_u χ_{B(u)}(y)² du = χ_M(y/ℓ)² .

The `u`-dependence of `χ_{B(u)}(y)²` sits entirely in the factor
`χ_M(y/(ℓd) − u)²`: the first factor is a constant, so

    χ_{B(u)}(y)² = χ_M(y/ℓ)² · χ_M(y/(ℓd) − u)² ,

and pulling the constant out of the integral leaves

    χ_M(y/ℓ)² · ∫_u χ_M(y/(ℓd) − u)² du .

The remaining integral is `∫_v χ_M(v)² dv = 1` by the measure preserving
reflection `u ↦ y/(ℓd) − u` on `ℝ³`
(`Work.SmallBoxSliding.nBox_integral_u_aux`) together with the `L²`
normalisation `Submission.BoseGases.chiSmall_L2`.

No positivity hypothesis on `ℓ` or `d` is needed: the reflection `u ↦ c − u`
is measure preserving for *every* `c` (and for `ℓ*d = 0` the Lean inverse
`(ℓ*d)⁻¹ = 0` simply gives `c = 0`).  For `M = 0` the normalisation integral
`∫(χ_M)²` is the divergent `∫ 1` on `ℝ³`, which the Bochner convention reads
as `0`; hence `χ_0 ≡ 0` and both sides vanish.
-/

noncomputable section

open MeasureTheory

namespace Work.SmallBoxSliding

/-- **The `u`-integral of `χ_{B(u)}(y)²` is the square of the big-box
factor.**  See the module docstring for the two ingredients (measure
preserving reflection + `L²` normalisation). -/
theorem integral_chiSmallB_sq_u {M : ℕ} (hM1 : 1 ≤ M) {ℓ d : ℝ}
    (y : EuclideanSpace ℝ (Fin 3)) :
    (∫ u : EuclideanSpace ℝ (Fin 3), (Submission.BoseGases.chiSmallB M ℓ d u y) ^ 2)
      = (Submission.BoseGases.chiScale ℓ y) ^ 2 := by
  -- `M ≥ 1`: separate the constant `u`-independent factor, then use the
    -- measure preserving reflection `u ↦ y/(ℓd) − u` and `∫χ_M² = 1`.
    have hpt : ∀ u : EuclideanSpace ℝ (Fin 3),
        (Submission.BoseGases.chiSmallB M ℓ d u y) ^ 2
          = (Submission.BoseGases.chiScale ℓ y) ^ 2
            * (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u)) ^ 2 := by
      intro u
      rw [Submission.BoseGases.chiSmallB, mul_pow]
    rw [funext hpt, MeasureTheory.integral_const_mul]
    rw [nBox_integral_u_aux
      (fun v : EuclideanSpace ℝ (Fin 3) => (Submission.BoseGases.chiSmall M v) ^ 2)
      ((ℓ * d)⁻¹ • y)]
    rw [Submission.BoseGases.chiSmall_L2 hM1, mul_one]

end Work.SmallBoxSliding
