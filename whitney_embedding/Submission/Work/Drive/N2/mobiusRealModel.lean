import Mathlib
import Submission.Work.Drive.Morse

/-!
# A `ℝ³` model of the Möbius band and its height

The twisted window of the assembly needs a *model surface in `ℝ³`* — the saddle window's model
(`Work.Drive.N2.saddleModelPsi`) lives in the plane, but the twisted block needs a Möbius band.  This file
fixes the standard parametrisation

  `mobS (η φ) = ((1 + sin η * cos (φ/2)) * cos φ, (1 + sin η * cos (φ/2)) * sin φ, sin η * sin (φ/2))`

(the band `|sin η| < 1/2`, say) together with its height `mobZ (η φ) = sin η * sin (φ/2)` (the third
coordinate), and the Möbius identification under which both descend to the band:

  `mobS (-η, φ + 2π) = mobS (η, φ)`,   `mobZ (-η, φ + 2π) = mobZ (η, φ)`.

The height `mobZ = (sin η)(sin (φ/2))` has, on the band, the critical-point structure of a twisted block:
`∂/∂η` vanishes on `cos η = 0` and `∂/∂φ` on `cos (φ/2) = 0`, so the only critical point is
`(η, φ) ≡ (0, 0)` where `mobZ ≈ (sin η)(φ/2)` — a *saddle*, exactly the "one circle twisting into itself"
block.  (This is the `ℝ³` counterpart of H8's Sudanese band, whose height `FN` instead has a minimum and a
saddle; the two are different elementary cobordisms, so the twisted model must be built rather than
borrowed.)

The properties proved here are the ones the block consumes: the identification above, and (delegated)
injectivity modulo the identification plus injectivity of the differential — i.e. `mobS` really is an
embedding of the Möbius band into `ℝ³`.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff

noncomputable section

/-- The `ℝ³` Möbius-band parametrisation (the standard "flat band" picture). -/
def mobS (η φ : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![(1 + Real.sin η * Real.cos (φ / 2)) * Real.cos φ,
    (1 + Real.sin η * Real.cos (φ / 2)) * Real.sin φ,
    Real.sin η * Real.sin (φ / 2)]

/-- The height of the `ℝ³` Möbius model: its third coordinate. -/
def mobZ (η φ : ℝ) : ℝ := Real.sin η * Real.sin (φ / 2)

/-- The third coordinate of `mobS` is `mobZ`. -/
theorem mobS_third (η φ : ℝ) : mobS η φ 2 = mobZ η φ := by
  simp [mobS, mobZ, WithLp.toLp]

/-- The Möbius identification, on the parametrisation. -/
theorem mobS_period (η φ : ℝ) : mobS (-η) (φ + 2 * Real.pi) = mobS η φ := by
  ext i
  fin_cases i <;>
    simp [mobS, WithLp.toLp, Real.cos_add, Real.sin_add, Real.cos_pi, Real.sin_pi,
      Real.cos_neg, Real.sin_neg, show (φ + 2 * Real.pi) / 2 = φ / 2 + Real.pi by ring]

/-- The height is invariant under the Möbius identification. -/
theorem mobZ_period (η φ : ℝ) : mobZ (-η) (φ + 2 * Real.pi) = mobZ η φ := by
  simp [mobZ, Real.sin_neg, Real.cos_neg, Real.sin_add, Real.sin_pi, Real.cos_pi,
    show (φ + 2 * Real.pi) / 2 = φ / 2 + Real.pi by ring]

end

end Work.Drive.N2
