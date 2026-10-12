import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.KinRowQuant
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

/-- `N`: the (frame-identity) total mass, `∑ₙ ℓ⁻³‖kinFT g kₙ‖²`. -/
def hsN (ℓ : ℝ) (g : EuclideanSpace ℝ (Fin 3) → ℂ) : ℝ :=
  ∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2

/-- `Λ(t)`: the lattice heat content. -/
def hsLam (ℓ : ℝ) (g : EuclideanSpace ℝ (Fin 3) → ℂ) (t : ℝ) : ℝ :=
  ∑' n : Fin 3 → ℤ,
    (ℓ ^ 3)⁻¹ * Real.exp (-t * ‖kmomInt ℓ n‖ ^ 2) *
      ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2

/-- `R(t)`: the continuum heat content. -/
def hsR (ℓ : ℝ) (g : EuclideanSpace ℝ (Fin 3) → ℂ) (t : ℝ) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
    Real.exp (-t * ‖p‖ ^ 2) * ‖Submission.BoseGases.kinFT g p‖ ^ 2

/-- The marginal `h(t) = 2R(t) + N - 3Λ(t)`; the target is `h ≥ 0`. -/
def hsMarg (ℓ : ℝ) (g : EuclideanSpace ℝ (Fin 3) → ℂ) (t : ℝ) : ℝ :=
  2 * hsR ℓ g t + hsN ℓ g - 3 * hsLam ℓ g t

/-- `K_T(t)`: the `|p|²`-weighted lattice heat content (the derivative `-Λ'`). -/
def hsKT (ℓ : ℝ) (g : EuclideanSpace ℝ (Fin 3) → ℂ) (t : ℝ) : ℝ :=
  ∑' n : Fin 3 → ℤ,
    (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖ ^ 2 * Real.exp (-t * ‖kmomInt ℓ n‖ ^ 2) *
      ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2

/-- `K_R(t)`: the `|p|²`-weighted continuum heat content (the derivative `-R'`). -/
def hsKR (ℓ : ℝ) (g : EuclideanSpace ℝ (Fin 3) → ℂ) (t : ℝ) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
    ‖p‖ ^ 2 * Real.exp (-t * ‖p‖ ^ 2) * ‖Submission.BoseGases.kinFT g p‖ ^ 2

/-- The **continuum mass** `(2π)⁻³∫‖kinFT g p‖²` (equal to `hsN` by the frame identity). -/
def hsM0 (ℓ : ℝ) (g : EuclideanSpace ℝ (Fin 3) → ℂ) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
    ‖Submission.BoseGases.kinFT g p‖ ^ 2

/-- The **continuum second moment** `(2π)⁻³∫‖p‖²‖kinFT g p‖²` (the free kinetic energy). -/
def hsM2 (ℓ : ℝ) (g : EuclideanSpace ℝ (Fin 3) → ℂ) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
    ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT g p‖ ^ 2

/-- `K_T^{(2)}(t)`: the `|p|⁴`-weighted lattice heat content (the second lattice moment). -/
def hsKT2 (ℓ : ℝ) (g : EuclideanSpace ℝ (Fin 3) → ℂ) (t : ℝ) : ℝ :=
  ∑' n : Fin 3 → ℤ,
    (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖ ^ 4 * Real.exp (-t * ‖kmomInt ℓ n‖ ^ 2) *
      ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2

/-- `K_R^{(2)}(t)`: the `|p|⁴`-weighted continuum heat content. -/
def hsKR2 (ℓ : ℝ) (g : EuclideanSpace ℝ (Fin 3) → ℂ) (t : ℝ) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
    ‖p‖ ^ 4 * Real.exp (-t * ‖p‖ ^ 2) * ‖Submission.BoseGases.kinFT g p‖ ^ 2

/-- The ratio whose antitonicity is the crux. -/
def hsRatio (ℓ : ℝ) (g : EuclideanSpace ℝ (Fin 3) → ℂ) (t : ℝ) : ℝ := hsKT ℓ g t / hsKR ℓ g t

end Work.BoseBoxFock
