import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.ScatKernelChosen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric
open scoped Real
open Submission BoseGases

set_option autoImplicit false

namespace Work.SmallBoxA0

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The **unnormalized spherical average** of a function `g` on `ℝ³`:
`H(r) = ∫_{S²} g(r • ω) dσ(ω)` with `σ = volume.toSphere` the surface measure
on the unit sphere (`σ(S²) = 4π`). -/
def sphAvg (g : ℝ³ → ℝ) (r : ℝ) : ℝ :=
  ∫ ω : Metric.sphere (0 : ℝ³) 1, g (r • (ω : ℝ³)) ∂(MeasureTheory.volume.toSphere)

/-- The **cumulative source mass** inside radius `t`:
`cumMass H t = ∫_0^t r ^ 2 * H r dr` (so that in the radial case
`cumMass (sphAvg g) t = ∫_{‖x‖ < t} g x dx`). -/
def cumMass (H : ℝ → ℝ) (t : ℝ) : ℝ := ∫ r in (0 : ℝ)..t, r ^ 2 * H r

/-- The **tail source mass** `∫_r^R s * H s ds`. -/
def tailMass (H : ℝ → ℝ) (R r : ℝ) : ℝ := ∫ s in r..R, s * H s

/-- The `shell`-formula profile function
`V(r) = (1/(8π)) (∫_0^r s^2 H(s) ds + r ∫_r^R s H(s) ds)`.  In the radial case
this is the profile `r · radialProfile w r` of the scattering solution `w` with
source profile `H`, as given by the Newton/shell representation. -/
def shellV (H : ℝ → ℝ) (R r : ℝ) : ℝ :=
  (1 / (8 * π)) * (cumMass H r + r * tailMass H R r)

/-- The **radial energy** functional of a source profile `H` (supported in
`[0,R]`): `∫_0^∞ H(r) · shellV H R r · r dr`. -/
def radEnergy (H : ℝ → ℝ) (R : ℝ) : ℝ :=
  ∫ r in Set.Ioi (0 : ℝ), H r * shellV H R r * r

end Work.SmallBoxA0
