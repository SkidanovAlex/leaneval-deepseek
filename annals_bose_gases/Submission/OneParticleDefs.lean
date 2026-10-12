import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
Shared definitions for the one-particle trial state (see `Submission.OneParticle`).
Only definitions live here (no theorems, no `sorry`), so that parallel helper
modules can import this file without creating import cycles.
-/

namespace Submission

set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory Laplacian
open scoped ContDiff Topology Real InnerProductSpace

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- the centre `(1/2,1/2,1/2)` of the unit cube -/
noncomputable def unitCentre : ℝ³ := WithLp.toLp 2 (fun _ : Fin 3 => (1 / 2 : ℝ))

/-- bump data: `ContDiffBump` with `rIn = 1/8 < rOut = 1/4` centred at `unitCentre` -/
noncomputable def unitBumpData : ContDiffBump (unitCentre : ℝ³) :=
  ⟨(1 / 8 : ℝ), (1 / 4 : ℝ), by norm_num, by norm_num⟩

/-- the unit bump `g : ℝ³ → ℝ` (smooth, `0 ≤ g ≤ 1`, `g = 1` on `closedBall unitCentre (1/8)`,
`tsupport g = closedBall unitCentre (1/4)`) -/
noncomputable def unitBump : ℝ³ → ℝ := fun x => unitBumpData x

/-- the open cube `{y | 0 < y m < L for all m}` -/
def openCube (L : ℝ) : Set ℝ³ := {y : ℝ³ | ∀ m : Fin 3, y m ∈ Set.Ioo 0 L}

/-- `A₀ := ∫ g² > 0` -/
noncomputable def unitNorm : ℝ := ∫ x : ℝ³, (unitBump x) ^ 2

/-- normalising coefficient `1 / √(L³ A₀)` -/
noncomputable def oneCoeff (L : ℝ) : ℝ := (Real.sqrt (L ^ 3 * unitNorm))⁻¹

/-- the one-particle trial state `x ↦ oneCoeff L * g (L⁻¹ • x)` -/
noncomputable def oneParticle (L : ℝ) : ℝ³ → ℝ :=
  fun x => oneCoeff L * unitBump (L⁻¹ • x)

/-- universal sup constant `1 / A₀` -/
noncomputable def supC : ℝ := 1 / unitNorm

/-- universal kinetic constant `(∫ |g Δg|) / A₀` -/
noncomputable def kinC : ℝ := (∫ x : ℝ³, |unitBump x * (Δ unitBump) x|) / unitNorm

end BoseGases

end Submission
