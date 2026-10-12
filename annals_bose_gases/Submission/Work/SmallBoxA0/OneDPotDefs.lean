import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory

namespace Work.SmallBoxA0

/-- Cumulative mass `Ffun p t = ∫_0^t r^2 p r dr`. -/
def Ffun (p : ℝ → ℝ) (t : ℝ) : ℝ := ∫ r in Set.Ioo (0 : ℝ) t, r ^ 2 * p r

/-- Tail flux `qfun p r = ∫_r^∞ (s^2 p s)/s ds`. -/
def qfun (p : ℝ → ℝ) (r : ℝ) : ℝ := ∫ s in Set.Ioi r, (s ^ 2 * p s) / s

/-- Shell potential `Ufun p r = ∫_0^r qfun p t dt`. -/
def Ufun (p : ℝ → ℝ) (r : ℝ) : ℝ := ∫ t in Set.Ioo (0 : ℝ) r, qfun p t

/-- Kernel potential `Gfun p r = ∫_0^∞ (s^2 p s)/max(r,s) ds`. -/
def Gfun (p : ℝ → ℝ) (r : ℝ) : ℝ := ∫ s in Set.Ioi (0 : ℝ), (s ^ 2 * p s) / max r s

end Work.SmallBoxA0
