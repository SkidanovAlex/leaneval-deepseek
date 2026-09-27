import Mathlib
import Submission.Mostow.SubHypDefs

/-!
# Shared setup for the Fermi measure-preservation lemma (`Work.Mostow.fermi_measurePreserving`)

Definitions used by the main proof and by the delegated auxiliary lemmas.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-- The zero-padding ("product") map `E k × E m → E (k+m)`, sending `(v,w)` to the vector whose
first `k` coordinates are `v` and last `m` coordinates are `w`. -/
def prodeMap (k m : ℕ) : E k × E m → E (k + m) :=
  fun p => WithLp.toLp 2 (Fin.append (p.1 : Fin k → ℝ) (p.2 : Fin m → ℝ))

/-- The "Fermi scaling" map `(v,w) ↦ (cosh‖w‖ • v, sinhc‖w‖ • w)`. -/
def gmap (k m : ℕ) (x : E k × E m) : E k × E m :=
  (Real.cosh ‖x.2‖ • x.1, sinhc ‖x.2‖ • x.2)

/-- `tpart` of the padded vector: `√(1 + ‖v‖² + ‖w‖²)`. -/
def tpartX (k m : ℕ) (x : E k × E m) : ℝ := tpart (prodeMap k m x)

end

end Work.Mostow
