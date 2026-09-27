import Mathlib
import Submission.Work.Mostow.stdFermiDefs

/-!
# Injectivity of the standard Fermi chart of `ℍ²`

The standard Fermi chart of `E 2 = ℍ²` is, in the linear coordinates
`(s, r) ↦ s • axis + r • axisPerp` of `E 2`, the self-map
`fermiSelf x = cosh (x 1) • lineStd (x 0) + sinh (x 1) • axisPerp`
of `stdFermiDefs`.  In these coordinates its two component functions are
`x ↦ sinh (x 1)` and `x ↦ cosh (x 1) · sinh (x 0)`, and `sinh` is injective, so the chart
is injective.  This is the parametrisation used by `stdFermiVolume`/`stdFermiSelfHjacLeb`.
-/

namespace Work.Mostow

open Submission.Mostow

/-- The Fermi chart is `stdFermi` read in the coordinates of `E 2`. -/
lemma fermiSelf_eq_stdFermi (x : E 2) :
    Work.Mostow.FermiTwo.fermiSelf x = Work.Mostow.FermiTwo.stdFermi (x 0, x 1) := rfl

/-- First coordinate of the Fermi chart: `(fermiSelf x) 1 = sinh (x 1)`. -/
lemma fermiSelf_coord_one (x : E 2) :
    (Work.Mostow.FermiTwo.fermiSelf x) 1 = Real.sinh (x 1) := by
  simp [FermiTwo.fermiSelf, FermiTwo.lineStd, FermiTwo.axis, FermiTwo.axisPerp]

/-- Zeroth coordinate of the Fermi chart: `(fermiSelf x) 0 = cosh (x 1) * sinh (x 0)`. -/
lemma fermiSelf_coord_zero (x : E 2) :
    (Work.Mostow.FermiTwo.fermiSelf x) 0 = Real.cosh (x 1) * Real.sinh (x 0) := by
  simp [FermiTwo.fermiSelf, FermiTwo.lineStd, FermiTwo.axis, FermiTwo.axisPerp]

theorem stdFermiSelfInjective : Function.Injective Work.Mostow.FermiTwo.fermiSelf := by
  intro x y h
  have h1 : Real.sinh (x 1) = Real.sinh (y 1) := by
    have hc := congrArg (fun z : E 2 => z 1) h
    rw [fermiSelf_coord_one x, fermiSelf_coord_one y] at hc
    exact hc
  have e1 : x 1 = y 1 := Real.sinh_injective h1
  have h0 : Real.cosh (x 1) * Real.sinh (x 0) = Real.cosh (y 1) * Real.sinh (y 0) := by
    have hc := congrArg (fun z : E 2 => z 0) h
    rw [fermiSelf_coord_zero x, fermiSelf_coord_zero y] at hc
    exact hc
  have e0 : x 0 = y 0 := by
    have : Real.sinh (x 0) = Real.sinh (y 0) := by
      rw [e1] at h0
      exact mul_left_cancel₀ (Real.cosh_pos (y 1)).ne' h0
    exact Real.sinh_injective this
  ext i
  fin_cases i
  · exact e0
  · exact e1

end Work.Mostow
