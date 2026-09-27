import Mathlib
import Submission.Work.Mostow.localIsomDefs

/-!
# `HasDerivAt` for the unit-speed geodesic segment `segfun`

The segment `segfun p q t = (sinh (d - t)/sinh d) • p + (sinh t/sinh d) • q`, where `d = hdist p q`,
is the arclength parametrisation of the geodesic from `p` to `q`.  Differentiating in `t` (the
"time" coordinate of the segment) gives the tangent vector

`(-cosh (d - s)/sinh d) • p + (cosh s/sinh d) • q` at `s`.

The computation does not use any hyperbolicity, and neither `p ≠ q` (which gives `d ≠ 0`, so that
`sinh d ≠ 0`) nor the restriction `s ∈ Icc 0 d` is needed for differentiability; the statement is
proved in the abstract form over an arbitrary real normed space `F` and then specialised to `E n`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-- Abstract form: for vectors `a b` in a real normed space and a fixed `hd : ℝ`, the two
"hyperbolic" coordinate functions `t ↦ sinh (hd - t)/sinh hd` and `t ↦ sinh t/sinh hd` have
derivatives `-cosh (hd - s)/sinh hd` and `cosh s/sinh hd` respectively. -/
theorem hasDerivAt_sinhSeg {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a b : F) (hd s : ℝ) :
    HasDerivAt (fun t : ℝ => (Real.sinh (hd - t) / Real.sinh hd) • a +
        (Real.sinh t / Real.sinh hd) • b)
      ((-Real.cosh (hd - s) / Real.sinh hd) • a + (Real.cosh s / Real.sinh hd) • b) s := by
  have hA : HasDerivAt (fun t : ℝ => Real.sinh (hd - t) / Real.sinh hd)
      ((-Real.cosh (hd - s)) / Real.sinh hd) s := by
    have h := ((Real.hasDerivAt_sinh (hd - s)).comp s
      (HasDerivAt.const_sub hd (hasDerivAt_id (x := s)))).div_const (Real.sinh hd)
    refine h.congr_deriv ?_
    ring
  have hB : HasDerivAt (fun t : ℝ => Real.sinh t / Real.sinh hd)
      (Real.cosh s / Real.sinh hd) s :=
    (Real.hasDerivAt_sinh s).div_const (Real.sinh hd)
  exact (hA.smul_const a).add (hB.smul_const b)

theorem segfunHasDerivAt {n : ℕ} (p q : E n) (hpq : p ≠ q) (s : ℝ) (hs : s ∈ Set.Icc 0 (hdist p q)) :
    HasDerivAt (segfun p q) ((- Real.cosh (hdist p q - s) / Real.sinh (hdist p q)) • p +
      (Real.cosh s / Real.sinh (hdist p q)) • q) s := by
  have _ : p ≠ q := hpq
  have _ : s ∈ Set.Icc 0 (hdist p q) := hs
  change HasDerivAt (fun t : ℝ => (Real.sinh (hdist p q - t) / Real.sinh (hdist p q)) • p +
      (Real.sinh t / Real.sinh (hdist p q)) • q) _ s
  exact hasDerivAt_sinhSeg p q (hdist p q) s

end Work.Mostow
