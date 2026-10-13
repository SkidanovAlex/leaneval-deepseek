/-
Copyright: work module for the Elgindi finite-time singularity project.

# `(deriv u)²` is interval integrable on `[a, b]` for `u` of class `C²` there

Elementary lemma used in the elliptic (`Wirtinger`/Poincaré) estimates for the
Elgindi construction: on a compact interval the derivative of a `C²` function is
continuous (in particular bounded on the interval up to the endpoints), hence its
square is interval integrable.

The proof works with `derivWithin u (Icc a b)`, whose `C⁰`-regularity on the closed
interval is `ContDiffOn.continuousOn_derivWithin` (note that the two-sided `deriv u`
need *not* be continuous at the endpoints `a`, `b`, since `u` is only smooth on the
closed interval). The integrability is then transferred to `deriv u` using a.e.
equality on `uIoo a b`, where `derivWithin u s = deriv u` because `s = Icc a b` is a
neighbourhood of each interior point.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.EllipticEst

theorem wirt_deriv_sq_integrable {a b : ℝ} (hab : a < b) {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Icc a b)) :
    IntervalIntegrable (fun x => (deriv u x) ^ 2) volume a b := by
  have hs : UniqueDiffOn ℝ (Set.Icc a b) := uniqueDiffOn_Icc hab
  have hd : ContDiffOn ℝ 1 (derivWithin u (Set.Icc a b)) (Set.Icc a b) :=
    hu.derivWithin (m := 1) hs (by norm_num)
  have hcont : ContinuousOn (fun x => (derivWithin u (Set.Icc a b) x) ^ 2) (Set.Icc a b) :=
    hd.continuousOn.pow 2
  have hii : IntervalIntegrable (fun x => (derivWithin u (Set.Icc a b) x) ^ 2) volume a b :=
    hcont.intervalIntegrable_of_Icc hab.le
  refine hii.congr_uIoo ?_
  intro x hx
  rw [Set.uIoo_of_le hab.le] at hx
  show (derivWithin u (Set.Icc a b) x) ^ 2 = (deriv u x) ^ 2
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]

end Work.FTS.EllipticEst
