import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Submission.Work.FTS.EllSol.Base

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollSmooth

open MeasureTheory Set Filter
open scoped Topology

/-- Taylor's formula of order two with the remainder in integral form, on the open interval
`(0, π/2)`: for `f : ℝ → ℝ` of class `C²` on `Ioo 0 (π/2)` and points `a, x ∈ Ioo 0 (π/2)`
(no ordering assumed — the interval integral is the signed one),
`f x = f a + (x - a) f'(a) + ∫_a^x (x - t) f''(t) dt`.

Both the fundamental theorem of calculus and the integration by parts used below are stated in
Mathlib for arbitrary (unordered) endpoints via `Set.uIcc`, so the two orderings need not be
separated. -/
theorem slice_taylor_two {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    {a x : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hx : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    f x = f a + (x - a) * deriv f a + ∫ t in a..x, (x - t) * deriv (deriv f) t := by
  -- the closed interval between `a` and `x` lies in the open interval where `f` is `C²`
  have hsub : Set.uIcc a x ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro t ht
    rcases le_total a x with h | h
    · rw [uIcc_of_le h] at ht
      exact ⟨lt_of_lt_of_le ha.1 ht.1, lt_of_le_of_lt ht.2 hx.2⟩
    · rw [uIcc_of_ge h] at ht
      exact ⟨lt_of_lt_of_le hx.1 ht.1, lt_of_le_of_lt ht.2 ha.2⟩
  have hcont1 : ContinuousOn (deriv f) (Set.uIcc a x) := (c2_continuousOn_deriv hf).mono hsub
  have hcont2 : ContinuousOn (deriv (deriv f)) (Set.uIcc a x) :=
    (c2_continuousOn_deriv_deriv hf).mono hsub
  have hderiv1 : ∀ t ∈ Set.uIcc a x, HasDerivAt (deriv f) (deriv (deriv f) t) t :=
    fun t ht => c2_hasDerivAt_deriv hf (hsub ht)
  -- fundamental theorem of calculus: `∫_a^x f' = f x - f a`
  have hFTC : ∫ t in a..x, deriv f t = f x - f a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := f) (f' := fun t : ℝ => deriv f t) (a := a) (b := x)
      (fun t ht => c2_hasDerivAt_self hf (hsub ht)) hcont1.intervalIntegrable
  -- integration by parts with `u t = x - t` (so `u' = -1`) and `v = deriv f` (so `v' = f''`):
  -- `∫_a^x (x - t) f'' = -(x - a) f'(a) + ∫_a^x f'`
  have hIBP : ∫ t in a..x, (x - t) * deriv (deriv f) t
      = -(x - a) * deriv f a + ∫ t in a..x, deriv f t := by
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (a := a) (b := x)
      (u := fun t : ℝ => x - t) (u' := fun _ : ℝ => (-1 : ℝ))
      (v := fun t : ℝ => deriv f t) (v' := fun t : ℝ => deriv (deriv f) t)
      (fun t _ => by simpa using (hasDerivAt_id t).const_sub x)
      hderiv1 intervalIntegrable_const hcont2.intervalIntegrable
    have hneg : (fun t : ℝ => (-1 : ℝ) * deriv f t) = fun t : ℝ => -(deriv f t) := by
      funext t
      ring
    rw [h, hneg, intervalIntegral.integral_neg]
    ring
  rw [hIBP, hFTC]
  ring

end Work.FTS.EllSol.EllPkgAux.MollSmooth
