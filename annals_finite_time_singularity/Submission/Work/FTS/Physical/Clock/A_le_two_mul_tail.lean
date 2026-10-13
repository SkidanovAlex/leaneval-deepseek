/-
# `Work.FTS.Physical.Clock.A_le_two_mul_tail` — the lower half of the clock comparison

The amplitude `A` solves `A' = -(1+μ)A` with `1 + μ ≤ 2`, so in integrated form

  `A s ≥ A τ · e^{-2(s-τ)}`  for `0 ≤ τ ≤ s`

(equivalently: `x ↦ A x e^{2x}` is monotone on `[0,∞)`).  Integrating over `[τ,∞)` and using the
tail identity `T - t(τ) = ∫_τ^∞ A` gives

  `A τ ≤ 2 · (T - t τ)`.

Together with `Work.FTS.Physical.PhysClock.tail_le_two_mul` (`T - t τ ≤ 2 A τ`) this is the full
comparison `A(τ) ≍ T - t(τ)`; the present half is the one consumed by the `c/(T-t)` lower bound
for the vorticity (it turns `‖ω‖ ≥ c/A(τ(t))` into `‖ω‖ ≥ c'/(T - t)`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.Physical.Clock.A_le_exp_mul
import Submission.Work.FTS.Physical.Clock.tail_le_two_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory
open scoped Topology

namespace Work.FTS.Physical.Clock

/-- **The amplitude decreases at most like `e^{-2(s-τ)}`**: `A τ e^{-2(s-τ)} ≤ A s` for
`0 ≤ τ ≤ s`.  This is the modulation bound `1 + μ ≤ 2` in integrated form. -/
theorem A_exp_two_le (C : Work.FTS.Physical.PhysClock) {τ s : ℝ} (hτ : 0 ≤ τ) (hτs : τ ≤ s) :
    C.A τ * Real.exp (-2 * (s - τ)) ≤ C.A s := by
  have hcont : ContinuousOn (fun x : ℝ => C.A x * Real.exp (2 * x)) (Set.Ici (0 : ℝ)) :=
    C.hAcont.mul (Real.continuous_exp.comp (continuous_id.const_mul 2)).continuousOn
  have hderiv : ∀ x ∈ interior (Set.Ici (0 : ℝ)),
      HasDerivWithinAt (fun x : ℝ => C.A x * Real.exp (2 * x))
        ((-(1 + C.mu x) * C.A x) * Real.exp (2 * x) + C.A x * (Real.exp (2 * x) * 2))
        (interior (Set.Ici (0 : ℝ))) x := by
    intro x hx
    have hx' : (0 : ℝ) < x := by simpa [interior_Ici] using hx
    have h1 : HasDerivAt (fun x : ℝ => C.A x) (-(1 + C.mu x) * C.A x) x := C.hAderiv x hx'.le
    have h2 : HasDerivAt (fun x : ℝ => Real.exp (2 * x)) (Real.exp (2 * x) * 2) x := by
      simpa using (((hasDerivAt_id x).const_mul 2)).exp
    exact (h1.mul h2).hasDerivWithinAt
  have hnonneg : ∀ x ∈ interior (Set.Ici (0 : ℝ)),
      0 ≤ (-(1 + C.mu x) * C.A x) * Real.exp (2 * x) + C.A x * (Real.exp (2 * x) * 2) := by
    intro x hx
    have hx' : (0 : ℝ) < x := by simpa [interior_Ici] using hx
    have hA : 0 < C.A x := C.hApos x hx'.le
    have hE : 0 < Real.exp (2 * x) := Real.exp_pos _
    have hmu : 1 + C.mu x ≤ 2 := C.hmu_hi x hx'.le
    have heq : (-(1 + C.mu x) * C.A x) * Real.exp (2 * x) + C.A x * (Real.exp (2 * x) * 2)
        = Real.exp (2 * x) * C.A x * (2 - (1 + C.mu x)) := by ring
    rw [heq]
    exact mul_nonneg (mul_nonneg hE.le hA.le) (by linarith)
  have hmono : MonotoneOn (fun x : ℝ => C.A x * Real.exp (2 * x)) (Set.Ici (0 : ℝ)) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) hcont hderiv hnonneg
  have h1 : C.A τ * Real.exp (2 * τ) ≤ C.A s * Real.exp (2 * s) :=
    hmono hτ (le_trans hτ hτs) hτs
  have hpos : 0 < Real.exp (2 * s) := Real.exp_pos _
  have key : (C.A τ * Real.exp (-2 * (s - τ))) * Real.exp (2 * s) ≤ C.A s * Real.exp (2 * s) := by
    calc (C.A τ * Real.exp (-2 * (s - τ))) * Real.exp (2 * s)
        = C.A τ * Real.exp (2 * τ) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 1
          ring_nf
      _ ≤ C.A s * Real.exp (2 * s) := h1
  exact (mul_le_mul_iff_left₀ hpos).mp key

/-- `s ↦ e^{-2(s-τ)}` is integrable on `[τ,∞)`. -/
theorem integrableOn_exp_two_shift (τ : ℝ) :
    IntegrableOn (fun s : ℝ => Real.exp (-2 * (s - τ))) (Set.Ici τ) := by
  have heq : (fun s : ℝ => Real.exp (-2 * (s - τ)))
      = fun s : ℝ => Real.exp (2 * τ) * Real.exp ((-2 : ℝ) * s) := by
    funext s
    rw [← Real.exp_add]
    congr 1
    ring_nf
  rw [heq]
  exact (integrable_exp_mul_Ici (-2) (by norm_num) τ).const_mul (Real.exp (2 * τ))

/-- `∫_τ^∞ e^{-2(s-τ)} ds = 1/2`. -/
theorem integral_exp_two_shift (τ : ℝ) :
    ∫ s in Set.Ici τ, Real.exp (-2 * (s - τ)) = 1 / 2 := by
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  have heq : (fun s : ℝ => Real.exp (-2 * (s - τ)))
      = fun s : ℝ => Real.exp (2 * τ) * Real.exp ((-2 : ℝ) * s) := by
    funext s
    rw [← Real.exp_add]
    congr 1
    ring_nf
  rw [heq, integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0) τ]
  have hval : -Real.exp ((-2 : ℝ) * τ) / (-2 : ℝ) = Real.exp (-2 * τ) / 2 := by ring
  rw [hval]
  have h1 : Real.exp (2 * τ) * Real.exp (-2 * τ) = 1 := by
    rw [← Real.exp_add, show 2 * τ + -2 * τ = 0 by ring, Real.exp_zero]
  calc Real.exp (2 * τ) * (Real.exp (-2 * τ) / 2)
      = (Real.exp (2 * τ) * Real.exp (-2 * τ)) / 2 := by ring
    _ = 1 / 2 := by rw [h1]

/-- **The lower half of the clock comparison**: `A τ ≤ 2 (T - t τ)` for `τ ≥ 0`. -/
theorem A_le_two_mul_tail (C : Work.FTS.Physical.PhysClock) {τ : ℝ} (hτ : 0 ≤ τ) :
    C.A τ ≤ 2 * (C.T - C.t τ) := by
  rw [tail_eq_integral C hτ]
  have hIntA : IntegrableOn C.A (Set.Ici τ) :=
    (integrableOn_A_local C).mono_set (Set.Ici_subset_Ici.mpr hτ)
  have hIntg : IntegrableOn (fun s : ℝ => C.A τ * Real.exp (-2 * (s - τ))) (Set.Ici τ) :=
    (integrableOn_exp_two_shift τ).const_mul (C.A τ)
  have hmono : ∫ s in Set.Ici τ, C.A τ * Real.exp (-2 * (s - τ)) ≤ ∫ s in Set.Ici τ, C.A s :=
    setIntegral_mono_on hIntg hIntA measurableSet_Ici (fun s hs => A_exp_two_le C hτ hs)
  have hval : ∫ s in Set.Ici τ, C.A τ * Real.exp (-2 * (s - τ)) = C.A τ * (1 / 2) := by
    rw [integral_const_mul, integral_exp_two_shift τ]
  have key : C.A τ * (1 / 2) ≤ ∫ s in Set.Ici τ, C.A s := by rw [← hval]; exact hmono
  linarith

end Work.FTS.Physical.Clock
