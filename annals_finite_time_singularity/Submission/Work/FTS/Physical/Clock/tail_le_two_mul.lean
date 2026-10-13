/-
# `Work.FTS.Physical.Clock.tail_le_two_mul` — the clock comparison `T - t ≤ 2A`

The amplitude `A` of the dynamic rescaling satisfies `A s ≤ A τ · e^{-(s-τ)/2}` for `0 ≤ τ ≤ s`
(`Work.FTS.Physical.Clock.A_le_exp_mul`).  Integrating this pointwise bound over the tail
`[τ,∞)` gives

  `T - t(τ) = ∫_τ^∞ A ≤ A τ · ∫_τ^∞ e^{-(s-τ)/2} ds = 2 A τ`,

the quantitative form `A ≍ T - t` of the clock, which is exactly the input of the `c/(T-t)`
vorticity lower bound of the physical reconstruction.

This module is self-contained: the three analytic ingredients (integrability of `A` on `[0,∞)`,
the tail identity `T - t(τ) = ∫_τ^∞ A`, and the elementary exponential integral
`∫_τ^∞ e^{-(s-τ)/2} ds = 2`) are proved here as helpers, on top of the (already proved)
exponential decay bound.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.Physical.Defs
import Submission.Work.FTS.Physical.Clock.A_le_exp_mul
import Submission.Work.FTS.Physical.Clock.T_sub_t_eq_tail

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory
open scoped Topology

namespace Work.FTS.Physical.Clock

/-! ### Integrability of exponentials on half-lines -/

/-- `e^{a x}` is integrable on `[c,∞)` for `a < 0` (transfer of `integrableOn_exp_mul_Ioi`
from `(c,∞)` to `[c,∞)`, which differ by a null set). -/
theorem integrable_exp_mul_Ici (a : ℝ) (ha : a < 0) (c : ℝ) :
    IntegrableOn (fun x : ℝ => Real.exp (a * x)) (Set.Ici c) :=
  (integrableOn_exp_mul_Ioi ha c).congr_set_ae Ioi_ae_eq_Ici.symm

/-- The shifted Gaussian-type exponential `s ↦ e^{-(s-τ)/2}` is integrable on `[τ,∞)`. -/
theorem integrableOn_exp_shift (τ : ℝ) :
    IntegrableOn (fun s : ℝ => Real.exp (-(s - τ) / 2)) (Set.Ici τ) := by
  have heq : (fun s : ℝ => Real.exp (-(s - τ) / 2))
      = fun s : ℝ => Real.exp (τ / 2) * Real.exp ((-1 / 2 : ℝ) * s) := by
    funext s
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq]
  exact (integrable_exp_mul_Ici (-1 / 2) (by norm_num) τ).const_mul (Real.exp (τ / 2))

/-- **`A` is integrable on `[0,∞)`**: the modulating amplitude decays at least like
`e^{-τ/2}`, so the blow-up happens in finite time and `T = ∫₀^∞ A < ∞`. -/
theorem integrableOn_A_local (C : Work.FTS.Physical.PhysClock) :
    IntegrableOn C.A (Set.Ici (0 : ℝ)) := by
  have hg : IntegrableOn (fun s : ℝ => C.A 0 * Real.exp ((-1 / 2 : ℝ) * s))
      (Set.Ici (0 : ℝ)) :=
    (integrable_exp_mul_Ici (-1 / 2) (by norm_num) 0).const_mul (C.A 0)
  refine hg.mono' (C.hAcont.aestronglyMeasurable measurableSet_Ici) ?_
  rw [ae_restrict_iff' measurableSet_Ici]
  filter_upwards with s hs
  rw [Real.norm_of_nonneg (C.hApos s hs).le]
  have h := A_le_exp_mul C (le_refl (0 : ℝ)) hs
  have hexp : Real.exp (-(s - 0) / 2) = Real.exp ((-1 / 2 : ℝ) * s) := by
    congr 1
    ring
  rw [hexp] at h
  exact h

/-! ### The tail identity and the exponential integral -/

/-- **Tail identity** `T - t(τ) = ∫_τ^∞ A ds`: the physical time left before blow-up is the
integral of the amplitude over `[τ,∞)`. -/
theorem tail_eq_integral (C : Work.FTS.Physical.PhysClock) {τ : ℝ} (hτ : 0 ≤ τ) :
    C.T - C.t τ = ∫ s in Set.Ici τ, C.A s := by
  have hf : IntegrableOn C.A (Set.Ici (0 : ℝ)) := integrableOn_A_local C
  have h1 : (∫ s in Set.Ici (0 : ℝ), C.A s) - (∫ s in Set.Ici τ, C.A s)
      = ∫ s in Set.Ico (0 : ℝ) τ, C.A s := intervalIntegral.integral_Ici_sub_Ici hf hτ
  have h2 : (∫ s in Set.Ico (0 : ℝ) τ, C.A s) = C.t τ := by
    rw [Work.FTS.Physical.PhysClock.t, intervalIntegral.integral_of_le hτ,
      integral_Ico_eq_integral_Ioc]
  rw [Work.FTS.Physical.PhysClock.T, ← h2]
  linarith

/-- `∫_τ^∞ e^{-(s-τ)/2} ds = 2`. -/
theorem integral_exp_shift (τ : ℝ) :
    ∫ s in Set.Ici τ, Real.exp (-(s - τ) / 2) = 2 := by
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  have heq : (fun s : ℝ => Real.exp (-(s - τ) / 2))
      = fun s : ℝ => Real.exp (τ / 2) * Real.exp ((-1 / 2 : ℝ) * s) := by
    funext s
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq, integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0) τ]
  have hE : Real.exp ((-1 / 2 : ℝ) * τ) = Real.exp (-(τ / 2)) := by
    congr 1
    ring
  rw [hE]
  have hval : -Real.exp (-(τ / 2)) / (-1 / 2 : ℝ) = 2 * Real.exp (-(τ / 2)) := by
    ring
  rw [hval]
  have h1 : Real.exp (τ / 2) * Real.exp (-(τ / 2)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc Real.exp (τ / 2) * (2 * Real.exp (-(τ / 2)))
      = 2 * (Real.exp (τ / 2) * Real.exp (-(τ / 2))) := by ring
    _ = 2 * 1 := by rw [h1]
    _ = 2 := by ring

/-! ### The clock comparison -/

theorem tail_le_two_mul (C : Work.FTS.Physical.PhysClock) {τ : ℝ} (hτ : 0 ≤ τ) : C.T - C.t τ ≤ 2 * C.A τ := by
  rw [tail_eq_integral C hτ]
  have hIntA : IntegrableOn C.A (Set.Ici τ) :=
    (integrableOn_A_local C).mono_set (Set.Ici_subset_Ici.mpr hτ)
  have hIntg : IntegrableOn (fun s : ℝ => C.A τ * Real.exp (-(s - τ) / 2)) (Set.Ici τ) :=
    (integrableOn_exp_shift τ).const_mul (C.A τ)
  have hmono : ∫ s in Set.Ici τ, C.A s
      ≤ ∫ s in Set.Ici τ, C.A τ * Real.exp (-(s - τ) / 2) :=
    setIntegral_mono_on hIntA hIntg measurableSet_Ici (fun s hs => A_le_exp_mul C hτ hs)
  calc ∫ s in Set.Ici τ, C.A s
      ≤ ∫ s in Set.Ici τ, C.A τ * Real.exp (-(s - τ) / 2) := hmono
    _ = C.A τ * ∫ s in Set.Ici τ, Real.exp (-(s - τ) / 2) := by rw [integral_const_mul]
    _ = C.A τ * 2 := by rw [integral_exp_shift τ]
    _ = 2 * C.A τ := by ring

end Work.FTS.Physical.Clock
