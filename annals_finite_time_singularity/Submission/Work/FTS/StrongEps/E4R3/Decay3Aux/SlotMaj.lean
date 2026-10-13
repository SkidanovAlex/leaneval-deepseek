/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/E4R3/Decay3Aux/SlotMaj.lean` — the majorant of the low slots of a
projected slice

Given a profile `f` which is `C⁴` on the open quadrant, honestly in `ℋ⁴`, in the small ball
`Xn α f ≤ C₀α²` and vanishing off the open quadrant (both true for the projected slices
`f = Pz (J_ε g(τ))` of the `ε`-scheme), this module produces a **single** majorant

    `Maj z = min 1 (max (C·C₀α²·z√z/(1+z)²) 0)`

with `0 ≤ Maj`, `Maj ≤ 1`, `IntegrableOn (Maj · / ·) (0,∞)` and `SlotMaj 1 Maj f`, i.e. the
`EpsDecay` slot clause, uniformly in `ε`, in the fake time `τ` and in the solution `g`.

The two inputs are `slot_crude` (the rate `min z 1` bound, used to cap `Maj` at `1`) and
`slot_tail` (the rate `z^{-1/2}` bound, used for the domination), both from
`Decay3Aux/SlotBound.lean`; the `1/z`-integrability is
`Decay3Aux/integrableOn_majProfile`.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E4R3.Decay3Aux.SlotBound
import Submission.Work.FTS.StrongEps.E4R3.Decay3Aux.integrableOn_majProfile
import Submission.Work.FTS.StrongEps.EpsE4Thr.slotMaj_of_offquadrant
import Submission.Work.FTS.StrongEps.E4R3.Chapters

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **The slot majorant of a small-`ℋ⁴` projected slice.** -/
theorem slotMaj_of_ball {α C₀ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hC₀ : 0 ≤ C₀)
    (hsmall : Real.sqrt (((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α - 1))) * 40)
      * (C₀ * α ^ 2) ≤ 1)
    {f : Fn} (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f)
    (hball : Work.FTS.Nonlin.Xn α f ≤ C₀ * α ^ 2)
    (hoff : ∀ z θ : ℝ, θ ∉ Set.Ioo 0 (Real.pi / 2) → f z θ = 0) :
    ∃ Maj : ℝ → ℝ, (∀ z, 0 ≤ Maj z) ∧ (∀ z, Maj z ≤ 1) ∧
      MeasureTheory.IntegrableOn (fun z => Maj z / z) (Set.Ioi 0) ∧
      Work.FTS.StrongEps.SlotMaj 1 Maj f := by
  obtain ⟨Ct, hCt0, hCt⟩ := slot_tail (α := α) hα hα1
  set D : ℝ := Real.sqrt Ct * (C₀ * α ^ 2) with hDdef
  have hD0 : 0 ≤ D := by rw [hDdef]; positivity
  set P : ℝ → ℝ := fun z => z * Real.sqrt z / (1 + z) ^ 2 with hPdef
  have hPnonneg : ∀ z : ℝ, 0 ≤ P z := by
    intro z
    by_cases hz : 0 ≤ z
    · rw [hPdef]
      exact div_nonneg (mul_nonneg hz (Real.sqrt_nonneg z)) (sq_nonneg _)
    · have hs : Real.sqrt z = 0 := Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hz)
      rw [hPdef]
      show (0 : ℝ) ≤ z * Real.sqrt z / (1 + z) ^ 2
      rw [hs]
      simp
  have hsqrt_id : ∀ z : ℝ, 0 < z →
      Real.sqrt (z ^ 3 / (1 + z) ^ 4) = P z := by
    intro z hz
    rw [hPdef]
    have h1 : Real.sqrt (z ^ 3) = z * Real.sqrt z := by
      rw [show z ^ 3 = z ^ 2 * z by ring, Real.sqrt_mul (by positivity), Real.sqrt_sq hz.le]
    have h2 : Real.sqrt ((1 + z) ^ 4) = (1 + z) ^ 2 := by
      rw [show (1 + z) ^ 4 = ((1 + z) ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    rw [Real.sqrt_div (by positivity), h1, h2]
  set Maj : ℝ → ℝ := fun z => min 1 (D * P z) with hMajdef
  have hMaj_nonneg : ∀ z, 0 ≤ Maj z :=
    fun z => le_min zero_le_one (mul_nonneg hD0 (hPnonneg z))
  have hMaj_le : ∀ z, Maj z ≤ 1 := fun z => min_le_left _ _
  have hcontP : ContinuousOn (fun z : ℝ => D * P z) (Set.Ioi 0) := by
    rw [hPdef]
    refine ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.div ?_ ?_ ?_
    · exact continuousOn_id.mul Real.continuous_sqrt.continuousOn
    · exact (continuousOn_const.add continuousOn_id).pow 2
    · intro z hz
      have h1z : (0 : ℝ) < 1 + z := by linarith [show (0 : ℝ) < z from hz]
      exact pow_ne_zero 2 (ne_of_gt h1z)
  refine ⟨Maj, hMaj_nonneg, hMaj_le, ?_, ?_⟩
  · -- `Maj · / ·` is `1/z`-integrable on `(0,∞)`
    refine (Work.FTS.StrongEps.E4R3.Decay3Aux.integrableOn_majProfile D).mono' ?_ ?_
    · have hM : ContinuousOn (fun z : ℝ => min (1 : ℝ) (D * P z)) (Set.Ioi 0) :=
        fun z hz => continuousWithinAt_const.min (hcontP z hz)
      have hcont : ContinuousOn (fun z : ℝ => Maj z / z) (Set.Ioi 0) := by
        rw [hMajdef]
        exact hM.div continuousOn_id (fun z hz => ne_of_gt hz)
      exact hcont.aestronglyMeasurable measurableSet_Ioi
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
      rw [Real.norm_of_nonneg (div_nonneg (hMaj_nonneg z) hz.le)]
      have hDP : 0 ≤ D * P z := mul_nonneg hD0 (hPnonneg z)
      have h1 : Maj z ≤ D * P z := by
        change min 1 (D * P z) ≤ D * P z
        exact min_le_right _ _
      have h2 : D * P z / z = D * (Real.sqrt z / (1 + z) ^ 2) := by
        rw [hPdef, div_eq_iff (ne_of_gt hz)]
        ring
      calc Maj z / z ≤ D * P z / z := div_le_div_of_nonneg_right h1 hz.le
        _ = D * (Real.sqrt z / (1 + z) ^ 2) := h2
  · -- the slot clause
    refine Work.FTS.StrongEps.EpsE4Thr.slotMaj_of_offquadrant (k := 1) hMaj_nonneg hoff ?_
    intro z hz θ hθ0 hθ1 j i hji
    have hPz0 : 0 ≤ P z := hPnonneg z
    by_cases hcase : D * P z ≤ 1
    · -- the tail bound does the job
      have hMajeq : Maj z = D * P z := by
        change min 1 (D * P z) = D * P z
        exact min_eq_right hcase
      rw [hMajeq]
      have hsq := hCt f h4 hmem j i hji z θ hz hθ0 hθ1
      have h1 : |Work.Spaces.mixed j i f z θ|
          ≤ Real.sqrt (Ct * Work.Spaces.HkSq α 4 f * (z ^ 3 / (1 + z) ^ 4)) := by
        rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt hsq
      have h2 : Real.sqrt (Ct * Work.Spaces.HkSq α 4 f * (z ^ 3 / (1 + z) ^ 4))
          = Real.sqrt Ct * Work.Spaces.HkNorm α 4 f * P z := by
        rw [Real.sqrt_mul (mul_nonneg hCt0 (Work.Spaces.HkSq_nonneg α 4 f)),
          Real.sqrt_mul hCt0, hsqrt_id z hz]
        rfl
      have h3 : Real.sqrt Ct * Work.Spaces.HkNorm α 4 f * P z ≤ D * P z := by
        rw [hDdef]
        have h := mul_le_mul_of_nonneg_right hball hPz0
        calc Real.sqrt Ct * Work.Spaces.HkNorm α 4 f * P z
            = Real.sqrt Ct * (Work.Spaces.HkNorm α 4 f * P z) := by ring
          _ ≤ Real.sqrt Ct * ((C₀ * α ^ 2) * P z) :=
              mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg Ct)
          _ = Real.sqrt Ct * (C₀ * α ^ 2) * P z := by ring
      calc |Work.Spaces.mixed j i f z θ|
          ≤ Real.sqrt (Ct * Work.Spaces.HkSq α 4 f * (z ^ 3 / (1 + z) ^ 4)) := h1
        _ = Real.sqrt Ct * Work.Spaces.HkNorm α 4 f * P z := h2
        _ ≤ D * P z := h3
    · -- the crude bound caps the majorant
      have hcase' : 1 < D * P z := lt_of_not_ge hcase
      have hMajeq : Maj z = 1 := by
        change min 1 (D * P z) = 1
        exact min_eq_left hcase'.le
      rw [hMajeq]
      have hCpt0 : 0 ≤ Real.sqrt (((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α - 1))) * 40) :=
        Real.sqrt_nonneg _
      have hcr := slot_crude (α := α) hα hα1 (f := f) (j := j) (i := i) (by omega) hz hθ0 hθ1 h4 hmem
      have hnorm : Work.Spaces.HkNorm α 4 f ≤ C₀ * α ^ 2 := hball
      calc |Work.Spaces.mixed j i f z θ|
          ≤ Real.sqrt (((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α - 1))) * 40)
              * min z 1 * Work.Spaces.HkNorm α 4 f := hcr
        _ ≤ Real.sqrt (((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α - 1))) * 40)
              * 1 * (C₀ * α ^ 2) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left (min_le_right z 1) hCpt0) hnorm
              (Work.Spaces.HkNorm_nonneg α 4 f) (by positivity)
        _ = Real.sqrt (((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α - 1))) * 40)
              * (C₀ * α ^ 2) := by ring
        _ ≤ 1 := hsmall

end Work.FTS.StrongEps.E4R3
