import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.GalBasis.cc.Defs
import Submission.Work.Elliptic.L12densFacts
import Submission.Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.L12

open scoped Real Topology
open MeasureTheory Set Filter

/-- namespace `Work.FTS.StrongEps.L12`, declaration name `WlamCS`.
Cauchy–Schwarz in the radial variable against the weight `Work.FTS.GalBasis.cc.Wlam s = s/(1+s)²`:
for `A ⊆ (0,∞)` and `H : ℝ → ℝ` with `H ≥ 0` and integrable on `A`,
`∫_{s∈A} Wlam s · √(H s) ≤ √(∫_{s∈A} (Wlam s)²) · √(∫_{s∈A} H s)`.
This is the plain `L²`-Cauchy–Schwarz for the two measurable functions `Wlam` (continuous) and
`√H` (measurable because `H` is integrable), with `(√H)² = H`; no weight bound (of the kind used by
`Work.FTS.StrongEps.Wlam_mul_le_sqrt`, the `A = Ioi z` instance) is needed.  The needed finiteness is
`∫_{Ioi 0} (Wlam s)² ≤ 2` (`Wlam s² ≤ 1/(1+s)²` and `∫_{Ioi 0} 1/(1+s)² = 1`). -/
theorem WlamCS {H : ℝ → ℝ} {A : Set ℝ}
    (hA : A ⊆ Set.Ioi 0) (hHnn : ∀ s, 0 ≤ H s) (hHint : MeasureTheory.IntegrableOn H A) :
    ∫ s in A, Work.FTS.GalBasis.cc.Wlam s * Real.sqrt (H s)
      ≤ Real.sqrt (∫ s in A, Work.FTS.GalBasis.cc.Wlam s ^ 2) * Real.sqrt (∫ s in A, H s) := by
  -- The squared weight is integrable on `(0,∞)` (`Work.Elliptic.psi_sq_integrable_aux`) and
  -- hence on the smaller set `A ⊆ (0,∞)`.
  have hWlam2Ioi : MeasureTheory.IntegrableOn (fun s => Work.FTS.GalBasis.cc.Wlam s ^ 2)
      (Set.Ioi 0) := by
    simpa only [Work.FTS.GalBasis.cc.Wlam] using Work.Elliptic.psi_sq_integrable_aux
  have hWlam2A : MeasureTheory.IntegrableOn (fun s => Work.FTS.GalBasis.cc.Wlam s ^ 2) A :=
    hWlam2Ioi.mono_set hA
  -- Measurability: `Wlam` is continuous on `(0,∞)`, and `volume.restrict A ≤ volume.restrict (0,∞)`.
  have hWlam_aesm : AEStronglyMeasurable Work.FTS.GalBasis.cc.Wlam (volume.restrict A) := by
    have h0 : AEStronglyMeasurable Work.FTS.GalBasis.cc.Wlam (volume.restrict (Set.Ioi 0)) := by
      change AEStronglyMeasurable (fun s : ℝ => s / (1 + s) ^ 2) (volume.restrict (Set.Ioi 0))
      refine ContinuousOn.aestronglyMeasurable (μ := volume)
        (continuousOn_id.div ((continuousOn_const.add continuousOn_id).pow 2) ?_) measurableSet_Ioi
      intro s hs
      have hne : (1 : ℝ) + s ≠ 0 := by
        simp only [Set.mem_Ioi] at hs
        linarith
      exact pow_ne_zero 2 hne
    exact h0.mono_measure (MeasureTheory.Measure.restrict_mono hA le_rfl)
  have hS_aesm : AEStronglyMeasurable (fun s => Real.sqrt (H s)) (volume.restrict A) :=
    (hHint.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable
  -- `(√H)² = H`, so `√H` is square-integrable on `A`.
  have hS2A : MeasureTheory.IntegrableOn (fun s => Real.sqrt (H s) ^ 2) A :=
    hHint.congr (Filter.Eventually.of_forall fun s => (Real.sq_sqrt (hHnn s)).symm)
  -- Both factors are `L²` on `A`.
  have hWlam_memLp : MemLp Work.FTS.GalBasis.cc.Wlam 2 (volume.restrict A) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hWlam_aesm).mpr hWlam2A
  have hS_memLp : MemLp (fun s => Real.sqrt (H s)) 2 (volume.restrict A) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hS_aesm).mpr hS2A
  -- Cauchy–Schwarz.
  have hcs := Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt
    (u := Work.FTS.GalBasis.cc.Wlam) (v := fun s => Real.sqrt (H s)) (s := A)
    hWlam_memLp hS_memLp
  -- The integrand is nonnegative a.e. on `A` (it is nonnegative on `A`, and `Wlam s < 0`
  -- forces `s < 0`, a null set for `volume.restrict A`).
  have hnn : 0 ≤ ∫ s in A, Work.FTS.GalBasis.cc.Wlam s * Real.sqrt (H s) := by
    refine MeasureTheory.integral_nonneg_of_ae ?_
    show ∀ᵐ s ∂(volume.restrict A),
      0 ≤ Work.FTS.GalBasis.cc.Wlam s * Real.sqrt (H s)
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null (t := Set.Iio 0) ?_ ?_
    · intro s hs
      have hs' : ¬ (0 ≤ Work.FTS.GalBasis.cc.Wlam s) := fun h0 =>
        hs (mul_nonneg h0 (Real.sqrt_nonneg (H s)))
      show s < 0
      by_contra h
      push Not at h
      exact hs' (Work.FTS.GalBasis.cc.Wlam_nonneg h)
    · rw [MeasureTheory.Measure.restrict_apply measurableSet_Iio]
      refine measure_mono_null (t := (∅ : Set ℝ)) ?_ (by simp)
      intro x hx
      exact absurd (hA hx.2) (by
        simp only [Set.mem_Ioi]
        exact not_lt.mpr (le_of_lt hx.1))
  have hsq : ∫ s in A, Real.sqrt (H s) ^ 2 = ∫ s in A, H s :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => Real.sq_sqrt (hHnn s))
  calc ∫ s in A, Work.FTS.GalBasis.cc.Wlam s * Real.sqrt (H s)
      = |∫ s in A, Work.FTS.GalBasis.cc.Wlam s * Real.sqrt (H s)| :=
        (abs_of_nonneg hnn).symm
    _ ≤ Real.sqrt (∫ s in A, Work.FTS.GalBasis.cc.Wlam s ^ 2)
          * Real.sqrt (∫ s in A, Real.sqrt (H s) ^ 2) := hcs
    _ = Real.sqrt (∫ s in A, Work.FTS.GalBasis.cc.Wlam s ^ 2)
          * Real.sqrt (∫ s in A, H s) := by rw [hsq]

end Work.FTS.StrongEps.L12
