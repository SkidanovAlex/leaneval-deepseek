import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB3.CS.fourierInv_fourier_eq_zero_of_not_integrable
import Submission.Work.BoseFixB3.CS.lowMult_eq_fourierInv_re
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.QBop.lowMult_sq_le_of_nonpos`

The pointwise bound on the complementary part of the low-momentum multiplier at a
*degenerate* cut-off `κ ≤ 0`:

  `(ψ b − lowMult fc κ ℓ ψ b)² ≤ 4 (ψ b)²`

for every `b` which is either in `interior (acube ℓ)` or outside `acube ℓ` — i.e. at
every point where the box extension `1_Λ ψ` is *decided* (`= ψ b` inside, `= 0`
outside), the boundary being excluded.

## Proof

Since `κ ≤ 0`, the symbol `p ↦ fc.f (‖p‖/κ)` is identically `1` (`LowCut.one`,
because `‖p‖/κ ≤ 0 ≤ 1`), so the multiplier collapses to the full inverse Fourier
transform of the box extension,

  `lowMult fc κ ℓ ψ b = (𝓕⁻ (𝓕 (1_Λ ψ)) b).re`
  (`Work.BoseFixB3.CS.lowMult_eq_fourierInv_re`).

Two cases.

* If `𝓕 (1_Λ ψ) ∉ L¹`, the inverse transform is the junk value `0`
  (`Work.BoseFixB3.CS.fourierInv_fourier_eq_zero_of_not_integrable`) and the claim
  reads `ψ b² ≤ 4 ψ b²`.
* If `𝓕 (1_Λ ψ) ∈ L¹`, then `1_Λ ψ ∈ L¹` (continuous on the compact cube, times the
  measurable indicator) and Fourier inversion
  (`MeasureTheory.Integrable.fourierInv_fourier_eq`) holds at every point of
  continuity of `1_Λ ψ`; `b` is such a point in both cases of the hypothesis. So
  `lowMult fc κ ℓ ψ b = (1_Λ ψ) b`, which is `ψ b` for `b ∈ interior (acube ℓ)` and
  `0` for `b ∉ acube ℓ`. The claim then reads `0 ≤ 4 ψ b²`, respectively
  `ψ b² ≤ 4 ψ b²`.

Note that `b` must be off the *frontier* of the cube: on the boundary of `acube ℓ`
the extension `1_Λ ψ` is discontinuous and Fourier inversion (hence the identity
`lowMult = ψ b` or `= 0`) can genuinely fail.
-/

noncomputable section

open MeasureTheory Filter
open scoped Real FourierTransform Topology

namespace Work.BoseFixB3.QBop

set_option autoImplicit false

theorem lowMult_sq_le_of_nonpos {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ} (hκ : κ ≤ 0) (hℓ : 0 < ℓ)
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : Continuous ψ) {b : EuclideanSpace ℝ (Fin 3)}
    (hb : b ∈ interior (Submission.BoseGases.acube ℓ) ∨ b ∉ Submission.BoseGases.acube ℓ) :
    (ψ b - Work.BoseBoxFix.lowMult fc κ ℓ ψ b) ^ 2 ≤ 4 * (ψ b) ^ 2 := by
  classical
  set g : EuclideanSpace ℝ (Fin 3) → ℂ :=
    fun z => (((Submission.BoseGases.acube ℓ).indicator ψ z : ℝ) : ℂ) with hg
  have hkey : Work.BoseBoxFix.lowMult fc κ ℓ ψ b = (𝓕⁻ (𝓕 g) b).re := by
    have h := Work.BoseFixB3.CS.lowMult_eq_fourierInv_re (fc := fc) (κ := κ) (ℓ := ℓ) hκ ψ b
    simpa only [hg] using h
  by_cases hint : MeasureTheory.Integrable (𝓕 g) MeasureTheory.volume
  · -- The Fourier transform of the box extension is `L¹`: Fourier inversion at `b`.
    have hψC : Continuous (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ)) :=
      Complex.continuous_ofReal.comp hψ
    have hgon : MeasureTheory.IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ))
        (Submission.BoseGases.acube ℓ) MeasureTheory.volume :=
      ContinuousOn.integrableOn_compact (Submission.BoseGases.acube_compact hℓ) hψC.continuousOn
    have hgt : MeasureTheory.Integrable g MeasureTheory.volume := by
      have heq : (Submission.BoseGases.acube ℓ).indicator
            (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ)) = g := by
        funext z
        by_cases hz : z ∈ Submission.BoseGases.acube ℓ
        · simp [hg, Set.indicator_of_mem hz]
        · simp [hg, Set.indicator_of_notMem hz]
      rw [← heq]
      exact hgon.integrable_indicator (Submission.BoseGases.acube_measurable ℓ)
    rcases hb with hbi | hbo
    · -- `b` inside the cube: the extension agrees with `ψ` near `b`.
      have hmem : ∀ᶠ z in 𝓝 b, z ∈ Submission.BoseGases.acube ℓ :=
        Filter.mem_of_superset (isOpen_interior.mem_nhds hbi) interior_subset
      have hev : g =ᶠ[𝓝 b] fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ) := by
        filter_upwards [hmem] with z hz
        simp [hg, Set.indicator_of_mem hz]
      have hca : ContinuousAt g b := (continuousAt_congr hev).mpr hψC.continuousAt
      have hgb : g b = ((ψ b : ℝ) : ℂ) := by
        simp [hg, Set.indicator_of_mem (interior_subset hbi)]
      have hval : Work.BoseBoxFix.lowMult fc κ ℓ ψ b = ψ b := by
        rw [hkey, MeasureTheory.Integrable.fourierInv_fourier_eq hgt hint hca, hgb]
        simp
      rw [hval]
      ring_nf
      positivity
    · -- `b` outside the closed cube: the extension vanishes near `b`.
      have hcompl : ∀ᶠ z in 𝓝 b, z ∉ Submission.BoseGases.acube ℓ :=
        (Submission.BoseGases.acube_isClosed ℓ).isOpen_compl.mem_nhds hbo
      have hev0 : g =ᶠ[𝓝 b] fun _ : EuclideanSpace ℝ (Fin 3) => (0 : ℂ) := by
        filter_upwards [hcompl] with z hz
        simp [hg, Set.indicator_of_notMem hz]
      have hca : ContinuousAt g b := continuousAt_const.congr hev0.symm
      have hgb : g b = 0 := by
        simp [hg, Set.indicator_of_notMem hbo]
      have hval : Work.BoseBoxFix.lowMult fc κ ℓ ψ b = 0 := by
        rw [hkey, MeasureTheory.Integrable.fourierInv_fourier_eq hgt hint hca, hgb]
        simp
      rw [hval]
      nlinarith [sq_nonneg (ψ b)]
  · -- The Fourier transform is not `L¹`: the inverse transform is the junk value `0`.
    have hval : Work.BoseBoxFix.lowMult fc κ ℓ ψ b = 0 := by
      rw [hkey, Work.BoseFixB3.CS.fourierInv_fourier_eq_zero_of_not_integrable hint b]
      simp
    rw [hval]
    nlinarith [sq_nonneg (ψ b)]

end Work.BoseFixB3.QBop
