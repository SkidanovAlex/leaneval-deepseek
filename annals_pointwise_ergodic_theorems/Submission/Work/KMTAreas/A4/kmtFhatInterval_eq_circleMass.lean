import Mathlib
import Submission.Work.KMTAreas.A4.lip2Projection

/-!
# The circle mass of the KMT Fourier transform equals its interval mass

For an absolutely summable `g : ℤ → ℂ` and a measurable `S : Set (ℝ/ℤ)`, the `L²` mass of the
Fourier transform of `g` over `S` on the frequency circle equals the Lebesgue mass over the
interval `(0,1]` of the pull-back of `S` under the parametrisation `t ↦ (t : ℝ/ℤ)`.

The two Fourier transforms involved are

* `Work.Analysis.InverseTheory.ZFourier g ξ = ∑'_x g x · e(-x ξ)` on the frequency circle
  `Work.Analysis.InverseTheory.FreqCircle = AddCircle 1`, and
* `Work.A3.kmtFhat g t = ∑'_x g x · e^{-2πi x t}` as a function on `ℝ`,

which agree under the parametrisation (`ZFourier_coe_eq_kmtFhat`).  The measure-theoretic input is
Mathlib's `AddCircle.integral_preimage`, which computes the integral over `AddCircle T` as the
integral over the fundamental interval `(t, t + T]`, together with
`AddCircle.volume_eq_smul_haarAddCircle` identifying the total mass `1` Haar measure
`AddCircle.haarAddCircle` with `volume` on `AddCircle 1`.
-/

set_option autoImplicit false

open MeasureTheory

namespace Work.KMTAreas.A4

noncomputable section

/-- The two Fourier transforms agree under the parametrisation of the frequency circle by `ℝ`:
`𝓕_ℤ g (t : ℝ/ℤ) = kmtFhat g t` for every `t : ℝ`. -/
theorem ZFourier_coe_eq_kmtFhat (g : ℤ → ℂ) (t : ℝ) :
    Work.Analysis.InverseTheory.ZFourier g
        ((t : ℝ) : Work.Analysis.InverseTheory.FreqCircle) = Work.A3.kmtFhat g t := by
  rw [Work.Analysis.InverseTheory.ZFourier, Work.A3.kmtFhat]
  refine tsum_congr fun x => ?_
  congr 1
  rw [fourier_coe_apply]
  push_cast
  ring_nf

/-- The total mass `1` Haar measure on `AddCircle 1` is the standard measure `volume`. -/
theorem volume_addCircle_one : (volume : Measure (AddCircle (1 : ℝ))) = AddCircle.haarAddCircle := by
  rw [AddCircle.volume_eq_smul_haarAddCircle (T := 1)]
  simp

theorem kmtFhatInterval_eq_circleMass (g : ℤ → ℂ) (hg : Summable fun x : ℤ => ‖g x‖)
    {S : Set Work.Analysis.InverseTheory.FreqCircle} (hS : MeasurableSet S) :
    (∫ ξ in S, ‖Work.Analysis.InverseTheory.ZFourier g ξ‖ ^ 2 ∂AddCircle.haarAddCircle)
      = ∫ t in (0 : ℝ)..1,
          (Set.indicator {t : ℝ | ((t : ℝ) : Work.Analysis.InverseTheory.FreqCircle) ∈ S}
            (fun t : ℝ => ‖Work.A3.kmtFhat g t‖ ^ 2)) t := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [← MeasureTheory.integral_indicator (μ := AddCircle.haarAddCircle) hS]
  rw [← volume_addCircle_one]
  rw [← AddCircle.integral_preimage (T := (1 : ℝ)) (0 : ℝ)
      (fun ξ => Set.indicator S
        (fun ξ : Work.Analysis.InverseTheory.FreqCircle =>
          ‖Work.Analysis.InverseTheory.ZFourier g ξ‖ ^ 2) ξ)]
  simp only [zero_add]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  change Set.indicator S
        (fun ξ : Work.Analysis.InverseTheory.FreqCircle =>
          ‖Work.Analysis.InverseTheory.ZFourier g ξ‖ ^ 2) ((t : ℝ) : Work.Analysis.InverseTheory.FreqCircle)
      = Set.indicator {t : ℝ | ((t : ℝ) : Work.Analysis.InverseTheory.FreqCircle) ∈ S}
          (fun t : ℝ => ‖Work.A3.kmtFhat g t‖ ^ 2) t
  by_cases ht : ((t : ℝ) : Work.Analysis.InverseTheory.FreqCircle) ∈ S
  · have ht' : t ∈ {t : ℝ | ((t : ℝ) : Work.Analysis.InverseTheory.FreqCircle) ∈ S} := ht
    rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht', ZFourier_coe_eq_kmtFhat]
  · have ht' : t ∉ {t : ℝ | ((t : ℝ) : Work.Analysis.InverseTheory.FreqCircle) ∈ S} := ht
    rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht']

end

end Work.KMTAreas.A4
