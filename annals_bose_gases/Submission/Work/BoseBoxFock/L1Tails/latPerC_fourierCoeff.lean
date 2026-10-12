import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.L1Tails.DefsC
import Submission.Work.BoseBoxFock.latTiling_integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.L1Tails

open MeasureTheory
open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000

/-- **The complex periodisation on the cube is the finite sum over `latFinSet ℓ R`.**

This is the `latPerC`-analogue of `Work.BoseBoxFock.LatFourier.latPer_eq_sum_finset`: if `Φ`
vanishes outside the ball of radius `R`, then on the closed cube only the translates
`z + ℓ • latVec m` with `m ∈ latFinSet ℓ R` can contribute to the periodisation. -/
theorem latPerC_eq_sum_finset {ℓ R : ℝ} (hℓ : 0 < ℓ) {Φ : E3 → ℂ}
    (hΦs : ∀ x, R < ‖x‖ → Φ x = 0) {z : E3} (hz : z ∈ Work.BoseBoxFock.LatFourier.latBox ℓ) :
    latPerC ℓ Φ z
      = ∑ m ∈ Work.BoseBoxFock.LatFourier.latFinSet ℓ R, Φ (z + ℓ • latVec m) := by
  rw [latPerC]
  refine tsum_eq_sum (s := Work.BoseBoxFock.LatFourier.latFinSet ℓ R) (fun m hm => ?_)
  have hnot : (R + Real.sqrt 3 * ℓ) / ℓ < ‖latVec m‖ := by
    rw [← not_le]
    intro hc
    exact hm ((Work.BoseBoxFock.LatFourier.mem_latFinSet).mpr hc)
  have hzb := Work.BoseBoxFock.LatFourier.latBox_subset_closedBall hℓ.le hz
  have hgt : R < ‖z + ℓ • latVec m‖ := by
    have h2 : ℓ * ‖latVec m‖ ≤ ‖z + ℓ • latVec m‖ + ‖z‖ := by
      have h := norm_sub_le (z + ℓ • latVec m) z
      rw [add_sub_cancel_left] at h
      rwa [Work.BoseBoxFock.LatFourier.latVec_norm_smul ℓ hℓ.le m] at h
    have h4 : R + Real.sqrt 3 * ℓ < ℓ * ‖latVec m‖ := by
      rw [div_lt_iff₀ hℓ] at hnot
      linarith
    linarith
  exact hΦs _ hgt

/-- The lattice Fourier coefficient of the complex periodisation `latPerC ℓ Φ` equals the sample
`kinFT Φ (κ_n)` (the complex twin of the already proved real-valued coefficient identity
`Work.BoseBoxFock.latPer_fourierCoeff`, whose hypotheses are the same except for the `ℂ`-vs-`ℝ`
codomain).  Route: split `Φ = (fun x => (Φ x).re) + I • (fun x => (Φ x).im)`, apply the real-valued
identity to the two parts (discharging its tiling hypothesis from
`Work.BoseBoxFock.latTiling_integral`), and add, or mirror its proof directly with
`Work.BoseBoxFock.LatFourier.latPer_eq_sum_finset` and the lattice invariance of the character
(`Work.BoseBoxFock.LatFourier.exp_neg_I_inner_add_latVec`). -/
theorem latPerC_fourierCoeff {ℓ R : ℝ} (hℓ : 0 < ℓ) {Φ : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hΦm : MeasureTheory.AEStronglyMeasurable Φ MeasureTheory.volume)
    (hΦb : ∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) (hΦs : ∀ x, R < ‖x‖ → Φ x = 0) (n : Fin 3 → ℤ) :
    (∫ z in Work.BoseBoxFock.LatFourier.latCell ℓ,
        Work.BoseBoxFock.L1Tails.latPerC ℓ Φ z
          * Complex.exp (-(Complex.I * ((inner ℝ (Work.BoseBoxFock.kappaL ℓ n) z : ℝ) : ℂ))))
      = Submission.BoseGases.kinFT Φ (Work.BoseBoxFock.kappaL ℓ n) := by
  obtain ⟨C, hC⟩ := hΦb
  -- The bounded, compactly supported test function whose periodisation is `latPerC ℓ Φ`.
  let g : E3 → ℂ := fun u =>
    Complex.exp (-(Complex.I * ((inner ℝ (kappaL ℓ n) u : ℝ) : ℂ))) * Φ u
  -- The character is invariant under the lattice translations.
  have hexp : ∀ (m : Fin 3 → ℤ) (z : E3),
      Complex.exp (-(Complex.I * ((inner ℝ (kappaL ℓ n) (z + ℓ • latVec m) : ℝ) : ℂ)))
        = Complex.exp (-(Complex.I * ((inner ℝ (kappaL ℓ n) z : ℝ) : ℂ))) :=
    fun m z => Work.BoseBoxFock.LatFourier.exp_neg_I_inner_add_latVec (ne_of_gt hℓ) n m z
  -- The exponential factor has modulus one.
  have hexp1 : ∀ t : ℝ, ‖Complex.exp (-(Complex.I * ((t : ℝ) : ℂ)))‖ = 1 := by
    intro t
    have h : -(Complex.I * ((t : ℝ) : ℂ)) = ((-t : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [h, Complex.norm_exp_ofReal_mul_I]
  have hgcont : Continuous (fun u : E3 =>
      Complex.exp (-(Complex.I * ((inner ℝ (kappaL ℓ n) u : ℝ) : ℂ)))) := by
    fun_prop
  have hgaesm : AEStronglyMeasurable g volume := by
    show AEStronglyMeasurable (fun u : E3 =>
      Complex.exp (-(Complex.I * ((inner ℝ (kappaL ℓ n) u : ℝ) : ℂ))) * Φ u) volume
    exact hgcont.aestronglyMeasurable.mul hΦm
  have hgbd : ∃ D : ℝ, ∀ u, ‖g u‖ ≤ D := by
    refine ⟨max C 0, fun u => ?_⟩
    have h1 : ‖g u‖ = ‖Φ u‖ := by
      show ‖Complex.exp (-(Complex.I * ((inner ℝ (kappaL ℓ n) u : ℝ) : ℂ))) * Φ u‖
        = ‖Φ u‖
      rw [norm_mul, hexp1, one_mul]
    rw [h1]
    exact le_trans (hC u) (le_max_left C 0)
  have hgsupp : ∀ u, max R 0 < ‖u‖ → g u = 0 := by
    intro u hu
    have hΦu : Φ u = 0 := hΦs u (lt_of_le_of_lt (le_max_left R 0) hu)
    show Complex.exp (-(Complex.I * ((inner ℝ (kappaL ℓ n) u : ℝ) : ℂ))) * Φ u = 0
    rw [hΦu, mul_zero]
  have hgint : Integrable g volume :=
    Work.BoseBoxFock.LatFourier.integrable_of_bdd_of_supp (ρ := max R 0) (le_max_right R 0)
      hgaesm hgbd hgsupp
  -- Off the finite set `latFinSet ℓ R` the function vanishes on the whole cell.
  have hvan : ∀ m : Fin 3 → ℤ, m ∉ Work.BoseBoxFock.LatFourier.latFinSet ℓ R →
      ∀ z ∈ Work.BoseBoxFock.LatFourier.latCell ℓ, Φ (z + ℓ • latVec m) = 0 := by
    intro m hm z hz
    have hnot : (R + Real.sqrt 3 * ℓ) / ℓ < ‖latVec m‖ := by
      rw [← not_le]; intro hc; exact hm (Work.BoseBoxFock.LatFourier.mem_latFinSet.mpr hc)
    have hzb := Work.BoseBoxFock.LatFourier.latBox_subset_closedBall hℓ.le
      (Work.BoseBoxFock.LatFourier.latCell_subset_latBox hz)
    have h2 : ℓ * ‖latVec m‖ ≤ ‖z + ℓ • latVec m‖ + ‖z‖ := by
      have h := norm_sub_le (z + ℓ • latVec m) z
      rw [add_sub_cancel_left] at h
      rwa [Work.BoseBoxFock.LatFourier.latVec_norm_smul ℓ hℓ.le m] at h
    have h4 : R + Real.sqrt 3 * ℓ < ℓ * ‖latVec m‖ := by
      rw [div_lt_iff₀ hℓ] at hnot
      linarith
    exact hΦs _ (by linarith)
  -- The pointwise identity on the cell: `latPerC` becomes the finite sum over `latFinSet ℓ R`.
  have hpoint : ∀ z ∈ Work.BoseBoxFock.LatFourier.latCell ℓ,
      Work.BoseBoxFock.L1Tails.latPerC ℓ Φ z
          * Complex.exp (-(Complex.I * ((inner ℝ (kappaL ℓ n) z : ℝ) : ℂ)))
        = ∑ m ∈ Work.BoseBoxFock.LatFourier.latFinSet ℓ R, g (z + ℓ • latVec m) := by
    intro z hz
    have hzbox := Work.BoseBoxFock.LatFourier.latCell_subset_latBox hz
    calc Work.BoseBoxFock.L1Tails.latPerC ℓ Φ z
            * Complex.exp (-(Complex.I * ((inner ℝ (kappaL ℓ n) z : ℝ) : ℂ)))
        = (∑ m ∈ Work.BoseBoxFock.LatFourier.latFinSet ℓ R, Φ (z + ℓ • latVec m))
            * Complex.exp (-(Complex.I * ((inner ℝ (kappaL ℓ n) z : ℝ) : ℂ))) := by
          rw [latPerC_eq_sum_finset (R := R) hℓ hΦs hzbox]
      _ = ∑ m ∈ Work.BoseBoxFock.LatFourier.latFinSet ℓ R, Φ (z + ℓ • latVec m)
            * Complex.exp (-(Complex.I * ((inner ℝ (kappaL ℓ n) z : ℝ) : ℂ))) :=
          Finset.sum_mul _ _ _
      _ = ∑ m ∈ Work.BoseBoxFock.LatFourier.latFinSet ℓ R, g (z + ℓ • latVec m) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          show Φ (z + ℓ • latVec m)
              * Complex.exp (-(Complex.I * ((inner ℝ (kappaL ℓ n) z : ℝ) : ℂ)))
            = Complex.exp (-(Complex.I * ((inner ℝ (kappaL ℓ n) (z + ℓ • latVec m) : ℝ) : ℂ)))
              * Φ (z + ℓ • latVec m)
          rw [← hexp m z, mul_comm]
  have hstep1 : ∫ z in Work.BoseBoxFock.LatFourier.latCell ℓ,
        Work.BoseBoxFock.L1Tails.latPerC ℓ Φ z
          * Complex.exp (-(Complex.I * ((inner ℝ (kappaL ℓ n) z : ℝ) : ℂ)))
      = ∫ z in Work.BoseBoxFock.LatFourier.latCell ℓ,
          ∑ m ∈ Work.BoseBoxFock.LatFourier.latFinSet ℓ R, g (z + ℓ • latVec m) :=
    MeasureTheory.setIntegral_congr_fun (μ := volume)
      (Work.BoseBoxFock.LatFourier.measurableSet_latCell ℓ) hpoint
  have hstep2 : ∫ z in Work.BoseBoxFock.LatFourier.latCell ℓ,
        (∑ m ∈ Work.BoseBoxFock.LatFourier.latFinSet ℓ R, g (z + ℓ • latVec m))
      = ∑ m ∈ Work.BoseBoxFock.LatFourier.latFinSet ℓ R,
          ∫ z in Work.BoseBoxFock.LatFourier.latCell ℓ, g (z + ℓ • latVec m) := by
    refine MeasureTheory.integral_finsetSum _ (fun m _ => ?_)
    have hshift : Integrable (fun z : E3 => g (z + ℓ • latVec m)) volume :=
      ((MeasureTheory.measurePreserving_add_right volume (ℓ • latVec m)).integrable_comp
        hgaesm).mpr hgint
    exact hshift.integrableOn (s := Work.BoseBoxFock.LatFourier.latCell ℓ)
  have hzero : ∀ m ∉ Work.BoseBoxFock.LatFourier.latFinSet ℓ R,
      ∫ z in Work.BoseBoxFock.LatFourier.latCell ℓ, g (z + ℓ • latVec m) = 0 := by
    intro m hm
    exact MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun z hz => by
      show Complex.exp (-(Complex.I * ((inner ℝ (kappaL ℓ n) (z + ℓ • latVec m) : ℝ) : ℂ)))
        * Φ (z + ℓ • latVec m) = 0
      rw [hvan m hm z hz, mul_zero]
  have hstep3 : ∑ m ∈ Work.BoseBoxFock.LatFourier.latFinSet ℓ R,
        ∫ z in Work.BoseBoxFock.LatFourier.latCell ℓ, g (z + ℓ • latVec m)
      = ∑' m : Fin 3 → ℤ,
        ∫ z in Work.BoseBoxFock.LatFourier.latCell ℓ, g (z + ℓ • latVec m) := by
    rw [tsum_eq_sum (s := Work.BoseBoxFock.LatFourier.latFinSet ℓ R) hzero]
  have htile := Work.BoseBoxFock.latTiling_integral hℓ g hgint
  have hft : ∫ u, g u = Submission.BoseGases.kinFT Φ (kappaL ℓ n) := rfl
  calc ∫ z in Work.BoseBoxFock.LatFourier.latCell ℓ,
        Work.BoseBoxFock.L1Tails.latPerC ℓ Φ z
          * Complex.exp (-(Complex.I * ((inner ℝ (kappaL ℓ n) z : ℝ) : ℂ)))
      = ∫ z in Work.BoseBoxFock.LatFourier.latCell ℓ,
          ∑ m ∈ Work.BoseBoxFock.LatFourier.latFinSet ℓ R, g (z + ℓ • latVec m) := hstep1
    _ = ∑ m ∈ Work.BoseBoxFock.LatFourier.latFinSet ℓ R,
          ∫ z in Work.BoseBoxFock.LatFourier.latCell ℓ, g (z + ℓ • latVec m) := hstep2
    _ = ∑' m : Fin 3 → ℤ,
          ∫ z in Work.BoseBoxFock.LatFourier.latCell ℓ, g (z + ℓ • latVec m) := hstep3
    _ = ∫ u, g u := htile.symm
    _ = Submission.BoseGases.kinFT Φ (kappaL ℓ n) := hft

end Work.BoseBoxFock.L1Tails
