import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.LatFourierDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.latPer_fourierCoeff` — the lattice Fourier coefficients of the periodisation

The `n`-th lattice Fourier coefficient of the periodisation `latPer ℓ W` of a bounded compactly
supported weight `W` equals the `n`-th lattice sample `latFt ℓ W n = kinFT W (kmomInt ℓ n)` of its
Fourier transform:

    ∫_{latCell ℓ} latPer ℓ W z · e^{−i⟪k_n,z⟫} dz = kinFT W k_n ,     k_n = kmomInt ℓ n = (2π/ℓ) n .

The proof uses the tiling hypothesis `htiling` (applied to the bounded compactly supported test
function `u ↦ e^{−i⟪k_n,u⟫}W u`), the invariance `e^{−i⟪k_n, z + ℓ•m⟫} = e^{−i⟪k_n,z⟫}` of the
character under lattice translations (`LatFourier.exp_neg_I_inner_add_latVec`, since
`⟪k_n, ℓ•m⟫ = 2π (n·m)`), the finiteness of `latPer` on the cube, and the linearity of the
Bochner integral over the finite sum `latFinSet ℓ R`.
-/

namespace Work.BoseBoxFock

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem latPer_fourierCoeff {ℓ R : ℝ} (hℓ : 0 < ℓ) {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hWm : MeasureTheory.AEStronglyMeasurable W MeasureTheory.volume)
    (hWb : ∃ C : ℝ, ∀ x, ‖W x‖ ≤ C) (hWs : ∀ x, R < ‖x‖ → W x = 0)
    (htiling : ∀ f : EuclideanSpace ℝ (Fin 3) → ℂ,
      MeasureTheory.Integrable f MeasureTheory.volume →
      ∫ u, f u = ∑' m : Fin 3 → ℤ,
        ∫ z in Work.BoseBoxFock.LatFourier.latCell ℓ,
          f (z + ℓ • Work.BoseBoxFock.latVec m))
    (n : Fin 3 → ℤ) :
    ∫ z in Work.BoseBoxFock.LatFourier.latCell ℓ,
        Work.BoseBoxFock.LatFourier.latPer ℓ W z
          * Complex.exp (-(Complex.I * ((inner ℝ (Work.BoseBoxFock.kmomInt ℓ n) z : ℝ) : ℂ)))
      = Work.BoseBoxFock.LatFourier.latFt ℓ W n := by
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  obtain ⟨C, hC⟩ := hWb
  -- The bounded, compactly supported test function whose periodisation is `latPer ℓ W`.
  let g : E3 → ℂ := fun u =>
    Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) u : ℝ) : ℂ))) * (W u : ℂ)
  -- The character is invariant under the lattice translations.
  have hexp : ∀ (m : Fin 3 → ℤ) (z : E3),
      Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) (z + ℓ • latVec m) : ℝ) : ℂ)))
        = Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ))) :=
    fun m z => LatFourier.exp_neg_I_inner_add_latVec hℓne n m z
  -- The exponential factor has modulus one.
  have hexp1 : ∀ t : ℝ, ‖Complex.exp (-(Complex.I * ((t : ℝ) : ℂ)))‖ = 1 := by
    intro t
    have h : -(Complex.I * ((t : ℝ) : ℂ)) = ((-t : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [h, Complex.norm_exp_ofReal_mul_I]
  have hgcont : Continuous (fun u : E3 =>
      Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) u : ℝ) : ℂ)))) := by
    fun_prop
  have hgaesm : AEStronglyMeasurable g volume := by
    show AEStronglyMeasurable (fun u : E3 =>
      Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) u : ℝ) : ℂ))) * (W u : ℂ)) volume
    exact hgcont.aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hWm)
  have hgbd : ∃ D : ℝ, ∀ u, ‖g u‖ ≤ D := by
    refine ⟨max C 0, fun u => ?_⟩
    have h1 : ‖g u‖ = ‖W u‖ := by
      show ‖Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) u : ℝ) : ℂ)))
        * (W u : ℂ)‖ = ‖W u‖
      rw [norm_mul, hexp1, one_mul]
      simp
    rw [h1]
    exact le_trans (hC u) (le_max_left C 0)
  have hgsupp : ∀ u, max R 0 < ‖u‖ → g u = 0 := by
    intro u hu
    have hWu : W u = 0 := hWs u (lt_of_le_of_lt (le_max_left R 0) hu)
    show Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) u : ℝ) : ℂ))) * (W u : ℂ) = 0
    rw [hWu]; simp
  have hgint : Integrable g volume :=
    LatFourier.integrable_of_bdd_of_supp (ρ := max R 0) (le_max_right R 0) hgaesm hgbd hgsupp
  -- Off the finite set `latFinSet ℓ R` the weight vanishes on the whole cell.
  have hvan : ∀ m : Fin 3 → ℤ, m ∉ LatFourier.latFinSet ℓ R → ∀ z ∈ LatFourier.latCell ℓ,
      W (z + ℓ • latVec m) = 0 := by
    intro m hm z hz
    have hnot : (R + Real.sqrt 3 * ℓ) / ℓ < ‖latVec m‖ := by
      rw [← not_le]; intro hc; exact hm (LatFourier.mem_latFinSet.mpr hc)
    have hzb := LatFourier.latBox_subset_closedBall hℓ.le (LatFourier.latCell_subset_latBox hz)
    have h2 : ℓ * ‖latVec m‖ ≤ ‖z + ℓ • latVec m‖ + ‖z‖ := by
      have h := norm_sub_le (z + ℓ • latVec m) z
      rw [add_sub_cancel_left] at h
      rwa [LatFourier.latVec_norm_smul ℓ hℓ.le m] at h
    have h4 : R + Real.sqrt 3 * ℓ < ℓ * ‖latVec m‖ := by
      rw [div_lt_iff₀ hℓ] at hnot; linarith
    exact hWs _ (by linarith)
  -- The pointwise identity on the cell: `latPer` becomes the finite sum over `latFinSet ℓ R`.
  have hpoint : ∀ z ∈ LatFourier.latCell ℓ,
      LatFourier.latPer ℓ W z
          * Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)))
        = ∑ m ∈ LatFourier.latFinSet ℓ R, g (z + ℓ • latVec m) := by
    intro z hz
    calc LatFourier.latPer ℓ W z
            * Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)))
        = (∑ m ∈ LatFourier.latFinSet ℓ R, (W (z + ℓ • latVec m) : ℂ))
            * Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ))) := by
          rw [LatFourier.latPer_eq_sum_finset (R := R) hℓ hWs
            (LatFourier.latCell_subset_latBox hz)]
      _ = ∑ m ∈ LatFourier.latFinSet ℓ R, (W (z + ℓ • latVec m) : ℂ)
            * Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ))) :=
          Finset.sum_mul _ _ _
      _ = ∑ m ∈ LatFourier.latFinSet ℓ R, g (z + ℓ • latVec m) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          show (W (z + ℓ • latVec m) : ℂ)
              * Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)))
            = Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) (z + ℓ • latVec m) : ℝ) : ℂ)))
              * (W (z + ℓ • latVec m) : ℂ)
          rw [← hexp m z, mul_comm]
  have hstep1 : ∫ z in LatFourier.latCell ℓ,
        LatFourier.latPer ℓ W z
          * Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)))
      = ∫ z in LatFourier.latCell ℓ, ∑ m ∈ LatFourier.latFinSet ℓ R, g (z + ℓ • latVec m) :=
    MeasureTheory.setIntegral_congr_fun (μ := volume) (LatFourier.measurableSet_latCell ℓ) hpoint
  have hstep2 : ∫ z in LatFourier.latCell ℓ,
        (∑ m ∈ LatFourier.latFinSet ℓ R, g (z + ℓ • latVec m))
      = ∑ m ∈ LatFourier.latFinSet ℓ R,
          ∫ z in LatFourier.latCell ℓ, g (z + ℓ • latVec m) := by
    refine MeasureTheory.integral_finsetSum _ (fun m _ => ?_)
    have hshift : Integrable (fun z : E3 => g (z + ℓ • latVec m)) volume :=
      ((MeasureTheory.measurePreserving_add_right volume (ℓ • latVec m)).integrable_comp
        hgaesm).mpr hgint
    exact hshift.integrableOn (s := LatFourier.latCell ℓ)
  have hzero : ∀ m ∉ LatFourier.latFinSet ℓ R,
      ∫ z in LatFourier.latCell ℓ, g (z + ℓ • latVec m) = 0 := by
    intro m hm
    exact MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun z hz => by
      show Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) (z + ℓ • latVec m) : ℝ) : ℂ)))
        * (W (z + ℓ • latVec m) : ℂ) = 0
      rw [hvan m hm z hz]; simp
  have hstep3 : ∑ m ∈ LatFourier.latFinSet ℓ R,
        ∫ z in LatFourier.latCell ℓ, g (z + ℓ • latVec m)
      = ∑' m : Fin 3 → ℤ, ∫ z in LatFourier.latCell ℓ, g (z + ℓ • latVec m) := by
    rw [tsum_eq_sum (s := LatFourier.latFinSet ℓ R) hzero]
  have htile := htiling g hgint
  have hft : ∫ u, g u = LatFourier.latFt ℓ W n := rfl
  calc ∫ z in LatFourier.latCell ℓ,
        LatFourier.latPer ℓ W z
          * Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)))
      = ∫ z in LatFourier.latCell ℓ, ∑ m ∈ LatFourier.latFinSet ℓ R, g (z + ℓ • latVec m) := hstep1
    _ = ∑ m ∈ LatFourier.latFinSet ℓ R,
          ∫ z in LatFourier.latCell ℓ, g (z + ℓ • latVec m) := hstep2
    _ = ∑' m : Fin 3 → ℤ, ∫ z in LatFourier.latCell ℓ, g (z + ℓ • latVec m) := hstep3
    _ = ∫ u, g u := htile.symm
    _ = LatFourier.latFt ℓ W n := hft

end Work.BoseBoxFock
