import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.BoseFixB1S.cubeProfHatSecondMoment
import Submission.Work.BoseFixB1S.symACubeMoments
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.profCubeMom2_le` — the explicit second-moment bound for the cube profile

`profHatCube M p = ∫_z chiSmall M z · cos⟪p,z⟫` is the cosine profile of the normalised cube
cutoff `chiSmall M` (`CubeWindowSymbol`), and

    cubeMomBound M = 3 · (M π)² · (2 M + 1)³

is the explicit constant attached to it (`symACubeMoments`).  This module proves

    (2π)⁻³ ∫_p (profHatCube M p)² ‖p‖² ≤ cubeMomBound M     (M ≥ 1),

the second moment bound consumed by the cube two-cut symbol comparison
(`symACube_fsKinCoeff_mix_scaled`).

## Route

The proved identity `pcProfHatCube_moment_eq` turns the left-hand side into the gradient energy
`∫_z ‖∇(chiSmall M) z‖²`, which is bounded without any Fourier analysis:

* a.e. the gradient coordinates are the *explicit* partial derivatives
  `pcD M k z = cSmall M · φ'(z_k) · ∏_{i≠k} φ(z_i)` (`pcAeGradCoord_chiSmall`), so
  `‖∇(chiSmall M) z‖² = Σ_k (pcD M k z)²`;
* each `pcD M k` is bounded by `cSmall M · Mπ` and supported in the closed unit cube
  `pcm2Cube = {z | ∀ j, |z_j| ≤ 1/2}`, which has volume `1`
  (`pcD_eq_zero_of_half_lt_abs`, `pcD_sq_le`, `pcm2Cube_volume`), whence
  `∫_z (pcD M k z)² ≤ (cSmall M · Mπ)²`;
* summing over the three coordinates and using `(cSmall M)² ≤ (2M+1)³` (`cSmall_sq_le`) gives
  `∫_z ‖∇(chiSmall M) z‖² ≤ 3 (2M+1)³ (Mπ)² = cubeMomBound M`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixB1S

open _root_.BoseGases Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## 1. The closed unit cube of `E3`, its measurability and its volume -/

/-- The closed unit cube `[-1/2,1/2]³` of `E3`, the support of the explicit partial derivatives
`pcD M k` of the cube bump. -/
def pcm2Cube : Set E3 := {z : E3 | ∀ j : Fin 3, |z.ofLp j| ≤ 1 / 2}

lemma pcm2_toLp_symm (z : E3) :
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm z = z.ofLp := rfl

/-- `pcm2Cube` is the preimage of the coordinate box under the measure-preserving identification
of `E3` with `Fin 3 → ℝ`. -/
lemma pcm2Cube_eq_preimage :
    pcm2Cube = (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm ⁻¹'
      Set.univ.pi (fun _ : Fin 3 => Set.Icc (-(1 / 2)) (1 / 2)) := by
  ext z
  simp only [pcm2Cube, Set.mem_preimage, Set.mem_univ_pi, Set.mem_Icc, Set.mem_ofPred_eq,
    abs_le, pcm2_toLp_symm]

lemma pcm2Cube_measurable : MeasurableSet pcm2Cube := by
  rw [pcm2Cube_eq_preimage]
  exact (MeasurableEquiv.measurableSet_preimage _).mpr
    (MeasurableSet.univ_pi fun _ => measurableSet_Icc)

/-- **The closed unit cube has volume one.** -/
lemma pcm2Cube_volume : (volume : Measure E3) pcm2Cube = 1 := by
  have hmp := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)
  set T : Set (Fin 3 → ℝ) :=
    Set.univ.pi (fun _ : Fin 3 => Set.Icc (-(1 / 2)) (1 / 2)) with hTdef
  have hpre : (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm ⁻¹' T = pcm2Cube := by
    rw [hTdef]; exact pcm2Cube_eq_preimage.symm
  rw [← hpre, hmp.measure_preimage]
  · rw [hTdef, volume_pi_pi]
    simp only [Real.volume_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [show (1 / 2 - -(1 / 2) : ℝ) = 1 by norm_num, ENNReal.ofReal_one, one_pow]
  · rw [hTdef]
    exact (MeasurableSet.univ_pi fun _ => measurableSet_Icc).nullMeasurableSet

/-! ## 2. The integral of the square of an explicit partial derivative -/

/-- **`∫_z (pcD M k z)² ≤ (cSmall M · Mπ)²`.**  The explicit partial derivative is bounded by
`cSmall M · Mπ` and supported in the closed unit cube, which has volume `1`. -/
lemma pcm2_pcD_sq_integral_le (M : ℕ) (hM : 1 ≤ M) (k : Fin 3) :
    (∫ z : E3, (pcD M k z) ^ 2) ≤ (cSmall M * ((M : ℝ) * Real.pi)) ^ 2 := by
  have hSmeas : MeasurableSet pcm2Cube := pcm2Cube_measurable
  have hvolS : (volume : Measure E3) pcm2Cube = 1 := pcm2Cube_volume
  have hint : Integrable (fun z : E3 => (pcD M k z) ^ 2) := by
    have h := (MeasureTheory.memLp_two_iff_integrable_sq_norm
        (cubeProfHatSecondMoment_measurable_pcD M k).aestronglyMeasurable).mp
        (cubeProfHatSecondMoment_memLp_pcD hM k).2
    refine h.congr (Filter.Eventually.of_forall fun z => ?_)
    show ‖((pcD M k z : ℝ) : ℂ)‖ ^ 2 = (pcD M k z) ^ 2
    rw [pcNorm_ofReal, sq_abs]
  have hmaj : Integrable (fun z : E3 =>
      (cSmall M * ((M : ℝ) * Real.pi)) ^ 2 * pcm2Cube.indicator (fun _ => (1 : ℝ)) z) := by
    have h1 : Integrable (pcm2Cube.indicator (fun _ : E3 => (1 : ℝ))) volume := by
      rw [MeasureTheory.integrable_indicator_iff hSmeas]
      refine MeasureTheory.integrableOn_const (C := (1 : ℝ)) ?_ ?_
      · rw [hvolS]; exact ENNReal.one_ne_top
      · simp
    exact h1.const_mul _
  have hpt : ∀ z : E3, (pcD M k z) ^ 2
      ≤ (cSmall M * ((M : ℝ) * Real.pi)) ^ 2 * pcm2Cube.indicator (fun _ => (1 : ℝ)) z := by
    intro z
    by_cases hz : z ∈ pcm2Cube
    · rw [Set.indicator_of_mem hz, mul_one]
      exact pcD_sq_le k z
    · obtain ⟨j, hj⟩ : ∃ j : Fin 3, 1 / 2 < |z.ofLp j| := by
        by_contra hcon
        rw [not_exists] at hcon
        exact hz (by rw [pcm2Cube]; exact fun j => le_of_not_gt (hcon j))
      rw [Set.indicator_of_notMem hz, mul_zero, pcD_eq_zero_of_half_lt_abs hM k hj]
      norm_num
  calc (∫ z : E3, (pcD M k z) ^ 2)
      ≤ ∫ z : E3,
          (cSmall M * ((M : ℝ) * Real.pi)) ^ 2 * pcm2Cube.indicator (fun _ => (1 : ℝ)) z :=
        MeasureTheory.integral_mono_ae hint hmaj (Filter.Eventually.of_forall hpt)
    _ = (cSmall M * ((M : ℝ) * Real.pi)) ^ 2
          * ∫ z : E3, pcm2Cube.indicator (fun _ => (1 : ℝ)) z :=
        MeasureTheory.integral_const_mul _ _
    _ = (cSmall M * ((M : ℝ) * Real.pi)) ^ 2 * (volume pcm2Cube).toReal := by
        rw [MeasureTheory.integral_indicator hSmeas, MeasureTheory.setIntegral_const,
          MeasureTheory.Measure.real_def]
        simp only [smul_eq_mul, mul_one]
    _ = (cSmall M * ((M : ℝ) * Real.pi)) ^ 2 := by
        rw [hvolS]
        norm_num

/-! ## 3. The gradient energy of the cube bump -/

/-- **The gradient energy of the cube bump is bounded by `cubeMomBound M`.** -/
lemma pcm2_winGrad_le (M : ℕ) (hM : 1 ≤ M) :
    (∫ z : E3, ‖gradient (chiSmall M) z‖ ^ 2) ≤ cubeMomBound M := by
  have hint : ∀ k : Fin 3, Integrable (fun z : E3 => (pcD M k z) ^ 2) := by
    intro k
    have h := (MeasureTheory.memLp_two_iff_integrable_sq_norm
        (cubeProfHatSecondMoment_measurable_pcD M k).aestronglyMeasurable).mp
        (cubeProfHatSecondMoment_memLp_pcD hM k).2
    refine h.congr (Filter.Eventually.of_forall fun z => ?_)
    show ‖((pcD M k z : ℝ) : ℂ)‖ ^ 2 = (pcD M k z) ^ 2
    rw [pcNorm_ofReal, sq_abs]
  have hpoint : ∀ᵐ z : E3 ∂(volume : Measure E3),
      ‖gradient (chiSmall M) z‖ ^ 2 = ∑ k : Fin 3, (pcD M k z) ^ 2 := by
    filter_upwards [pcAeGradCoord_chiSmall M hM] with z hz
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Real.norm_eq_abs, sq_abs, hz k]
  have hsum_eq : (∫ z : E3, ‖gradient (chiSmall M) z‖ ^ 2)
      = ∑ k : Fin 3, ∫ z : E3, (pcD M k z) ^ 2 := by
    rw [integral_congr_ae hpoint]
    simpa using MeasureTheory.integral_finsetSum (Finset.univ : Finset (Fin 3))
      (μ := volume) (f := fun (k : Fin 3) (z : E3) => (pcD M k z) ^ 2)
      (fun k _ => hint k)
  have hcsm : (cSmall M) ^ 2 ≤ (2 * (M : ℝ) + 1) ^ 3 := cSmall_sq_le M hM
  calc (∫ z : E3, ‖gradient (chiSmall M) z‖ ^ 2)
      = ∑ k : Fin 3, ∫ z : E3, (pcD M k z) ^ 2 := hsum_eq
    _ ≤ ∑ _k : Fin 3, (cSmall M * ((M : ℝ) * Real.pi)) ^ 2 :=
        Finset.sum_le_sum fun k _ => pcm2_pcD_sq_integral_le M hM k
    _ = 3 * (cSmall M * ((M : ℝ) * Real.pi)) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        norm_num
    _ ≤ cubeMomBound M := by
        have hπ : (0 : ℝ) ≤ ((M : ℝ) * Real.pi) ^ 2 := sq_nonneg _
        calc 3 * (cSmall M * ((M : ℝ) * Real.pi)) ^ 2
            = 3 * ((cSmall M) ^ 2 * ((M : ℝ) * Real.pi) ^ 2) := by ring
          _ ≤ 3 * ((2 * (M : ℝ) + 1) ^ 3 * ((M : ℝ) * Real.pi) ^ 2) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcsm hπ) (by norm_num)
          _ = cubeMomBound M := by rw [cubeMomBound]; ring

/-! ## 4. The target -/

theorem profCubeMom2_le (M : ℕ) (hM : 1 ≤ M) :
    ((2 * Real.pi) ^ 3)⁻¹ *
      (∫ p : EuclideanSpace ℝ (Fin 3), (Work.BoseFixB1S.profHatCube M p) ^ 2 * ‖p‖ ^ 2)
    ≤ Work.BoseFixB1S.cubeMomBound M := by
  have hkey := pcProfHatCube_moment_eq M hM
  have hcomm : (∫ p : E3, (profHatCube M p) ^ 2 * ‖p‖ ^ 2)
      = ∫ p : E3, ‖p‖ ^ 2 * (profHatCube M p) ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)
  rw [hcomm, hkey]
  exact pcm2_winGrad_le M hM

end Work.BoseFixB1S
