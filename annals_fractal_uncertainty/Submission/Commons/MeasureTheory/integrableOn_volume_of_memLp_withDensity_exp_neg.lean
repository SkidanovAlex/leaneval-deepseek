import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

open MeasureTheory
open scoped ENNReal

namespace Commons.MeasureTheory

/-- **Local integrability under the weighted measure `e^{-φ} dz`.**  If `V ∈ L²(μ)` where
`μ = volume.withDensity (fun z => ENNReal.ofReal (Real.exp (-(φ z))))` and `φ` is continuous,
then `V` is (Lebesgue-)integrable on every compact set.  The point is that on a compact set the
density `e^{-φ}` is bounded below by a positive constant. -/
theorem integrableOn_volume_of_memLp_withDensity_exp_neg {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] {φ : (Fin d → ℂ) → ℝ} (hφ : Continuous φ) {V : (Fin d → ℂ) → E}
    (hV : MeasureTheory.MemLp V 2
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)).withDensity
        (fun z => ENNReal.ofReal (Real.exp (-(φ z))))))
    {K : Set (Fin d → ℂ)} (hK : IsCompact K) :
    MeasureTheory.IntegrableOn V K (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) := by
  -- `φ` is bounded above on the compact set `K`.
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ z ∈ K, φ z ≤ M := by
    rcases hK.bddAbove_image hφ.continuousOn with ⟨M, hM⟩
    exact ⟨M, fun z hz => hM ⟨z, hz, rfl⟩⟩
  let g : (Fin d → ℂ) → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp (-(φ z)))
  let cst : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-M))
  let C : ℝ≥0∞ := cst⁻¹
  have hcst0 : cst ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hcsttop : cst ≠ ∞ := ENNReal.ofReal_ne_top
  have hCtop : C ≠ ∞ := ENNReal.inv_ne_top.mpr hcst0
  have hK_meas : MeasurableSet K := hK.measurableSet
  -- On `K` the density is bounded below by `cst > 0`, so the restricted Lebesgue measure is
  -- dominated by `C • μ` where `μ = volume.withDensity g`.
  have hle : (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)).restrict K
      ≤ C • ((MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)).withDensity g) := by
    have hpoint : (K.indicator (1 : (Fin d → ℂ) → ℝ≥0∞)) ≤ (C • g) := by
      intro z
      by_cases hz : z ∈ K
      · rw [Set.indicator_of_mem hz]
        show (1 : ℝ≥0∞) ≤ C * g z
        have hgz : cst ≤ g z :=
          ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg (hM z hz)))
        calc (1 : ℝ≥0∞) = C * cst := (ENNReal.inv_mul_cancel hcst0 hcsttop).symm
          _ ≤ C * g z := by gcongr
      · rw [Set.indicator_of_notMem hz]
        exact zero_le
    have hthis := MeasureTheory.withDensity_mono
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)))
      (Filter.Eventually.of_forall hpoint)
    rw [MeasureTheory.withDensity_indicator_one hK_meas,
      MeasureTheory.withDensity_smul' C g hCtop] at hthis
    exact hthis
  -- Transfer `MemLp` from `μ` to `volume.restrict K`.
  have hVK : MeasureTheory.MemLp V 2
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)).restrict K) :=
    MeasureTheory.MemLp.mono_measure hle (hV.smul_measure hCtop)
  have _instFin : IsFiniteMeasure ((MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)).restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  -- Finite measure space: `L² ⊆ L¹`, and `L¹` is `Integrable`.
  have hV1 : MeasureTheory.MemLp V 1
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)).restrict K) :=
    hVK.mono_exponent (by norm_num)
  exact MeasureTheory.memLp_one_iff_integrable.mp hV1

end Commons.MeasureTheory