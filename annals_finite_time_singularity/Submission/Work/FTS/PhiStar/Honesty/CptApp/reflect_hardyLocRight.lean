import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.lintegral_Ioo_reflect

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.PhiStar.Honesty.CptApp

/-- The reflection `φ ↦ b - φ` sends the one-sided neighbourhood `0⁺` to `b⁻`. -/
private lemma tendsto_const_sub_nhdsWithin_right (b : ℝ) :
    Filter.Tendsto (fun φ : ℝ => b - φ) (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin b (Set.Iio b)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have hcont : Continuous (fun φ : ℝ => b - φ) := continuous_const.sub continuous_id
    have hbase : Filter.Tendsto (fun φ : ℝ => b - φ) (nhds (0 : ℝ)) (nhds b) := by
      have h := hcont.tendsto 0
      simpa using h
    exact hbase.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with φ hφ
    simpa using hφ

/-- The weight `sin (2 ·)` is invariant under the reflection `θ = π/2 - φ`. -/
private lemma sin_two_reflect (φ : ℝ) :
    Real.sin (2 * (Real.pi / 2 - φ)) = Real.sin (2 * φ) := by
  rw [show 2 * (Real.pi / 2 - φ) = Real.pi - 2 * φ by ring, Real.sin_pi_sub]

theorem reflect_hardyLocRight (c θ₁ : ℝ) (hθ : θ₁ < Real.pi / 2) {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 1 u (Set.Ioo θ₁ (Real.pi / 2)))
    (h1 : Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    ContDiffOn ℝ 1 (fun φ => u (Real.pi / 2 - φ)) (Set.Ioo 0 (Real.pi / 2 - θ₁)) ∧
    Filter.Tendsto (fun φ => u (Real.pi / 2 - φ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
    (∫⁻ θ in Set.Ioo θ₁ (Real.pi / 2),
        ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2))
      = (∫⁻ φ in Set.Ioo (0 : ℝ) (Real.pi / 2 - θ₁),
          ENNReal.ofReal ((Real.sin (2 * φ)) ^ (-c)
            * ((fun ψ => u (Real.pi / 2 - ψ)) φ) ^ 2)) ∧
    (∫⁻ θ in Set.Ioo θ₁ (Real.pi / 2),
        ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2))
      = (∫⁻ φ in Set.Ioo (0 : ℝ) (Real.pi / 2 - θ₁),
          ENNReal.ofReal ((Real.sin (2 * φ)) ^ (2 - c)
            * (deriv (fun ψ => u (Real.pi / 2 - ψ)) φ) ^ 2)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the reflected function is `C¹` on the reflected interval
    have hf : ContDiffOn ℝ 1 (fun φ : ℝ => Real.pi / 2 - φ)
        (Set.Ioo 0 (Real.pi / 2 - θ₁)) :=
      (contDiffOn_const (c := Real.pi / 2)).sub contDiffOn_id
    have hmaps : Set.MapsTo (fun φ : ℝ => Real.pi / 2 - φ) (Set.Ioo 0 (Real.pi / 2 - θ₁))
        (Set.Ioo θ₁ (Real.pi / 2)) := by
      intro φ hφ
      simp only [Set.mem_Ioo] at hφ ⊢
      constructor <;> linarith [hφ.1, hφ.2, hθ]
    exact hu.comp hf hmaps
  · -- the reflected function still vanishes at the left endpoint
    exact h1.comp (tendsto_const_sub_nhdsWithin_right (Real.pi / 2))
  · -- the weighted `L²` integrals coincide
    have h := Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.lintegral_Ioo_reflect
      (fun θ : ℝ => ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2)) θ₁ (Real.pi / 2)
    rw [h]
    refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo (fun φ _ => ?_)
    rw [sin_two_reflect]
  · -- the weighted `L²` integrals of the derivatives coincide
    have h := Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.lintegral_Ioo_reflect
      (fun θ : ℝ => ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2))
      θ₁ (Real.pi / 2)
    rw [h]
    refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo (fun φ _ => ?_)
    have hd : (deriv (fun ψ : ℝ => u (Real.pi / 2 - ψ)) φ) ^ 2
        = (deriv u (Real.pi / 2 - φ)) ^ 2 := by
      rw [deriv_comp_const_sub u (Real.pi / 2) φ]
      ring
    rw [sin_two_reflect, hd]

end Work.FTS.PhiStar.Honesty.CptApp
