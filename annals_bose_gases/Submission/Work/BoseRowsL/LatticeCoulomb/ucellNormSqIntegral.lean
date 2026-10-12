import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.BoseRowsL.LatticeCoulomb.kernelDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped Real BigOperators Topology
open MeasureTheory Metric

namespace Work.BoseRowsL.LatticeCoulomb

set_option autoImplicit false
set_option linter.style.haveILetI false

/-- The one-dimensional model integral: `∫_{[-1/2,1/2]} t^2 dt = 1/12`. -/
lemma integral_sq_Icc_half :
    ∫ t in (Set.Icc (-(1 / 2) : ℝ) (1 / 2)), t ^ 2 = 1 / 12 := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2)]
  rw [integral_pow]
  norm_num

theorem ucellNormSqIntegral : ∫ w in ucell 0, ‖w‖ ^ 2 = 1 / 4 := by
  set S : Set (Fin 3 → ℝ) :=
    Set.univ.pi (fun _ : Fin 3 => Set.Icc (-(1 / 2) : ℝ) (1 / 2)) with hS
  set ν : Measure ℝ := (volume : Measure ℝ).restrict (Set.Icc (-(1 / 2) : ℝ) (1 / 2)) with hν
  have hucell : ucell (0 : Fin 3 → ℤ) = WithLp.ofLp ⁻¹' S := by
    rw [hS, ucell_eq_preimage]
    simp
  have hnorm : ∀ x : E3, (∑ i : Fin 3, (WithLp.ofLp x i) ^ 2) = ‖x‖ ^ 2 := by
    intro x
    rw [PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) x]
    simp only [Real.norm_eq_abs, sq_abs]
  have hmp : MeasurePreserving (WithLp.ofLp : E3 → (Fin 3 → ℝ)) volume volume :=
    PiLp.volume_preserving_ofLp (Fin 3)
  have hemb : MeasurableEmbedding (WithLp.ofLp : E3 → (Fin 3 → ℝ)) :=
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.measurableEmbedding
  have h0 := MeasurePreserving.setIntegral_preimage_emb hmp hemb
    (fun y : Fin 3 → ℝ => ∑ i : Fin 3, (y i) ^ 2) S
  rw [← hucell] at h0
  have hpi : (volume : Measure (Fin 3 → ℝ)).restrict S = Measure.pi (fun _ : Fin 3 => ν) := by
    rw [hS, hν, volume_pi]
    exact Measure.restrict_pi_pi (fun _ : Fin 3 => (volume : Measure ℝ))
      (fun _ : Fin 3 => Set.Icc (-(1 / 2) : ℝ) (1 / 2))
  haveI : IsProbabilityMeasure ν := ⟨by
    rw [hν, Measure.restrict_apply_univ, Real.volume_Icc]
    norm_num⟩
  have hint : Integrable (fun t : ℝ => t ^ 2) ν := by
    rw [hν]
    exact Continuous.integrableOn_Icc (by fun_prop : Continuous fun t : ℝ => t ^ 2)
  have hper : ∀ i : Fin 3, ∫ y, (y i) ^ 2 ∂(Measure.pi (fun _ : Fin 3 => ν)) = 1 / 12 := by
    intro i
    rw [MeasureTheory.integral_comp_eval (μ := fun _ : Fin 3 => ν)
      (f := fun t : ℝ => t ^ 2) ((continuous_id.pow 2).aestronglyMeasurable)]
    have : ∫ t, t ^ 2 ∂ν = 1 / 12 := by
      rw [hν]
      exact integral_sq_Icc_half
    exact this
  have hfinal : ∫ y, (∑ i : Fin 3, (y i) ^ 2) ∂(Measure.pi (fun _ : Fin 3 => ν)) = 1 / 4 := by
    rw [MeasureTheory.integral_finsetSum Finset.univ
      (fun i _ => MeasureTheory.integrable_comp_eval (μ := fun _ : Fin 3 => ν)
        (i := i) (f := fun t : ℝ => t ^ 2) hint)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hper]
    norm_num
  calc ∫ w in ucell 0, ‖w‖ ^ 2
      = ∫ x in ucell (0 : Fin 3 → ℤ), (∑ i : Fin 3, (WithLp.ofLp x i) ^ 2) := by
        refine integral_congr_ae ?_
        filter_upwards with x
        exact (hnorm x).symm
    _ = ∫ y in S, (∑ i : Fin 3, (y i) ^ 2) := h0
    _ = ∫ y, (∑ i : Fin 3, (y i) ^ 2) ∂(volume.restrict S) := rfl
    _ = ∫ y, (∑ i : Fin 3, (y i) ^ 2) ∂(Measure.pi (fun _ : Fin 3 => ν)) := by rw [hpi]
    _ = 1 / 4 := hfinal

end Work.BoseRowsL.LatticeCoulomb
