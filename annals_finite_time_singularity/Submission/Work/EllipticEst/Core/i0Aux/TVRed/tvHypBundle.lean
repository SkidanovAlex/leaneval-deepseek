import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.Defs
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.BumpFacts
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.tvHypAux
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux.TVRed

open scoped Real Topology
open MeasureTheory Set Filter

theorem tvHypBundle {f : ℝ → ℝ} {ψ : ℝ → ℝ} {C F₀ F₁ L : ℝ}
    (hψ : Work.EllipticEst.Core.i0Aux.IsBump ψ C) (hL : 0 < L) (hLp : L ≤ Real.pi / 4)
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hlim0 : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds F₀))
    (hlim1 : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds F₁))
    (hP : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hA : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hE : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ) :
    ContDiffOn ℝ 2 (fun θ : ℝ => f θ - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ)
        (Set.Ioo 0 (Real.pi / 2)) ∧
    Filter.Tendsto (fun θ : ℝ => f θ - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (fun θ : ℝ => f θ - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) ∧
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (f θ - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) ^ 2 *
          Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ ∧
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv (fun θ : ℝ => f θ - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) θ) ^ 2 *
          Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ ∧
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv (deriv (fun θ : ℝ => f θ - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ)) θ) ^ 2 *
          Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
  obtain ⟨hS0, hS1, hS2⟩ := tvh_surr_sq_integrable hψ hL
  have hs : ContDiff ℝ 2 (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) :=
    surr_smooth hψ (ne_of_gt hL)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hf.sub hs.contDiffOn
  · simpa only [sub_self] using hlim0.sub (surr_tendsto_left (F₀ := F₀) (F₁ := F₁) hψ hL hLp)
  · simpa only [sub_self] using hlim1.sub (surr_tendsto_right (F₀ := F₀) (F₁ := F₁) hψ hL hLp)
  · exact tvh_integrableOn_sq_sub hP hS0 (tvh_aesm_of_contDiffOn hf)
      hs.continuous.aestronglyMeasurable
  · -- first derivative
    have hdf : AEStronglyMeasurable (deriv f) (volume.restrict Work.Spaces.Iθ) :=
      tvh_aesm_of_contDiffOn (hf.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num))
    have hds : AEStronglyMeasurable
        (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L))
        (volume.restrict Work.Spaces.Iθ) :=
      (hs.continuous_deriv (by norm_num)).aestronglyMeasurable
    have hbase := tvh_integrableOn_sq_sub hA hS1 hdf hds
    refine hbase.congr ?_
    have hae : deriv (fun θ : ℝ => f θ - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ)
        =ᵐ[volume.restrict Work.Spaces.Iθ]
        (fun θ : ℝ => deriv f θ
          - deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ) :=
      tvh_ae_eq_of_forall_Ioo (fun θ hθ => tvh_deriv_sub hf hs θ hθ)
    filter_upwards [hae] with θ hθ
    rw [hθ]
  · -- second derivative
    have hdf2 : AEStronglyMeasurable (deriv (deriv f)) (volume.restrict Work.Spaces.Iθ) :=
      tvh_aesm_of_contDiffOn
        ((hf.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).deriv_of_isOpen
          isOpen_Ioo (m := 0) (by norm_num))
    have hds2 : AEStronglyMeasurable
        (deriv (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)))
        (volume.restrict Work.Spaces.Iθ) := by
      have h1 : ContDiff ℝ 1 (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) := by
        simpa using hs.deriv' (n := 1)
      exact (h1.continuous_deriv (by norm_num)).aestronglyMeasurable
    have hbase := tvh_integrableOn_sq_sub hE hS2 hdf2 hds2
    refine hbase.congr ?_
    have hae : deriv (deriv (fun θ : ℝ => f θ - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ))
        =ᵐ[volume.restrict Work.Spaces.Iθ]
        (fun θ : ℝ => deriv (deriv f) θ
          - deriv (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) θ) :=
      tvh_ae_eq_of_forall_Ioo (fun θ hθ => tvh_deriv2_sub hf hs θ hθ)
    filter_upwards [hae] with θ hθ
    rw [hθ]

end Work.EllipticEst.Core.i0Aux.TVRed
