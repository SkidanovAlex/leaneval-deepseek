import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE3.Taylor.Arc.complexify_order
import Submission.Work.WilE3.Taylor.Arc.order_restrict
import Submission.Work.WilE3.Frame.eaEvalC_toC
import Submission.Work.WilE3.API.eaEvalC_fderiv_analytic

namespace Work.WilE3.Taylor.Arc

open Filter Function
open scoped Topology
open WilkiesDesign.E

/-- Finitely many positive reals admit a common positive lower bound. -/
lemma exists_pos_le_all {k : ℕ} {r : Fin k → ℝ} (hr : ∀ i, 0 < r i) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ i, ρ ≤ r i := by
  by_cases h : (Finset.univ : Finset (Fin k)).Nonempty
  · refine ⟨(Finset.univ : Finset (Fin k)).inf' h r, ?_, ?_⟩
    · rw [Finset.lt_inf'_iff h]; exact fun i _ => hr i
    · intro i; exact Finset.inf'_le r (Finset.mem_univ i)
  · exact ⟨1, one_pos, fun i => absurd ⟨i, Finset.mem_univ i⟩ h⟩

theorem eaEvalC_arc_order {k r : ℕ} (c : WilkiesDesign.E.EAChain k r) (Φ : WilkiesDesign.E.EAPoly k r)
    (γ : ℝ → Fin k → ℝ) (hγ : ∀ i, AnalyticAt ℝ (fun t => γ t i) 0) :
    ∃ (σ : ℂ → Fin k → ℂ) (ρ : ℝ), 0 < ρ ∧
      (∀ i, AnalyticOnNhd ℂ (fun s : ℂ => σ s i) (Metric.ball 0 ρ)) ∧
      (∀ t : ℝ, |t| < ρ → σ t = fun i => ((γ t i : ℝ) : ℂ)) ∧
      analyticOrderAt (fun s : ℂ => Work.WilE3.eaEvalC c Φ (σ s)) 0
        = analyticOrderAt (fun t : ℝ => ((WilkiesDesign.E.eaEval c Φ (γ t) : ℝ) : ℂ)) 0 := by
  classical
  -- Complexify each coordinate of `γ`; the extra order information of `complexify_order` is not
  -- needed, only analyticity on a disk and agreement with `γ` on the reals.
  choose F rad hrad hFrad hFeq _hFord using fun i => complexify_order (fun t => γ t i) (hγ i)
  -- A common radius on which all coordinates are holomorphic.
  obtain ⟨ρ, hρpos, hρle⟩ := exists_pos_le_all hrad
  let σ : ℂ → Fin k → ℂ := fun s i => F i s
  refine ⟨σ, ρ, hρpos, ?_, ?_, ?_⟩
  · -- Coordinatewise analyticity on the disk of radius `ρ`.
    intro i
    exact (hFrad i).mono (Metric.ball_subset_ball (hρle i))
  · -- Agreement with `γ` on real points.
    intro t ht
    funext i
    exact hFeq i t (lt_of_lt_of_le ht (hρle i))
  · -- The composite is holomorphic at `0`, so `order_restrict` relates its order on the real line
    -- to its order on `ℂ`; the two agree with the complexification of `eaEval c Φ ∘ γ` near `0`.
    have hσan : AnalyticAt ℂ σ 0 := by
      have h : ∀ i, AnalyticAt ℂ (fun s : ℂ => F i s) 0 := fun i =>
        hFrad i 0 (by rw [Metric.mem_ball, dist_zero_right, norm_zero]; exact hrad i)
      exact AnalyticAt.pi h
    have hGan : AnalyticAt ℂ (fun s : ℂ => Work.WilE3.eaEvalC c Φ (σ s)) 0 :=
      (Work.WilE3.API.eaEvalC_fderiv_analytic c Φ (σ 0)).1.comp hσan
    have hres := order_restrict (fun s : ℂ => Work.WilE3.eaEvalC c Φ (σ s)) hGan
    have hev : (fun x : ℝ => Work.WilE3.eaEvalC c Φ (σ (x : ℂ))) =ᶠ[𝓝 (0 : ℝ)]
        (fun t : ℝ => ((WilkiesDesign.E.eaEval c Φ (γ t) : ℝ) : ℂ)) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hρpos] with t ht
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at ht
      have h1 : σ (t : ℂ) = Work.WilE3.Frame.toC (γ t) := by
        funext i
        exact hFeq i t (lt_of_lt_of_le ht (hρle i))
      rw [h1, Work.WilE3.Frame.eaEvalC_toC]
    exact hres.symm.trans (analyticOrderAt_congr hev)

end Work.WilE3.Taylor.Arc
