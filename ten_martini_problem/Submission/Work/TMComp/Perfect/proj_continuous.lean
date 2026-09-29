import Mathlib
import Submission.Work.TMComp.PerfectDefs

namespace Work.TMComp.Perfect

open Filter
open scoped ENNReal

/-- Spectra of a family of operators which is continuous at a point are, near that point,
contained in a fixed compact set. -/
lemma exists_compact_spectrum_eventually {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] {a : ℝ → A} {θ₀ : ℝ} (hcont : ContinuousAt a θ₀) :
    ∃ K : Set ℂ, IsCompact K ∧ ∀ᶠ θ in nhds θ₀, spectrum ℂ (a θ) ⊆ K := by
  refine ⟨Metric.closedBall 0 ((‖a θ₀‖ + 1) * ‖(1 : A)‖), isCompact_closedBall _ _, ?_⟩
  have h1 : Tendsto (fun θ : ℝ => ‖a θ - a θ₀‖) (nhds θ₀) (nhds 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hcont
  filter_upwards [h1.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with θ hθ
  refine (spectrum.subset_closedBall_norm_mul (a θ)).trans
    (Metric.closedBall_subset_closedBall ?_)
  have h2 : ‖a θ‖ ≤ ‖a θ₀‖ + ‖a θ - a θ₀‖ := norm_le_norm_add_norm_sub' _ _
  have h3 : ‖a θ - a θ₀‖ < 1 := hθ
  exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

/-- The canonical spectral projection depends continuously (in operator norm) on the phase,
whenever the spectra of the family are contained in a fixed set `s` on which the tent function
is continuous. -/
theorem proj_continuous (α lam : ℝ) (E δ : ℝ) (s : Set ℂ)
    (hsa : ∀ θ : ℝ, IsSelfAdjoint (Work.TMComp.Perfect.amoOp α lam θ))
    (hnc : ∀ θ θ' : ℝ, ‖Work.TMComp.Perfect.amoOp α lam θ - Work.TMComp.Perfect.amoOp α lam θ'‖
      ≤ 4 * Real.pi * |lam| * |θ - θ'|)
    (hcont : ContinuousOn (Work.TMComp.Perfect.projFun E δ) s)
    (hspec : ∀ θ : ℝ, spectrum ℂ (Work.TMComp.Perfect.amoOp α lam θ) ⊆ s) :
    Continuous (fun θ : ℝ => Work.TMComp.Perfect.proj α lam θ E δ) := by
  -- The tent function `projFun E δ` is continuous on all of `ℂ` (`projFun_continuous`), so the
  -- hypotheses `hcont` and `hspec` are not needed: it suffices that, at each phase, the spectrum
  -- of a nearby operator is contained in a fixed compact set, which `exists_compact_spectrum_eventually`
  -- supplies from the norm-continuity `hnc` of the family. Continuity in the operator variable is
  -- then exactly Mathlib's `ContinuousAt.cfc`.
  have hLip : LipschitzWith (Real.toNNReal (4 * Real.pi * |lam|))
      (fun θ : ℝ => amoOp α lam θ) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro θ θ'
    rw [dist_eq_norm, dist_eq_norm, Real.norm_eq_abs,
      Real.coe_toNNReal _ (by positivity)]
    exact hnc θ θ'
  have hcont_a : Continuous (fun θ : ℝ => amoOp α lam θ) := hLip.continuous
  rw [continuous_iff_continuousAt]
  intro θ₀
  obtain ⟨K, hK, hKspec⟩ := exists_compact_spectrum_eventually hcont_a.continuousAt
  exact ContinuousAt.cfc hK (projFun E δ) hcont_a.continuousAt hKspec
    (Filter.Eventually.of_forall (fun θ => (hsa θ).isStarNormal))
    (projFun_continuous E δ).continuousOn

end Work.TMComp.Perfect
