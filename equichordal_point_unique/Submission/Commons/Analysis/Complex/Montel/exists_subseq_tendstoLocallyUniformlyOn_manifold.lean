import Mathlib
import Submission.Commons.Analysis.Complex.ChartedSpace.exists_chartBall_analyticAt
import Submission.Commons.Analysis.Complex.Montel.exists_subseq_tendstoLocallyUniformlyOn_of_chartBall_analytic
import Submission.Commons.Analysis.Complex.ChartedSpace.analyticAt_comp_chart_symm_of_tendstoLocallyUniformlyOn

noncomputable section
open Set Metric Filter Topology
open scoped Topology

namespace Commons.Analysis.Complex.Montel

/-- **Montel's theorem on a `ℂ`-charted space.**  Let `X` be a locally compact, second countable
space charted over `ℂ`, and let `f : ℕ → X → ℂ` be a sequence of functions each of which is analytic
in the preferred chart at every point of `X`, all bounded by `1`.  Then some strictly monotone
subsequence converges locally uniformly on `X` to a function which is again analytic in the preferred
chart at every point.

The proof splits into three parts, all in the shared commons:
* `Commons.Analysis.Complex.ChartedSpace.exists_chartBall_analyticAt`: around each point there is a
  chart ball on which *every* `f n` is analytic (this uses the rigidity lemma
  `analyticAt_comp_chart_symm_of_witness`: at a regular point of one member of the family, every
  member is analytic in that chart; together with Riemann's removable singularity theorem applied to
  the isolated critical points of the witness, and the fact that the set of points where a function
  is locally constant is clopen);
* `Commons.Analysis.Complex.Montel.exists_subseq_tendstoLocallyUniformlyOn_of_chartBall_analytic`:
  a diagonal extraction over a countable cover by such chart balls, using Montel's theorem on balls;
* `Commons.Analysis.Complex.ChartedSpace.analyticAt_comp_chart_symm_of_tendstoLocallyUniformlyOn`:
  the locally uniform limit of the subsequence is analytic in every preferred chart (Weierstrass'
  theorem on the chart balls, and the local-constancy alternative). -/
theorem exists_subseq_tendstoLocallyUniformlyOn_manifold {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] [LocallyCompactSpace X] [SecondCountableTopology X] {f : ℕ → X → ℂ}
    (hf : ∀ n x, AnalyticAt ℂ (f n ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
    (hb : ∀ n x, ‖f n x‖ ≤ 1) :
    ∃ (φ : ℕ → ℕ) (g : X → ℂ), StrictMono φ ∧
      TendstoLocallyUniformlyOn (fun n => f (φ n)) g Filter.atTop Set.univ ∧
      (∀ x, AnalyticAt ℂ (g ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)) := by
  classical
  -- ## Chart balls on which every `f n` is analytic
  have hball : ∀ x : X, ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target ∧
      ∀ n, ∀ z ∈ Metric.ball ((chartAt ℂ x) x) ρ, AnalyticAt ℂ (f n ∘ (chartAt ℂ x).symm) z :=
    fun x => Commons.Analysis.Complex.ChartedSpace.exists_chartBall_analyticAt hf x
  -- ## Diagonal extraction
  obtain ⟨φ, g, hφ, hconv⟩ :=
    Commons.Analysis.Complex.Montel.exists_subseq_tendstoLocallyUniformlyOn_of_chartBall_analytic
      hb hball
  -- ## Analyticity of the limit
  have hball' : ∀ x : X, ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target ∧
      ∀ n, ∀ z ∈ Metric.ball ((chartAt ℂ x) x) ρ, AnalyticAt ℂ (f (φ n) ∘ (chartAt ℂ x).symm) z := by
    intro x
    obtain ⟨ρ, hρ, hsub, han⟩ := hball x
    exact ⟨ρ, hρ, hsub, fun n z hz => han (φ n) z hz⟩
  exact ⟨φ, g, hφ, hconv,
    Commons.Analysis.Complex.ChartedSpace.analyticAt_comp_chart_symm_of_tendstoLocallyUniformlyOn
      (fun n x => hf (φ n) x) hball' hconv⟩

end Commons.Analysis.Complex.Montel
