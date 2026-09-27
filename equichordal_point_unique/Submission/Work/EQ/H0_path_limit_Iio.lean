import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.H0_path_limit
import Submission.Work.Topology.reparam_tendsto_Iio

/-!
# Rychlik's path-limit theorem at `1⁻`

`Work.EQ.H0_path_limit` (Rychlik Theorem 11) is stated for a path parametrised by `s → +∞` on
`[0,∞)`.  The radius of the uniformising disc is naturally parametrised by `r → 1⁻`; this module
transfers the statement along the order isomorphism `s ↦ s/(s+1)`.
-/

noncomputable section

open Filter _root_.Topology

namespace Work.EQ

/-- **Rychlik's path-limit theorem at `1⁻`** (the form used by `H0_regular`). -/
theorem H0_path_limit_Iio {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {γ : ℝ → ChainData}
    (hγ : ∀ s : ℝ, s ∈ Set.Iio (1 : ℝ) → γ s ∈ H0 a h)
    (hcont : ContinuousOn γ (Set.Iio (1 : ℝ))) {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0)
    (h1 : Tendsto (fun s : ℝ => (γ s).2.1) (nhdsWithin 1 (Set.Iio (1 : ℝ))) (nhds u))
    (h2 : Tendsto (fun s : ℝ => (γ s).2.2) (nhdsWithin 1 (Set.Iio (1 : ℝ))) (nhds v)) :
    (∃ q ∈ H0 a h, Tendsto γ (nhdsWithin 1 (Set.Iio (1 : ℝ))) (nhds q)) ∨
      ∃ (e : ℂ → ChainData) (k : ℕ), IsPuncturedChart a h e u k ∧
        ∀ ρ : ℝ, 0 < ρ → ∀ᶠ s in nhdsWithin 1 (Set.Iio (1 : ℝ)),
          γ s ∈ e '' (Metric.ball (0 : ℂ) ρ \ {0}) := by
  set γ' : ℝ → ChainData := fun s => γ (s / (s + 1)) with hγ'def
  have hmem : ∀ s : ℝ, 0 ≤ s → γ' s ∈ H0 a h := by
    intro s hs
    exact hγ _ (div_succ_lt_one (by linarith))
  have hcont' : ContinuousOn γ' (Set.Ici 0) := continuousOn_comp_div hcont
  have h1' : Tendsto (fun s : ℝ => (γ' s).2.1) atTop (nhds u) :=
    tendsto_iff_tendsto_comp_div.mpr h1
  have h2' : Tendsto (fun s : ℝ => (γ' s).2.2) atTop (nhds v) :=
    tendsto_iff_tendsto_comp_div.mpr h2
  rcases H0_path_limit ha0 ha1 hh hmem hcont' hu hv h1' h2' with ⟨q, hq, hql⟩ | ⟨e, k, hchart, hρ⟩
  · left
    exact ⟨q, hq, tendsto_iff_tendsto_comp_div.mp hql⟩
  · right
    refine ⟨e, k, hchart, fun ρ hρpos => ?_⟩
    exact (eventually_nhdsWithin_Iio_iff_eventually_atTop_div
      (P := fun s => γ s ∈ e '' (Metric.ball (0 : ℂ) ρ \ {0}))).mp (hρ ρ hρpos)

end Work.EQ
