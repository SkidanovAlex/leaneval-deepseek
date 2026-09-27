import Mathlib
import Submission.Work.EQ.EquiLocalDefs

namespace Work.EQ

/-- One inclusion of the fibre comparison: if the `ρ`-truncated legs (as point sets) satisfy the
inclusion `E '' {ζ ≠ 0 | ‖κ ζ^k‖ < ρ} ⊆ F '' {η ≠ 0 | ‖κ' η^{k'}‖ < ρ}`, then the fibres over any
`v` with `dist v u₁ < ρ` satisfy the same inclusion. -/
private lemma legFibre_subset_of_trunc_subset {a : ℝ} {h : ℂ → ℂ} {u₁ : ℂ}
    {E F : ℂ → ChainData} {κ κ' : ℂ} {k k' : ℕ} (hE : IsChartData a h E u₁ κ k)
    (hF : IsChartData a h F u₁ κ' k') {ρ : ℝ}
    (hsmallE : ∀ u ζ : ℂ, dist u u₁ < ρ → u₁ + κ * ζ ^ k = u → ‖ζ‖ < 1)
    (hsmallF : ∀ u ζ : ℂ, dist u u₁ < ρ → u₁ + κ' * ζ ^ k' = u → ‖ζ‖ < 1)
    (hsub : E '' {ζ : ℂ | ζ ≠ 0 ∧ ‖κ * ζ ^ k‖ < ρ} ⊆
      F '' {η : ℂ | η ≠ 0 ∧ ‖κ' * η ^ k'‖ < ρ})
    {v : ℂ} (hv : dist v u₁ < ρ) :
    legFibre E u₁ v κ k ⊆ legFibre F u₁ v κ' k' := by
  have hchartE := hE.2.2.1
  have hchartF := hF.2.2.1
  rintro q ⟨ζ, ⟨hζne, hζv⟩, rfl⟩
  have hmemE : ζ ∈ Metric.ball (0 : ℂ) 1 \ {0} := by
    have hsmall : ‖ζ‖ < 1 := hsmallE v ζ hv hζv
    exact ⟨by simpa [Metric.mem_ball, dist_eq_norm] using hsmall, hζne⟩
  have hEval : (E ζ).2.1 = v := by
    rw [(hchartE ζ hmemE).2, hζv]
  -- the value `u₁ + κ ζ^k` lies in the disc, whence `E ζ` is in the truncated leg
  have hnorm : ‖κ * ζ ^ k‖ = dist v u₁ := by
    have hv' : v - u₁ = κ * ζ ^ k := by rw [← hζv]; ring
    rw [dist_eq_norm, hv']
  have htrunc : E ζ ∈ E '' {ζ : ℂ | ζ ≠ 0 ∧ ‖κ * ζ ^ k‖ < ρ} :=
    ⟨ζ, ⟨hζne, by rw [hnorm]; exact hv⟩, rfl⟩
  obtain ⟨η, ⟨hηne, hηnorm⟩, hηeq⟩ := hsub htrunc
  -- the partner chart point also has modulus `< 1`
  have hmemF : η ∈ Metric.ball (0 : ℂ) 1 \ {0} := by
    have hsmall : ‖η‖ < 1 := by
      refine hsmallF (u₁ + κ' * η ^ k') η ?_ rfl
      rw [dist_eq_norm, add_sub_cancel_left]
      exact hηnorm
    exact ⟨by simpa [Metric.mem_ball, dist_eq_norm] using hsmall, hηne⟩
  have hvalue : u₁ + κ' * η ^ k' = v := by
    rw [← (hchartF η hmemF).2, hηeq, hEval]
  exact ⟨η, ⟨hηne, hvalue⟩, hηeq⟩

/-- **Equal truncations of the two legs give equal fibres.**  If two chart data with the same
centre `u₁` agree as point sets over the value disc `ball u₁ ρ` (i.e. the two truncated legs
`E '' {ζ ≠ 0 | ‖κ ζ^k‖ < ρ}` and `F '' {η ≠ 0 | ‖κ' η^{k'}‖ < ρ}` are the same set, for `ρ > 0`
small enough that all roots of the value equations in that disc have modulus `< 1`, hypotheses
`hsmallE`/`hsmallF`), then for every `v` with `dist v u₁ < ρ` the two fibres over `v` are the same
set of chains (`legFibre E u₁ v κ k = legFibre F u₁ v κ' k'`).

Route: both sides are the slice of the common leg over `v`, namely
`legFibre E u₁ v κ k = (E '' {ζ ≠ 0 | ‖κ ζ^k‖ < ρ}) ∩ {q | q.2.1 = v}`: for `ζ ≠ 0` with
`u₁ + κ ζ^k = v` one has `‖κ ζ^k‖ = dist v u₁ < ρ` by hypothesis, and conversely a point of the
truncated leg over `v` is `E ζ` with `u₁ + κ ζ^k = v` by the chart formula (which needs `‖ζ‖ < 1`,
from `hsmallE`).  Same for `F`, and the two slices of the same set coincide. -/
theorem legFibre_eq_of_legImg_eq {a : ℝ} {h : ℂ → ℂ} {u₁ : ℂ}
    {E F : ℂ → ChainData} {κ κ' : ℂ} {k k' : ℕ} (hE : IsChartData a h E u₁ κ k)
    (hF : IsChartData a h F u₁ κ' k') {ρ : ℝ} (hρ : 0 < ρ)
    (hsmallE : ∀ u ζ : ℂ, dist u u₁ < ρ → u₁ + κ * ζ ^ k = u → ‖ζ‖ < 1)
    (hsmallF : ∀ u ζ : ℂ, dist u u₁ < ρ → u₁ + κ' * ζ ^ k' = u → ‖ζ‖ < 1)
    (himg : E '' {ζ : ℂ | ζ ≠ 0 ∧ ‖κ * ζ ^ k‖ < ρ} =
      F '' {η : ℂ | η ≠ 0 ∧ ‖κ' * η ^ k'‖ < ρ})
    {v : ℂ} (hv : dist v u₁ < ρ) (hvne : v ≠ u₁) :
    legFibre E u₁ v κ k = legFibre F u₁ v κ' k' :=
  Set.Subset.antisymm
    (legFibre_subset_of_trunc_subset hE hF hsmallE hsmallF himg.le hv)
    (legFibre_subset_of_trunc_subset hF hE hsmallF hsmallE himg.ge hv)

end Work.EQ
