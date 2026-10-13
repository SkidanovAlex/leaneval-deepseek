/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.Closed3` — the order-3 reduction, and its small-α form

The order-`3` analogue of `Closed.ellClosed_of_compact_uniq`: the same subsequence argument
(`Filter.tendsto_of_subseq_tendsto` + reindexing) shows that **obligation 1 at order 3**
(`ClosedCompact3`) and **obligation 2 at order 3** (`ClosedUniq3`) give the order-`3` closure
`ClosedE3` — and hence, in the small-α shape of the ruling, that `SmallCompact3 ∧ SmallUniq3` give
`ClosedE3` for every `α` below `min α₁ α₂` and every package operator.
-/
import Mathlib.Topology.Instances.Nat
import Mathlib.Topology.Metrizable.Uniformity
import Submission.Work.FTS_EllLimOK.Defs3
import Submission.Work.FTS_EllLimOK.Closed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The order-3 reduction (proved)**: obligations 1 and 2 at order 3 give the order-3 closure of
every operator carrying the packages. -/
theorem ClosedE3_of_compact3_uniq3 {α Ce : ℝ} (hα : 0 < α) {E : Fn →ₗ[ℝ] Fn}
    (hE : HasPkg α Ce E) (hcomp : ClosedCompact3 α Ce) (huniq : ClosedUniq3 α Ce) :
    ClosedE3 α E := by
  intro fn f hL
  obtain ⟨Ψ, hΨlim⟩ := hcomp E hE fn f hL
  refine ⟨Ψ, hΨlim.1, ?_⟩
  intro j i hji z θ hz
  refine tendsto_of_subseq_tendsto (fun ns hns => ?_)
  -- reindex `ns` by a cofinal subsequence and apply compactness to the reindexed sequence
  obtain ⟨ψ, -, hnsψ⟩ := strictMono_subseq_of_tendsto_atTop hns
  have hL' : LimSeq4 α (fun n => fn (ns (ψ n))) f := limSeq4_comp hL hnsψ.tendsto_atTop
  obtain ⟨Ψ₂, hfat₂, σ, hσ, hJ₂⟩ := hcomp E hE _ f hL'
  have h₂ : IsJetLimit3 α E fn f Ψ₂ :=
    ⟨hfat₂, ⟨fun n => ns (ψ (σ n)), hnsψ.tendsto_atTop.comp hσ, by
      simpa only [Function.comp_apply] using hJ₂⟩⟩
  have hjet := huniq E hE fn f hL Ψ Ψ₂ hΨlim h₂ j i hji z θ hz
  refine ⟨fun n => ψ (σ n), ?_⟩
  rw [hjet]
  simpa only [Function.comp_apply] using hJ₂ j i hji z θ hz

/-- **The small-α reduction**: `SmallCompact3 ∧ SmallUniq3` give `ClosedE3` for every `α` in
`(0, min α₁ α₂]` and every package operator. -/
theorem ClosedE3_of_smallObligations (hcomp : SmallCompact3) (huniq : SmallUniq3) :
    ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ α : ℝ, 0 < α → α ≤ α₁ →
      ∀ Ce : ℝ, ∀ E : Fn →ₗ[ℝ] Fn, HasPkg α Ce E → ClosedE3 α E := by
  obtain ⟨αc, hαc, hc⟩ := hcomp
  obtain ⟨αu, hαu, hu⟩ := huniq
  refine ⟨min αc αu, lt_min hαc hαu, fun α hα hle Ce E hE => ?_⟩
  exact ClosedE3_of_compact3_uniq3 hα hE (hc α hα (le_trans hle (min_le_left _ _)) Ce)
    (hu α hα (le_trans hle (min_le_right _ _)) Ce)

end Work.FTS_EllLimOK
