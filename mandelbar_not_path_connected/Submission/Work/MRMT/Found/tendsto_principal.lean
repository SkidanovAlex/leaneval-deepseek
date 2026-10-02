import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.tendsto_of_modulus_and_small
import Submission.Work.MRMT.Found.eLpNorm_dev_le_family_of_weakDeriv
import Submission.Work.MRMT.Found.record_dev_energy
import Submission.Work.MRMT.Found.records_agree
import Submission.Work.Found.principalData_exists_bounded
import Submission.Work.Found.record_modulus_of_bound

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false




noncomputable section

open MeasureTheory Filter Topology Complex Function
open scoped ENNReal

namespace Work.MRMT.Found

/-- **Courant–Lebesgue modulus for the family of records.**  The principal solutions of a family
of admissible coefficients which are all bounded by `k` and supported in a fixed ball share one
logarithmic modulus of continuity on each ball: the constant depends only on `R`, `k` and the
radius `ρ`, not on the record.

The proof replaces each record `d j` by the canonical record `d' j` of
`principalData_exists_bounded`, whose approximating coefficients are bounded by `max k 0`; the two
records have the same principal solution by `records_agree`, and
`record_modulus_of_bound` gives the modulus for the canonical family with a constant independent
of `j`. -/
theorem modulus_of_records {μs : ℕ → ℂ → ℂ} (hμ : ∀ j, Admissible (μs j))
    (d : ∀ j, PrincipalData (μs j)) {R k : ℝ} (hk : k < 1)
    (hsupp : ∀ j, Function.support (μs j) ⊆ Metric.closedBall 0 R)
    (hb : ∀ j, ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μs j z‖ ≤ k)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℕ) (z₀ z : ℂ), ‖z₀‖ ≤ ρ → ‖z - z₀‖ ≤ 1 / 4 →
      ‖((d j).φ : ℂ → ℂ) z - ((d j).φ : ℂ → ℂ) z₀‖ ^ 2
        ≤ C / Real.log (1 / ‖z - z₀‖) := by
  have hk0 : (0 : ℝ) ≤ max k 0 := le_max_right k 0
  have hk1 : max k 0 < 1 := max_lt hk zero_lt_one
  have hR0 : (0 : ℝ) ≤ max R 0 := le_max_right R 0
  have hb' : ∀ j, ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      ‖μs j z‖ ≤ max k 0 :=
    fun j => (hb j).mono fun z hz => le_trans hz (le_max_left k 0)
  have hsupp' : ∀ j, Function.support (μs j) ⊆ Metric.closedBall 0 (max R 0) :=
    fun j => (hsupp j).trans (Metric.closedBall_subset_closedBall (le_max_left R 0))
  choose d' hd' using fun j =>
    Work.Found.principalData_exists_bounded (hμ j) hk0 hk1 (hb' j)
  obtain ⟨C, hC, hmod⟩ :=
    Work.Found.record_modulus_of_bound hμ d' hk0 hk1 hR0 hsupp' hb' hd' ρ hρ
  refine ⟨C, hC, ?_⟩
  intro j z₀ z hz₀ hz
  rw [records_agree (d j) (d' j)]
  exact hmod j z₀ z hz₀ hz

/-- **Mandelbar drive, M6.**  The principal solutions of a uniformly bounded, uniformly
supported family of Beltrami coefficients converge locally uniformly to the identity as soon as
the coefficients converge to `0` in `L^∞`. -/
theorem tendsto_principal {μs : ℕ → ℂ → ℂ} (hμ : ∀ j, Admissible (μs j))
    (d : ∀ j, PrincipalData (μs j)) {R k : ℝ} (hk : k < 1)
    (hsupp : ∀ j, Function.support (μs j) ⊆ Metric.closedBall 0 R)
    (hb : ∀ j, ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μs j z‖ ≤ k)
    (h0 : Filter.Tendsto (fun j => MeasureTheory.eLpNorm (μs j) ⊤ (MeasureTheory.volume : MeasureTheory.Measure ℂ))
      Filter.atTop (nhds 0)) :
    TendstoLocallyUniformly (fun j => ((d j).φ : ℂ → ℂ)) id Filter.atTop := by
  have hk0 : (0 : ℝ) ≤ max k 0 := le_max_right k 0
  have hk1 : max k 0 < 1 := max_lt hk zero_lt_one
  have hR0 : (0 : ℝ) ≤ max R 0 := le_max_right R 0
  have hb' : ∀ j, ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      ‖μs j z‖ ≤ max k 0 :=
    fun j => (hb j).mono fun z hz => le_trans hz (le_max_left k 0)
  have hsupp' : ∀ j, Function.support (μs j) ⊆ Metric.closedBall 0 (max R 0) :=
    fun j => (hsupp j).trans (Metric.closedBall_subset_closedBall (le_max_left R 0))
  refine tendsto_of_modulus_and_small (μs := μs) (φs := fun j => ((d j).φ : ℂ → ℂ))
    (fun j => (d j).φ.continuous) ?_ ?_ h0
  · intro ρ hρ
    exact modulus_of_records hμ d hk hsupp hb ρ hρ
  · intro ρ hρ
    have hwk : ∀ j, ∃ D : ℂ → ℂ, MemL2Loc D ∧ IsDzDeriv ((d j).φ : ℂ → ℂ) D ∧
        IsDbarDeriv ((d j).φ : ℂ → ℂ) (fun z => μs j z * D z) := by
      intro j
      obtain ⟨E, hE, hEd⟩ := record_dev_energy (max k 0) (max R 0) hk0 hk1 hR0
      obtain ⟨D, hDmem, hDz, hDbar, -⟩ :=
        hEd (μs j) (hμ j) (d j) (hsupp' j) (hb' j)
      exact ⟨D, hDmem, hDz, hDbar⟩
    obtain ⟨C, hC, hC'⟩ := eLpNorm_dev_le_family_of_weakDeriv d hk hsupp hb hwk ρ hρ
    exact ⟨C, hC, hC'⟩

end Work.MRMT.Found
