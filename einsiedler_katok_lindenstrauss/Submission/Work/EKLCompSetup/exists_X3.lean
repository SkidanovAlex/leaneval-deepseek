import Mathlib
import Submission.Work.EKLComp.C8Defs
import Submission.Work.EKLCompSetup.not_bad_implies
import Submission.Work.EKLCompSetup.exists_compact_of_measure_le
import Submission.Work.EKLCompSetup.measure_bad_le

namespace Work.EKLCompSetup

open MeasureTheory
open scoped ENNReal

/-!
## Building the flow-averaging compact `X₃` of the low-entropy assembly

The two flow-density clauses of `C8Setup` (`X₃_avg₁`, `X₃_avg₂`) are produced from the
maximal-inequality hypothesis `hMF` (Hopf's maximal inequality for the contracting flow
`Φ_τ`) together with the measure lower bounds for `X₂` and `Xrho`.

Write `B₁`, `B₂` for the "bad" sets on which the flow average of the complement indicators
`1 - 1_{X₂}` resp. `1 - 1_{Xrho}` exceeds `ε` at some time scale.  `measure_bad_le` turns `hMF`
(at `α = ε`) plus `μ X₂ ≥ 1 - C ε²` resp. `μ Xrho > 1 - ε²` into

`μ B₁ ≤ ofReal (C ε)`,  `μ B₂ ≤ ofReal ε`,

so the exceptional set `bad = X''ᶜ ∪ B₁ ∪ B₂` has measure at most `ofReal ((C+1) ε)`.

* If `(C+2) ε > 1` the required measure bound `1 - (C+2) ε < (μ X₃).toReal` is automatic, and
  the empty set is a legitimate witness (it is compact, contained in `X''`, and the two
  density clauses are vacuous).
* Otherwise `(C+1) ε ≤ 1 - ε < 1`, and replacing `bad` by a measurable superset `M` of the same
  measure (`exists_measurable_superset`) and invoking inner regularity of `μ` on the Polish
  space `X₃` (`exists_compact_of_measure_le`) yields a compact `K ⊆ Mᶜ ⊆ badᶜ` with
  `(μ K).toReal > 1 - (C+2) ε`.  Since `K ⊆ X'' ∩ B₁ᶜ ∩ B₂ᶜ`, the pointwise bridge
  `not_bad_implies` converts membership in `B₁ᶜ`/`B₂ᶜ` into the two flow-average inequalities,
  uniformly in `T > 0`.
-/

theorem exists_X3
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    [PolishSpace Work.EKLContract.X3]
    {X'' X₂ Xrho : Set Work.EKLContract.X3}
    (hX''meas : MeasurableSet X'') (hX''conull : μ X''ᶜ = 0)
    (hX₂meas : MeasurableSet X₂) (hXrhomeas : MeasurableSet Xrho)
    {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε)
    (hX₂ : 1 - C * ε^2 ≤ (μ X₂).toReal) (hXrho : 1 - ε^2 < (μ Xrho).toReal)
    (hMF : ∀ (f : Work.EKLContract.X3 → ℝ), Measurable f → (∀ x, 0 ≤ f x) →
      MeasureTheory.Integrable f μ →
      ∀ α : ℝ, 0 < α →
        μ {x | ∃ T : ℝ, 0 < T ∧
            α * T < ∫ τ in (0 : ℝ)..T, f (Work.EKLComp.Phi τ x)}
          ≤ ENNReal.ofReal ((∫ x, f x ∂μ) / α)) :
    ∃ X₃ : Set Work.EKLContract.X3, IsCompact X₃ ∧ X₃ ⊆ X'' ∧
      1 - (C + 2) * ε < (μ X₃).toReal ∧
      (∀ x ∈ X₃, ∀ T : ℝ, 0 < T →
        (1 - ε) * T ≤ ∫ τ in (0 : ℝ)..T,
          Set.indicator X₂ (fun _ => (1 : ℝ)) (Work.EKLComp.Phi τ x)) ∧
      (∀ x ∈ X₃, ∀ T : ℝ, 0 < T →
        (1 - ε) * T ≤ ∫ τ in (0 : ℝ)..T,
          Set.indicator Xrho (fun _ => (1 : ℝ)) (Work.EKLComp.Phi τ x)) := by
  -- Measurability of `X''` is not needed: only its conullity is used.
  have _ : MeasurableSet X'' := hX''meas
  set B₁ : Set Work.EKLContract.X3 := {x | ∃ T : ℝ, 0 < T ∧
      ε * T < ∫ τ in (0 : ℝ)..T,
        (1 - Set.indicator X₂ (fun _ => (1 : ℝ)) (Work.EKLComp.Phi τ x))} with hB₁
  set B₂ : Set Work.EKLContract.X3 := {x | ∃ T : ℝ, 0 < T ∧
      ε * T < ∫ τ in (0 : ℝ)..T,
        (1 - Set.indicator Xrho (fun _ => (1 : ℝ)) (Work.EKLComp.Phi τ x))} with hB₂
  have hμB₁ : μ B₁ ≤ ENNReal.ofReal (C * ε) := by
    have h := measure_bad_le (μ := μ) hX₂meas hC hε hX₂ hMF
    rwa [hB₁]
  have hμB₂ : μ B₂ ≤ ENNReal.ofReal ε := by
    have h := measure_bad_le (μ := μ) (S := Xrho) hXrhomeas (C := 1) one_pos hε
      (by nlinarith [hXrho]) hMF
    simpa using h
  have hbad : μ (X''ᶜ ∪ B₁ ∪ B₂) ≤ ENNReal.ofReal ((C + 1) * ε) := by
    calc μ (X''ᶜ ∪ B₁ ∪ B₂) ≤ μ (X''ᶜ ∪ B₁) + μ B₂ := measure_union_le _ _
      _ ≤ (μ X''ᶜ + μ B₁) + μ B₂ := add_le_add_left (measure_union_le _ _) _
      _ ≤ (0 + ENNReal.ofReal (C * ε)) + ENNReal.ofReal ε := by
          rw [hX''conull]
          exact add_le_add (add_le_add_right hμB₁ 0) hμB₂
      _ = ENNReal.ofReal ((C + 1) * ε) := by
          rw [zero_add, ← ENNReal.ofReal_add (by positivity) (le_of_lt hε)]
          congr 1
          ring
  rcases lt_or_ge (1 : ℝ) ((C + 2) * ε) with hcase | hcase
  · refine ⟨∅, isCompact_empty, Set.empty_subset _, ?_, ?_, ?_⟩
    · rw [MeasureTheory.measure_empty, ENNReal.toReal_zero]
      linarith
    · intro x hx
      exact absurd hx (Set.notMem_empty x)
    · intro x hx
      exact absurd hx (Set.notMem_empty x)
  · have hγ1 : (C + 1) * ε < 1 := by linarith
    have hγ0 : 0 ≤ (C + 1) * ε := by positivity
    obtain ⟨M, hbadM, hMmeas, hMμ⟩ := exists_measurable_superset μ (X''ᶜ ∪ B₁ ∪ B₂)
    have hMγ : μ M ≤ ENNReal.ofReal ((C + 1) * ε) := by rw [hMμ]; exact hbad
    have hr0 : 0 ≤ 1 - (C + 2) * ε := by linarith
    have hr : 1 - (C + 2) * ε < 1 - (C + 1) * ε := by linarith
    obtain ⟨K, hKcomp, hKM, hKr⟩ := exists_compact_of_measure_le hMmeas hγ0 hγ1 hMγ hr0 hr
    have hMsub : Mᶜ ⊆ (X''ᶜ ∪ B₁ ∪ B₂)ᶜ := Set.compl_subset_compl.mpr hbadM
    have hKbad : K ⊆ (X''ᶜ ∪ B₁ ∪ B₂)ᶜ := hKM.trans hMsub
    refine ⟨K, hKcomp, ?_, ?_, ?_, ?_⟩
    · intro x hx
      by_contra hx''
      exact hKbad hx (Or.inl (Or.inl hx''))
    · have hne : μ K ≠ ⊤ := measure_ne_top μ K
      have hlt : (ENNReal.ofReal (1 - (C + 2) * ε)).toReal < (μ K).toReal :=
        (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hne).mpr hKr
      rwa [ENNReal.toReal_ofReal hr0] at hlt
    · intro x hx T hT
      have hxb : ¬ (∃ T : ℝ, 0 < T ∧ ε * T < ∫ τ in (0 : ℝ)..T,
          (1 - Set.indicator X₂ (fun _ => (1 : ℝ)) (Work.EKLComp.Phi τ x))) := by
        intro h
        refine hKbad hx (Or.inl (Or.inr ?_))
        rw [hB₁]
        exact h
      exact not_bad_implies hX₂meas hε x hxb T hT
    · intro x hx T hT
      have hxb : ¬ (∃ T : ℝ, 0 < T ∧ ε * T < ∫ τ in (0 : ℝ)..T,
          (1 - Set.indicator Xrho (fun _ => (1 : ℝ)) (Work.EKLComp.Phi τ x))) := by
        intro h
        refine hKbad hx (Or.inr ?_)
        rw [hB₂]
        exact h
      exact not_bad_implies hXrhomeas hε x hxb T hT

end Work.EKLCompSetup
