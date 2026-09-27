import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLComp.partSigma_mono_iterate

open MeasureTheory
open Work.EKLContract

set_option linter.style.haveILetI false

namespace Work.EKLComp

/-- Monotonicity of the σ-algebras `partSigma (P ·)` along the refining sequence. -/
theorem partSigma_mono_of_le {X : Type} [mX : MeasurableSpace X]
    (P : ℕ → FinPart X) (hmono : ∀ m, Refines (P (m+1)) (P m)) {a b : ℕ} (h : a ≤ b) :
    partSigma (P a) ≤ partSigma (P b) :=
  partSigma_mono_iterate P hmono h

theorem exists_measurable_approx {X : Type} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X)
    (P : ℕ → Work.EKLContract.FinPart X) (hmono : ∀ m, Work.EKLContract.Refines (P (m+1)) (P m))
    (hgen : (⨆ m, Work.EKLContract.partSigma (P m)) = mX)
    (S : Set X) (hS : MeasurableSet S) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, ∃ T : Set X, (Work.EKLContract.partSigma (P M)).MeasurableSet' T ∧
      (μ (symmDiff S T)).toReal < ε := by
  have hmono' : ∀ a b : ℕ, a ≤ b → partSigma (P a) ≤ partSigma (P b) :=
    fun a b h => partSigma_mono_of_le P hmono h
  by_cases hSinf : μ S = ⊤
  · refine ⟨0, ∅, ?_, ?_⟩
    · exact @MeasurableSet.empty X (partSigma (P 0))
    · have h1 : symmDiff S (∅ : Set X) = S := by ext x; simp [symmDiff]
      rw [h1, hSinf, ENNReal.toReal_top]
      exact hε
  · by_cases hSinfc : μ Sᶜ = ⊤
    · refine ⟨0, Set.univ, ?_, ?_⟩
      · exact @MeasurableSet.univ X (partSigma (P 0))
      · have h1 : symmDiff S (Set.univ : Set X) = Sᶜ := by ext x; simp [symmDiff]
        rw [h1, hSinfc, ENNReal.toReal_top]
        exact hε
    · -- finite measure case
      have hSlt : μ S < ⊤ := lt_top_iff_ne_top.mpr hSinf
      have hSclt : μ Sᶜ < ⊤ := lt_top_iff_ne_top.mpr hSinfc
      have hfin : μ Set.univ < ⊤ := by
        rw [← Set.union_compl_self S]
        exact (measure_union_le S Sᶜ).trans_lt (ENNReal.add_lt_top.mpr ⟨hSlt, hSclt⟩)
      haveI : IsFiniteMeasure μ := ⟨hfin⟩
      -- the generating ring of sets
      have hC : IsSetRing (⋃ M, {t : Set X | MeasurableSet[partSigma (P M)] t}) := by
        refine ⟨?_, ?_, ?_⟩
        · exact Set.mem_iUnion.mpr ⟨0, @MeasurableSet.empty X (partSigma (P 0))⟩
        · intro s t hs ht
          rw [Set.mem_iUnion] at hs ht ⊢
          obtain ⟨a, ha⟩ := hs
          obtain ⟨b, hb⟩ := ht
          exact ⟨max a b, (hmono' a (max a b) (le_max_left a b) s ha).union
            (hmono' b (max a b) (le_max_right a b) t hb)⟩
        · intro s t hs ht
          rw [Set.mem_iUnion] at hs ht ⊢
          obtain ⟨a, ha⟩ := hs
          obtain ⟨b, hb⟩ := ht
          exact ⟨max a b, (hmono' a (max a b) (le_max_left a b) s ha).diff
            (hmono' b (max a b) (le_max_right a b) t hb)⟩
      -- a countable subfamily whose union is everything
      have hD : ∃ D : Set (Set X),
          D.Countable ∧ D ⊆ (⋃ M, {t : Set X | MeasurableSet[partSigma (P M)] t}) ∧
          μ (⋃₀ D)ᶜ = 0 := by
        refine ⟨⋃ M, Set.range ((P M).parts), ?_, ?_, ?_⟩
        · exact Set.countable_iUnion (fun M => (Set.finite_range ((P M).parts)).countable)
        · intro s hs
          rw [Set.mem_iUnion] at hs ⊢
          obtain ⟨M, hM⟩ := hs
          rw [Set.mem_range] at hM
          obtain ⟨i, hi⟩ := hM
          exact ⟨M, by rw [← hi]; exact MeasurableSpace.measurableSet_generateFrom ⟨i, rfl⟩⟩
        · have huniv : (⋃₀ (⋃ M, Set.range ((P M).parts)) : Set X) = Set.univ := by
            apply subset_antisymm (Set.subset_univ _)
            rw [← (P 0).cover]
            exact Set.iUnion_subset (fun i =>
              Set.subset_sUnion_of_mem (Set.mem_iUnion.mpr ⟨0, Set.mem_range.mpr ⟨i, rfl⟩⟩))
          rw [huniv]
          simp
      -- the generating σ-algebra
      have hgenC : mX =
          MeasurableSpace.generateFrom (⋃ M, {t : Set X | MeasurableSet[partSigma (P M)] t}) :=
        ((MeasurableSpace.generateFrom_iUnion_measurableSet (fun M => partSigma (P M))).trans
          hgen).symm
      obtain ⟨t, htC, ht⟩ :=
        exists_measure_symmDiff_lt_of_generateFrom_isSetRing hC hD hgenC hS
          (ε := ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
      rw [Set.mem_iUnion] at htC
      obtain ⟨M, hM⟩ := htC
      refine ⟨M, t, hM, ?_⟩
      have ht2 : μ (symmDiff S t) < ENNReal.ofReal ε := by
        rw [symmDiff_comm]; exact ht
      have hane : μ (symmDiff S t) ≠ ⊤ :=
        lt_top_iff_ne_top.mp (lt_of_lt_of_le ht2 le_top)
      have hlt : (μ (symmDiff S t)).toReal < (ENNReal.ofReal ε).toReal :=
        (ENNReal.toReal_lt_toReal hane ENNReal.ofReal_ne_top).mpr ht2
      rw [ENNReal.toReal_ofReal (le_of_lt hε)] at hlt
      exact hlt

end Work.EKLComp
