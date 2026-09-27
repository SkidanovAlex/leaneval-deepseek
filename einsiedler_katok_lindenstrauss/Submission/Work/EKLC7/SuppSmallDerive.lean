import Mathlib
import Submission.Work.EKLC7.Defs
import Submission.Work.EKLRelCross.Instances
import Submission.Work.EKLContract.Lemmas.Uij_range
import Submission.Work.EKLContract.Lemmas.Box1_Uij

/-!
# Deriving the "small support points" condition from the ball positivity

If a Radon measure `ν` on `SL₃(ℝ)` has positive mass on `ballU hij ε` for every `ε > 0` and no
atom at `1`, then every `ε > 0` admits `p ≠ 0` with `|p| ≤ ε` and `uij hij p` in the support of
`ν`.  This is the form of the "arbitrarily small non-trivial elements in the support" input that
the commutator lemma C7 consumes (Pisa 9.11, "by Poincaré recurrence ...").
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

namespace Work.EKLC7

lemma one_mem_ballU {i j : Fin 3} (hij : i ≠ j) {ε : ℝ} (hε : 0 ≤ ε) :
    (1 : SL3) ∈ ballU hij ε := by
  refine ⟨0, ⟨by linarith, hε⟩, ?_⟩
  simp [uij, Matrix.SpecialLinearGroup.transvection_coeff_zero]

lemma exists_small_support {i j : Fin 3} (hij : i ≠ j) (ν : Measure SL3)
    (hpos : ∀ ε : ℝ, 0 < ε → 0 < ν (ballU hij ε)) (hno : ν {1} = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ p : ℝ, p ≠ 0 ∧ |p| ≤ ε ∧ uij hij p ∈ ν.support := by
  intro ε hε
  have hsub : ({1} : Set SL3) ⊆ ballU hij ε := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact one_mem_ballU hij (le_of_lt hε)
  have hdiff : ν (ballU hij ε \ {1}) = ν (ballU hij ε) :=
    MeasureTheory.measure_sdiff_null (by rw [hno])
  have hpos' : 0 < ν (ballU hij ε \ {1}) := by rw [hdiff]; exact hpos ε hε
  -- the set meets the support
  have hmeet : ((ballU hij ε \ {1}) ∩ ν.support).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    rw [Set.eq_empty_iff_forall_notMem] at hcon
    have hle : ballU hij ε \ {1} ⊆ ν.supportᶜ := by
      intro x hx
      by_contra hxs
      exact hcon x ⟨hx, by simpa using hxs⟩
    have hzero : ν (ballU hij ε \ {1}) = 0 :=
      le_antisymm (le_trans (MeasureTheory.measure_mono hle)
        (le_of_eq (Measure.measure_compl_support (μ := ν)))) bot_le
    rw [hzero] at hpos'
    exact lt_irrefl _ hpos'
  obtain ⟨g, hg⟩ := hmeet
  obtain ⟨hgball, hgsupp⟩ := hg
  obtain ⟨hgin, hgne⟩ := hgball
  obtain ⟨p, hpIcc, hp_eq⟩ := hgin
  refine ⟨p, ?_, ?_, ?_⟩
  · intro hp0
    apply hgne
    rw [Set.mem_singleton_iff, ← hp_eq, hp0]
    simp [uij, Matrix.SpecialLinearGroup.transvection_coeff_zero]
  · exact abs_le.mpr hpIcc
  · simpa only [hp_eq] using hgsupp

end Work.EKLC7
