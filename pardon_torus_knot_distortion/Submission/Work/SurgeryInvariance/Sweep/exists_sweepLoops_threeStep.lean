import Mathlib
import Submission.Work.SurgeryInvariance.Loops
import Submission.Work.SurgeryInvariance.API

/-!
# Chaining two zero-winding surgeries into a sweep

`SurgeryStepZero P A B` and `SurgeryStepZero P B C` are two consecutive local moves of a family of
spheres, each changing the region `F ∩ int(S_t)` by an open piece of zero winding span.  This file
turns the pair of moves into an honest loop-level sweep (`SweepLoops P`) whose region at time `0` is
`A` and whose region at time `1` is `C`: the piecewise constant family

  `region t = A` for `t ≤ 1/3`,  `region t = B` for `1/3 < t ≤ 2/3`,  `region t = C` otherwise,

with exceptional parameters `1/3` and `2/3`.  Between the exceptional parameters the family is
constant, hence transports loops (`RegionEquivalent`); at `1/3` it performs the move `A → B` and at
`2/3` the move `B → C`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.SurgeryInvariance.Sweep

/-- The piecewise constant family of regions with break points `1/3 < 2/3`: `A` up to `1/3`, `B`
from `1/3` to `2/3`, and `C` from `2/3` on. -/
def threeStepRegion (A B C : Set R3) : ℝ → Set R3 :=
  fun t => if t ≤ (1/3 : ℝ) then A else if t ≤ (2/3 : ℝ) then B else C

lemma threeStepRegion_of_le {A B C : Set R3} {t : ℝ} (h : t ≤ (1/3 : ℝ)) :
    threeStepRegion A B C t = A := by
  unfold threeStepRegion
  rw [if_pos h]

lemma threeStepRegion_of_mid {A B C : Set R3} {t : ℝ}
    (h1 : ¬ t ≤ (1/3 : ℝ)) (h2 : t ≤ (2/3 : ℝ)) :
    threeStepRegion A B C t = B := by
  unfold threeStepRegion
  rw [if_neg h1, if_pos h2]

lemma threeStepRegion_of_gt {A B C : Set R3} {t : ℝ} (h : ¬ t ≤ (2/3 : ℝ)) :
    threeStepRegion A B C t = C := by
  have h1 : ¬ t ≤ (1/3 : ℝ) := by
    rw [not_le] at h ⊢
    linarith
  unfold threeStepRegion
  rw [if_neg h1, if_neg h]

theorem exists_sweepLoops_threeStep {P : Work.CoreTopology.ParamTorus}
    {A B C : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (hAB : Work.SurgeryInvariance.SurgeryStepZero P A B)
    (hBC : Work.SurgeryInvariance.SurgeryStepZero P B C) :
    ∃ S : Work.SurgeryInvariance.SweepLoops P, S.region 0 = A ∧ S.region 1 = C := by
  classical
  refine ⟨⟨threeStepRegion A B C, ({1/3, 2/3} : Finset ℝ), ?_, ?_⟩, ?_, ?_⟩
  · -- away from the exceptional parameters the family is locally constant
    intro t ht
    have ht1 : t ≠ 1/3 := fun h => ht (by rw [h]; simp)
    have ht2 : t ≠ 2/3 := fun h => ht (by rw [h]; simp)
    by_cases h13 : t < (1/3 : ℝ)
    · -- `t < 1/3`
      refine ⟨1/3 - t, by linarith, ?_, ?_⟩
      · intro s hs
        obtain ⟨-, hsh⟩ := abs_lt.mp hs
        have hs13 : s < 1/3 := by linarith
        have hs23 : s < 2/3 := by linarith
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨ne_of_lt hs13, ne_of_lt hs23⟩
      · intro s hs
        obtain ⟨-, hsh⟩ := abs_lt.mp hs
        have hs13 : s ≤ 1/3 := by linarith
        rw [threeStepRegion_of_le (le_of_lt h13), threeStepRegion_of_le hs13]
        exact RegionEquivalent.refl (P := P) A
    · by_cases h23 : t < (2/3 : ℝ)
      · -- `1/3 < t < 2/3`
        have ht13 : ¬ t ≤ (1/3 : ℝ) := not_le.mpr (lt_of_le_of_ne (not_lt.mp h13) (Ne.symm ht1))
        have htlo : 0 < t - 1/3 := sub_pos.mpr (lt_of_le_of_ne (not_lt.mp h13) (Ne.symm ht1))
        have hthi : 0 < 2/3 - t := sub_pos.mpr h23
        refine ⟨min (t - 1/3) (2/3 - t), lt_min htlo hthi, ?_, ?_⟩
        · intro s hs
          obtain ⟨hsl, hsh⟩ := abs_lt.mp hs
          have hεa : min (t - 1/3) (2/3 - t) ≤ t - 1/3 := min_le_left _ _
          have hεb : min (t - 1/3) (2/3 - t) ≤ 2/3 - t := min_le_right _ _
          have hs13 : 1/3 < s := by linarith
          have hs23 : s < 2/3 := by linarith
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨ne_of_gt hs13, ne_of_lt hs23⟩
        · intro s hs
          obtain ⟨hsl, hsh⟩ := abs_lt.mp hs
          have hεa : min (t - 1/3) (2/3 - t) ≤ t - 1/3 := min_le_left _ _
          have hεb : min (t - 1/3) (2/3 - t) ≤ 2/3 - t := min_le_right _ _
          have hs13 : 1/3 < s := by linarith
          have hs23 : s < 2/3 := by linarith
          rw [threeStepRegion_of_mid ht13 (le_of_lt h23),
            threeStepRegion_of_mid (not_le.mpr hs13) (le_of_lt hs23)]
          exact RegionEquivalent.refl (P := P) B
      · -- `t > 2/3`
        have ht23 : 2/3 < t := lt_of_le_of_ne (not_lt.mp h23) (Ne.symm ht2)
        refine ⟨t - 2/3, by linarith, ?_, ?_⟩
        · intro s hs
          obtain ⟨hsl, -⟩ := abs_lt.mp hs
          have hs23 : 2/3 < s := by linarith
          have hs13 : 1/3 < s := by linarith
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨ne_of_gt hs13, ne_of_gt hs23⟩
        · intro s hs
          obtain ⟨hsl, -⟩ := abs_lt.mp hs
          have hs23 : 2/3 < s := by linarith
          rw [threeStepRegion_of_gt (not_le.mpr ht23), threeStepRegion_of_gt (not_le.mpr hs23)]
          exact RegionEquivalent.refl (P := P) C
  · -- at `1/3` the family performs the move `A → B`, at `2/3` the move `B → C`
    intro t ht
    have ht' : t = 1/3 ∨ t = 2/3 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using ht
    rcases ht' with rfl | rfl
    · refine ⟨1/3, by norm_num, fun s hs => ?_⟩
      obtain ⟨hsl, hsh⟩ := abs_lt.mp hs
      by_cases hsle : s ≤ (1/3 : ℝ)
      · right
        rw [threeStepRegion_of_le (le_refl (1/3 : ℝ)), threeStepRegion_of_le hsle]
        exact RegionEquivalent.refl (P := P) A
      · left
        have hs23 : s ≤ 2/3 := by linarith
        rw [threeStepRegion_of_le (le_refl (1/3 : ℝ)), threeStepRegion_of_mid hsle hs23]
        exact hAB
    · have hnot13 : ¬ (2/3 : ℝ) ≤ 1/3 := by norm_num
      have hreg : threeStepRegion A B C (2/3) = B :=
        threeStepRegion_of_mid hnot13 (le_refl (2/3 : ℝ))
      refine ⟨1/3, by norm_num, fun s hs => ?_⟩
      by_cases hsle1 : s ≤ (1/3 : ℝ)
      · left
        rw [hreg, threeStepRegion_of_le hsle1]
        exact hAB.symm
      · by_cases hsle2 : s ≤ (2/3 : ℝ)
        · right
          rw [hreg, threeStepRegion_of_mid hsle1 hsle2]
          exact RegionEquivalent.refl (P := P) B
        · left
          rw [hreg, threeStepRegion_of_gt hsle2]
          exact hBC
  · exact threeStepRegion_of_le (by norm_num : (0 : ℝ) ≤ 1/3)
  · exact threeStepRegion_of_gt (by norm_num : ¬ (1 : ℝ) ≤ 2/3)

end Work.SurgeryInvariance.Sweep
