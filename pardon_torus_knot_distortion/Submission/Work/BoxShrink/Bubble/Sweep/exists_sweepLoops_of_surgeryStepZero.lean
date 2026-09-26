import Mathlib
import Submission.Work.SurgeryInvariance.All

/-!
# A single zero-winding surgery is a loop-level sweep

`Work.SurgeryInvariance.SurgeryStepZero P A B` is a single local move of a family of spheres: the
region `F ∩ int(S_t)` changes by adding or removing an open piece of zero winding span.  This file
turns that single move into an honest loop-level sweep (`SweepLoops P`) whose region at time `0` is
`A` and whose region at time `1` is `B`, by the piecewise constant family

  `region t = A` for `t ≤ 1/2`,  `region t = B` for `1/2 < t`,

with exceptional parameter `1/2`.  Away from `1/2` the family is constant, hence transports loops
(`RegionEquivalent`); at `1/2` it performs the move `A → B`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Bubble.Sweep

/-- The piecewise constant family of regions with a single break point at `1/2`: `A` up to `1/2`,
`B` from `1/2` on. -/
def oneStepRegion (A B : Set R3) : ℝ → Set R3 :=
  fun t => if t ≤ (1 / 2 : ℝ) then A else B

lemma oneStepRegion_of_le {A B : Set R3} {t : ℝ} (h : t ≤ (1 / 2 : ℝ)) :
    oneStepRegion A B t = A := by
  unfold oneStepRegion
  rw [if_pos h]

lemma oneStepRegion_of_gt {A B : Set R3} {t : ℝ} (h : ¬ t ≤ (1 / 2 : ℝ)) :
    oneStepRegion A B t = B := by
  unfold oneStepRegion
  rw [if_neg h]

theorem exists_sweepLoops_of_surgeryStepZero {P : Work.CoreTopology.ParamTorus}
    {A B : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (h : Work.SurgeryInvariance.SurgeryStepZero P A B) :
    ∃ S : Work.SurgeryInvariance.SweepLoops P, S.region 0 = A ∧ S.region 1 = B := by
  classical
  refine ⟨⟨oneStepRegion A B, ({1 / 2} : Finset ℝ), ?_, ?_⟩, ?_, ?_⟩
  · -- away from the exceptional parameter the family is locally constant
    intro t ht
    have ht' : t ≠ 1 / 2 := fun hc => ht (by rw [hc]; simp)
    by_cases hlt : t < (1 / 2 : ℝ)
    · -- `t < 1/2`
      refine ⟨1 / 2 - t, by linarith, ?_, ?_⟩
      · intro s hs
        obtain ⟨-, hsh⟩ := abs_lt.mp hs
        have hs' : s < 1 / 2 := by linarith
        simp only [Finset.mem_singleton]
        exact ne_of_lt hs'
      · intro s hs
        obtain ⟨-, hsh⟩ := abs_lt.mp hs
        have hs' : s ≤ 1 / 2 := le_of_lt (by linarith : s < (1 / 2 : ℝ))
        rw [oneStepRegion_of_le (le_of_lt hlt), oneStepRegion_of_le hs']
        exact Work.SurgeryInvariance.RegionEquivalent.refl (P := P) A
    · -- `t > 1/2`
      have hgt : (1 / 2 : ℝ) < t := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm ht')
      refine ⟨t - 1 / 2, by linarith, ?_, ?_⟩
      · intro s hs
        obtain ⟨hsl, -⟩ := abs_lt.mp hs
        have hs' : (1 / 2 : ℝ) < s := by linarith
        simp only [Finset.mem_singleton]
        exact ne_of_gt hs'
      · intro s hs
        obtain ⟨hsl, -⟩ := abs_lt.mp hs
        have hs' : (1 / 2 : ℝ) < s := by linarith
        rw [oneStepRegion_of_gt (not_le.mpr hgt), oneStepRegion_of_gt (not_le.mpr hs')]
        exact Work.SurgeryInvariance.RegionEquivalent.refl (P := P) B
  · -- at the exceptional parameter the family performs the move `A → B`
    intro t ht
    have ht' : t = 1 / 2 := by simpa only [Finset.mem_singleton] using ht
    subst ht'
    refine ⟨1 / 2, by norm_num, fun s hs => ?_⟩
    obtain ⟨hsl, hsh⟩ := abs_lt.mp hs
    by_cases hsle : s ≤ (1 / 2 : ℝ)
    · right
      rw [oneStepRegion_of_le (le_refl (1 / 2 : ℝ)), oneStepRegion_of_le hsle]
      exact Work.SurgeryInvariance.RegionEquivalent.refl (P := P) A
    · left
      rw [oneStepRegion_of_le (le_refl (1 / 2 : ℝ)), oneStepRegion_of_gt hsle]
      exact h
  · exact oneStepRegion_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)
  · exact oneStepRegion_of_gt (by norm_num : ¬ (1 : ℝ) ≤ 1 / 2)

end Work.BoxShrink.Bubble.Sweep
