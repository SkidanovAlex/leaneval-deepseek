import Mathlib
import Submission.Work.BMF.mr_direct.badDefs
import Submission.Work.BMF.mr_direct.remPolyEnergyLe
import Submission.Work.BMF.mr_direct.wellspaced_cells

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

open MeasureTheory

/-- The mean-square of the remainder polynomial over an arbitrary measurable subset of a
symmetric interval, discretised by `wellspaced_cells` and bounded by `remPolyREnergyLe`. -/
theorem remPolySetEnergy :
    ∃ Crem : ℝ, 0 < Crem ∧
      ∀ (b : ℕ → ℂ), (∀ n, ‖b n‖ ≤ 1) →
      ∀ (P Q K X₁ X₂ : ℝ) (j : ℕ) (S : ℝ) (U : Set ℝ),
        1 ≤ X₁ → 1 ≤ K → 0 ≤ S → X₂ ≤ 4 * X₁ →
        1 ≤ X₁ * Real.exp (-(((j : ℝ) + 1) / K)) →
        MeasurableSet U → U ⊆ Set.Icc (-S) S →
        (∫ t in U, ‖Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2)
          ≤ Crem * (1 + S * Real.exp ((j : ℝ) / K) / X₁) := by
  obtain ⟨C, hCpos, hE⟩ := Work.BMF.mr_direct.remPolyREnergyLe
  refine ⟨4 * C, by positivity, ?_⟩
  intro b hb P Q K X₁ X₂ j S U hX₁ hK hS hX₂ hA hUmeas hUsub
  -- the integrand
  set g : ℝ → ℝ := fun t => ‖Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2 with hg
  have hgcont : Continuous g := by
    rw [hg]
    refine Continuous.pow ?_ 2
    refine Continuous.norm ?_
    unfold Work.BMF.mrDirect.remPolyR
    refine continuous_finsetSum _ fun m hm => ?_
    have hm1 : 1 ≤ m := by
      rw [Work.BMF.natIcc, Finset.mem_Icc] at hm
      have hceil : 1 ≤ ⌈X₁ * Real.exp (-((j : ℝ) + 1) / K)⌉₊ := by
        rw [Nat.one_le_ceil_iff]
        exact lt_of_lt_of_le zero_lt_one (by simpa only [neg_div] using hA)
      omega
    exact Continuous.mul (Continuous.mul continuous_const continuous_const)
      (Work.BMF.mr_direct.continuous_cpow_neg_one_sub hm1)
  have hgnn : ∀ x, 0 ≤ g x := by intro x; rw [hg]; positivity
  have hnegS_le_S : -S ≤ S := by linarith
  obtain ⟨R₁, R₂, t₁, t₂, ht₁mem, ht₂mem, ht₁sep, ht₂sep, hint⟩ :=
    Work.BMF.mr_direct.wellspaced_cells g hgcont hgnn hnegS_le_S hUmeas hUsub
  have hhint : (∫ t in U, ‖Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2)
      ≤ 2 * ((∑ i, ‖Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j (t₁ i)‖ ^ 2)
        + (∑ i, ‖Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j (t₂ i)‖ ^ 2)) := by
    simpa only [hg] using hint
  have h1 := hE b hb P Q K X₁ X₂ j S R₁ t₁ hX₁ hK hS hX₂ hA
    (fun i => hUsub (ht₁mem i)) ht₁sep
  have h2 := hE b hb P Q K X₁ X₂ j S R₂ t₂ hX₁ hK hS hX₂ hA
    (fun i => hUsub (ht₂mem i)) ht₂sep
  calc (∫ t in U, ‖Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2)
      ≤ 2 * ((∑ i, ‖Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j (t₁ i)‖ ^ 2)
          + (∑ i, ‖Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j (t₂ i)‖ ^ 2)) := hhint
    _ ≤ 2 * (C * (1 + S * Real.exp ((j : ℝ) / K) / X₁)
          + C * (1 + S * Real.exp ((j : ℝ) / K) / X₁)) := by linarith
    _ = 4 * C * (1 + S * Real.exp ((j : ℝ) / K) / X₁) := by ring

end Work.BMF.mr_direct
