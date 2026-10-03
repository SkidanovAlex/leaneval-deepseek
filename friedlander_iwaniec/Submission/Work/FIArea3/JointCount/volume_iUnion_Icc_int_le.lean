import Mathlib

namespace Work.FIArea3.JointCount

open MeasureTheory Set

noncomputable section

/-- The part of the period-`2π` translate `[α + 2πk, β + 2πk]` of `[α, β]` that falls inside
the fundamental window `(-π, π]`. -/
def periodicPiece (α β : ℝ) (k : ℤ) : Set ℝ :=
  Set.Icc (α + 2 * Real.pi * k) (β + 2 * Real.pi * k) ∩ Set.Ioc (-Real.pi) Real.pi

/-- `periodicPiece α β k` translated back by `2πk`, so that it lies in the window centred at `2πk`.
It is the preimage of `periodicPiece α β k` under the translation `x ↦ x + 2πk`. -/
def unwrappedPiece (α β : ℝ) (k : ℤ) : Set ℝ :=
  (fun x : ℝ => x + 2 * Real.pi * k) ⁻¹' (periodicPiece α β k)

/-- The union over all integer translates of `[α, β]` of the part meeting the fundamental window
`(-π, π]` has measure at most the length `β - α` of the original interval.  Indeed, translating
the `k`-th piece back by `2πk` produces pairwise disjoint subsets of `[α, β]` of equal measure. -/
theorem volume_iUnion_Icc_int_le (α β : ℝ) :
    MeasureTheory.volume (⋃ k : ℤ, (Set.Icc (α + 2 * Real.pi * k) (β + 2 * Real.pi * k)) ∩ Set.Ioc (-Real.pi) Real.pi)
      ≤ ENNReal.ofReal (β - α) := by
  have hmeasure : ∀ k : ℤ, volume (periodicPiece α β k) = volume (unwrappedPiece α β k) := by
    intro k
    rw [unwrappedPiece]
    exact (measure_preimage_add_right volume (2 * Real.pi * (k:ℝ)) _).symm
  have hdisj : Pairwise (Function.onFun Disjoint (unwrappedPiece α β)) := by
    intro k k' h
    change Disjoint (unwrappedPiece α β k) (unwrappedPiece α β k')
    rw [Set.disjoint_left]
    intro x hx hx'
    unfold unwrappedPiece periodicPiece at hx hx'
    rw [Set.mem_preimage, Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioc] at hx hx'
    obtain ⟨⟨-, -⟩, hklo, hkhi⟩ := hx
    obtain ⟨⟨-, -⟩, hk'lo, hk'hi⟩ := hx'
    rcases lt_or_gt_of_ne h with hlt | hgt
    · have hcast : (1:ℝ) ≤ (k':ℝ) - (k:ℝ) := by
        have hsub : (1:ℤ) ≤ k' - k := by omega
        have := (Int.cast_le (R := ℝ)).2 hsub
        push_cast at this
        linarith
      nlinarith [Real.pi_pos]
    · have hcast : (1:ℝ) ≤ (k:ℝ) - (k':ℝ) := by
        have hsub : (1:ℤ) ≤ k - k' := by omega
        have := (Int.cast_le (R := ℝ)).2 hsub
        push_cast at this
        linarith
      nlinarith [Real.pi_pos]
  have hmeas : ∀ k : ℤ, MeasurableSet (unwrappedPiece α β k) := by
    intro k
    rw [unwrappedPiece]
    exact (measurableSet_Icc.inter measurableSet_Ioc).preimage (by fun_prop)
  have hsub : (⋃ k : ℤ, unwrappedPiece α β k) ⊆ Set.Icc α β := by
    intro x hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨k, hk⟩ := hx
    unfold unwrappedPiece periodicPiece at hk
    rw [Set.mem_preimage, Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioc] at hk
    obtain ⟨⟨hl, hr⟩, -, -⟩ := hk
    exact ⟨by linarith, by linarith⟩
  calc volume (⋃ k : ℤ, periodicPiece α β k)
      ≤ ∑' k : ℤ, volume (periodicPiece α β k) := measure_iUnion_le _
    _ = ∑' k : ℤ, volume (unwrappedPiece α β k) := tsum_congr hmeasure
    _ = volume (⋃ k : ℤ, unwrappedPiece α β k) := (measure_iUnion hdisj hmeas).symm
    _ ≤ volume (Set.Icc α β) := measure_mono hsub
    _ = ENNReal.ofReal (β - α) := Real.volume_Icc

end

end Work.FIArea3.JointCount
