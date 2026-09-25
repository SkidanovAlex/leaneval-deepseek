import Mathlib

open Filter Finset

namespace Work.BourgainPlan.IonescuWainger

/-- The symmetric integer intervals `Icc (-j) j` are monotone and cofinal in the directed
family of finite subsets of `ℤ`, hence converge to `atTop` on `Finset ℤ`. -/
lemma tendsto_Icc_neg_atTop :
    Filter.Tendsto (fun j : ℕ => Finset.Icc (-(j : ℤ)) (j : ℤ)) Filter.atTop Filter.atTop := by
  apply tendsto_atTop_finset_of_monotone
  · intro a b hab
    apply Finset.Icc_subset_Icc
    · exact neg_le_neg (Int.ofNat_le.mpr hab)
    · exact Int.ofNat_le.mpr hab
  · intro x
    refine ⟨x.natAbs, ?_⟩
    rw [Finset.mem_Icc]
    constructor
    · have h := Int.le_natAbs (a := -x)
      rw [Int.natAbs_neg] at h
      exact neg_le.mp h
    · exact Int.le_natAbs

theorem tendsto_sum_Icc_atTop_tsum {g : ℤ → ℂ} (hg : Summable g) :
    Filter.Tendsto (fun j : ℕ => ∑ i ∈ Finset.Icc (-(j : ℤ)) (j : ℤ), g i)
      Filter.atTop (nhds (∑' i : ℤ, g i)) := by
  have h := (show Tendsto (fun s : Finset ℤ => ∑ i ∈ s, g i) Filter.atTop
      (nhds (∑' i : ℤ, g i)) from hg.hasSum).comp tendsto_Icc_neg_atTop
  change Tendsto ((fun s : Finset ℤ => ∑ i ∈ s, g i) ∘
      fun j : ℕ => Finset.Icc (-(j : ℤ)) (j : ℤ)) Filter.atTop (nhds (∑' i : ℤ, g i)) at h
  exact h

end Work.BourgainPlan.IonescuWainger
