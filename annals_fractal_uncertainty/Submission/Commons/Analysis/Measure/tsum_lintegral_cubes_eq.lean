import Mathlib
import Submission.Commons.Analysis.Measure.linearForm_level_volume_zero

namespace Commons.Analysis.Measure

open MeasureTheory Metric Set

/-- A coordinate hyperplane `{x : Fin d → ℝ | x i₀ = p}` has Lebesgue measure zero.

This is the special case of `Commons.Analysis.Measure.linearForm_level_volume_zero` for the
linear form `x ↦ x i₀` (an integer linear form with a single non-zero coefficient). -/
private lemma volume_coord_eq_zero {d : ℕ} (i0 : Fin d) (p : ℝ) :
    (volume : Measure (Fin d → ℝ)) {x | x i0 = p} = 0 := by
  have h := linearForm_level_volume_zero
      (fun i : Fin d => if i = i0 then (1 : ℤ) else 0) ⟨i0, by simp⟩ p
  have hset : {x : Fin d → ℝ | x i0 = p}
      = {y : Fin d → ℝ | ∑ i, ((if i = i0 then (1 : ℤ) else 0 : ℤ) : ℝ) * y i = p} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    rw [show (∑ i, ((if i = i0 then (1 : ℤ) else 0 : ℤ) : ℝ) * x i) = x i0 from by
      rw [Finset.sum_eq_single i0]
      · simp
      · intro j _ hj; simp [hj]
      · intro h; exact absurd (Finset.mem_univ i0) h]
  rw [hset]; exact h

/-- Two distinct cells `∏ᵢ [2nᵢ+γᵢ, 2nᵢ+γᵢ+2]` and `∏ᵢ [2mᵢ+γᵢ, 2mᵢ+γᵢ+2]` of the `2ℤ^d`
lattice meet in a null set: the cells are unit boxes of the lattice shifted by `γ`, and two
distinct such boxes overlap at most along a coordinate hyperplane. -/
private lemma volume_cell_inter_eq_zero {d : ℕ} (γ : Fin d → ℝ) (n m : Fin d → ℤ) (hnm : n ≠ m) :
    (volume : Measure (Fin d → ℝ))
      (Set.pi Set.univ (fun i => Set.Icc (2 * (n i : ℝ) + γ i) (2 * (n i : ℝ) + γ i + 2))
        ∩ Set.pi Set.univ (fun i => Set.Icc (2 * (m i : ℝ) + γ i) (2 * (m i : ℝ) + γ i + 2))) = 0 := by
  -- some coordinate differs
  obtain ⟨i0, hi0⟩ : ∃ i, n i ≠ m i := by
    by_contra h; push Not at h; exact hnm (funext h)
  have key : (volume : Measure (Fin d → ℝ))
      (Set.pi Set.univ (fun i => Set.Icc (2 * (n i : ℝ) + γ i) (2 * (n i : ℝ) + γ i + 2))
        ∩ Set.pi Set.univ (fun i => Set.Icc (2 * (m i : ℝ) + γ i) (2 * (m i : ℝ) + γ i + 2))) ≤ 0 := by
    rcases lt_or_gt_of_ne hi0 with hlt | hgt
    · -- `n i0 < m i0`: the intersection is contained in the hyperplane `x i0 = 2 n i0 + γ i0 + 2`
      have hsub : Set.pi Set.univ (fun i => Set.Icc (2 * (n i : ℝ) + γ i) (2 * (n i : ℝ) + γ i + 2))
          ∩ Set.pi Set.univ (fun i => Set.Icc (2 * (m i : ℝ) + γ i) (2 * (m i : ℝ) + γ i + 2))
          ⊆ {x : Fin d → ℝ | x i0 = 2 * (n i0 : ℝ) + γ i0 + 2} := by
        intro x hx
        have hxn := Set.mem_univ_pi.mp hx.1 i0
        have hxm := Set.mem_univ_pi.mp hx.2 i0
        rw [Set.mem_Icc] at hxn hxm
        simp only [Set.mem_ofPred_eq]
        have h1 : ((n i0 : ℤ) : ℝ) + 1 ≤ (m i0 : ℝ) := by
          have : n i0 + 1 ≤ m i0 := Int.add_one_le_iff.mpr hlt
          exact_mod_cast this
        have h2 : 2 * (n i0 : ℝ) + γ i0 + 2 ≤ 2 * (m i0 : ℝ) + γ i0 := by linarith
        linarith [hxn.2, hxm.1]
      calc (volume : Measure (Fin d → ℝ)) _
          ≤ volume {x : Fin d → ℝ | x i0 = 2 * (n i0 : ℝ) + γ i0 + 2} := measure_mono hsub
        _ = 0 := volume_coord_eq_zero i0 _
    · -- `m i0 < n i0`: symmetric case
      have hsub : Set.pi Set.univ (fun i => Set.Icc (2 * (n i : ℝ) + γ i) (2 * (n i : ℝ) + γ i + 2))
          ∩ Set.pi Set.univ (fun i => Set.Icc (2 * (m i : ℝ) + γ i) (2 * (m i : ℝ) + γ i + 2))
          ⊆ {x : Fin d → ℝ | x i0 = 2 * (m i0 : ℝ) + γ i0 + 2} := by
        intro x hx
        have hxn := Set.mem_univ_pi.mp hx.1 i0
        have hxm := Set.mem_univ_pi.mp hx.2 i0
        rw [Set.mem_Icc] at hxn hxm
        simp only [Set.mem_ofPred_eq]
        have h1 : ((m i0 : ℤ) : ℝ) + 1 ≤ (n i0 : ℝ) := by
          have : m i0 + 1 ≤ n i0 := Int.add_one_le_iff.mpr hgt
          exact_mod_cast this
        have h2 : 2 * (m i0 : ℝ) + γ i0 + 2 ≤ 2 * (n i0 : ℝ) + γ i0 := by linarith
        linarith [hxm.2, hxn.1]
      calc (volume : Measure (Fin d → ℝ)) _
          ≤ volume {x : Fin d → ℝ | x i0 = 2 * (m i0 : ℝ) + γ i0 + 2} := measure_mono hsub
        _ = 0 := volume_coord_eq_zero i0 _
  exact le_antisymm key (by simp)

/-- The boxes `∏ᵢ [a n i, a n i + 2c₁]`, one inside each cell `∏ᵢ [2nᵢ+γᵢ, 2nᵢ+γᵢ+2]` of the
`2ℤ^d` lattice, are essentially disjoint, so the sum of the `lintegral`s over them equals the
`lintegral` over their union. -/
theorem tsum_lintegral_cubes_eq {d : ℕ} {c₁ : ℝ} (hc₁ : 0 ≤ c₁) (γ : Fin d → ℝ)
    (a : (Fin d → ℤ) → Fin d → ℝ)
    (ha : ∀ n : Fin d → ℤ, ∀ i : Fin d,
      2 * (n i : ℝ) + γ i ≤ a n i ∧ a n i + 2 * c₁ ≤ 2 * (n i : ℝ) + γ i + 2)
    (f : (Fin d → ℝ) → ENNReal) :
    ∑' n : Fin d → ℤ,
        ∫⁻ x in Set.pi Set.univ (fun i : Fin d => Set.Icc (a n i) (a n i + 2 * c₁)), f x
      = ∫⁻ x in ⋃ n : Fin d → ℤ,
          Set.pi Set.univ (fun i : Fin d => Set.Icc (a n i) (a n i + 2 * c₁)), f x := by
  classical
  have _hc₁ : (0 : ℝ) ≤ c₁ := hc₁
  -- Each box lies in the corresponding lattice cell `∏ᵢ [2nᵢ+γᵢ, 2nᵢ+γᵢ+2]`.
  have hsub_cell : ∀ n : Fin d → ℤ,
      Set.pi Set.univ (fun i : Fin d => Set.Icc (a n i) (a n i + 2 * c₁))
        ⊆ Set.pi Set.univ (fun i : Fin d => Set.Icc (2 * (n i : ℝ) + γ i) (2 * (n i : ℝ) + γ i + 2)) := by
    intro n x hx
    have hx' : ∀ i : Fin d, x i ∈ Set.Icc (a n i) (a n i + 2 * c₁) := Set.mem_univ_pi.mp hx
    refine Set.mem_univ_pi.mpr fun i => ?_
    have h := ha n i
    have hxi := hx' i
    rw [Set.mem_Icc] at hxi ⊢
    exact ⟨le_trans h.1 hxi.1, le_trans hxi.2 h.2⟩
  refine (lintegral_iUnion₀
    (μ := (volume : Measure (Fin d → ℝ)))
    (s := fun n : Fin d → ℤ => Set.pi Set.univ (fun i : Fin d => Set.Icc (a n i) (a n i + 2 * c₁)))
    (fun n => (MeasurableSet.pi Set.countable_univ (fun i _ => measurableSet_Icc)).nullMeasurableSet)
    (fun n m hnm => ?_) f).symm
  -- Essential disjointness of the boxes.
  unfold AEDisjoint
  apply le_antisymm _ (by simp)
  calc (volume : Measure (Fin d → ℝ))
        (Set.pi Set.univ (fun i : Fin d => Set.Icc (a n i) (a n i + 2 * c₁))
          ∩ Set.pi Set.univ (fun i : Fin d => Set.Icc (a m i) (a m i + 2 * c₁)))
      ≤ volume (Set.pi Set.univ (fun i => Set.Icc (2 * (n i : ℝ) + γ i) (2 * (n i : ℝ) + γ i + 2))
          ∩ Set.pi Set.univ (fun i => Set.Icc (2 * (m i : ℝ) + γ i) (2 * (m i : ℝ) + γ i + 2))) :=
        measure_mono (Set.inter_subset_inter (hsub_cell n) (hsub_cell m))
    _ = 0 := volume_cell_inter_eq_zero γ n m hnm

end Commons.Analysis.Measure
