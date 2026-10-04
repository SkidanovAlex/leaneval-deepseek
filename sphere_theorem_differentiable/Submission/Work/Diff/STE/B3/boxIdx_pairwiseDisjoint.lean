import Mathlib
import Submission.Work.Diff.STE.CSq_periodization_le_of_sup_bound
import Submission.Work.Diff.STE.periodization_contDiff_periodic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

/-- The cubes `k + (0,1]^ι`, for the lattice vectors `k ∈ {-1,0}^ι`, are pairwise disjoint.

Indeed, if `k ≠ k'` then there is a coordinate `i` with `k i ≠ k' i`, and (as both coordinates lie
in `{-1, 0}`) this forces `k i = -1, k' i = 0` or `k i = 0, k' i = -1`.  If the two translated
cubes met at a point `x`, then in the coordinate `i` we would have
`y i + k i = y' i + k' i` with `y i, y' i ∈ (0,1]`, i.e. `y i - y' i = ±1` — impossible since
`|y i - y' i| < 1`. -/
theorem boxIdx_pairwiseDisjoint {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (↑(Work.Diff.STE.csqp_boxIdx ι) : Set (ι → ℤ)).Pairwise
      (Function.onFun Disjoint
        (fun k : ι → ℤ =>
          (fun y : ι → ℝ => y + Work.Diff.STE.iVec k) '' Work.Diff.STE.unitCube)) := by
  intro k hk k' hk' hne
  simp only [Function.onFun]
  -- Two intersecting cubes would give points `y, y'` of the standard cube with
  -- `y + iVec k = y' + iVec k'`.
  rw [Set.disjoint_left]
  rintro x hx hx'
  rw [Set.mem_image] at hx hx'
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨y', hy', hy'eq⟩ := hx'
  -- Membership in the standard cube is a coordinatewise condition `(0,1]`.
  have hmem : ∀ i, y i ∈ Set.Ioc (0 : ℝ) 1 := by
    intro i
    have h := Set.mem_pi.mp hy i (Set.mem_univ i)
    simpa [Work.Diff.STE.unitCube] using h
  have hmem' : ∀ i, y' i ∈ Set.Ioc (0 : ℝ) 1 := by
    intro i
    have h := Set.mem_pi.mp hy' i (Set.mem_univ i)
    simpa [Work.Diff.STE.unitCube] using h
  -- Membership in the box of indices means every coordinate is `-1` or `0`.
  have hkI : ∀ i, -1 ≤ k i ∧ k i ≤ 0 :=
    fun i => Finset.mem_Icc.mp (Work.Diff.STE.csqp_mem_boxIdx.mp hk i)
  have hk'I : ∀ i, -1 ≤ k' i ∧ k' i ≤ 0 :=
    fun i => Finset.mem_Icc.mp (Work.Diff.STE.csqp_mem_boxIdx.mp hk' i)
  -- Pick a coordinate where `k` and `k'` differ.
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ k' i := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hne (funext h)
  have hdiff : (k' i : ℝ) - (k i : ℝ) = 1 ∨ (k' i : ℝ) - (k i : ℝ) = -1 := by
    have h1 : k i = -1 ∨ k i = 0 := by have := hkI i; omega
    have h2 : k' i = -1 ∨ k' i = 0 := by have := hk'I i; omega
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hi
    · left; rw [h1, h2]; norm_num
    · right; rw [h1, h2]; norm_num
    · exact absurd (h1.trans h2.symm) hi
  have hcoord := congr_fun hy'eq i
  simp only [Pi.add_apply, Work.Diff.STE.iVec_apply] at hcoord
  rcases hdiff with h | h
  · linarith [(Set.mem_Ioc.mp (hmem i)).2, (Set.mem_Ioc.mp (hmem' i)).1]
  · linarith [(Set.mem_Ioc.mp (hmem i)).1, (Set.mem_Ioc.mp (hmem' i)).2]

end Work.Diff.STE.B3
