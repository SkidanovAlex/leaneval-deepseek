import Mathlib
import Submission.Work.Diff.STE.periodization_contDiff_periodic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

/-- An integer vector as a real vector is the corresponding `ℤ`-linear combination of the
coordinate unit vectors. -/
lemma iVec_eq_sum_smul_single {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → ℤ) :
    Work.Diff.STE.iVec m = ∑ i : ι, (m i) • Pi.single i (1 : ℝ) := by
  funext j
  simp [Finset.sum_apply, Pi.single_apply, Work.Diff.STE.iVec]

/-- **`Periodic1` iterates to invariance under every integer translation.**  A function which is
`1`-periodic in every coordinate is invariant under translation by `iVec m` for any
`m : ι → ℤ`. -/
theorem Periodic1_iVec {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*}
    {f : (ι → ℝ) → β} (hf : Work.Diff.STE.Periodic1 f) (m : ι → ℤ) (x : ι → ℝ) :
    f (x + Work.Diff.STE.iVec m) = f x := by
  classical
  -- periodicity by each single integer multiple of a coordinate unit vector
  have hsingle : ∀ i : ι, Function.Periodic f ((m i) • Pi.single i (1 : ℝ)) :=
    fun i => (show Function.Periodic f (Pi.single i (1 : ℝ)) from hf i).zsmul (m i)
  -- and hence by any finite sum of them (periodicity is closed under addition)
  have key : Function.Periodic f (∑ i : ι, (m i) • Pi.single i (1 : ℝ)) := by
    have hgen : ∀ s : Finset ι,
        Function.Periodic f (∑ i ∈ s, (m i) • Pi.single i (1 : ℝ)) := by
      intro s
      refine Finset.induction ?base ?step s
      · simp
      · intro a s ha ih
        rw [Finset.sum_insert ha]
        exact (hsingle a).add_period ih
    simpa using hgen Finset.univ
  rw [iVec_eq_sum_smul_single]
  exact key x

end Work.Diff.STE.B3
