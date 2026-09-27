import Mathlib
import Submission.Work.EKLRelCross.flower

namespace Work.EKLProd

open MeasureTheory

/-- The atom of the pull-back σ-algebra `comap f (borel β)` at `x` is the `f`-fibre of `x`.

Since `β` is `T2` (hence `T1`) and carries its Borel σ-algebra, its singletons are Borel;
hence the fibre `f ⁻¹' {f x}` is measurable in `comap f (borel β)` and contains `x`, and
conversely every `comap f (borel β)`-measurable set containing `x` is a preimage of a Borel
set containing `f x`, hence contains the whole fibre. -/
theorem atom_comap_borel {β : Type*} [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    [T2Space β] [SecondCountableTopology β]
    (f : Work.EKLContract.X3 → β) (x : Work.EKLContract.X3) :
    Work.EKLContract.atom (MeasurableSpace.comap f (borel β)) x =
      {y : Work.EKLContract.X3 | f y = f x} := by
  have hsing : @MeasurableSet β (borel β) ({f x} : Set β) := by
    rw [← BorelSpace.measurable_eq (α := β)]
    exact MeasurableSet.singleton (f x)
  apply Set.Subset.antisymm
  · -- `f ⁻¹' {f x}` is measurable in the comap σ-algebra and contains `x`, so it is one of
    -- the sets intersected to form the atom.
    intro y hy
    have hmem : f ⁻¹' ({f x} : Set β) ∈ {s | @MeasurableSet Work.EKLContract.X3
        (MeasurableSpace.comap f (borel β)) s ∧ x ∈ s} := by
      refine ⟨?_, rfl⟩
      exact MeasurableSpace.measurableSet_comap.mpr ⟨_, hsing, rfl⟩
    exact (Set.mem_sInter.mp hy) _ hmem
  · -- Every measurable set containing `x` is `f ⁻¹' s'` with `s'` Borel and `f x ∈ s'`.
    intro y hy
    simp only [Work.EKLContract.atom, Set.mem_sInter]
    intro s hs
    obtain ⟨s', hs', h⟩ := MeasurableSpace.measurableSet_comap.mp hs.1
    have hx' : f x ∈ s' := by
      have h2 := hs.2
      rw [← h] at h2
      exact h2
    rw [← h]
    show f y ∈ s'
    rw [hy]
    exact hx'

end Work.EKLProd
