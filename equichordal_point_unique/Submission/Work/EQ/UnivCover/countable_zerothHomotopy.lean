import Mathlib

namespace Work.EQ.UnivCover

/-- In a second-countable, locally path-connected space `X`, any open subset `W` has only
countably many path components; equivalently the zeroth homotopy `ZerothHomotopy W` is
countable.

The path components of `W` (which is locally path-connected as an open subspace) are
nonempty open pairwise disjoint subsets of `W`; in a separable space such a family is
countable. -/
theorem countable_zerothHomotopy {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [LocallyPathConnectedSpace X] {W : Set X} (hW : IsOpen W) :
    Countable (ZerothHomotopy ↥W) := by
  have : LocallyPathConnectedSpace ↥W := hW.locallyPathConnectedSpace
  -- Attach to each path component of `W` (i.e. each element of the zeroth homotopy) the
  -- corresponding subset of `W`.
  let s : ZerothHomotopy ↥W → Set ↥W :=
    ZerothHomotopy.lift (fun x => pathComponent x) (fun x y p => by
      apply pathComponent_congr
      exact mem_pathComponent_iff.mpr (Joined.symm (Nonempty.intro p)))
  refine Pairwise.countable_of_isOpen_disjoint (s := s) ?_ ?_ ?_
  · -- Distinct path components are disjoint.
    intro c c' hcc'
    obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective c
    obtain ⟨y, rfl⟩ := ZerothHomotopy.mk_surjective c'
    show Disjoint (s (ZerothHomotopy.mk x)) (s (ZerothHomotopy.mk y))
    rw [Set.disjoint_left]
    intro z hz hz'
    change z ∈ pathComponent x at hz
    change z ∈ pathComponent y at hz'
    rw [mem_pathComponent_iff] at hz hz'
    exact hcc' (ZerothHomotopy.sound (Classical.choice (hz.trans hz'.symm)))
  · -- Each path component is open.
    intro c
    obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective c
    change IsOpen (pathComponent x)
    exact IsOpen.pathComponent x
  · -- Each path component is nonempty.
    intro c
    obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective c
    change (pathComponent x).Nonempty
    exact pathComponent.nonempty x

end Work.EQ.UnivCover
