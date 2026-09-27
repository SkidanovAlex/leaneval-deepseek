import Mathlib

/-!
# The frame space of the Whitney-disc construction

The Whitney move is built from the normal bundle of the Whitney disc.  Along the disc's boundary the
two sheets of the immersion prescribe a *splitting* of that normal bundle into two `(n-1)`-plane
fields; the move is possible exactly because this boundary datum extends over the disc, which is the
content of `OppositeType` (the sign hypothesis).

This module only fixes the vocabulary: the **frame space** `Work.Drive.Whitney.Frame k`, the space of
orthonormal `k`-frames of `EuclideanSpace ℝ (Fin k)` (i.e. a concrete model of the orthogonal group
`O(k)`), with the subspace topology coming from the ambient function space (it is an `abbrev`, so that
instance search sees through it).  Everything else in the
construction (the splitting of a `(2n-2)`-frame into its first `n-1` and last `n-1` vectors, the
transport of the geometric boundary datum into the frame space along a trivialisation of the normal
bundle) is built on top of it.
-/

namespace Work.Drive.Whitney

open scoped ContDiff

/-- **The frame space**: orthonormal `k`-frames of `EuclideanSpace ℝ (Fin k)`.  As a subtype of
`Fin k → EuclideanSpace ℝ (Fin k)` it carries the subspace topology, so a "continuous family of
frames" is literally a continuous map into this type. -/
abbrev Frame (k : ℕ) : Type :=
  {F : Fin k → EuclideanSpace ℝ (Fin k) //
    (∀ i : Fin k, ‖F i‖ = 1) ∧ (∀ i j : Fin k, i ≠ j → inner ℝ (F i) (F j) = 0)}

/-- The underlying frame of an element of the frame space. -/
def Frame.toFun {k : ℕ} (F : Frame k) : Fin k → EuclideanSpace ℝ (Fin k) := F.1

/-- The vectors of a frame are unit vectors. -/
theorem Frame.norm_eq_one {k : ℕ} (F : Frame k) (i : Fin k) : ‖F.1 i‖ = 1 := F.2.1 i

/-- The vectors of a frame are pairwise orthogonal. -/
theorem Frame.inner_eq_zero {k : ℕ} (F : Frame k) {i j : Fin k} (hij : i ≠ j) :
    inner ℝ (F.1 i) (F.1 j) = 0 := F.2.2 i j hij

end Work.Drive.Whitney
