import Mathlib
import Submission.Work.Smooth.JordanSeparation.plSplit
import Submission.Work.Smooth.JordanSeparation.plCut
import Submission.Work.Smooth.JordanSeparation.plTransport

/-!
# The loop-level cut (step (B))

The polygonal loop of step (A) is the join `joinNat F N` of the chords `F k : p k → p (k+1)`.
Cutting it at the vertex `p i = p (i+j)` splits it, by `joinNat_add` (`plSplit`) applied twice, as

  `joinNat F (i + (j+k))  ~  (joinNat F i) · (join of the next j chords) · (join of the last k)`.

The index is written `i + (j + k)` throughout, *never* `(i+j)+k`: with that choice the two sides
have the same type and **no** `Nat.add_assoc` cast appears (`plTransport`'s `cast_index` machinery is
consequently not needed here).

The middle piece `M` is a loop at `p i` only *up to* the double point `hpt : p i = p (i+j)`; the
single `Path.cast` that realises this is supplied by the caller in
`nullhomotopic_of_joinNat_cut` below, and being a `Prop`-level cast it is harmless.
-/

namespace Work.Smooth.JordanSeparation

noncomputable section

variable {X : Type*} [TopologicalSpace X]

/-- **The cut, homotopy form.**  The join of `i + (j + k)` chords is homotopic to the composite of
the first `i`, the next `j` and the last `k` chords. -/
theorem joinNat_cut {p : ℕ → X} (F : ∀ k, Path (p k) (p (k + 1))) (i j k : ℕ) :
    Path.Homotopic (joinNat F (i + (j + k)))
      ((joinNat F i).trans
        ((joinNat (p := fun l => p (i + l)) (fun l => F (i + l)) j).trans
          (joinNat (p := fun l => p (i + (j + l))) (fun l => F (i + (j + l))) k))) := by
  refine (joinNat_add F i (j + k)).trans ?_
  exact Path.Homotopic.hcomp (Path.Homotopic.refl _)
    (joinNat_add (p := fun l => p (i + l)) (fun l => F (i + l)) j k)

end

end Work.Smooth.JordanSeparation
