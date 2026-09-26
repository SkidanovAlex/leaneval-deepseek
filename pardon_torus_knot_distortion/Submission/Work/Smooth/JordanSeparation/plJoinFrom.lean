import Mathlib
import Submission.Work.Smooth.JordanSeparation.plApprox
import Submission.Work.Smooth.JordanSeparation.plSplit

/-!
# The indexed join `joinNatFrom` (step (B))

`exists_polygonal_homotopic` (step (A)) represents a loop as the join `joinNat F N` of its chords.
To cut such a join at a repeated *vertex* `p i = p j` one needs the join of the chords from index
`i` to index `j`, and the two-sided splitting

  `joinNat F (i + (j + k)) ~ ((joinNat F i) · (join of the next j)) · (join of the last k)`.

The naive formulation of the shifted family (`fun l => F (i + j + l)`) does **not** elaborate:
`joinNat`'s type demands `Path (p (i+j+l)) (p (i+j+(l+1)))` while `F (i+j+l)` has type
`Path (p (i+j+l)) (p ((i+j+l)+1))`, and these endpoints differ by `Nat.add_assoc`, which is not
definitional.

The fix implemented here is to absorb that associativity **once**, in the definition of the shifted
family, and then to reuse the already-proved `joinNat_add` verbatim:

* `joinNatShift F i` — the family of paths `F (i+l)`, with the endpoints of the `l`-th member
  re-labelled as `p (i+l) → p (i+(l+1))` (the `Path.cast` discharges exactly one `Nat.add_assoc`);
* `joinNatFrom F i j` — the join of `F i, …, F (i+j-1)`, a path `p i → p (i+j)`;
* `joinNatFrom_add` — the two-sided splitting, immediate from `joinNat_add (joinNatShift F i)`.

Still to come (small, fiddly): the link back to step (A), `joinNatFrom F 0 j = joinNat F j`, which
needs `Eq.ndrec`-transport along `Nat.zero_add` (the index `0 + l` is only propositionally equal to
`l`, so `congrArg F` does not apply).
-/

namespace Work.Smooth.JordanSeparation

noncomputable section

variable {X : Type*} [TopologicalSpace X]

/-- The family `F` shifted by `i`: the `l`-th member is `F (i + l)`, with its endpoints re-labelled
from `p (i+l) → p ((i+l)+1)` to `p (i+l) → p (i+(l+1))`. -/
def joinNatShift {p : ℕ → X} (F : ∀ k, Path (p k) (p (k + 1))) (i : ℕ) :
    ∀ l, Path (p (i + l)) (p (i + (l + 1))) :=
  fun l => Path.cast (F (i + l)) rfl (congrArg p (Nat.add_assoc i l 1).symm)

/-- The join of the paths `F i, F (i+1), …, F (i+j-1)`: a path from `p i` to `p (i + j)`. -/
def joinNatFrom {p : ℕ → X} (F : ∀ k, Path (p k) (p (k + 1))) (i j : ℕ) :
    Path (p i) (p (i + j)) :=
  joinNat (joinNatShift F i) j

/-- **Splitting the indexed join (two-sided).**  The join of `j + k` paths starting at `i` is the
join of the first `j` followed by the join of the last `k`.  This is `joinNat_add` applied to the
shifted family. -/
theorem joinNatFrom_add {p : ℕ → X} (F : ∀ k, Path (p k) (p (k + 1))) (i j k : ℕ) :
    Path.Homotopic (joinNatFrom F i (j + k))
      ((joinNatFrom F i j).trans
        (joinNat (p := fun l => p (i + (j + l))) (fun l => joinNatShift F i (j + l)) k)) :=
  joinNat_add (joinNatShift F i) j k

end

end Work.Smooth.JordanSeparation
