/-
Area DSCOH (curric-46) — the normalization comparison: the tuple-level data of the homotopy.

For a nondecreasing tuple `y : Fin (k+2) → ι` which is not strictly increasing we introduce

* `frA y` : the position of the first repeat of `y` (an element of `Fin (k+1)`);
* `frV y` : the value `y (frA y)`, the first value occurring twice;
* `frA2 y` : the last position of `y` carrying the value `frV y` (so that the positions
  `frA y, …, frA2 y` are exactly the block of entries equal to `frV y`).

The homotopy `semiHom` reads, on a nondecreasing tuple `z`, the component of the cochain at the
index obtained by duplicating the first repeat of `z`; when the component of `semiHom ≫ semiD` is
computed at an index `y`, the read index attached to the deletion position `b` is `readD y b`
(with sign `signD y b`), and the read index attached to the second differential at the position
`c` is `readH y c` (with sign `signH y c`).  The basic properties of these read indices and signs
are stated in `HomoStruct`-lemmas; they are the combinatorial input of the homotopy identity.
-/
import Submission.Work.DSCOH.Norm.HomoDefs

namespace Work.DSCOH.Norm

open CategoryTheory Limits Opposite TopologicalSpace
open scoped Simplicial BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

universe u v w

variable {X : Type u} [TopologicalSpace X] {A : Type v} [CommRing A]
variable {ι : Type w} [LinearOrder ι]

/-- The position of the first repeat of a nondecreasing tuple which is not strictly increasing. -/
noncomputable def frA {k : ℕ} (y : Fin (k + 2) → ι) (hy : Monotone y) (hh : ¬ StrictMono y) :
    Fin (k + 1) :=
  firstRepeat y hy hh

/-- The first value which occurs twice in `y` (at the positions `frA y` and `frA y + 1`). -/
noncomputable def frV {k : ℕ} (y : Fin (k + 2) → ι) (hy : Monotone y) (hh : ¬ StrictMono y) : ι :=
  y (frA y hy hh).castSucc

/-- The last position of `y` which carries the value `frV y`. -/
noncomputable def frA2 {k : ℕ} (y : Fin (k + 2) → ι) (hy : Monotone y) (hh : ¬ StrictMono y) :
    Fin (k + 2) :=
  (Finset.univ.filter (fun i : Fin (k + 2) => y i = frV y hy hh)).max' (by
    refine ⟨(frA y hy hh).castSucc, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩)

/-- The read index of the `b`-th term of the first differential: the deletion of `b` followed by
the duplication of the first repeat of the resulting tuple (zero terms are given the junk value
`y`). -/
noncomputable def readD {k : ℕ} (y : Fin (k + 2) → ι) (hy : Monotone y) (hh : ¬ StrictMono y)
    (b : Fin (k + 2)) : Fin (k + 2) → ι :=
  if hz : StrictMono (del y b) then y
  else dup (del y b) (firstRepeat (del y b) (monotone_del y b hy) hz).castSucc

/-- The sign of the `b`-th term of the first differential (zero if the term vanishes). -/
noncomputable def signD {k : ℕ} (y : Fin (k + 2) → ι) (hy : Monotone y) (hh : ¬ StrictMono y)
    (b : Fin (k + 2)) : ℤ :=
  if hz : StrictMono (del y b) then 0
  else (-1 : ℤ) ^ ((b : ℕ) + (firstRepeat (del y b) (monotone_del y b hy) hz : ℕ))

/-- The read index of the `c`-th term of the second differential: the duplication of the first
repeat of `y`, followed by the deletion of the position `c`. -/
noncomputable def readH {k : ℕ} (y : Fin (k + 2) → ι) (hy : Monotone y) (hh : ¬ StrictMono y)
    (c : Fin (k + 3)) : Fin (k + 2) → ι :=
  del (dup y (frA y hy hh).castSucc) c

/-- The sign of the `c`-th term of the second differential. -/
noncomputable def signH {k : ℕ} (y : Fin (k + 2) → ι) (hy : Monotone y) (hh : ¬ StrictMono y)
    (c : Fin (k + 3)) : ℤ :=
  (-1 : ℤ) ^ ((frA y hy hh : ℕ) + (c : ℕ))

end Work.DSCOH.Norm
