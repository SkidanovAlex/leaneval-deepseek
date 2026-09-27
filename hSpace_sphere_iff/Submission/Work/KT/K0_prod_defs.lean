import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic

/-!
# Shared definitions for `Work.KT.K0_prod`

`K₀(R × S) ≅ K₀(R) × K₀(S)`: the two "diagonal" embeddings of matrices.
`diagA`/`diagB` view a matrix over `A` (resp. `B`) as a matrix over `A × B` with the other
component zero; they induce the two summands of the inverse map.  `zeroMat` is the zero matrix
of a given size, used to pad matrices so that block sums have matching size.
-/

namespace Work.KT

open _root_.Matrix

noncomputable section

/-- The zero matrix of size `n` (as an element of `Mat R`). -/
abbrev zeroMat (R : Type) [Ring R] (n : ℕ) : Mat R := ⟨n, 0⟩

/-- View a matrix over `A` as a matrix over `A × B` with zero `B`-component. -/
abbrev diagA (A B : Type) [Ring A] [Ring B] (p : Mat A) : Mat (A × B) :=
  ⟨p.1, fun i j => (p.2 i j, 0)⟩

/-- View a matrix over `B` as a matrix over `A × B` with zero `A`-component. -/
abbrev diagB (A B : Type) [Ring A] [Ring B] (q : Mat B) : Mat (A × B) :=
  ⟨q.1, fun i j => (0, q.2 i j)⟩

end

end Work.KT
