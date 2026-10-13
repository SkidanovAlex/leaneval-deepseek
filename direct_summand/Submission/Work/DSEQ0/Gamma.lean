import Mathlib
import Submission.Work.DSMap.Map

/-!
# `Work.DSEQ0`: the sections of the structure sheaf as an explicit type

The scoped notation `Γ(X, U)` (from `open scoped AlgebraicGeometry`) is not available in every
context in which the lemmas of this area are *stated* (for instance inside the statement checker
used for delegation, which only imports the modules named in `depends_on`).  This file provides
the same type as an explicit abbreviation, so that statements about `Γ(X, ⊤)` can be written
without the notation: `Work.DSEQ0.GammaTop X` is definitionally `↥(X.presheaf.obj (op ⊤))`.
-/

universe a

namespace Work.DSEQ0

/-- The ring of global sections `Γ(X, ⊤)` of a scheme, as an explicit type (no notation). -/
abbrev GammaTop (X : AlgebraicGeometry.Scheme.{a}) : Type a :=
  ↥(X.presheaf.obj (Opposite.op (⊤ : X.Opens)))

end Work.DSEQ0
