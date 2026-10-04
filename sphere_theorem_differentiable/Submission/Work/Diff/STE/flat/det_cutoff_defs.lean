/-
# Vocabulary for the determinant cut-off (`Work.Diff.STE.flat.det_cutoff`)

The cut-off lemma `det_cutoff` produces a smooth nonnegative function on the space `Jet n` of
spatial `2`-jets which

* equals one on the *admissible set* `goodSet n lam KA`: jets whose entries are bounded by `KA`
  and whose real metric matrix `reMat w.1` is uniformly elliptic with constant `lam / 2`;
* is supported in the *nondegenerate set* `detSet n`: jets whose real metric matrix has nonzero
  determinant.

The two sets are defined here so that the cut-off is a statement about them.
-/
import Mathlib
import Submission.Work.Diff.STE.FlatPDE

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat

open scoped Topology
open Set

/-- **The admissible set.**  Jets whose three blocks have entries of norm at most `KA` and whose
real metric matrix dominates `(lam / 2) ‖·‖²` as a quadratic form. -/
def goodSet (n : ℕ) (lam KA : ℝ) : Set (Work.Diff.STE.Flat.Jet n) :=
  {w | (∀ i j, ‖w.1 i j‖ ≤ KA) ∧ (∀ c i j, ‖w.2.1 c i j‖ ≤ KA) ∧
       (∀ c d i j, ‖w.2.2 c d i j‖ ≤ KA) ∧
       (∀ v : Fin n → ℝ, (lam / 2) * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
          Work.Diff.STE.Flat.reMat w.1 i j * v i * v j)}

/-- **The nondegenerate set.**  Jets whose real metric matrix is invertible. -/
def detSet (n : ℕ) : Set (Work.Diff.STE.Flat.Jet n) :=
  {w | (Work.Diff.STE.Flat.reMat w.1).det ≠ 0}

end Work.Diff.STE.flat
