import Submission.Work.ORLyndon.hasProjDimLE_trivial_of_lyndon
import Submission.Work.ORLyndon.hasProjDimLE_of_trivial
import Submission.Work.ORLyndon.hasProjectiveDimensionLE_of_hasProjDimLE
import Submission.Work.ORLyndon.globalDim_le_of_forall_projectiveDimension
import Submission.Work.ORLyndon.globalDim_le_of_ringEquiv

/-!
# `gl.dim K[G] ≤ 2` for a one-relator group

The Lyndon resolution of a one-relator presentation (`Submission/Work/ORLyndon/Lyndon.lean`) is a
projective resolution of the trivial module `K[G]/I_{K[G]}` of length two; together with the
Jaikin-Zapirain–Linton argument (their Proposition 2.2, adapted to the field `K` and to the
presentation resolution over `K`), this shows that *every* left `K[G]`-module has a projective
resolution of length at most two, i.e. that the (left) global dimension of `K[G]` is at most two.

The two ingredients are proved in separate modules:

* `Work.ORLyndon.hasProjDimLE_trivial_of_lyndon`: the trivial module `K[G]/I_{K[G]}` has a
  projective resolution of length at most two (from Lyndon's identity theorem);
* `Work.ORLyndon.hasProjDimLE_of_trivial`: if the trivial module of a group algebra has a projective
  resolution of length at most `n`, then so does every module (JL Prop. 2.2).

The bridge from the concrete notion `HasProjDimLE` to Mathlib's `CategoryTheory.projectiveDimension`
is `Work.ORLyndon.hasProjectiveDimensionLE_of_hasProjDimLE`, and the bridge from that to
`Work.ORCoherence.globalDim` is `Work.ORLyndon.globalDim_le_of_forall_projectiveDimension`; the two
together give `Work.ORCoherence.globalDim (K[G]) ≤ 2`.
-/

set_option autoImplicit false

namespace Work.ORLyndon

open MonoidAlgebra

universe u v

/-- **`gl.dim K[G] ≤ 2` for one-relator groups** (JL Prop. 2.2 applied to the Lyndon resolution):
if Lyndon's identity theorem holds for the one-relator presentation `⟨X | r⟩`, `r = u ^ l`, then
every left `K[G]`-module admits a projective resolution of length at most `2`. -/
theorem hasProjDimLE_two_of_lyndon {X : Type u} [DecidableEq X] {K : Type v} [Field K] [CharZero K]
    {r u : FreeGroup X} {l : ℕ} (h : LyndonIdentity K X r u l)
    (M : Type (max u v)) [AddCommGroup M] [Module (MonoidAlgebra K (OneRelatorGroup r)) M] :
    HasProjDimLE (MonoidAlgebra K (OneRelatorGroup r)) M 2 :=
  hasProjDimLE_of_trivial (K := K) (G := OneRelatorGroup r) 2
    (M := M) (hasProjDimLE_trivial_of_lyndon h)

/-- **`Work.ORCoherence.globalDim (K[G]) ≤ 2` for one-relator groups.**  This is the statement
consumed by the coherence criterion (`Work.ORCoherence`); it combines the previous theorem with the
bridges `Work.ORLyndon.hasProjectiveDimensionLE_of_hasProjDimLE` and
`Work.ORLyndon.globalDim_le_of_forall_projectiveDimension`. -/
theorem globalDim_le_two_of_lyndon {X : Type u} [DecidableEq X] {K : Type v} [Field K]
    [CharZero K] {r u : FreeGroup X} {l : ℕ} (h : LyndonIdentity K X r u l) :
    Work.ORCoherence.globalDim (MonoidAlgebra K (OneRelatorGroup r)) ≤ (2 : WithBot ℕ∞) := by
  apply globalDim_le_of_forall_projectiveDimension
  intro M
  exact hasProjectiveDimensionLE_of_hasProjDimLE (hasProjDimLE_two_of_lyndon h ↥M)

/-- **`Work.ORCoherence.globalDim (K[G]) ≤ 2`** for a group `G` isomorphic to the one-relator group
`⟨X | r⟩` of the presentation data.  This is the form in which the statement is consumed by the
assembly: `Group.OneRelator G` provides such an isomorphism `G ≃* ⟨X | r⟩`. -/
theorem globalDim_le_two_of_mulEquiv {X : Type u} [DecidableEq X] {K : Type v} [Field K]
    [CharZero K] {r u : FreeGroup X} {l : ℕ} {G : Type u} [Group G]
    (e : OneRelatorGroup r ≃* G) (h : LyndonIdentity K X r u l) :
    Work.ORCoherence.globalDim (MonoidAlgebra K G) ≤ (2 : WithBot ℕ∞) :=
  globalDim_le_of_ringEquiv (MonoidAlgebra.mapDomainRingEquiv K e)
    (globalDim_le_two_of_lyndon h)

end Work.ORLyndon
