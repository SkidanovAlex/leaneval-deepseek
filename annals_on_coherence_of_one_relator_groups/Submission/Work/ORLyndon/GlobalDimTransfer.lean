import Submission.Work.ORLyndon.ProjDim
import Submission.Work.ORLyndon.Augmentation
import Submission.Work.ORLyndon.Lyndon
import Submission.Work.ORLyndon.hasProjDimLE_trivial_of_lyndon
import Submission.Work.ORLyndon.hasProjectiveDimensionLE_of_hasProjDimLE
import Submission.Work.ORLyndon.globalDim_le_of_forall_projectiveDimension

/-!
# The transfer step of JL Proposition 2.2

Jaikin-Zapirain–Linton, *On the coherence of one-relator groups and their group algebras*,
Proposition 2.2, for a group algebra over a field: a projective resolution of the trivial module
`K[G]/I_{K[G]}` of length `n` produces projective resolutions of length `n` of *every* left
`K[G]`-module, by tensoring the resolution with `M` over `K` (the terms `P ⊗_K M` are projective
because `K[G] ⊗_K M` is a free `K[G]`-module).

The statement is recorded here as an explicit hypothesis, `GlobalDimTransfer`, so that the chapters
that use it stay independent of this construction; the unconditional form is
`Work.ORLyndon.hasProjDimLE_of_hasProjDimLE_trivial` (module
`Submission.Work.ORLyndon.hasProjDimLE_of_hasProjDimLE_trivial`).
-/

set_option autoImplicit false

namespace Work.ORLyndon

open MonoidAlgebra

universe u v

/-- **JL Proposition 2.2 (transfer step)**: if the trivial module of the group algebra `K[G]` has a
projective resolution of length at most `n`, then so does every left `K[G]`-module. -/
def GlobalDimTransfer (K : Type v) [Field K] (G : Type u) [Group G] : Prop :=
  ∀ (n : ℕ) (M : Type (max u v)) [AddCommGroup M] [Module (MonoidAlgebra K G) M],
    HasProjDimLE (MonoidAlgebra K G) (MonoidAlgebra K G ⧸ augIdeal K G) n →
      HasProjDimLE (MonoidAlgebra K G) M n

/-- **`Work.ORCoherence.globalDim (K[G]) ≤ 2` for one-relator groups**, conditional on the transfer
step `Work.ORLyndon.GlobalDimTransfer` (JL Prop. 2.2).  The unconditional form, using
`Work.ORLyndon.hasProjDimLE_of_hasProjDimLE_trivial`, is
`Work.ORLyndon.globalDim_le_two_of_lyndon`. -/
theorem globalDim_le_two_of_lyndon_of_transfer {X : Type u} [DecidableEq X] {K : Type v} [Field K]
    [CharZero K] {r u : FreeGroup X} {l : ℕ} (htrans : GlobalDimTransfer K (OneRelatorGroup r))
    (h : LyndonIdentity K X r u l) :
    Work.ORCoherence.globalDim (MonoidAlgebra K (OneRelatorGroup r)) ≤ (2 : WithBot ℕ∞) := by
  apply globalDim_le_of_forall_projectiveDimension
  intro M
  exact hasProjectiveDimensionLE_of_hasProjDimLE (htrans 2 ↥M (hasProjDimLE_trivial_of_lyndon h))

end Work.ORLyndon
