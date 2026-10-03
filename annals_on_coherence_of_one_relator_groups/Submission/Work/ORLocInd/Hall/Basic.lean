/-
# Residual `p`-finiteness of free groups (P. Hall 1950)

This module records the combinatorial input used by the Fischer--Karrass--Solitar 1972 proof
of the virtual torsion-freeness of one-relator groups: *a finitely generated free group is
residually a finite `p`-group*, for every prime `p` (P. Hall, 1950).  The statement is packaged
as `Work.ORLocInd.ResiduallyFinitePGroup`, with the witnessing quotient pinned to the universe
of the generating type (so that it can be used with groups in the universe of the group `G` of
the main theorems).

The single-word form (which is all that is needed, by taking finite products of quotients) is

`residuallyFinitePGroup_iff`:
`ResiduallyFinitePGroup α` says exactly that for every prime `p` and every `w ≠ 1` in `FreeGroup α`
there is a finite `p`-group `Q` and a homomorphism `ψ : FreeGroup α →* Q` with `ψ w ≠ 1`.
-/
import Mathlib
import Submission.Work.ORLocInd.Basic

set_option autoImplicit false

universe u

namespace Work.ORLocInd

/-- **P. Hall (1950)**: the free group on `α` is *residually a finite `p`-group*: for every prime
`p` and every nontrivial element `w`, there is a finite `p`-group quotient in which `w` survives.

This is the residual finiteness input of the Fischer--Karrass--Solitar proof that one-relator
groups are virtually torsion-free: given the relator `u` and the exponent `l`, one separates the
finitely many powers `u, u ^ 2, …, u ^ (l - 1)` by finite `p`-group quotients, for each prime
power `p ^ k ‖ l` separately. -/
def ResiduallyFinitePGroup (α : Type u) : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ w : FreeGroup α, w ≠ 1 →
    ∃ (Q : Type u) (_ : Group Q) (_ : Finite Q) (_ : IsPGroup p Q)
      (ψ : FreeGroup α →* Q), ψ w ≠ 1

theorem residuallyFinitePGroup_iff {α : Type u} :
    ResiduallyFinitePGroup α ↔
      ∀ (p : ℕ), p.Prime → ∀ w : FreeGroup α, w ≠ 1 →
        ∃ (Q : Type u) (_ : Group Q) (_ : Finite Q) (_ : IsPGroup p Q)
          (ψ : FreeGroup α →* Q), ψ w ≠ 1 :=
  Iff.rfl

end Work.ORLocInd
