/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The case predicates of the Magnus (Magnus--Moldavanskii) step, at the bottom of the hierarchy

This module exists *only* to break an import cycle of the workspace.  The three predicates
`Work.OROneRel.FreeKernelCase`, `Work.OROneRel.NielsenCountCase` and `Work.OROneRel.BlockWordCase`
were originally declared in `Submission/Work/OROneRel/magnus_step_root.lean`, where they are the
case hypotheses of the residual of the Magnus step.  Several modules that the residual of
`magnus_step_root` itself *needs* (e.g. the `Z`-domain splitting with case hypotheses,
`Submission/Work/OROneRel/winRhoRange_cosetTree_window_v2.lean` and
`Submission/Work/OROneRel/winVertex_generation_exists_windowWalk_v2.lean`) mention those predicates
in their *hypotheses*, and therefore had to import `magnus_step_root.lean` -- which put them *above*
it in the module order, so that their statements can never be consumed by `magnus_step_root.lean`.

Declaring the predicates here, below everything, removes that obstruction: a module that only needs
the predicates (and not the Magnus step itself) imports this file instead, and its statements become
available to `magnus_step_root.lean`.

The definitions are moved verbatim from `magnus_step_root.lean`; nothing else changes.
-/
import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.MagnusGenDefs
import Submission.Work.OROneRel.MagnusRewrite
import Submission.Work.OROneRel.vertexKernelDefs
import Submission.Work.OROneRel.wgtMMDefs
import Submission.Work.OROneRel.wordOfDefs

namespace Work.OROneRel

universe u

/-- **The free-kernel case of the residual.**  At `l = 1` a killing weight `c` whose kernel
`ker (presentedCohom c u 1 hc)` is a *free* group is a case of the Magnus step that is *proved*:
`Work.OROneRel.magnusStepCase2_of_freeKernel` (a colleague's file, which imports the proved
assembly `magnusStepKernelForm`/`hnnKernelForm_tracking` of the residual) produces the target
outright, with the free vertex presented by the terminal one-relator group `⟨Option γ | of none⟩`.
The residual therefore carries the *negation* of this case as a hypothesis. -/
def FreeKernelCase {α : Type u} (u : FreeGroup α) (l : ℕ) : Prop :=
  l = 1 ∧ ∃ (c : α → ℤ) (hc : Work.OROneRel.cohom c u = 1),
    (∃ τ : FreeGroup α, Work.OROneRel.cohom c τ = Multiplicative.ofAdd 1) ∧
    ∃ γ : Type u, Nonempty (↥(presentedCohom c u 1 hc).ker ≃* FreeGroup γ)

/-- **The Nielsen count case of the residual.**  If some automorphic image `ψ u` is cyclically
reduced, has all exponent sums non-zero and carries a letter `t` together with a killing weight `c`
(`c t = 1`, `cohom c (ψ u) = 1`) whose decorated word with the `t`-symbols deleted is *shorter* than
`relatorNorm u`, then the target holds for `u` and every `l ≥ 1`
(`Work.OROneRel.magnusStepData_of_count_image`, a colleague's file).  This case removes the
two-letter torus-type roots `x ^ p y ^ q` on which the transvection `x ↦ x y ^ m` (with `p m + q = 1`)
makes the count drop below `p + q` (`magnusStepNielsenTorusFamily`) from the residual; the residual
carries the *negation* of this case as a hypothesis, which is strictly stronger than the negation
`hnd` of the plain divisibility condition. -/
def NielsenCountCase {α : Type u} [DecidableEq α] (u : FreeGroup α) : Prop :=
  ∃ (ψ : FreeGroup α ≃* FreeGroup α) (t : α) (c : α → ℤ),
    ¬ Work.OROneRel.IsProperPower (ψ u) ∧ Work.OROneRel.IsCyclicallyReducedRelator (ψ u) ∧
    2 ≤ Work.OROneRel.relatorNorm (ψ u) ∧
    (∀ x : α, x ∈ Work.OROneRel.relatorLetters (ψ u) → Work.OROneRel.eps x (ψ u) ≠ 0) ∧
    t ∈ Work.OROneRel.relatorLetters (ψ u) ∧ c t = 1 ∧ Work.OROneRel.cohom c (ψ u) = 1 ∧
    (Work.OROneRel.wvListAux c t 0 (Work.OROneRel.wordOf (ψ u))).length <
      Work.OROneRel.relatorNorm u

/-- **The two-letter block case of the residual (proved, for every `l ≥ 1`).**  `u` is a block word
`a ^ p * b ^ q` on two distinct letters with `p, q ≥ 1` and `gcd p q = 1`.  These are exactly the
root patterns for which the elementary routes provably fail (no Nielsen image feeds the
exponent-sum-zero step, the `⊤`/kernel route needs a fibered relator) and which therefore motivated
the whole `Z`-domain development -- and they are *solved*: `Work.OROneRel.magnusStepAt_blockWord`
(`Submission/Work/OROneRel/magnusStepAt_blockWord.lean`) proves the target's second disjunct for
them, for every `l ≥ 1`, from the colleague's two-letter `Z`-domain splitting
`Work.OROneRel.twoLetter_hnnData` (the band `[0, p*q]` of the weight `a ↦ q`, `b ↦ -p`) together
with the injective relabelling `Fin 2 → α`.  The case is therefore peeled off *before* the residual
machinery. -/
def BlockWordCase {α : Type u} (u : FreeGroup α) : Prop :=
  ∃ (a b : α) (p q : ℕ), a ≠ b ∧ 1 ≤ p ∧ 1 ≤ q ∧ Nat.Coprime p q ∧
    u = FreeGroup.of a ^ p * FreeGroup.of b ^ q

end Work.OROneRel
