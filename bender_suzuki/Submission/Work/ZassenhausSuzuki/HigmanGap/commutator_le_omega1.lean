-- LOCAL COPY of `Submission/Work/Higman/commutator_le_omega1.lean` (namespace `Work.ZassenhausSuzuki.HigmanLocal`), made so that the modules
-- `Submission.Work.Higman.no_square_maximal` and `Submission.Work.Higman.reducible_aux`
-- (which do not build while `Work.Higman.NSM.redcase` is unfinished) are not needed.
-- Identical to the original except for the import/namespace changes below.
import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.OmegaAux
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.lemma9_maximal_abelian
import Submission.Work.Higman.NSM.higmanLemma13

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end
-- RE-WIRED (area owner): the C₄ exclusion in the maximal setting is now
-- `Work.Higman.NSM.noSquareMaximal` (`NSM/higmanLemma13.lean`, builds); the stale
-- `no_square_maximal` module (which referred to the not-yet-written `NSM.redcase`) is no
-- longer imported.

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped commutatorElement

namespace Work.ZassenhausSuzuki.HigmanLocal

open Work.Higman

/-- In a Suzuki 2-group `P` the commutator subgroup lies in `Ω₁(P)`: `[P,P] ≤ Ω₁(P)`
(Higman 1963, Theorem 1: `G' = Z(G) = Ω₁(G)`).

The proof is assembled in `Work.Higman.core` (`Submission/Work/Higman/OmegaAux.lean`) from
Higman's Lemma 1 (`homogeneous_structure`), Higman's Lemma 9 (`lemma9_maximal_abelian`: a
maximal `ξ`-invariant abelian normal subgroup `A` with `Φ(P) ≤ A` and `A ^ 4 = ⊥`) and the
exclusion of the `C₄`-shape of the derived subgroup (`no_square_maximal`, Higman's Lemma 8). -/
theorem commutator_le_omega1 {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Work.Higman.omega1 P := by
  obtain ⟨A, hAn, hAxi, hAab, hAmax, hNA, hDA, hsq, hA4⟩ := lemma9_maximal_abelian h
  obtain ⟨e, hexp, hcard, htop, hsub⟩ := homogeneous_structure h hAab hAxi
  exact core h hAxi hAab hNA hDA hsq hA4 hexp hcard htop hsub
    (fun hGs htop2 hcardA =>
      Work.Higman.NSM.noSquareMaximal h hAab hAxi hAmax hNA hGs hsq hA4 htop2 hcardA)

end Work.ZassenhausSuzuki.HigmanLocal
