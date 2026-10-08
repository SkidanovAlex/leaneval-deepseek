import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.OmegaAux
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.lemma9_maximal_abelian
import Submission.Work.Higman.no_square_derived

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped commutatorElement

namespace Work.Higman

/-- In a Suzuki 2-group `P` the commutator subgroup lies in `Ω₁(P)`: `[P,P] ≤ Ω₁(P)`
(Higman 1963, Theorem 1: `G' = Z(G) = Ω₁(G)`).

The proof is assembled in `Work.Higman.core` (`Submission/Work/Higman/OmegaAux.lean`) from
Higman's Lemma 1 (`homogeneous_structure`), Higman's Lemma 9 (`lemma9_maximal_abelian`: a
maximal `ξ`-invariant abelian normal subgroup `A` with `Φ(P) ≤ A` and `A ^ 4 = ⊥`) and the
exclusion of the `C₄`-shape of the derived subgroup (`no_square_derived`, Higman's Lemma 8). -/
theorem commutator_le_omega1 {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Work.Higman.omega1 P := by
  obtain ⟨A, -, hAxi, hAab, -, hNA, hDA, hsq, hA4⟩ := lemma9_maximal_abelian h
  obtain ⟨e, hexp, hcard, htop, hsub⟩ := homogeneous_structure h hAab hAxi
  exact core h hAxi hAab hNA hDA hsq hA4 hexp hcard htop hsub
    (fun hGs htop2 hcardA => no_square_derived h hAxi hAab hNA hGs hsq hA4 htop2 hcardA)

end Work.Higman
