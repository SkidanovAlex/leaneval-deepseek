import Mathlib
import Submission.Work.Higman.clo_hard_defs
import Submission.Work.Higman.OmegaAux
import Submission.Work.Higman.bracket_expansion
import Submission.Work.Higman.commutator_powSub_A_C
import Submission.Work.Higman.Fq_structure

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman

theorem clo_betaV_props {P : Type} [Group P] [Finite P] {h : IsSuzuki2Grp P} {A C : Subgroup P}
    [A.Normal] (S : CloH8Data h A C) :
    (∀ (x : ↥C ⧸ (A.subgroupOf C)) (u : ↥C) (w : ↥(omega1 P)) (a : ↥A),
      QuotientGroup.mk u = x → (a : P) ^ 2 ^ (S.e - 1) = (w : P) →
      ((cloBetaV S x w : ↥(omega1 P)) : P)
        = ((commutatorElement (G := P)).bracket ((u : P)) ((a : P))) ^ 2 ^ (S.e - 2)) ∧
    (∀ x x' : ↥C ⧸ (A.subgroupOf C), ∀ w : ↥(omega1 P),
      cloBetaV S (x * x') w = cloBetaV S x w * cloBetaV S x' w) ∧
    (∀ x : ↥C ⧸ (A.subgroupOf C), ∀ w w' : ↥(omega1 P),
      cloBetaV S x (w * w') = cloBetaV S x w * cloBetaV S x w') ∧
    (∀ x : ↥C ⧸ (A.subgroupOf C), ∀ w : ↥(omega1 P),
      cloXiOm h (cloBetaV S x w)
        = cloBetaV S (cloXiQuot h S.hA.map_eq S.hCinv x) (cloXiOm h w)) ∧
    (∀ x : ↥C ⧸ (A.subgroupOf C), cloBetaV S x (cloSM S x) = 1) ∧
    (∃ x : ↥C ⧸ (A.subgroupOf C), ∃ w : ↥(omega1 P), cloBetaV S x w ≠ 1) := by sorry

end Work.Higman
