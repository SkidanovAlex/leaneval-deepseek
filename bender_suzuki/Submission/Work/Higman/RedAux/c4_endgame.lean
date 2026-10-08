import Mathlib
import Submission.Work.Higman.RedAux.c4_reduction

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.RedAux

theorem c4_endgame {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A C : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ E : Subgroup P, E.Normal → E.map (h.xi : MulAut P).toMonoidHom = E →
      A ≤ E → E ≤ C → E = A ∨ E = C)
    (hCd : ⁅C, C⁆ = Work.Higman.powSub A 2)
    (hC2 : Work.Higman.powSub C 2 = Work.Higman.powSub A 2)
    (hCP : ⁅(⊤ : Subgroup P), C⁆ = A)
    (hACd : ⁅A, C⁆ = Work.Higman.powSub A 2) :
    False := by sorry

end Work.Higman.RedAux
