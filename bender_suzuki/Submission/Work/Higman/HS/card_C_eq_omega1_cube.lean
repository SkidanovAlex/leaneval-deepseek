import Mathlib
import Submission.Work.Higman.HS.card_quot_C_A_eq
import Submission.Work.Higman.HS.xi_pow_triv_quot_C_A
import Submission.Work.Higman.PowSub

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.HS

theorem card_C_eq_omega1_cube {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A C : Subgroup P} [hAn : A.Normal]
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hC2 : Work.Higman.powSub C 2 ≤ A) (hCAd : ⁅C, A⁆ = Work.Higman.powSub A 2) :
    Nat.card ↥C = (Nat.card ↥(Work.Higman.omega1 P)) ^ 3 := by
  -- `η = ξ ^ (|Ω₁(P)| - 1)` acts trivially on `C/A`
  have hstep : ∀ x ∈ C, (h.xi ^ (Nat.card ↥(Work.Higman.omega1 P) - 1)) x * x⁻¹ ∈ A :=
    xi_pow_triv_quot_C_A h (A := A) (C := C) hAxi hAab hNA hCn hCinv hAC hCA hcover hCAd htop
  -- the index `[C : A]` equals `|Ω₁(P)|`
  have hquot : Nat.card (↥C ⧸ (A.subgroupOf C)) = Nat.card ↥(Work.Higman.omega1 P) :=
    card_quot_C_A_eq h (A := A) (C := C) hAxi hAab hNA hGs hsq hA4 htop hcard hCn hCinv hAC
      hCA hcover hC2 hCAd hstep
  -- `|C| = [C : A] * |A|`
  have hCcard : Nat.card ↥C
      = Nat.card (↥C ⧸ (A.subgroupOf C)) * Nat.card ↥(A.subgroupOf C) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf C)
  have hAcard : Nat.card ↥(A.subgroupOf C) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC)
  rw [hCcard, hAcard, hcard, hquot]
  ring

end Work.Higman.HS
