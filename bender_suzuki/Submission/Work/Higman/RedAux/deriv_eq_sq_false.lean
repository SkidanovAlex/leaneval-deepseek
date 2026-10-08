import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.OmegaAux
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.MSA.basic
import Submission.Work.Higman.sq_lemma7

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped commutatorElement

namespace Work.Higman.RedAux

/-- **The `C₄` configuration with `⁅E,E⁆ = A²` and `E² = A` is impossible.** -/
theorem deriv_eq_sq_false {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A E : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : commutator P = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hAE : A ≤ E) (hEne : E ≠ A)
    (hEinv : E.map (h.xi : MulAut P).toMonoidHom = E)
    (hEirr : ∀ F : Subgroup P, A ≤ F → F ≤ E → F.map (h.xi : MulAut P).toMonoidHom = F →
      F = A ∨ F = E)
    (hEE : ⁅E, E⁆ = Work.Higman.powSub A 2)
    (hE2 : Work.Higman.powSub E 2 = A) :
    False := by
  have hAn : A.Normal := by rw [← hGs]; exact Subgroup.commutator_normal ⊤ ⊤
  haveI : A.Normal := hAn
  have hAis : IsXiAbelNormal h A := ⟨hAn, hAxi, hAab⟩
  -- `E` is normal: `[P,E] ≤ [P,P] = A ≤ E`.
  have hEn : E.Normal := by
    refine Subgroup.Normal.mk fun n hn g => ?_
    have h1 : ⁅g, n⁆ ∈ A := by
      rw [← hGs]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n)
    rw [show g * n * g⁻¹ = ⁅g, n⁆ * n from by rw [commutatorElement_def]; group]
    exact E.mul_mem (hAE h1) hn
  have hPhi : Work.Higman.powSub E 2 ⊔ ⁅E, E⁆ = A := by
    rw [hE2, hEE]
    exact sup_eq_left.mpr (Work.Higman.powSub_le (by norm_num))
  have hCd : ⁅E, E⁆ ≤ Work.Higman.powSub A 2 := hEE ▸ le_rfl
  have hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x :=
    Work.Higman.sq_lemma7 h hAis hEn hEinv hAE hEne.symm
      (fun D _ hDinv hAD hDE => hEirr D hAD hDE hDinv) hPhi hCd
  have hbot : ⁅E, E⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hEab x hx y hy
  have hA2bot : Work.Higman.powSub A 2 = ⊥ := by rw [← hEE]; exact hbot
  have hOmbot : Work.Higman.omega1 P = ⊥ := by rw [← htop]; exact hA2bot
  have h1 : Nat.card ↥(Work.Higman.omega1 P) = 1 := by rw [hOmbot, Subgroup.card_bot]
  have h4 := h.omega1_card_ge_four
  omega

end Work.Higman.RedAux
