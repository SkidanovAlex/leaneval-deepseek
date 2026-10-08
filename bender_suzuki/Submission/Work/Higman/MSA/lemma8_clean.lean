import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.MSA.l8_local
import Submission.Work.Higman.MSA.l8_BV
import Submission.Work.Higman.MSA.l8_betaV
import Submission.Work.Higman.MSA.l8_sV
import Submission.Work.Higman.MSA.l8_triv
import Submission.Work.Higman.MSA.l8_step1
import Submission.Work.Higman.MSA.l8_card
import Submission.Work.Higman.MSA.l8_exp_data
import Submission.Work.Higman.HS.core_mul

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped commutatorElement

namespace Work.Higman.MSA

theorem lemma8_clean {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A C : Subgroup P} (hA : Work.Higman.IsXiAbelNormal h A)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hC2 : Work.Higman.powSub C 2 ≤ A)
    (hCd : ⁅C, C⁆ = A) :
    ∀ a ∈ A, a * a = 1 := by
  by_cases hA0 : A = ⊥
  · intro a ha
    rw [hA0, Subgroup.mem_bot] at ha
    subst ha
    simp
  · by_cases hA2ne : Work.Higman.powSub A 2 = ⊥
    · intro a ha
      have h2 : a ^ 2 ∈ Work.Higman.powSub A 2 := Work.Higman.pow_mem_powSub ha
      rw [hA2ne, Subgroup.mem_bot] at h2
      rwa [pow_two] at h2
    · exfalso
      haveI hAn : A.Normal := hA.normal
      obtain ⟨e, he2, hOmega, he1, htopA, hkey⟩ := l8_exp_data h hA hA0 hA2ne
      have he : 1 ≤ e := by omega
      let S : L8.D h A C :=
        { hA := hA, hCn := hCn, hCinv := hCinv, hAC := hAC, hCA := hCA, hcover := hcover,
          hC2 := hC2, hCd := hCd, hAne := hA0, hOmega := hOmega, e := e, he := he, he2 := he2,
          he1 := he1, htopA := htopA, hkey := hkey }
      obtain ⟨n, hn⟩ := h.exists_card_omega1_eq_two_pow
      have hn2 : 2 ≤ n := by
        by_contra hcon
        have h1 : n ≤ 1 := by omega
        have h2 : 2 ^ n ≤ 2 := by simpa using Nat.pow_le_pow_right (by norm_num) h1
        have h4 := h.omega1_card_ge_four
        omega
      have htriv : ∀ x ∈ C, (h.xi ^ (Nat.card ↥(omega1 P) - 1)) x * x⁻¹ ∈ A :=
        L8.l8_xi_pow_card_sub_one_triv_quot S
      have hcard : Nat.card (↥C ⧸ (A.subgroupOf C)) = Nat.card ↥(omega1 P) :=
        L8.l8_quot_card S hn hn2 htriv
      obtain ⟨hSinj, _hSsurj, hSone, hSxi, hSpol⟩ := L8.l8_sV S hcard
      obtain ⟨_, hBV1, hBV2, hBVdiag, hBVeq, hBVne⟩ := L8.l8_BV S
      obtain ⟨_, hβ1, hβ2, hβeq, hβrel, hβne⟩ := L8.l8_betaV S
      letI hCG : CommGroup (↥C ⧸ (A.subgroupOf C)) :=
        { (inferInstance : Group (↥C ⧸ (A.subgroupOf C))) with mul_comm := L8.quot_comm S.hCd }
      letI hWG : CommGroup ↥(omega1 P) :=
        { (inferInstance : Group ↥(omega1 P)) with
          mul_comm := fun a b => Subtype.ext (h.omega1_comm a.2 b.2) }
      have hWtrans : ∀ a b : ↥(omega1 P), a ≠ 1 → b ≠ 1 →
          ∃ k : ℕ, ((Work.Higman.xiZ h) ^ k) a = b := by
        intro a b ha hb
        have ha1 : (a : P) ≠ 1 := fun hc => ha (Subtype.ext hc)
        have hb1 : (b : P) ≠ 1 := fun hc => hb (Subtype.ext hc)
        obtain ⟨k, hk⟩ := Work.Higman.xi_trans_omega1 h a.2 b.2 ha1 hb1
        exact ⟨k, Subtype.ext (by rw [Work.Higman.xiZ_pow_coe]; exact hk)⟩
      have hsne : ∀ a : ↥C ⧸ (A.subgroupOf C), a ≠ 1 → L8.sV S a ≠ 1 := by
        intro a ha hcon
        exact ha (hSinj (by rw [hcon, hSone]))
      have hVtrans : ∀ a b : ↥C ⧸ (A.subgroupOf C), a ≠ 1 → b ≠ 1 →
          ∃ k : ℕ, ((L8.xiQuot h S.hA.map_eq S.hCinv) ^ k) a = b := by
        intro a b ha hb
        obtain ⟨k, hk⟩ := hWtrans (L8.sV S a) (L8.sV S b) (hsne a ha) (hsne b hb)
        exact ⟨k, hSinj (by rw [← L8.sV_xi_pow S k a]; exact hk)⟩
      exact Work.Higman.HS.core_mul
        (fun v => L8.quot_sq_one S.hC2 v)
        (fun w => Subtype.ext (by
          have h1 := h.omega1_sq_eq_one w.2
          rw [pow_two] at h1
          simpa using h1))
        hn2
        (by rw [hcard, hn])
        hn
        (L8.xiQuot h S.hA.map_eq S.hCinv) (Work.Higman.xiZ h)
        hVtrans hWtrans
        (L8.BV S) hBV1 hBV2 hBVdiag hBVeq hBVne
        (L8.sV S) hSone hSxi hSpol hsne
        (L8.betaV S) hβ1 hβ2 hβeq hβrel hβne

end Work.Higman.MSA
