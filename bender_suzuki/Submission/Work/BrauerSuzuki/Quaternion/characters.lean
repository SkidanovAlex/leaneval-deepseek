import Mathlib
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.Defs
import Submission.Work.CharCore.linear_char_iff_deg_one
import Submission.Work.CharCore.exists_irr_of_monoidHom
import Submission.Work.CharCore.irr_orthonormal
import Submission.Work.CharCore.vchar_norm_one
import Submission.Work.Induction.Defs
import Submission.Work.Induction.isVChar_indFun
import Submission.Work.Induction.frobenius_reciprocity
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.Quaternion.character_setup
import Submission.Work.BrauerSuzuki.Quaternion.character_values
import Submission.Work.BrauerSuzuki.Quaternion.I_pow_add
import Submission.Work.BrauerSuzuki.Quaternion.tau_zpow_mem_zpowers_two_four
import Submission.Work.BrauerSuzuki.Quaternion.signHom_index_two

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Dade's two characters of a generalized quaternion group

Let `P = ⟨τ, ρ⟩` be a generalized quaternion group in the normal form of Dade (1971), (6.1):
`τ` has order `2 ^ n` with `n ≥ 2`, `ρ τ ρ⁻¹ = τ⁻¹` and `ρ ^ 2 = τ ^ (2 ^ (n-1))`
(`Work.BrauerSuzuki.GenQuaternionData`).  This file produces, as required by the
character-theoretic step of Dade's proof of the Brauer–Suzuki theorem, the two irreducible
complex characters

* `lam`, the non-trivial linear character of the quotient `P / ⟨τ⟩` (so `lam = 1` on `⟨τ⟩` and
  `lam = -1` off it), and
* `th = Ind_{⟨τ⟩}^P λ`, where `λ` is the linear character of the cyclic group `⟨τ⟩` with
  `λ (τ ^ i) = I ^ i` (`I = √-1`), of degree `2`,

together with the values of `1 + lam - th` on the three `⟨τ⟩`-cosets
`P \ ⟨τ⟩`, `⟨τ⟩ \ ⟨τ²⟩`, `⟨τ²⟩ \ ⟨τ⁴⟩` and `⟨τ⁴⟩`.
-/

namespace Work.BrauerSuzuki.Quaternion

open Classical

theorem characters {P : Type*} [Group P] [Fintype P]
    (d : Work.BrauerSuzuki.GenQuaternionData P) :
    ∃ lam th : P → ℂ, lam ∈ Work.CharCore.Irr P ∧ th ∈ Work.CharCore.Irr P ∧
      lam ≠ th ∧ lam ≠ (fun _ => (1 : ℂ)) ∧ th ≠ (fun _ => (1 : ℂ)) ∧
      (∀ x ∈ Subgroup.zpowers d.tau, lam x = (1 : ℂ)) ∧
      (∀ x : P, x ∉ Subgroup.zpowers d.tau → lam x = -1) ∧
      th 1 = 2 ∧
      (∀ x : P, x ∉ Subgroup.zpowers d.tau → th x = 0) ∧
      (∀ i : ℤ, th (d.tau ^ i) = Complex.I ^ i + Complex.I ^ (-i)) ∧
      (∀ x : P, x ∉ Subgroup.zpowers d.tau → (1 : ℂ) + lam x - th x = 0) ∧
      (∀ x : P, x ∈ Subgroup.zpowers d.tau → x ∉ Subgroup.zpowers (d.tau ^ 2) → (1 : ℂ) + lam x - th x = 2) ∧
      (∀ x : P, x ∈ Subgroup.zpowers (d.tau ^ 2) → x ∉ Subgroup.zpowers (d.tau ^ 4) → (1 : ℂ) + lam x - th x = 4) ∧
      (∀ x : P, x ∈ Subgroup.zpowers (d.tau ^ 4) → (1 : ℂ) + lam x - th x = 0) := by
  refine ⟨signFun d, Work.Induction.indFun (tauSub d) (lamFun d), signFun_mem_Irr d,
    indFun_lamFun_mem_Irr d, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h1 := congrFun h 1
    rw [signFun_mem d (Subgroup.one_mem _), indFun_lamFun_one d] at h1
    norm_num at h1
  · obtain ⟨x, hx⟩ := exists_notMem_tauSub d
    intro h
    have h1 := congrFun h x
    rw [signFun_notMem d hx] at h1
    norm_num at h1
  · intro h
    have h1 := congrFun h 1
    rw [indFun_lamFun_one d] at h1
    norm_num at h1
  · intro x hx
    exact signFun_mem d hx
  · intro x hx
    exact signFun_notMem d hx
  · exact indFun_lamFun_one d
  · intro x hx
    exact indFun_lamFun_apply_notMem d hx
  · intro i
    exact indFun_lamFun_tau_zpow d i
  · intro x hx
    rw [signFun_notMem d hx, indFun_lamFun_apply_notMem d hx]
    norm_num
  · intro x hx hx2
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hth : Work.Induction.indFun (tauSub d) (lamFun d) x = 0 := by
      rw [← hi, indFun_lamFun_tau_zpow]
      refine (I_pow_add i).2.2 ?_
      intro hdvd
      exact hx2 (by rw [← hi]; exact (tau_zpow_mem_zpowers_two_four d i).1.mpr hdvd)
    rw [signFun_mem d hx, hth]
    norm_num
  · intro x hx hx4
    have hxH : x ∈ tauSub d := zpowers_two_le d hx
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hxH
    have hth : Work.Induction.indFun (tauSub d) (lamFun d) x = -2 := by
      rw [← hi, indFun_lamFun_tau_zpow]
      refine (I_pow_add i).2.1 ?_ ?_
      · have hxi : d.tau ^ i ∈ Subgroup.zpowers (d.tau ^ 2) := by rw [hi]; exact hx
        exact (tau_zpow_mem_zpowers_two_four d i).1.mp hxi
      · intro hdvd
        exact hx4 (by rw [← hi]; exact (tau_zpow_mem_zpowers_two_four d i).2.mpr hdvd)
    rw [signFun_mem d hxH, hth]
    norm_num
  · intro x hx
    have hxH : x ∈ tauSub d := zpowers_four_le d hx
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hxH
    have hth : Work.Induction.indFun (tauSub d) (lamFun d) x = 2 := by
      rw [← hi, indFun_lamFun_tau_zpow]
      refine (I_pow_add i).1 ?_
      have hxi : d.tau ^ i ∈ Subgroup.zpowers (d.tau ^ 4) := by rw [hi]; exact hx
      exact (tau_zpow_mem_zpowers_two_four d i).2.mp hxi
    rw [signFun_mem d hxH, hth]
    norm_num

end Work.BrauerSuzuki.Quaternion
