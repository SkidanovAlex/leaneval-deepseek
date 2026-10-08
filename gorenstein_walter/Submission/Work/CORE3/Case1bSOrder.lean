import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.PcoreInBasic
import Submission.Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot

set_option linter.dupNamespace false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.CORE3

namespace Work.CORE3

open Subgroup
open Work.GW2

/-- Design pass 6 §3(b), verbatim from `_design_gw/Core6.lean`: `|S| = 8` in the subcase
`V = O₂(Ĥ)`.  Deliverable `Work.CORE3.Case1bSOrderProp`.

`V = pCoreIn 2 B.Hhat` is a four-group and `U` is odd, so `V ⊓ U = ⊥` and
`|Ĥ| = 6·|V ⊔ U| = 6·4·|U| = 24|U|`, whence `|Ĥ|₂ = 8`; and `S ≤ Ĥ`
(`Work.CORE2A.bSetup_S_le_Hhat`) is a Sylow 2-subgroup of `G` inside `Ĥ`, so `|S| = 8`. -/
theorem Case1bSOrder (I : Case1Inputs) : Case1bSOrderProp := by
  intro G _instG _instFin _hFT _hBc B h4 hidx hVS
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- `U = O(H)` has odd order.
  have hUodd : Odd (Nat.card B.U) := Work.CORE2A.bSetup_U_odd B
  -- `V = O₂(Ĥ)` is a `2`-group and `U` is odd, so `V ⊓ U = ⊥`: a subgroup of `V` whose order
  -- divides `|U|` has order dividing `gcd 4 |U| = 1`.
  have hVU : pCoreIn 2 B.Hhat ⊓ B.U = ⊥ := by
    have h2g : IsPGroup 2 ↥(pCoreIn 2 B.Hhat ⊓ B.U) :=
      (Work.CORE2A.pCoreIn_isPGroup B).to_le inf_le_left
    have hodd : Odd (Nat.card ↥(pCoreIn 2 B.Hhat ⊓ B.U)) :=
      Odd.of_dvd_nat hUodd (Subgroup.card_dvd_of_le inf_le_right)
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp h2g
    have hm0 : m = 0 := by
      by_contra h
      rw [hm] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (dvd_pow_self 2 h))
    exact Subgroup.card_eq_one.mp (by rw [hm, hm0]; norm_num)
  -- `V ⊴ Ĥ` (it is `O₂`), so `Ĥ ≤ N_G(V)`; since `U ≤ Ĥ`, `U` normalizes `V`.
  have hUleNV : B.U ≤ Subgroup.normalizer ((pCoreIn 2 B.Hhat : Subgroup G) : Set G) :=
    Subgroup.le_normalizer_iff.mpr fun u hu v hv =>
      Work.CORE2A.conj_mem_pCoreIn B (Work.CORE2A.bSetup_U_le_Hhat B hu) hv
  -- `|V ⊔ U| = |V|·|U| = 4·|U|`.
  have hcardVU : Nat.card ↥(pCoreIn 2 B.Hhat ⊔ B.U) = 4 * Nat.card B.U := by
    rw [Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot (H := pCoreIn 2 B.Hhat)
      (K := B.U) hUleNV hVU, h4.1]
  -- `|Ĥ| = |Ĥ : V ⊔ U|·|V ⊔ U| = 6·|V ⊔ U| = 24·|U|`.
  have hVUle : pCoreIn 2 B.Hhat ⊔ B.U ≤ B.Hhat :=
    sup_le (Work.CORE2A.pCoreIn_le_Hhat B) (Work.CORE2A.bSetup_U_le_Hhat B)
  have hcardHhat : Nat.card B.Hhat = 6 * Nat.card ↥(pCoreIn 2 B.Hhat ⊔ B.U) := by
    have h := Subgroup.relIndex_mul_card (pCoreIn 2 B.Hhat ⊔ B.U) B.Hhat
    rw [hidx, inf_eq_left.mpr hVUle] at h
    exact h.symm
  have hcardHhat24 : Nat.card B.Hhat = 24 * Nat.card B.U := by
    rw [hcardHhat, hcardVU]; ring
  -- `8 ∣ |Ĥ| ∣ |G|`, and `S` is a Sylow `2`-subgroup of `G`, so `8 ∣ |S|`.
  have h8dvdH : 8 ∣ Nat.card B.Hhat := ⟨3 * Nat.card B.U, by rw [hcardHhat24]; ring⟩
  have h8dvdG : 8 ∣ Nat.card G := h8dvdH.trans (Subgroup.card_subgroup_dvd_card B.Hhat)
  have h8dvdS : 8 ∣ Nat.card (B.S : Subgroup G) := by
    have h23 : (2 : ℕ) ^ 3 ∣ Nat.card G := by
      rw [show (2 : ℕ) ^ 3 = 8 from by norm_num]; exact h8dvdG
    have h := (B.S).pow_dvd_card_of_pow_dvd_card (p := 2) (n := 3) h23
    rwa [show (2 : ℕ) ^ 3 = 8 from by norm_num] at h
  -- `|S| = 2^f` where `f = v₂|G|`, and `|S| ∣ |Ĥ| = 24·|U|` with `|U|` odd forces `|S| ∣ 8`.
  have hSpow : Nat.card (B.S : Subgroup G) = 2 ^ (Nat.card G).factorization 2 :=
    Sylow.card_eq_multiplicity B.S
  have hSdvd8 : Nat.card (B.S : Subgroup G) ∣ 8 := by
    have hdvd : (2 : ℕ) ^ (Nat.card G).factorization 2 ∣ 24 * Nat.card B.U := by
      rw [← hcardHhat24, ← hSpow]
      exact Subgroup.card_dvd_of_le (Work.CORE2A.bSetup_S_le_Hhat B)
    have hcop : Nat.Coprime ((2 : ℕ) ^ (Nat.card G).factorization 2) (Nat.card B.U) :=
      (hUodd.coprime_two_left).pow_left _
    have h24 : (2 : ℕ) ^ (Nat.card G).factorization 2 ∣ 24 := hcop.dvd_of_dvd_mul_right hdvd
    have hcop3 : Nat.Coprime ((2 : ℕ) ^ (Nat.card G).factorization 2) 3 :=
      (by norm_num : Nat.Coprime 2 3).pow_left _
    have h38 : (2 : ℕ) ^ (Nat.card G).factorization 2 ∣ 3 * 8 := by
      rw [show (3 : ℕ) * 8 = 24 from by norm_num]; exact h24
    rw [hSpow]
    exact hcop3.dvd_of_dvd_mul_left h38
  exact Nat.dvd_antisymm hSdvd8 h8dvdS

end Work.CORE3

open Work.GW2

/-- The same statement, exposed under the name `Work.CORE3.Case1bSOrder` requested by the lead
(the module's main declaration sits in the doubly nested namespace `Work.CORE3.Work.CORE3`). -/
theorem Case1bSOrder (I : Case1Inputs) : Case1bSOrderProp :=
  _root_.Work.CORE3.Work.CORE3.Case1bSOrder I

end Work.CORE3
