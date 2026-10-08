import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.ASM.Defs
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE3.Case1bDStructure
import Submission.Work.CORE3.SixInvSetElements
import Submission.Work.CORE3.SixInvSetMulTable
import Submission.Work.CORE3.CosetInvCountLeSix
import Submission.Work.CORE3.CosetInvCountNeFive
import Submission.Work.CORE3.InvSetVUSingleton
import Submission.Work.CORE3.NormalizerPcoreEqHhat
import Submission.Work.CORE3.CentralizerPcoreEqVU
import Submission.Work.CORE3.SevenConjU
import Submission.Work.CORE3.SevenNoInvolCentralizer
import Submission.Work.CORE3.BenderSix
import Submission.Work.CORE3.J4.J4ConjKAndNormalizer
import Submission.Work.CORE3.CosetInvCountNeSixOf
import Submission.Work.CORE3.Case1bSevenU3OfConjK
import Submission.Work.CORE3.LeZpowersOfSixInvSetIn

/-!
# `Work.CORE3.Case1bLeFourNotLeD`

Bender 1981, §3 (5)–(7), in the subcase `V = O₂(Ĥ)` of type (2,2) with `|U| = 3`: **`U` is not
contained in `D = Ĥ ⊓ Ĥ^y`** for an involution `y ∉ Ĥ` whose coset carries six involutions.

The proof shows the stronger statement that the hypothesis `cosetInvCount Ĥ y = 6` is already
absurd, by the elementary contradiction recorded in
`Submission/Work/CORE3/J4/NOTES_J4SevenD6.md` §(1)–(2) (this is Bender's (6) together with the
*elementary* exclusion of `n = 6`, using neither step (7) nor `|U| = 3`):

* Bender's (6) (`Work.CORE3.BenderSix`) produces an involution `z ∉ Ĥ` in the coset `Ĥy` and a
  nontrivial odd-order subgroup `X ≤ Ĥ` inverted by `z` with `|C_G(X)|` even.
* The inverted set `I = I_Ĥ(z)` has six elements; `X ⊆ I` and `X` has odd order force
  `X ≤ ⟨a⟩` for the element `a ∈ I` of order `3` (`Work.CORE3.LeZpowersOfSixInvSetIn`).
* `Work.CORE3.J4.J4ConjKAndNormalizer` gives `g` with `X ≤ K^g`, `N_G(X) ≤ Ĥ^g`, and
  `Work.CORE3.involution_mem_conjSub_pcore_of_mem_centralizer` shows every involution of
  `C_G(X)` lies in `V^g = O₂(Ĥ^g)`.
* For the involutions `b₁ ≠ b₂` of `I`, the elements `b₁z`, `b₂z` are distinct involutions of
  `C_G(X)` (because `bᵢ a bᵢ = a⁻¹`), hence lie in the four-group `V^g`; so
  `b₁b₂ = (b₁z)(b₂z) ∈ V^g` has order dividing `2`, while `(b₁b₂)^3 = 1` and `b₁b₂ ≠ 1` give
  order `3`.  Contradiction.
-/

namespace Work.CORE3

open Subgroup
open Work.GW2

theorem Case1bLeFourNotLeD (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) (hU3 : Nat.card B.U = 3)
    {y : G} (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat)
    (h6 : Work.GW2.cosetInvCount B.Hhat y = 6) :
    ¬ (B.U ≤ B.Hhat ⊓ Work.GW2.conjSub y B.Hhat) := by
  classical
  intro _
  -- ## Bender's (5)
  have h5 : ∀ z : G, orderOf z = 2 → z ∉ B.Hhat →
      invSet (pCoreIn 2 B.Hhat ⊔ B.U) z = {1} :=
    InvSetVUSingleton G I hBc B h1 D
  -- ## Bender's (6)
  obtain ⟨z, hz2, hzk, X, hXle, hXne, hXodd, hinvz, hCe, _hNe⟩ :=
    BenderSix G I hBc B h1 D h5 hy2 hyH (by omega)
  obtain ⟨k0, hk0, hzk0⟩ := hzk
  have hyy : y * y = 1 := ((orderOf_eq_two_iff_mul_self y).mp hy2).1
  have hz : z * z = 1 := ((orderOf_eq_two_iff_mul_self z).mp hz2).1
  have hzH : z ∉ B.Hhat := by
    intro hzm
    apply hyH
    have hy_eq : y = k0⁻¹ * z := by rw [hzk0]; group
    rw [hy_eq]
    exact B.Hhat.mul_mem (B.Hhat.inv_mem hk0) hzm
  -- ## `|I_Ĥ(z)| = 6`, the coset count being a coset invariant
  have hIz : (invSetIn B.Hhat z).ncard = 6 := by
    have h := ncard_invSetIn_mul_eq B.Hhat hk0 hyy (by rw [← hzk0]; exact hz)
    rw [← hzk0] at h
    rw [h, ncard_invSetIn_eq_cosetInvCount B.Hhat y hyy hyH]
    exact h6
  have hcntz : cosetInvCount B.Hhat z = 6 := by
    rw [← ncard_invSetIn_eq_cosetInvCount B.Hhat z hz hzH]
    exact hIz
  -- ## the six-element structure of `I_Ĥ(z)`
  obtain ⟨a, b1, b2, haI, ha3, hb1I, hb1o, hb2I, hb2o, hb12⟩ :=
    SixInvSetElements G I hBc B h1 D h5 z hz2 hzH hcntz
  obtain ⟨hbab, hcube⟩ :=
    SixInvSetMulTable G I hBc B h1 D h5 z hz2 hzH hcntz a b1 b2 haI ha3 hb1I hb1o hb2I hb2o hb12
  have hb1sq : b1 * b1 = 1 := ((orderOf_eq_two_iff_mul_self b1).mp hb1o).1
  have hb2sq : b2 * b2 = 1 := ((orderOf_eq_two_iff_mul_self b2).mp hb2o).1
  have hb1inv : b1⁻¹ = b1 := inv_eq_of_mul_eq_one_right hb1sq
  -- ## `X ≤ ⟨a⟩`
  have hXa : X ≤ Subgroup.zpowers a :=
    LeZpowersOfSixInvSetIn hz haI ha3 hb1I hb1o hb2I hb2o hb12 hIz
      (fun x hxX => ⟨hXle hxX, by
        simpa [inv_eq_of_mul_eq_one_right hz] using hinvz x hxX⟩) hXodd hXne
  -- ## Bender's (7)-input: `X ≤ K^g`, `N_G(X) ≤ Ĥ^g`
  obtain ⟨g, hKg, hNg⟩ :=
    J4.J4ConjKAndNormalizer I hBc B h1 D hz2 hzH hXle hXne hXodd hinvz hCe
  -- ## `V^g = O₂(Ĥ^g)` is a four-group
  have hV4g : IsFourGroup (conjSub g (pCoreIn 2 B.Hhat)) := by
    constructor
    · rw [Work.CORE2A.card_conjSub]
      exact D.four.1
    · intro v hv
      have hv' : g⁻¹ * v * g ∈ pCoreIn 2 B.Hhat := (Work.CORE2A.mem_conjSub_iff).mp hv
      have hsq : (g⁻¹ * v * g) * (g⁻¹ * v * g) = 1 := by
        simpa [pow_two] using D.four.2 (g⁻¹ * v * g) hv'
      rw [pow_two]
      have hconj : v * v = g * ((g⁻¹ * v * g) * (g⁻¹ * v * g)) * g⁻¹ := by group
      rw [hconj, hsq]; group
  -- ## `b₁z`, `b₂z` are involutions
  have hzb1 : z * b1 * z = b1 := by rw [hb1I.2, hb1inv]
  have hzb2 : z * b2 * z = b2 := by rw [hb2I.2, inv_eq_of_mul_eq_one_right hb2sq]
  have hbab2 : b2 * a * b2 = a⁻¹ := by
    have h := SixInvSetMulTable G I hBc B h1 D h5 z hz2 hzH hcntz a b2 b1 haI ha3 hb2I hb2o
      hb1I hb1o (Ne.symm hb12)
    exact h.1
  have hb1z_sq : (b1 * z) * (b1 * z) = 1 := by
    calc (b1 * z) * (b1 * z) = b1 * (z * b1 * z) := by group
      _ = b1 * b1 := by rw [hzb1]
      _ = 1 := hb1sq
  have hb1z_ne : b1 * z ≠ 1 := by
    intro hone
    have hz_eq : z = b1 := by
      calc z = b1 * (b1 * z) := by rw [← mul_assoc, hb1sq, one_mul]
        _ = b1 * 1 := by rw [hone]
        _ = b1 := mul_one b1
    exact hzH (hz_eq ▸ hb1I.1)
  have hb1z2 : orderOf (b1 * z) = 2 :=
    (orderOf_eq_two_iff_mul_self (b1 * z)).mpr ⟨hb1z_sq, hb1z_ne⟩
  have hb2z_sq : (b2 * z) * (b2 * z) = 1 := by
    calc (b2 * z) * (b2 * z) = b2 * (z * b2 * z) := by group
      _ = b2 * b2 := by rw [hzb2]
      _ = 1 := hb2sq
  have hb2z_ne : b2 * z ≠ 1 := by
    intro hone
    have hz_eq : z = b2 := by
      calc z = b2 * (b2 * z) := by rw [← mul_assoc, hb2sq, one_mul]
        _ = b2 * 1 := by rw [hone]
        _ = b2 := mul_one b2
    exact hzH (hz_eq ▸ hb2I.1)
  have hb2z2 : orderOf (b2 * z) = 2 :=
    (orderOf_eq_two_iff_mul_self (b2 * z)).mpr ⟨hb2z_sq, hb2z_ne⟩
  -- ## `bᵢz` centralizes `X`
  have centralizer_mem : ∀ (b : G), b ∈ invSetIn B.Hhat z → b * b = 1 → b * a * b = a⁻¹ →
      b * z ∈ Subgroup.centralizer (X : Set G) := by
    intro b hbI hbsq hba
    have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbsq
    have hzb : z * b * z = b := by rw [hbI.2, hbinv]
    rw [Subgroup.mem_centralizer_iff]
    intro x hxX
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hXa hxX)
    have hzx : z * x * z = x⁻¹ := by
      have h := hinvz x hxX
      rwa [inv_eq_of_mul_eq_one_right hz] at h
    have hconja : (MulAut.conj b) a = a⁻¹ := by
      rw [MulAut.conj_apply, hbinv]
      exact hba
    have hbx : b * x * b = x⁻¹ := by
      have hconj : (MulAut.conj b) x = x⁻¹ := by
        rw [← hn, map_zpow, hconja, inv_zpow]
      have h2 : b * x * b⁻¹ = x⁻¹ := by
        rw [← hconj, MulAut.conj_apply]
      rwa [hbinv] at h2
    have hconj : (b * z) * x * (b * z)⁻¹ = x := by
      have hbinv' : (b * z)⁻¹ = z * b := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hbsq, inv_eq_of_mul_eq_one_right hz]
      rw [hbinv']
      calc (b * z) * x * (z * b) = b * (z * x * z) * b := by group
        _ = b * x⁻¹ * b := by rw [hzx]
        _ = (b * x * b)⁻¹ := by rw [mul_inv_rev, mul_inv_rev, hbinv, mul_assoc]
        _ = (x⁻¹)⁻¹ := by rw [hbx]
        _ = x := inv_inv x
    have hcomm : (b * z) * x = x * (b * z) := mul_inv_eq_iff_eq_mul.mp hconj
    exact hcomm.symm
  have hb1zC : b1 * z ∈ Subgroup.centralizer (X : Set G) :=
    centralizer_mem b1 hb1I hb1sq hbab
  have hb2zC : b2 * z ∈ Subgroup.centralizer (X : Set G) :=
    centralizer_mem b2 hb2I hb2sq hbab2
  -- ## every involution of `C_G(X)` lies in `V^g`
  have hb1zV : b1 * z ∈ conjSub g (pCoreIn 2 B.Hhat) :=
    involution_mem_conjSub_pcore_of_mem_centralizer G I hBc B h1 D hz2 hzH hXle hXne
      hXodd hinvz hCe g hKg hNg hb1z2 hb1zC
  have hb2zV : b2 * z ∈ conjSub g (pCoreIn 2 B.Hhat) :=
    involution_mem_conjSub_pcore_of_mem_centralizer G I hBc B h1 D hz2 hzH hXle hXne
      hXodd hinvz hCe g hKg hNg hb2z2 hb2zC
  -- ## `b₁b₂ ∈ V^g`, so `(b₁b₂)² = 1`, contradicting `(b₁b₂)³ = 1`
  have hprod : (b1 * z) * (b2 * z) = b1 * b2 := by
    rw [show (b1 * z) * (b2 * z) = b1 * (z * b2 * z) from by group, hzb2]
  have hmem : b1 * b2 ∈ conjSub g (pCoreIn 2 B.Hhat) := by
    rw [← hprod]
    exact (conjSub g (pCoreIn 2 B.Hhat)).mul_mem hb1zV hb2zV
  have hsq : (b1 * b2) * (b1 * b2) = 1 := by
    have h := hV4g.2 (b1 * b2) hmem
    simpa [pow_two] using h
  have hone : b1 * b2 = 1 := by
    have h : (b1 * b2) ^ 2 * (b1 * b2) = 1 := by simpa [pow_succ] using hcube
    rw [pow_two, hsq, one_mul] at h
    exact h
  have hb12' : b1 = b2 := by
    have h : b1 = b2⁻¹ := eq_inv_of_mul_eq_one_left hone
    rwa [inv_eq_of_mul_eq_one_right hb2sq] at h
  exact hb12 hb12'

end Work.CORE3
