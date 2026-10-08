import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.NormalizerPcoreEqHhat
import Submission.Work.CORE3.SylowDihedral
import Submission.Work.CORE3.InvolutionNotMemOfCardEightDihedral
import Submission.Work.CORE3.ConjMemSOfOrderTwoPow
import Submission.Work.CORE3.OddPowTwoPowInverting

set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.CORE3

open Subgroup
open Work.GW2

/-! ## The uniform conjugation action of `S − O₂(Ĥ)` on `U`

`O₂(Ĥ) = S ⊓ C_G(U)` (Theorem 2.6), so the conjugation action of `S` on the odd group `U`
factors through `S / O₂(Ĥ) ≅ Z₂`: every element of `S \ O₂(Ĥ)` acts on `U` in the same way. -/
theorem conj_eq_of_mem_S_notMem_pCoreIn {G : Type} [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) (h26 : Work.GW2.Thm26Concl B)
    (hcard : Nat.card (B.S : Subgroup G) = 8)
    (h4 : Work.GW2.IsFourGroup (Work.GW2.pCoreIn 2 B.Hhat))
    {y z w : G} (hyS : y ∈ (B.S : Subgroup G)) (hzS : z ∈ (B.S : Subgroup G))
    (hyV : y ∉ Work.GW2.pCoreIn 2 B.Hhat) (hzV : z ∉ Work.GW2.pCoreIn 2 B.Hhat)
    (hwU : w ∈ B.U) : y * w * y⁻¹ = z * w * z⁻¹ := by
  have hVleS : Work.GW2.pCoreIn 2 B.Hhat ≤ (B.S : Subgroup G) :=
    Work.CORE2A.thm26Concl_O2_le_S h26
  have hVleCU : Work.GW2.pCoreIn 2 B.Hhat ≤ Subgroup.centralizer (B.U : Set G) :=
    (Work.CORE2A.thm26Concl_centralizer_eq h26) ▸ inf_le_right
  have hrel : (Work.GW2.pCoreIn 2 B.Hhat).relIndex (B.S : Subgroup G) = 2 := by
    have h := Subgroup.relIndex_mul_card (Work.GW2.pCoreIn 2 B.Hhat) (B.S : Subgroup G)
    rw [inf_eq_left.mpr hVleS, h4.1, hcard] at h
    omega
  have hzVin : z⁻¹ ∉ Work.GW2.pCoreIn 2 B.Hhat := fun h =>
    hzV (by simpa using (Work.GW2.pCoreIn 2 B.Hhat).inv_mem h)
  have hzy : z⁻¹ * y ∈ Work.GW2.pCoreIn 2 B.Hhat := by
    have hmem : (⟨z⁻¹, (B.S).inv_mem hzS⟩ : ↥(B.S : Subgroup G)) * ⟨y, hyS⟩ ∈
        (Work.GW2.pCoreIn 2 B.Hhat).subgroupOf (B.S : Subgroup G) := by
      rw [Subgroup.mul_mem_iff_of_index_two hrel]
      refine ⟨fun hc => absurd hc (fun hh => hzVin ?_), fun hc => absurd hc (fun hh => hyV ?_)⟩
      · simpa using Subgroup.mem_subgroupOf.mp hh
      · exact Subgroup.mem_subgroupOf.mp hh
    simpa using Subgroup.mem_subgroupOf.mp hmem
  have hcomm : w * (z⁻¹ * y) = (z⁻¹ * y) * w :=
    (Subgroup.mem_centralizer_iff.mp (hVleCU hzy)) w hwU
  calc y * w * y⁻¹ = z * ((z⁻¹ * y) * w * (z⁻¹ * y)⁻¹) * z⁻¹ := by group
    _ = z * w * z⁻¹ := by rw [← hcomm]; group

/-! ## A `2`-element of `Ĥ` has order at most `4`

Any `2`-element of `Ĥ` is conjugate inside `Ĥ` into the Sylow `2`-subgroup `S`
(`ConjMemSOfOrderTwoPow`) and `S ≅ DihedralGroup 4` has exponent `4`. -/

/-- In the dihedral group of order `8` every element has order at most `4`. -/
lemma dihedralFour_orderOf_le_four (y : DihedralGroup 4) : orderOf y ≤ 4 := by
  rcases y with i | i
  · rw [DihedralGroup.orderOf_r]
    exact Nat.div_le_self 4 _
  · rw [DihedralGroup.orderOf_sr]
    norm_num

/-- A `2`-element of `Ĥ` has order at most `4`: its order is `2 ^ v`, and `v ≤ 2`. -/
theorem twoPow_le_two_of_mem_Hhat {G : Type} [Group G] [Finite G] (hBc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (hcard : Nat.card (B.S : Subgroup G) = 8)
    {g : G} (hg : g ∈ B.Hhat) {v : ℕ} (hord : orderOf g = 2 ^ v) : v ≤ 2 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hcH, hcS⟩ := ConjMemSOfOrderTwoPow B hg hord
  have hordc : orderOf (c * g * c⁻¹) = 2 ^ v := by
    rw [show c * g * c⁻¹ = (MulAut.conj c) g from by simp [mul_assoc],
      MulEquiv.orderOf_eq, hord]
  obtain ⟨n, hn2, hdihn⟩ := SylowDihedral G hBc B
  have hn4 : n = 4 := by
    obtain ⟨e⟩ := hdihn
    have hcardn : Nat.card ↥(B.S : Subgroup G) = 2 * n := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    omega
  obtain ⟨e⟩ := hn4 ▸ hdihn
  have hle4 : 2 ^ v ≤ 4 := by
    have h := dihedralFour_orderOf_le_four (e ⟨c * g * c⁻¹, hcS⟩)
    rw [MulEquiv.orderOf_eq] at h
    rw [← Subgroup.orderOf_coe] at h
    rw [hordc] at h
    exact h
  by_contra hcon
  have h3 : 3 ≤ v := by omega
  have h32 : (2 : ℕ) ^ 3 ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) h3
  rw [show (2 : ℕ) ^ 3 = 8 by norm_num] at h32
  omega

/-! ## The main lemma -/

/-- **Bender 1981 §3, p. 223.**  In the subcase `V = O₂(Ĥ)` of type (2,2), with `x ∈ U = O(Ĥ)`
non-trivial and `h ∈ Ĥ` inverting `x`, there is an involution `s ∈ Ĥ − V` which inverts `x`.

`h` necessarily has even order (`OddPowTwoPowInverting`), so some odd power `h ^ d` is a
`2`-element of order `2 ^ v`, `v ≥ 1`, still inverting `x`, and `v ≤ 2`
(`twoPow_le_two_of_mem_Hhat`).
For `v = 1` this `2`-element is the involution sought.  For `v = 2` the element has order `4`;
conjugating it into the Sylow `2`-subgroup `S` (`ConjMemSOfOrderTwoPow`) and using that all
elements of `S − V` act on `U` in the same way, together with the existence of an involution of
`S` outside `V` (`InvolutionNotMemOfCardEightDihedral`), produces the required involution. -/
theorem InvolutionInvertingMemU (I : Work.CORE3.Case1Inputs) (G : Type) [Group G] [Finite G]
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) {x h : G}
    (hxU : x ∈ B.U) (hx1 : x ≠ 1) (hhH : h ∈ B.Hhat) (hhx : h * x * h⁻¹ = x⁻¹) :
    ∃ s : G, s ∈ B.Hhat ∧ orderOf s = 2 ∧ s ∉ Work.GW2.pCoreIn 2 B.Hhat ∧
      s * x * s⁻¹ = x⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h26 : Work.GW2.Thm26Concl B := I.h26 G I.T.ft hBc B
  have hS8 : Nat.card (B.S : Subgroup G) = 8 := D.S8
  have h4 : Work.GW2.IsFourGroup (Work.GW2.pCoreIn 2 B.Hhat) := D.four
  have hVleS : Work.GW2.pCoreIn 2 B.Hhat ≤ (B.S : Subgroup G) :=
    Work.CORE2A.thm26Concl_O2_le_S h26
  have hVleCU : Work.GW2.pCoreIn 2 B.Hhat ≤ Subgroup.centralizer (B.U : Set G) :=
    (Work.CORE2A.thm26Concl_centralizer_eq h26) ▸ inf_le_right
  have hUnorm : B.Hhat ≤ Subgroup.normalizer (B.U : Set G) := by
    rw [← Work.CORE2A.thm26Concl_oddCore_eq h26]
    simpa [oddCoreIn] using
      le_normalizer_map_subtype B.Hhat (Work.GW2.oddCore ↥B.Hhat)
  have hVnorm : B.Hhat ≤
      Subgroup.normalizer ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) := by
    simpa [pCoreIn] using le_normalizer_map_subtype B.Hhat (Work.GW2.pCore 2 ↥B.Hhat)
  have hUodd : Odd (Nat.card B.U) := Work.CORE2A.bSetup_U_odd B
  have hxodd : Odd (orderOf x) :=
    Odd.of_dvd_nat hUodd (Subgroup.orderOf_dvd_natCard B.U hxU)
  have hxne : x ≠ x⁻¹ := by
    intro hcon
    have h2 : x ^ 2 = 1 := by rw [pow_two]; exact eq_inv_iff_mul_eq_one.mp hcon
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1' | h1'
    · exact hx1 (orderOf_eq_one_iff.mp h1')
    · exact absurd (h1' ▸ hxodd) (by decide)
  have hVcentU : ∀ w ∈ Work.GW2.pCoreIn 2 B.Hhat, ∀ y ∈ B.U, w * y * w⁻¹ = y := by
    intro w hw y hy
    have hcomm : y * w = w * y := (Subgroup.mem_centralizer_iff.mp (hVleCU hw)) y hy
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  -- ## Step 1: an odd power of `h` is a non-trivial `2`-element inverting `x`
  obtain ⟨d, hdodd, hdinv, v, hv1, hvord⟩ := OddPowTwoPowInverting hx1 hxodd hhx
  have hdmem : h ^ d ∈ B.Hhat := B.Hhat.pow_mem hhH d
  have hvle : v ≤ 2 := twoPow_le_two_of_mem_Hhat hBc B hS8 hdmem hvord
  by_cases hv : v = 1
  · refine ⟨h ^ d, hdmem, ?_, ?_, hdinv⟩
    · rw [hvord, hv, pow_one]
    · intro hmem
      exact hxne (hdinv.symm.trans (hVcentU _ hmem x hxU)).symm
  · -- ## Step 2: the `2`-element has order `4`
    have hv2 : v = 2 := by omega
    obtain ⟨c, hcH, hcS⟩ := ConjMemSOfOrderTwoPow B hdmem hvord
    have huord : orderOf (c * h ^ d * c⁻¹) = 4 := by
      rw [show c * h ^ d * c⁻¹ = (MulAut.conj c) (h ^ d) from by
            simp [MulAut.conj_apply, mul_assoc],
        MulEquiv.orderOf_eq, hvord, hv2]
      norm_num
    obtain ⟨n, hn2, hdihn⟩ := SylowDihedral G hBc B
    have hn4 : n = 4 := by
      obtain ⟨e⟩ := hdihn
      have hcard : Nat.card ↥(B.S : Subgroup G) = 2 * n := by
        rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
      omega
    have hdih : Nonempty ((B.S : Subgroup G) ≃* DihedralGroup 4) := hn4 ▸ hdihn
    obtain ⟨s₁, hs₁S, hs₁ord, hs₁V⟩ :=
      InvolutionNotMemOfCardEightDihedral (B.S : Subgroup G) (Work.GW2.pCoreIn 2 B.Hhat)
        hS8 hdih h4 hVleS
    have hx'U : c * x * c⁻¹ ∈ B.U :=
      ((Subgroup.mem_normalizer_iff.mp (hUnorm hcH)) x).mp hxU
    have hx'ne : c * x * c⁻¹ ≠ (c * x * c⁻¹)⁻¹ := by
      intro hcon
      apply hxne
      have key : c⁻¹ * (c * x * c⁻¹) * c = c⁻¹ * (c * x * c⁻¹)⁻¹ * c :=
        congrArg (fun t => c⁻¹ * t * c) hcon
      have h1 : c⁻¹ * (c * x * c⁻¹) * c = x := by group
      have h2 : c⁻¹ * (c * x * c⁻¹)⁻¹ * c = x⁻¹ := by
        have h2a : c⁻¹ * (c * x * c⁻¹)⁻¹ * c = (c⁻¹ * (c * x * c⁻¹) * c)⁻¹ := by group
        rw [h2a, h1]
      rw [h1, h2] at key
      exact key
    have huinv :
        c * h ^ d * c⁻¹ * (c * x * c⁻¹) * (c * h ^ d * c⁻¹)⁻¹ = (c * x * c⁻¹)⁻¹ := by
      calc c * h ^ d * c⁻¹ * (c * x * c⁻¹) * (c * h ^ d * c⁻¹)⁻¹
          = c * (h ^ d * x * (h ^ d)⁻¹) * c⁻¹ := by group
        _ = c * x⁻¹ * c⁻¹ := by rw [hdinv]
        _ = (c * x * c⁻¹)⁻¹ := by group
    have huV : c * h ^ d * c⁻¹ ∉ Work.GW2.pCoreIn 2 B.Hhat := by
      intro hmem
      have hfix :
          c * h ^ d * c⁻¹ * (c * x * c⁻¹) * (c * h ^ d * c⁻¹)⁻¹ = c * x * c⁻¹ :=
        hVcentU _ hmem (c * x * c⁻¹) hx'U
      rw [hfix] at huinv
      exact hx'ne huinv
    have hs₁inv : s₁ * (c * x * c⁻¹) * s₁⁻¹ = (c * x * c⁻¹)⁻¹ := by
      rw [conj_eq_of_mem_S_notMem_pCoreIn B h26 hS8 h4 hs₁S hcS hs₁V huV hx'U]
      exact huinv
    refine ⟨c⁻¹ * s₁ * c, ?_, ?_, ?_, ?_⟩
    · exact B.Hhat.mul_mem (B.Hhat.mul_mem (B.Hhat.inv_mem hcH)
        (Work.CORE2A.bSetup_S_le_Hhat B hs₁S)) hcH
    · calc orderOf (c⁻¹ * s₁ * c) = orderOf ((MulAut.conj c⁻¹) s₁) := by
            simp [mul_assoc]
        _ = orderOf s₁ := MulEquiv.orderOf_eq _ s₁
        _ = 2 := hs₁ord
    · intro hmem
      apply hs₁V
      have hconj : c * (c⁻¹ * s₁ * c) * c⁻¹ ∈ Work.GW2.pCoreIn 2 B.Hhat :=
        ((Subgroup.mem_normalizer_iff.mp (hVnorm hcH)) (c⁻¹ * s₁ * c)).mp hmem
      rwa [show c * (c⁻¹ * s₁ * c) * c⁻¹ = s₁ from by group] at hconj
    · calc c⁻¹ * s₁ * c * x * (c⁻¹ * s₁ * c)⁻¹
          = c⁻¹ * (s₁ * (c * x * c⁻¹) * s₁⁻¹) * c := by group
        _ = c⁻¹ * (c * x * c⁻¹)⁻¹ * c := by rw [hs₁inv]
        _ = (c⁻¹ * (c * x * c⁻¹) * c)⁻¹ := by group
        _ = x⁻¹ := by group

end Work.CORE3
