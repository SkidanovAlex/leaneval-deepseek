import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.CentralizerPcoreEqVU
import Submission.Work.CORE3.NormalizerPcoreEqHhat
import Submission.Work.CORE3.RelIndexHHhat
import Submission.Work.CORE3.FourGroupOddOrderFixed
import Submission.Work.CORE3.FourGroupOddOrderCommutingInvolution
import Submission.Work.CORE3.OddOrderMemOfMemSup

/-!
# CORE3: odd-order elements of `Ĥ` commuting with an involution lie in `U = O(H)`

`Work.CORE3.SevenOddCentralizer`: in the subcase `V = O₂(Ĥ)` of type `(2,2)` of Bender 1981 §3,
every element `h ∈ Ĥ` of **odd** order which commutes with an involution `s ∈ Ĥ` already lies in
`U = B.U = O(H) = O(Ĥ)`.

Mathematical content.  Write `V = O₂(Ĥ)` (a Klein four-group, `D.four`), `U = O(Ĥ)`, so that
`V ⊓ U = ⊥`, `V` centralizes `U`, and Bender's Theorem 2.6 together with
`Work.CORE3.CentralizerPcoreEqVU` gives `C_Ĥ(V) = C_G(V) ⊓ Ĥ = V ⊔ U`.  Let `h ∈ Ĥ` have odd
order and `s ∈ Ĥ` be an involution commuting with `h`.

* If `h ∈ V ⊔ U` then, writing `h = v * u` with `v ∈ V`, `u ∈ U` (the two commute), the oddness
  of `orderOf h` gives `v = 1`, so `h = u ∈ U` (`Work.CORE3.OddOrderMemOfMemSup`).
* If `h ∉ V ⊔ U`, then `h ∉ C_G(V)` and `h` has odd order, so `h` acts on the four-group `V`
  as a fixed-point-free automorphism: `V ⊓ C_G(h) = ⊥` (`Work.CORE3.FourGroupOddOrderFixed`).
  Since `s` normalizes `V` and commutes with `h` while `s² = 1`, the conjugation action of `s`
  on `V` is a power of that of `h`, and being an involution it must be trivial:
  `s ∈ C_G(V)` (`Work.CORE3.FourGroupOddOrderCommutingInvolution`).  Hence
  `s ∈ C_G(V) ⊓ Ĥ = V ⊔ U`, and since `s^2 = 1` with `U` of odd order, `s ∈ V`
  (`sq_eq_one_mem_left` below).  But then `s ∈ V ⊓ C_G(h) = ⊥`, contradicting `s ≠ 1`.

The argument is purely structural: it uses `I.h26` (Bender's Theorem 2.6, for the shape of `Ĥ`)
and `Work.CORE3.CentralizerPcoreEqVU`, but none of the counting data of §3.
-/

namespace Work.CORE3

open Subgroup
open Work.GW2
open Pointwise

/-- If `V` is a four-group, `U` has odd order and `V` centralizes `U`, then every element of
`V ⊔ U` whose square is `1` lies in `V`.  (Mirror image of `Work.CORE3.OddOrderMemOfMemSup`,
which handles elements of odd order.) -/
private theorem sq_eq_one_mem_left {G : Type} [Group G] [Finite G] {V U : Subgroup G} {x : G}
    (hV4 : Work.GW2.IsFourGroup V) (hUodd : Odd (Nat.card U))
    (hVU : V ≤ Subgroup.centralizer (U : Set G))
    (hx : x ∈ V ⊔ U) (hx2 : x ^ 2 = 1) : x ∈ V := by
  have hcoe : (↑(V ⊔ U) : Set G) = (V : Set G) * (U : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right V U
      (hVU.trans (Subgroup.centralizer_le_normalizer _))
  have hx' : x ∈ (V : Set G) * (U : Set G) := by rw [← hcoe]; exact hx
  rw [Set.mem_mul] at hx'
  obtain ⟨v, hv, u, hu, rfl⟩ := hx'
  have hcomm : Commute v u := ((Subgroup.mem_centralizer_iff.mp (hVU hv)) u hu).symm
  have hv2 : v ^ 2 = 1 := hV4.2 v hv
  have hu2 : u ^ 2 = 1 := by
    have h := hx2
    rw [hcomm.mul_pow 2, hv2, one_mul] at h
    exact h
  have hu1 : u = 1 := by
    have hdvd : orderOf u ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hu2
    have hdvdU : orderOf u ∣ Nat.card U := Subgroup.orderOf_dvd_natCard U hu
    have hcop : Nat.Coprime 2 (Nat.card U) := Nat.coprime_two_left.mpr hUodd
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvd hdvdU)
  rw [hu1, mul_one]
  exact hv

theorem SevenOddCentralizer (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) {s h : G} (hs : s ∈ B.Hhat) (hs2 : orderOf s = 2)
    (hh : h ∈ B.Hhat) (hcomm : s * h = h * s) (hodd : Odd (orderOf h)) : h ∈ B.U := by
  classical
  -- Bender's Theorem 2.6: `V = O₂(Ĥ) = S ⊓ C_G(U)` and `C_Ĥ(V) = V ⊔ U`.
  have h26 : Thm26Concl B := I.h26 G I.T.ft hBc B
  have hVU : pCoreIn 2 B.Hhat ≤ Subgroup.centralizer (B.U : Set G) := by
    rw [← h26.2.1]
    exact inf_le_right
  have hcentV : Subgroup.centralizer ((pCoreIn 2 B.Hhat : Subgroup G) : Set G) ⊓ B.Hhat
      = pCoreIn 2 B.Hhat ⊔ B.U := CentralizerPcoreEqVU G I hBc B h1 D
  have hVnorm : B.Hhat ≤ Subgroup.normalizer ((pCoreIn 2 B.Hhat : Subgroup G) : Set G) :=
    le_normalizer_map_subtype B.Hhat (Work.GW2.pCore 2 ↥B.Hhat)
  have hUodd : Odd (Nat.card B.U) := Work.CORE2A.bSetup_U_odd B
  -- `V` and `U` have coprime order, so they intersect trivially.
  have hdisj : pCoreIn 2 B.Hhat ⊓ B.U = ⊥ := by
    have hcop : Nat.Coprime (Nat.card (pCoreIn 2 B.Hhat)) (Nat.card B.U) := by
      rw [D.four.1, show (4 : ℕ) = 2 ^ 2 from rfl]
      exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hUodd)
    exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)
  by_cases hmem : h ∈ pCoreIn 2 B.Hhat ⊔ B.U
  · -- `h ∈ V ⊔ U`: an odd-order element of `V · U` lies in the odd factor `U`.
    exact OddOrderMemOfMemSup D.four hUodd hdisj hVU hmem hodd
  · -- `h ∉ V ⊔ U`, hence `h ∉ C_G(V)`: `h` acts fixed-point-freely on `V`.
    have hnc : h ∉ Subgroup.centralizer ((pCoreIn 2 B.Hhat : Subgroup G) : Set G) := fun hc =>
      hmem (hcentV ▸ Subgroup.mem_inf.mpr ⟨hc, hh⟩)
    have hfix : pCoreIn 2 B.Hhat ⊓ Subgroup.centralizer ({h} : Set G) = ⊥ :=
      FourGroupOddOrderFixed D.four (hVnorm hh) hodd hnc
    -- an involution commuting with `h` centralizes `V`
    have hs2' : s ^ 2 = 1 := by
      rw [← hs2]
      exact pow_orderOf_eq_one s
    have hsc : s ∈ Subgroup.centralizer ((pCoreIn 2 B.Hhat : Subgroup G) : Set G) :=
      FourGroupOddOrderCommutingInvolution D.four (hVnorm hh) (hVnorm hs) hodd hnc hs2' hcomm
    have hsVU : s ∈ pCoreIn 2 B.Hhat ⊔ B.U :=
      hcentV ▸ Subgroup.mem_inf.mpr ⟨hsc, hs⟩
    have hsV : s ∈ pCoreIn 2 B.Hhat :=
      sq_eq_one_mem_left D.four hUodd hVU hsVU hs2'
    have hsc2 : s ∈ Subgroup.centralizer ({h} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hcomm
    have hbot : s ∈ pCoreIn 2 B.Hhat ⊓ Subgroup.centralizer ({h} : Set G) := ⟨hsV, hsc2⟩
    rw [hfix] at hbot
    have hs1 : s = 1 := Subgroup.mem_bot.mp hbot
    rw [hs1, orderOf_one] at hs2
    exact absurd hs2 (by decide)

end Work.CORE3
