import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.Case1bEightNineDefs
import Submission.Work.CORE3.InvSetThreeSubgroup
import Submission.Work.CORE3.Case1bCount
import Submission.Work.CORE3.Case1bEightNine
import Submission.Work.CORE3.Case1bDStructure
import Submission.Work.CORE3.NormalizerPcoreEqHhat
import Submission.Work.CORE3.SylowDihedral
import Submission.Work.CORE3.VUInvSetTrivial
import Submission.Work.CORE3.OrderThreeLeCentralizer
import Submission.Work.CORE3.SevenConjU
import Submission.Work.CORE3.CentralizerPcoreEqVU
import Submission.Work.CORE3.J4.J4GStructNoInvCentralizer
import Submission.Work.CORE3.J4.ExistsConjEqInvOrderThree
import Submission.Work.CORE3.CosetInvCountLeSix
import Submission.Work.CORE2A.lemma24
import Submission.Work.BSW.Cases.K4.CardSup


/-!
# Cycle-free copy of `Submission/Work/CORE3/J4/J4SevenNeThree.lean`

The original module imports `Submission.Work.CORE3.CentHhatOrderThree`, which in turn imports
`Submission.Work.CORE3.Case1bThree` — but that import is unused in the file.  This module is a
verbatim copy with that single import line removed, so that the `J₃`-argument in
`Submission.Work.CORE3.JthreeOddNC` (and hence `Work.CORE3.Case1bThree`) can use Bender's step (7)
without importing its own module.  All declarations are unchanged.
-/

/-!
# `Work.CORE3.J4.J4SevenNeThree`

The `J₃`-exclusion of Bender 1981 §3, p. 224, in the `J₄`-form needed by the assembly
`Work.CORE3.J4.J4SevenCore`: if an involution `y ∉ Ĥ` inverts a non-trivial odd-order subgroup
`X ≤ Ĥ` whose centralizer and normalizer in `G` both have even order, then the coset `y Ĥ` does
*not* carry exactly three involutions.

## The argument

Assume `n := cosetInvCount Ĥ y = 3`.  Then the inverted set `I_Ĥ(y)` is the order-`3` subgroup
`X = ⟨x⟩` with `x ∉ VU = O₂(Ĥ)·O(Ĥ)` (Bender (5), (6)).

1. `Even |C_G(X)|` gives `X = U^g` for some `g` (`Work.CORE3.SevenConjU`), whence
   `N_G(X) = Ĥ^g = conjSub g B.Hhat`.  As `V^g ≤ C_G(X)` and `C_Ĥ(X)` has no involution
   (`Work.CORE3.J4.J4GStructNoInvCentralizer`), `V^g ⊓ Ĥ = ⊥`.
2. `y ∈ Ĥ^g ∖ V^g` (it inverts the order-`3` element `x`).
3. Counting: `P := ⟨x⟩ ⊔ U` has order `9` and lies in `D := Ĥ ⊓ Ĥ^g` (it centralizes `x`, hence
   normalizes `⟨x⟩ = X`), while `4 * |D| = |V^g ⊔ D| ≤ |Ĥ^g| = 72`; hence `|D| = 18` and
   `Ĥ^g = D · V^g`.
4. So `y = d · v` with `d ∈ D`, `v ∈ V^g`, `d ≠ 1`, and `y d y⁻¹ = d`.  As `|D : P| = 2`:
   * if `d ∈ P`, then `d` and `v` both centralize `x`, so `y` centralizes `x`, contradicting
     `y x y⁻¹ = x⁻¹ ≠ x`;
   * if `d ∉ P`, then `d² ∈ P`, so an odd `orderOf d` would give `d = (d²)^{-t} ∈ P`; hence
     `orderOf d` is even and a power of `d` is an involution of `Ĥ` commuting with `y` —
     contradicting `Work.CORE3.eq_one_of_sq_eq_one_of_ncard_three` (for `n = 3` the only
     involution of `Ĥ` commuting with `y` is `1`).
-/

namespace Work.CORE3.J4

open Subgroup
open Work.GW2
open Pointwise
open Pointwise
open Pointwise
open Pointwise
open Pointwise
open Pointwise
open Pointwise
open Pointwise
open Pointwise
open Pointwise
open Pointwise
open Pointwise
open Pointwise
open Pointwise

variable {G : Type} [Group G] [Finite G]

set_option maxHeartbeats 1000000

/-- `N_G(U) = Ĥ` in the `Case1bData` setting, from `|U| = 3` alone (without the counting input
`Case1bEightNineProp` consumed by `Work.CORE3.Jthree_normalizer_U_eq_Hhat`). -/
theorem normalizer_U_eq_Hhat_of_card_three (I : Work.CORE3.Case1Inputs)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) (hU3 : Nat.card B.U = 3) :
    Subgroup.normalizer (B.U : Set G) = B.Hhat := by
  haveI : IsSimpleGroup G := hBc.simple
  have hU : Work.GW2.oddCoreIn B.Hhat = B.U := (I.h26 G I.T.ft hBc B).1
  have hUmap : (Work.GW2.oddCore ↥B.Hhat).map B.Hhat.subtype = B.U := by
    rw [← hU]; rfl
  have hUle : B.U ≤ B.Hhat := hUmap ▸ Subgroup.map_subtype_le _
  have hne : B.U ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card (B.U : Subgroup G) = 1 := by rw [hbot]; exact Subgroup.card_bot
    omega
  have hle : B.Hhat ≤ Subgroup.normalizer (B.U : Set G) := by
    have h := Work.CORE3.le_normalizer_map_subtype B.Hhat (Work.GW2.oddCore ↥B.Hhat)
    rwa [hUmap] at h
  exact Work.CORE2A.normalizer_eq_of_coatom B.Hhat_coatom hUle hne hle

/-- `|Ĥ| = 72` in the `Case1bData` setting, from `|U| = 3` alone. -/
theorem card_Hhat_eq_72_of_card_three (I : Work.CORE3.Case1Inputs)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) (hU3 : Nat.card B.U = 3) :
    Nat.card B.Hhat = 72 := by
  classical
  have h26 : Work.GW2.Thm26Concl B := I.h26 G I.T.ft hBc B
  have hVpS : Work.GW2.pCoreIn 2 B.Hhat ≤ (B.S : Subgroup G) :=
    Work.CORE2A.thm26Concl_O2_le_S h26
  have hUcV : B.U ≤ Subgroup.centralizer (Work.GW2.pCoreIn 2 B.Hhat : Set G) := by
    intro u hu
    have hmem : u ∈ Subgroup.centralizer ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) ⊓
        B.Hhat := by
      rw [Work.CORE3.CentralizerPcoreEqVU G I hBc B h1 D]
      exact Subgroup.mem_sup_right hu
    exact hmem.1
  have hdisj : Work.GW2.pCoreIn 2 B.Hhat ⊓ B.U = ⊥ := by
    refine le_bot_iff.mp ?_
    intro xval hx
    rw [Subgroup.mem_inf] at hx
    have hxS : xval ∈ (B.S : Subgroup G) := hVpS hx.1
    have hbot : xval ∈ B.U ⊓ (B.S : Subgroup G) := ⟨hx.2, hxS⟩
    rwa [Work.CORE2A.inf_U_S_eq_bot B] at hbot
  have hcardVU : Nat.card ↥(Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) = 12 := by
    have h := Work.BSW.Cases.K4.card_sup_of_le_normalizer_of_inf_eq_bot
      (H := Work.GW2.pCoreIn 2 B.Hhat) (K := B.U)
      (Subgroup.centralizer_le_normalizer _ |> fun hh => hUcV.trans hh) hdisj
    rw [h, D.four.1, hU3]
  have hrel : (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U).relIndex B.Hhat = 6 :=
    Work.CORE3.relIndex_VU_Hhat G I hBc B h1 D
  have hVUleH : Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U ≤ B.Hhat :=
    sup_le (Work.CORE2A.thm26Concl_O2_le_Hhat h26) (Work.CORE2A.thm26Concl_U_le_Hhat h26)
  have h := Subgroup.relIndex_mul_card (H := Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) (K := B.Hhat)
  rw [inf_eq_left.mpr hVUleH, hcardVU, hrel] at h
  exact h.symm

/-- An element of a subgroup of index two outside the subgroup has even order. -/
theorem even_orderOf_of_index_two {P Dsub : Subgroup G} (hPle : P ≤ Dsub)
    (hcard : Nat.card ↥Dsub = 2 * Nat.card ↥P) {d : G} (hdD : d ∈ Dsub) (hdP : d ∉ P) :
    Even (orderOf d) := by
  classical
  -- `P` has index `2` in `Dsub`
  have hrel : P.relIndex Dsub = 2 := by
    have h := Subgroup.relIndex_mul_card (H := P) (K := Dsub)
    rw [inf_eq_left.mpr hPle, hcard] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hidx : (P.subgroupOf Dsub).index = 2 := by
    have h := Subgroup.relIndex_subgroupOf (H := P) (K := Dsub) (L := Dsub) le_rfl
    rw [Subgroup.subgroupOf_self, Subgroup.relIndex_top_right, hrel] at h
    exact h
  -- hence `d ^ 2 ∈ P`
  have hd2P : d ^ 2 ∈ P := by
    haveI : (P.subgroupOf Dsub).Normal := Subgroup.normal_of_index_eq_two hidx
    have hq : Nat.card (↥Dsub ⧸ (P.subgroupOf Dsub)) = 2 := by
      rw [← Subgroup.index_eq_card (P.subgroupOf Dsub), hidx]
    have h2 : (QuotientGroup.mk' (P.subgroupOf Dsub) (⟨d, hdD⟩ : ↥Dsub)) ^ 2 = 1 := by
      have hdvd : orderOf (QuotientGroup.mk' (P.subgroupOf Dsub) (⟨d, hdD⟩ : ↥Dsub)) ∣
          Nat.card (↥Dsub ⧸ (P.subgroupOf Dsub)) := by
        simpa using Subgroup.orderOf_dvd_natCard
          (⊤ : Subgroup (↥Dsub ⧸ (P.subgroupOf Dsub))) (Subgroup.mem_top _)
      rw [hq] at hdvd
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd
    rw [← map_pow (QuotientGroup.mk' (P.subgroupOf Dsub))] at h2
    have h4 : (⟨d, hdD⟩ : ↥Dsub) ^ 2 ∈ P.subgroupOf Dsub :=
      (QuotientGroup.eq_one_iff _).mp h2
    have h5 : (d ^ 2 : G) ∈ P := by
      have := Subgroup.mem_subgroupOf.mp h4
      simpa using this
    exact h5
  -- an odd order would force `d ∈ P`
  by_contra hnot
  rw [Nat.not_even_iff_odd] at hnot
  obtain ⟨t, ht⟩ := hnot
  have hpow : d ^ orderOf d = 1 := pow_orderOf_eq_one d
  have heq : (d ^ 2) ^ t * d = 1 := by
    have h2 : d ^ (2 * t + 1) = 1 := by rw [← ht]; exact hpow
    rwa [pow_succ, pow_mul] at h2
  have hdt : (d ^ 2) ^ t = d⁻¹ := eq_inv_of_mul_eq_one_left (by rw [heq]) 
  have hmem : (d ^ 2) ^ t ∈ P := Subgroup.pow_mem P hd2P t
  rw [hdt] at hmem
  exact hdP (by simpa using P.inv_mem hmem)

/-- The `J₃`-exclusion, in contradiction form. -/
theorem not_cosetInvCount_eq_three (I : Work.CORE3.Case1Inputs)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) (hU3 : Nat.card B.U = 3)
    {y : G} (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat) {X : Subgroup G} (hXne : X ≠ ⊥)
    (hXodd : Odd (Nat.card X)) (hXH : X ≤ B.Hhat)
    (hinv : ∀ x ∈ X, y * x * y⁻¹ = x⁻¹)
    (hCe : Even (Nat.card (Subgroup.centralizer (X : Set G))))
    (hNe : Even (Nat.card (Subgroup.normalizer (X : Set G))))
    (h3 : Work.GW2.cosetInvCount B.Hhat y = 3) : False := by
  classical
  have hy1 : y * y = 1 := (Work.CORE3.orderOf_eq_two_iff_mul_self y).mp hy2 |>.1
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy1
  -- ## Step 1: `X = I_Ĥ(y)` is an order-`3` subgroup `⟨x⟩`
  have hXI : (X : Set G) ⊆ Work.CORE3.invSetIn B.Hhat y := by
    intro xval hx
    exact ⟨hXH hx, by simpa [hyinv] using hinv xval hx⟩
  have hIcard : (Work.CORE3.invSetIn B.Hhat y).ncard = 3 := by
    rw [Work.CORE3.ncard_invSetIn_eq_cosetInvCount B.Hhat y hy1 hyH]
    exact h3
  have hcoeX : (X : Set G).ncard = Nat.card X := Nat.card_coe_set_eq (X : Set G)
  have hXcard : Nat.card X = 3 := by
    have hle : Nat.card X ≤ (Work.CORE3.invSetIn B.Hhat y).ncard := by
      have h := Set.ncard_le_ncard hXI (Set.toFinite _)
      rw [hcoeX] at h
      exact h
    have h1lt : 1 < Nat.card X := (Subgroup.one_lt_card_iff_ne_bot X).mpr hXne
    obtain ⟨k, hk⟩ := hXodd
    omega
  have hXIeq' : (X : Set G) = Work.CORE3.invSetIn B.Hhat y := by
    refine Set.eq_of_subset_of_ncard_le hXI ?_
    rw [hIcard, hcoeX, hXcard]
  have hXIeq : Work.CORE3.invSetIn B.Hhat y = (X : Set G) := hXIeq'.symm
  obtain ⟨x, hxH, hx3, hxinv, hcl⟩ :=
    Work.CORE3.InvSetThreeSubgroup B.Hhat y hy1 hyH h3
  have hxI : x ∈ Work.CORE3.invSetIn B.Hhat y := ⟨hxH, hxinv⟩
  have hxX : x ∈ X := by
    change x ∈ (X : Set G)
    rw [← hXIeq]
    exact hxI
  have hXeqz : X = Subgroup.zpowers x :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxX)
      (by rw [Nat.card_zpowers, hx3, hXcard])).symm
  have hxVU : x ∉ (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U : Subgroup G) := by
    intro hxmem
    have h5 := Work.CORE3.VUInvSetTrivial G I hBc B h1 D y hy2 hyH
    have hmem : x ∈ Work.GW2.invSet (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) y :=
      ⟨hxmem, by rw [hyinv]; exact hxinv⟩
    rw [h5] at hmem
    have hx1 : x = 1 := Set.mem_singleton_iff.mp hmem
    rw [hx1] at hx3
    exact absurd hx3 (by norm_num)
  -- for `n = 3` the only involution of `Ĥ` commuting with `y` is `1`
  have hnoinv : ∀ w ∈ B.Hhat, w * w = 1 → y * w * y⁻¹ = w → w = 1 := by
    intro w hwH hwsq hwcomm
    have hwI : w ∈ Work.CORE3.invSetIn B.Hhat y := by
      refine ⟨hwH, ?_⟩
      show y * w * y = w⁻¹
      calc y * w * y = y * w * y⁻¹ := by rw [hyinv]
        _ = w := hwcomm
        _ = w⁻¹ := (inv_eq_of_mul_eq_one_right hwsq).symm
    exact Work.CORE3.eq_one_of_sq_eq_one_of_ncard_three hy1 hIcard hwI hwsq
  -- ## Step 2: `X = U^g`, `N_G(X) = Ĥ^g`
  obtain ⟨g, hXg⟩ :=
    Work.CORE3.SevenConjU G I hBc B h1 D hU3 hy2 hyH hXH hXne hXodd hinv hCe
  set Vg : Subgroup G := Work.GW2.conjSub g (Work.GW2.pCoreIn 2 B.Hhat) with hVg
  set Hg : Subgroup G := Work.GW2.conjSub g B.Hhat with hHg
  have hVgsq : ∀ v ∈ Vg, v * v = 1 := by
    intro v hv
    rw [hVg, Work.CORE2A.conjSub_eq_map, Subgroup.mem_map] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    have hu2 : u * u = 1 := by
      have h := D.four.2 u hu
      rwa [pow_two] at h
    show (g * u * g⁻¹) * (g * u * g⁻¹) = 1
    rw [show (g * u * g⁻¹) * (g * u * g⁻¹) = g * (u * u) * g⁻¹ by group, hu2, mul_one,
      mul_inv_cancel]
  have hUcV : B.U ≤ Subgroup.centralizer (Work.GW2.pCoreIn 2 B.Hhat : Set G) := by
    intro w hw
    have hmem : w ∈ Subgroup.centralizer
        ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) ⊓ B.Hhat := by
      rw [Work.CORE3.CentralizerPcoreEqVU G I hBc B h1 D]
      exact Subgroup.mem_sup_right hw
    exact hmem.1
  have hVgC : Vg ≤ Subgroup.centralizer (X : Set G) := by
    rw [hXg, hVg]
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    rw [Work.CORE2A.conjSub_eq_map] at hv hu
    obtain ⟨v₀, hv₀, rfl⟩ := Subgroup.mem_map.mp hv
    obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.mp hu
    have hcomm : v₀ * u₀ = u₀ * v₀ := (Subgroup.mem_centralizer_iff.mp (hUcV hu₀)) v₀ hv₀
    rw [← map_mul, ← map_mul, hcomm]
  have hVgInfH : Vg ⊓ B.Hhat = ⊥ := by
    refine le_bot_iff.mp ?_
    intro w hw
    rw [Subgroup.mem_inf] at hw
    obtain ⟨hwV, hwH⟩ := hw
    rw [Subgroup.mem_bot]
    by_contra hw1
    have hwsq : w * w = 1 := hVgsq w hwV
    exact Work.CORE3.J4.J4GStructNoInvCentralizer I hBc B h1 D hy2 hyH hXH hXne hXodd
      hinv ⟨w, hwH, (Work.CORE3.orderOf_eq_two_iff_mul_self w).mpr ⟨hwsq, hw1⟩, hVgC hwV⟩
  have hyinv_mem : ∀ w ∈ X, y * w * y⁻¹ = w⁻¹ :=
    fun w hw => by simpa [hyinv] using hinv w hw
  have hyN : y ∈ Subgroup.normalizer (X : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · intro hv
      rw [hyinv_mem v hv]
      exact X.inv_mem hv
    · intro hv
      have h3 : v = y * (y * v * y⁻¹) * y⁻¹ := by
        have h4 : y * (y * v * y⁻¹) * y⁻¹ = v := by
          rw [hyinv]
          calc y * (y * v * y) * y = (y * y) * v * (y * y) := by group
            _ = v := by rw [hy1, one_mul, mul_one]
        exact h4.symm
      rw [h3, hyinv_mem (y * v * y⁻¹) hv]
      exact X.inv_mem hv
  have hNX : Subgroup.normalizer (X : Set G) = Hg := by
    rw [hXg, hHg, Work.CORE2A.normalizer_conjSub,
      normalizer_U_eq_Hhat_of_card_three I hBc B h1 D hU3]
  have hyHg : y ∈ Hg := by rw [← hNX]; exact hyN
  have hyVg : y ∉ Vg := by
    intro hyv
    have hcomm : y * x = x * y := ((Subgroup.mem_centralizer_iff.mp (hVgC hyv)) x hxX).symm
    have hthis : y * x * y⁻¹ = x := by
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    rw [hinv x hxX] at hthis
    have hx2 : x * x = 1 := by
      have h2 : x⁻¹ = x := hthis
      calc x * x = x⁻¹ * x := by rw [h2]
        _ = 1 := inv_mul_cancel x
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hx2)
    rw [hx3] at hdvd
    norm_num at hdvd
  -- ## Step 3: `P = ⟨x⟩ ⊔ U` has order `9` and lies in `Ĥ ⊓ Ĥ^g`
  set P : Subgroup G := Subgroup.zpowers x ⊔ B.U with hP
  have hUcX : B.U ≤ Subgroup.centralizer ({x} : Set G) := by
    refine Work.CORE3.OrderThreeLeCentralizer ?_ hx3 hU3
    have hUmap : (Work.GW2.oddCore ↥B.Hhat).map B.Hhat.subtype = B.U := by
      have hU : Work.GW2.oddCoreIn B.Hhat = B.U := (I.h26 G I.T.ft hBc B).1
      rw [← hU]; rfl
    have hHnorm : B.Hhat ≤ Subgroup.normalizer ((B.U : Subgroup G) : Set G) := by
      have h := Work.CORE3.le_normalizer_map_subtype B.Hhat (Work.GW2.oddCore ↥B.Hhat)
      rwa [hUmap] at h
    refine Subgroup.mem_normalizer_iff.mpr (fun k => ?_)
    constructor
    · intro hk
      exact (Subgroup.le_normalizer_iff.mp hHnorm) x hxH k hk
    · intro hk
      have hk' := (Subgroup.le_normalizer_iff.mp hHnorm) x⁻¹ (B.Hhat.inv_mem hxH)
        (x * k * x⁻¹) hk
      rwa [show x⁻¹ * (x * k * x⁻¹) * (x⁻¹)⁻¹ = k by group] at hk'
  have hUleNorm : B.U ≤ Subgroup.normalizer (X : Set G) := by
    have hcle : Subgroup.centralizer ({x} : Set G) ≤
        Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
      intro u hu
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hh
        have hux : u * x * u⁻¹ = x := by
          rw [Subgroup.mem_centralizer_singleton_iff.mp hu]
          rw [mul_assoc, mul_inv_cancel, mul_one]
        have h2 : u * x ^ n * u⁻¹ = x ^ n := by
          rw [show u * x ^ n * u⁻¹ = (u * x * u⁻¹) ^ n by
            rw [← MulAut.conj_apply u (x ^ n), map_zpow, MulAut.conj_apply], hux]
        rw [← hn, h2]
        exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) n
      · intro hh
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hh
        have hux : u⁻¹ * x * u = x := by
          have h1 : u * x = x * u := Subgroup.mem_centralizer_singleton_iff.mp hu
          calc u⁻¹ * x * u = u⁻¹ * (x * u) := by rw [mul_assoc]
            _ = u⁻¹ * (u * x) := by rw [← h1]
            _ = x := by rw [← mul_assoc, inv_mul_cancel, one_mul]
        have h2 : u⁻¹ * (u * h * u⁻¹) * u = h := by group
        have h3 : u⁻¹ * x ^ n * u = x ^ n := by
          have hb : u⁻¹ * x * u = (MulAut.conj u⁻¹) x := by
            rw [MulAut.conj_apply, inv_inv]
          have hl : u⁻¹ * x ^ n * u = (MulAut.conj u⁻¹) (x ^ n) := by
            rw [MulAut.conj_apply, inv_inv]
          rw [hl, map_zpow, ← hb, hux]
        rw [← hn, h3] at h2
        rw [← h2]
        exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) n
    rw [hXeqz]
    exact hUcX.trans hcle
  have hPcard : Nat.card P = 9 := by
    have hdisj : Subgroup.zpowers x ⊓ B.U = ⊥ := by
      refine le_bot_iff.mp ?_
      intro w hw
      rw [Subgroup.mem_inf] at hw
      obtain ⟨hwz, hwU⟩ := hw
      rw [Subgroup.mem_bot]
      by_contra hw1
      have hw3 : orderOf w = 3 := by
        have hdvd : orderOf w ∣ 3 := by
          have h := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers x) hwz
          rwa [Nat.card_zpowers, hx3] at h
        rcases Nat.Prime.eq_one_or_self_of_dvd (by norm_num : Nat.Prime 3) _ hdvd with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) hw1
        · exact h
      have hweq : Subgroup.zpowers w = B.U := by
        refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hwU) ?_
        rw [Nat.card_zpowers, hw3, hU3]
      have hUle : B.U ≤ Subgroup.zpowers x := by
        rw [← hweq]
        exact Subgroup.zpowers_le.mpr hwz
      have hxU : x ∈ B.U := by
        rw [Subgroup.eq_of_le_of_card_ge hUle (by rw [Nat.card_zpowers, hx3, hU3])]
        exact Subgroup.mem_zpowers x
      exact hxVU (Subgroup.mem_sup_right hxU)
    have hun : B.U ≤ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
      rw [← hXeqz]
      exact hUleNorm
    have h := Work.BSW.Cases.K4.card_sup_of_le_normalizer_of_inf_eq_bot
      (H := Subgroup.zpowers x) (K := B.U) hun hdisj
    rw [hP, h, Nat.card_zpowers, hx3, hU3]
  have hPleD : P ≤ B.Hhat ⊓ Hg := by
    refine le_inf ?_ ?_
    · rw [hP]
      exact sup_le (Subgroup.zpowers_le.mpr hxH) (Work.CORE2A.thm26Concl_U_le_Hhat
        (I.h26 G I.T.ft hBc B))
    · rw [hP, ← hNX]
      refine sup_le ?_ ?_
      · rw [hXeqz]; exact Subgroup.le_normalizer
      · exact hUleNorm
  -- ## Step 4: the preliminaries of the counting step
  have hDnorm : B.Hhat ⊓ Hg ≤ Subgroup.normalizer (Vg : Set G) := by
    rw [hHg, hVg, Work.CORE2A.normalizer_conjSub,
      Work.CORE3.NormalizerPcoreEqHhat G hBc B D.four]
    exact inf_le_right
  have hle1 : Vg ⊔ (B.Hhat ⊓ Hg) ≤ Hg := by
    rw [sup_le_iff]
    refine ⟨?_, inf_le_right⟩
    rw [hVg, hHg]
    exact Work.CORE2A.conjSub_mono (Subgroup.map_subtype_le _) g
  have hinf : Vg ⊓ (B.Hhat ⊓ Hg) = ⊥ := by
    refine le_bot_iff.mp ?_
    intro w hw
    rw [Subgroup.mem_inf] at hw
    exact (le_bot_iff.mpr hVgInfH) ⟨hw.1, hw.2.1⟩
  have hcardVg : Nat.card Vg = 4 := by rw [hVg, Work.CORE2A.card_conjSub]; exact D.four.1
  have hcardHg : Nat.card Hg = 72 := by
    rw [hHg, Work.CORE2A.card_conjSub, card_Hhat_eq_72_of_card_three I hBc B h1 D hU3]
  -- ## Step 5: `|Ĥ ⊓ Ĥ^g| = 18`
  have hDcard : Nat.card ↥(B.Hhat ⊓ Hg) = 18 := by
    -- `9 ∣ |D|` (via `P ≤ D` of order `9`)
    have h9 : 9 ∣ Nat.card ↥(B.Hhat ⊓ Hg) := by
      rw [← hPcard]
      exact Subgroup.card_dvd_of_le hPleD
    -- `4 * |D| ≤ 72`
    have h4 : Nat.card ↥(Vg ⊔ (B.Hhat ⊓ Hg)) = 4 * Nat.card ↥(B.Hhat ⊓ Hg) := by
      have h := Work.BSW.Cases.K4.card_sup_of_le_normalizer_of_inf_eq_bot
        (H := Vg) (K := B.Hhat ⊓ Hg) hDnorm hinf
      rw [h, hcardVg]
    have hcardle : Nat.card ↥(Vg ⊔ (B.Hhat ⊓ Hg)) ≤ Nat.card ↥Hg := by
      have h := Subgroup.card_le_card_group ((Vg ⊔ (B.Hhat ⊓ Hg)).subgroupOf Hg)
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle1).toEquiv] at h
    have hle18 : Nat.card ↥(B.Hhat ⊓ Hg) ≤ 18 := by omega
    -- `D ≠ C_Ĥ(x) = P`, so `|D| ≠ 9`
    have hne9 : Nat.card ↥(B.Hhat ⊓ Hg) ≠ 9 := by
      intro h9'
      have hDeq : B.Hhat ⊓ Hg = P :=
        (Subgroup.eq_of_le_of_card_ge hPleD (by rw [h9', hPcard])).symm
      -- some element of `Ĥ` inverts `x`, hence normalizes `X = ⟨x⟩` without centralizing it
      obtain ⟨h, hhH, hhinv⟩ :=
        ExistsConjEqInvOrderThree I hBc B h1 D hU3 hxH hx3 hxVU
      have hconj : Work.GW2.conjSub h X = X := by
        rw [hXeqz, Work.CORE2A.conjSub_eq_map, MonoidHom.map_zpowers]
        rw [show (MulAut.conj h).toMonoidHom x = h * x * h⁻¹ by
          rw [show (MulAut.conj h).toMonoidHom x = (MulAut.conj h) x from rfl,
            MulAut.conj_apply]]
        rw [hhinv]
        exact Subgroup.zpowers_inv
      have hhN : h ∈ Subgroup.normalizer (X : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro v
        constructor
        · intro hv
          rw [← hconj]
          exact (Work.CORE2A.mem_conjSub_iff (g := h) (K := X)).mpr (by
            rwa [show h⁻¹ * (h * v * h⁻¹) * h = v by group])
        · intro hv
          have h3 : h * v * h⁻¹ ∈ Work.GW2.conjSub h X := by rw [hconj]; exact hv
          have h2 : h⁻¹ * (h * v * h⁻¹) * h ∈ X :=
            (Work.CORE2A.mem_conjSub_iff (g := h) (K := X)).mp h3
          rwa [show h⁻¹ * (h * v * h⁻¹) * h = v by group] at h2
      have hhD : h ∈ B.Hhat ⊓ Hg := by
        rw [← hNX]
        exact ⟨hhH, hhN⟩
      have hhP : h ∈ P := by rw [← hDeq]; exact hhD
      have hle : P ≤ Subgroup.centralizer ({x} : Set G) := by
        rw [hP]
        exact sup_le (Subgroup.zpowers_le.mpr
          (Subgroup.mem_centralizer_singleton_iff.mpr rfl)) hUcX
      have hcomm : h * x = x * h := Subgroup.mem_centralizer_singleton_iff.mp (hle hhP)
      have hthis : h * x * h⁻¹ = x := by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      rw [hhinv] at hthis
      have hx2 : x * x = 1 := by
        have h2 : x⁻¹ = x := hthis
        calc x * x = x⁻¹ * x := by rw [h2]
          _ = 1 := inv_mul_cancel x
      have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hx2)
      rw [hx3] at hdvd
      norm_num at hdvd
    obtain ⟨m, hm⟩ := h9
    have hmle : m ≤ 2 := by omega
    have hmne0 : m ≠ 0 := by
      intro h0
      have hzero : Nat.card ↥(B.Hhat ⊓ Hg) = 0 := by rw [hm, h0, mul_zero]
      exact Nat.card_pos.ne' hzero
    have hmne1 : m ≠ 1 := by
      intro h1
      rw [h1, mul_one] at hm
      exact hne9 hm
    omega
  have hsup : Vg ⊔ (B.Hhat ⊓ Hg) = Hg := by
    have h := Work.BSW.Cases.K4.card_sup_of_le_normalizer_of_inf_eq_bot
      (H := Vg) (K := B.Hhat ⊓ Hg) hDnorm hinf
    have hcard : Nat.card ↥(Vg ⊔ (B.Hhat ⊓ Hg)) = Nat.card ↥Hg := by
      rw [h, hDcard, hcardVg, hcardHg]
    exact Subgroup.eq_of_le_of_card_ge hle1 (le_of_eq hcard.symm)
  have hcoe : ((Vg ⊔ (B.Hhat ⊓ Hg) : Subgroup G) : Set G) =
      (Vg : Set G) * ((B.Hhat ⊓ Hg : Subgroup G) : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left Vg (B.Hhat ⊓ Hg) hDnorm
  obtain ⟨v, hvV, d, hdD, hvd⟩ : ∃ v ∈ Vg, ∃ d ∈ B.Hhat ⊓ Hg, v * d = y := by
    have hymem : y ∈ ((Vg ⊔ (B.Hhat ⊓ Hg) : Subgroup G) : Set G) := by
      rw [hsup]; exact hyHg
    rw [hcoe, Set.mem_mul] at hymem
    exact hymem
  have hd1 : d ≠ 1 := by
    intro hd0
    rw [hd0, mul_one] at hvd
    exact hyVg (hvd.symm ▸ hvV)
  have hvv : v * v = 1 := hVgsq v hvV
  have hv1 : v * d = d⁻¹ * v := by
    have h2 : (v * d) * (v * d) = 1 := by rw [hvd, hy1]
    have h3 : v * d = (v * d)⁻¹ := eq_inv_of_mul_eq_one_right h2
    calc v * d = (v * d)⁻¹ := h3
      _ = d⁻¹ * v⁻¹ := mul_inv_rev v d
      _ = d⁻¹ * v := by rw [inv_eq_of_mul_eq_one_right hvv]
  have hyd : y * d * y⁻¹ = d⁻¹ := by
    rw [hyinv, ← hvd]
    have h4 : d * (v * d) = v := by
      calc d * (v * d) = d * (d⁻¹ * v) := by rw [hv1]
        _ = v := by group
    calc (v * d) * d * (v * d) = (v * d) * (d * (v * d)) := by group
      _ = (v * d) * v := by rw [h4]
      _ = d⁻¹ := by rw [hv1, mul_assoc, hvv, mul_one]
  -- ## Step 6: the two cases
  rcases em (d ∈ P) with hdP | hdPnP
  · -- `d ∈ P`: then `y` centralizes `x`
    have hdx : d * x = x * d := by
      have hle : P ≤ Subgroup.centralizer ({x} : Set G) := by
        rw [hP]
        exact sup_le (Subgroup.zpowers_le.mpr
          (Subgroup.mem_centralizer_singleton_iff.mpr rfl)) hUcX
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hdP)
    have hvx : v * x = x * v := ((Subgroup.mem_centralizer_iff.mp (hVgC hvV)) x hxX).symm
    have hcomm : y * x = x * y := by
      rw [← hvd]
      calc (v * d) * x = v * (d * x) := by group
        _ = v * (x * d) := by rw [hdx]
        _ = (v * x) * d := by group
        _ = (x * v) * d := by rw [hvx]
        _ = x * (v * d) := by group
    have hthis : y * x * y⁻¹ = x := by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    rw [hinv x hxX] at hthis
    have hx2 : x * x = 1 := by
      have h2 : x⁻¹ = x := hthis
      calc x * x = x⁻¹ * x := by rw [h2]
        _ = 1 := inv_mul_cancel x
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hx2)
    rw [hx3] at hdvd
    norm_num at hdvd
  · -- `d ∉ P`: then `d` has even order, giving an involution of `Ĥ` commuting with `y`
    have heven : Even (orderOf d) :=
      even_orderOf_of_index_two (P := P) (Dsub := B.Hhat ⊓ Hg) hPleD
        (by rw [hDcard, hPcard]) hdD hdPnP
    obtain ⟨k, hk⟩ := heven
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · exfalso
        rw [h0] at hk
        have hpos := orderOf_pos d
        omega
      · exact h0
    have hdH : d ∈ B.Hhat := hdD.1
    have hw : d ^ k ∈ B.Hhat := Subgroup.pow_mem _ hdH k
    have hw1 : d ^ k ≠ 1 := by
      intro hzero
      have hdvd : orderOf d ∣ k := orderOf_dvd_iff_pow_eq_one.mpr hzero
      have hle : orderOf d ≤ k := Nat.le_of_dvd hkpos hdvd
      omega
    have hwsq : d ^ k * d ^ k = 1 := by
      rw [← pow_add]
      have h2k : k + k = orderOf d := by omega
      rw [h2k, pow_orderOf_eq_one]
    have hwcomm : y * d ^ k * y⁻¹ = d ^ k := by
      have hstep : y * d ^ k * y⁻¹ = (y * d * y⁻¹) ^ k := by
        rw [← MulAut.conj_apply y (d ^ k), map_pow, MulAut.conj_apply]
      rw [hstep, hyd, inv_pow]
      exact (eq_inv_of_mul_eq_one_right hwsq).symm
    exact hw1 (hnoinv (d ^ k) hw hwsq hwcomm)

theorem J4SevenNeThree (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) (hU3 : Nat.card B.U = 3) :
    ∀ y : G, orderOf y = 2 → y ∉ B.Hhat → ∀ X : Subgroup G, X ≠ ⊥ → Odd (Nat.card X) →
      X ≤ B.Hhat → (∀ x ∈ X, y * x * y⁻¹ = x⁻¹) →
      Even (Nat.card (Subgroup.centralizer (X : Set G))) →
      Even (Nat.card (Subgroup.normalizer (X : Set G))) →
      Work.GW2.cosetInvCount B.Hhat y ≠ 3 := by
  intro y hy2 hyH X hXne hXodd hXH hinv hCe hNe h3
  exact not_cosetInvCount_eq_three I hBc B h1 D hU3 hy2 hyH hXne hXodd hXH hinv hCe hNe h3

end Work.CORE3.J4
