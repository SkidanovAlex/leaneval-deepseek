import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.CentralizerPcoreEqVU
import Submission.Work.CORE3.VUInvSetTrivial
import Submission.Work.CORE3.CosetInvCountLeSix
import Submission.Work.CORE3.FourGroupOrderThreeFixed
import Submission.Work.CORE3.exists_mul_of_mem_sup_of_normal
import Submission.Work.CORE2A.inf_U_S_eq_bot
import Submission.Work.CORE3.orderOf_ne_six_of_not_isMulCommutative

/-!
# CORE3: no involution of `Ĥ` centralizes an odd `y`-inverted subgroup of `Ĥ`

Bender 1981, §3, p. 224 (`Submission/Work/lead_gw_prior/bender2_1981.txt`), the step that reads

> Suppose `y ∈ J₃`.  Then `X := I_Ĥ(y)` is a subgroup of order `3`; and by (7),
> `A := C_Ĥ(X)` has odd order.

Here we prove the general form of `A = C_Ĥ(X)` being odd, in its involution-free phrasing:

**`Work.CORE3.SevenNoInvolCentralizer`.**  In Case (1) of Bender's Theorem 2.10, if
`y ∉ Ĥ` is an involution inverting a nontrivial odd-order subgroup `X ≤ Ĥ`, then no involution
`s ∈ Ĥ` centralizes `X`.

## Route

Write `V = O₂(Ĥ)` (a four-group, `D.four`), `U = O(Ĥ)`, `W = V ⊔ U ⊴ Ĥ` with `|Ĥ : W| = 6`
and `Ĥ/W` non-abelian of order `6` (Theorem 2.6), and let `x ∈ X`, `x ≠ 1`.

* `x ∉ U`: otherwise `y` inverts the nontrivial element `x ∈ U = O(Ĥ)`, which is Bender's (5)
  and is already proved in this area (`Work.CORE3.not_invset_U_mem`).
* `x ∉ W`: an odd-order element of `W = V ⊔ U` lies in `U`
  (`MemOddCoreInOfMemSupVUOfOdd`), since `V` is a `2`-group, `U` has odd order and
  `V ∩ U = 1`; so `x` has a nontrivial image in `Ĥ/W`.  In particular `x ∉ C_Ĥ(V) = V ⊔ U`,
  i.e. `x` acts non-trivially on `V` (`Work.CORE3.CentralizerPcoreEqVU`).
* In `Q = Ĥ/W` (non-abelian of order `6`) the image of `x` has odd order `≠ 1`, hence order `3`
  (`x`'s odd order kills `2` and `6`); the image of `s` is an involution commuting with it, so it
  must be `1` (`InvolutionCommuteOrderThreeCardSix`).  Hence `s ∈ W`, and as `s² = 1`, `s ∈ V`
  (`MemPCoreInOfMemSupVUOfMulSelf`).
* But `x ∈ N_G(V) = Ĥ` has odd order and does not centralize `V`, so it centralizes no
  nontrivial element of `V` (`FourGroupNoFixedOdd`).  As `s ∈ V \ {1}` commutes with `x`, this is
  a contradiction.
-/

namespace Work.CORE3

open Subgroup

/-! ## Auxiliary group-theoretic lemmas -/

/-- **An odd-order element of `N_G(V)` fixes no nontrivial element of the four-group `V`.**

`x ∈ N_G(V)` acts on the Klein four-group `V` by conjugation.  If `x` commuted with some
`v ∈ V`, `v ≠ 1`, while not centralizing `V`, then (as in `Work.CORE3.FourGroupOrderThreeFixed`)
`x * x` would centralize all of `V` and hence, `orderOf x` being odd, so would `x` itself — a
contradiction.  (This is the `orderOf x = 3`-lemma with `3` replaced by any odd order; the
reduction to order `3` is *not* available, see the review notes.) -/
theorem fourGroup_no_fixed_of_odd {G : Type} [Group G] [Finite G] {V : Subgroup G} {x : G}
    (hV4 : Work.GW2.IsFourGroup V) (hxN : x ∈ Subgroup.normalizer (V : Set G))
    (hxodd : Odd (orderOf x)) (hxnc : x ∉ Subgroup.centralizer (V : Set G)) :
    ∀ v ∈ V, x * v = v * x → v = 1 := by
  intro w hwV hxw
  by_contra hw1
  -- an element `v ∈ V` at which conjugation by `x` is non-trivial
  have hex : ∃ v ∈ V, x * v ≠ v * x := by
    by_contra h
    push_neg at h
    exact hxnc (Subgroup.mem_centralizer_iff.mpr (fun y hy => (h y hy).symm))
  obtain ⟨v, hvV, hvx⟩ := hex
  have hv1 : v ≠ 1 := by intro hh; exact hvx (by rw [hh, mul_one, one_mul])
  have hvw : v ≠ w := by intro hh; exact hvx (by rw [hh]; exact hxw)
  -- `V = {1, v, w, v * w}`
  have hVset : (V : Set G) = {1, v, w, v * w} :=
    fourGroup_eq_four hV4.1 hV4.2 hvV hwV hv1 hw1 hvw
  have hw2 : w * w = 1 := by simpa [pow_two] using hV4.2 w hwV
  -- `x * v * x⁻¹ = v * w`
  have huV : x * v * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hxN v).mp hvV
  have hu_mem : x * v * x⁻¹ ∈ ({1, v, w, v * w} : Set G) := hVset ▸ huV
  have hu_eq : x * v * x⁻¹ = v * w := by
    rcases (Set.mem_insert_iff.mp hu_mem) with h | h
    · exfalso
      apply hv1
      have hxveq : x * v = x * 1 := by
        rw [mul_one]
        calc x * v = x * v * x⁻¹ * x := by group
          _ = 1 * x := by rw [h]
          _ = x := one_mul x
      exact mul_left_cancel hxveq
    · rcases (Set.mem_insert_iff.mp h) with h | h
      · exfalso
        apply hvx
        calc x * v = x * v * x⁻¹ * x := by group
          _ = v * x := by rw [h]
      · rcases (Set.mem_insert_iff.mp h) with h | h
        · exfalso
          apply hvw
          have hxveq : x * v = x * w := by
            calc x * v = x * v * x⁻¹ * x := by group
              _ = w * x := by rw [h]
              _ = x * w := hxw.symm
          exact mul_left_cancel hxveq
        · exact Set.mem_singleton_iff.mp h
  -- `x * w * x⁻¹ = w`
  have hxw' : x * w * x⁻¹ = w := by rw [hxw, mul_assoc, mul_inv_cancel, mul_one]
  -- `x * x` centralizes `V`
  have hyv : (x * x) * v * (x * x)⁻¹ = v := by
    calc (x * x) * v * (x * x)⁻¹ = x * (x * v * x⁻¹) * x⁻¹ := by group
      _ = x * (v * w) * x⁻¹ := by rw [hu_eq]
      _ = (x * v * x⁻¹) * (x * w * x⁻¹) := by group
      _ = (v * w) * w := by rw [hu_eq, hxw']
      _ = v := by rw [mul_assoc, hw2, mul_one]
  have hyw : (x * x) * w * (x * x)⁻¹ = w := by
    have hx2 : (x * x) * w * (x * x)⁻¹ = x * (x * w * x⁻¹) * x⁻¹ := by group
    rw [hx2]
    nth_rewrite 1 [hxw']
    exact hxw'
  have hyc : ∀ y ∈ V, (x * x) * y * (x * x)⁻¹ = y := by
    intro y hy
    have hy' : y ∈ ({1, v, w, v * w} : Set G) := hVset ▸ hy
    rcases (Set.mem_insert_iff.mp hy') with h | h
    · rw [h]; group
    · rcases (Set.mem_insert_iff.mp h) with h | h
      · rw [h]; exact hyv
      · rcases (Set.mem_insert_iff.mp h) with h | h
        · rw [h]; exact hyw
        · rw [Set.mem_singleton_iff.mp h]
          have e1 : (x * x) * (v * w) * (x * x)⁻¹ =
              ((x * x) * v * (x * x)⁻¹) * ((x * x) * w * (x * x)⁻¹) := by group
          rw [e1, hyv, hyw]
  have hyC : x * x ∈ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := hyc y hy
    calc y * (x * x) = ((x * x) * y * (x * x)⁻¹) * (x * x) := by rw [h]
      _ = (x * x) * y := by group
  -- `x` is a power of `x * x`, since `orderOf x` is odd, so `x ∈ C_G(V)`: contradiction
  obtain ⟨k, hk⟩ := hxodd
  have hx_eq : x = ((x * x) ^ k)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    have h1 : x ^ orderOf x = 1 := pow_orderOf_eq_one x
    rw [hk] at h1
    have e : x ^ (2 * k + 1) = (x * x) ^ k * x := by
      have h2 : x ^ (2 * k) = (x * x) ^ k := by rw [pow_mul, pow_two]
      rw [pow_succ, h2]
    rw [e] at h1
    exact h1
  have hxmem : x ∈ Subgroup.centralizer (V : Set G) := by
    rw [hx_eq]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hyC k)
  exact hxnc hxmem

/-- **A non-abelian group of order `6` has no involution centralizing an element of order `3`.**

Otherwise `t * z` would have order `2 * 3 = 6`, and a group of order `6` with an element of
order `6` is cyclic, hence abelian (`Work.CORE3.orderOf_ne_six_of_not_isMulCommutative`). -/
theorem involution_commute_order_three_card_six {Q : Type} [Group Q] [Finite Q]
    (hcard : Nat.card Q = 6) (hnab : ¬ IsMulCommutative Q) {t z : Q}
    (ht : t * t = 1) (hz : orderOf z = 3) (hc : t * z = z * t) : t = 1 := by
  by_contra ht1
  have htord : orderOf t = 2 := by
    have hd : orderOf t ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact ht)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ht1
    · exact h
  have hcop : (orderOf t).Coprime (orderOf z) := by rw [htord, hz]; norm_num
  have h6 : orderOf (t * z) = 6 := by
    rw [((commute_iff_eq t z).mpr hc).orderOf_mul_eq_mul_orderOf_of_coprime hcop, htord, hz]
  exact Work.CORE3.orderOf_ne_six_of_not_isMulCommutative hcard hnab (t * z) h6

/-- **An odd-order element of `V ⊔ U` lies in `U`** (`V = O₂(Ĥ)`, `U = O(Ĥ)`).

`V` is a `2`-group, `U` has odd order, `V ⊓ U = ⊥` and `V` commutes with `U`, so for
`x = v * u ∈ V ⊔ U` of odd order `n` we have `v^n = (u^n)⁻¹ ∈ V ⊓ U = ⊥`; as `v` lies in a
`2`-group and `n` is odd, `v = 1`, and `x = u ∈ U`. -/
theorem mem_oddCoreIn_of_mem_sup_VU_of_odd {G : Type} [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) (h26 : Work.GW2.Thm26Concl B) {x : G}
    (hx : x ∈ Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) (hodd : Odd (orderOf x)) : x ∈ B.U := by
  have hVle : Work.GW2.pCoreIn 2 B.Hhat ≤ B.Hhat := Work.CORE2A.thm26Concl_O2_le_Hhat h26
  have hUle : B.U ≤ B.Hhat := Work.CORE2A.thm26Concl_U_le_Hhat h26
  have hVnorm : B.Hhat ≤
      Subgroup.normalizer ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) := by
    simpa [Work.GW2.pCoreIn] using
      Work.CORE3.le_normalizer_map_subtype B.Hhat (Work.GW2.pCore 2 ↥B.Hhat)
  have hUnorm : B.Hhat ≤ Subgroup.normalizer (B.U : Set G) := by
    rw [← Work.CORE2A.thm26Concl_oddCore_eq h26]
    simpa [Work.GW2.oddCoreIn] using
      Work.CORE3.le_normalizer_map_subtype B.Hhat (Work.GW2.oddCore ↥B.Hhat)
  obtain ⟨v, hv, u, hu, hxeq⟩ := Work.CORE3.exists_mul_of_mem_sup_of_normal hVle hUle
    (fun s hs v hv => (Subgroup.mem_normalizer_iff.mp (hVnorm hs) v).mp hv)
    (fun s hs u hu => (Subgroup.mem_normalizer_iff.mp (hUnorm hs) u).mp hu) x hx
  have hvcU : Work.GW2.pCoreIn 2 B.Hhat ≤ Subgroup.centralizer (B.U : Set G) := by
    rw [← Work.CORE2A.thm26Concl_centralizer_eq h26]; exact inf_le_right
  have hcomm : v * u = u * v := ((Subgroup.mem_centralizer_iff.mp (hvcU hv)) u hu).symm
  have hVUbot : Work.GW2.pCoreIn 2 B.Hhat ⊓ B.U = ⊥ := by
    rw [inf_comm]
    exact Work.CORE2A.inf_eq_bot_of_odd_of_isPGroup_two (U := B.U)
      (S := Work.GW2.pCoreIn 2 B.Hhat) (Work.CORE2A.bSetup_U_odd B)
      (Work.CORE2A.thm26Concl_isPGroup_O2 h26)
  have hvu : v ^ orderOf x * u ^ orderOf x = 1 := by
    have h := ((commute_iff_eq v u).mpr hcomm).mul_pow (orderOf x)
    rw [← h, ← hxeq]
    exact pow_orderOf_eq_one x
  have hvinv : v ^ orderOf x = (u ^ orderOf x)⁻¹ := eq_inv_of_mul_eq_one_left hvu
  have hmem : v ^ orderOf x ∈ Work.GW2.pCoreIn 2 B.Hhat ⊓ B.U :=
    ⟨Subgroup.pow_mem _ hv (orderOf x),
      by rw [hvinv]; exact Subgroup.inv_mem B.U (Subgroup.pow_mem _ hu (orderOf x))⟩
  rw [hVUbot] at hmem
  have hvpow1 : v ^ orderOf x = 1 := Subgroup.mem_bot.mp hmem
  have hv1 : v = 1 := by
    have hdv : orderOf v ∣ orderOf x := orderOf_dvd_iff_pow_eq_one.mpr hvpow1
    have hoddv : Odd (orderOf v) := Odd.of_dvd_nat hodd hdv
    obtain ⟨j, hj⟩ := Work.CORE2A.thm26Concl_isPGroup_O2 h26 ⟨v, hv⟩
    have hdvd2 : orderOf v ∣ 2 ^ j := by
      rw [orderOf_dvd_iff_pow_eq_one]
      have := congrArg Subtype.val hj
      simpa using this
    exact orderOf_eq_one_iff.mp ((hoddv.coprime_two_right.pow_right j).eq_one_of_dvd hdvd2)
  rw [hxeq, hv1, one_mul]
  exact hu

/-- **An involution of `V ⊔ U` lies in `V`** (`V = O₂(Ĥ)`, `U = O(Ĥ)` odd, `V ⊓ U = ⊥`).

For `s = v * u ∈ V ⊔ U` with `s * s = 1` we get `u * u = (v * v)⁻¹ ∈ V ⊓ U = ⊥`; as `U` has odd
order, `u = 1` and `s = v ∈ V`. -/
theorem mem_pCoreIn_of_mem_sup_VU_of_mul_self {G : Type} [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) (h26 : Work.GW2.Thm26Concl B) {s : G}
    (hs : s ∈ Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) (hs2 : s * s = 1) :
    s ∈ Work.GW2.pCoreIn 2 B.Hhat := by
  have hVle : Work.GW2.pCoreIn 2 B.Hhat ≤ B.Hhat := Work.CORE2A.thm26Concl_O2_le_Hhat h26
  have hUle : B.U ≤ B.Hhat := Work.CORE2A.thm26Concl_U_le_Hhat h26
  have hVnorm : B.Hhat ≤
      Subgroup.normalizer ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) := by
    simpa [Work.GW2.pCoreIn] using
      Work.CORE3.le_normalizer_map_subtype B.Hhat (Work.GW2.pCore 2 ↥B.Hhat)
  have hUnorm : B.Hhat ≤ Subgroup.normalizer (B.U : Set G) := by
    rw [← Work.CORE2A.thm26Concl_oddCore_eq h26]
    simpa [Work.GW2.oddCoreIn] using
      Work.CORE3.le_normalizer_map_subtype B.Hhat (Work.GW2.oddCore ↥B.Hhat)
  obtain ⟨v, hv, u, hu, hseq⟩ := Work.CORE3.exists_mul_of_mem_sup_of_normal hVle hUle
    (fun t ht v hv => (Subgroup.mem_normalizer_iff.mp (hVnorm ht) v).mp hv)
    (fun t ht u hu => (Subgroup.mem_normalizer_iff.mp (hUnorm ht) u).mp hu) s hs
  have hvcU : Work.GW2.pCoreIn 2 B.Hhat ≤ Subgroup.centralizer (B.U : Set G) := by
    rw [← Work.CORE2A.thm26Concl_centralizer_eq h26]; exact inf_le_right
  have hcomm : v * u = u * v := ((Subgroup.mem_centralizer_iff.mp (hvcU hv)) u hu).symm
  have hVUbot : Work.GW2.pCoreIn 2 B.Hhat ⊓ B.U = ⊥ := by
    rw [inf_comm]
    exact Work.CORE2A.inf_eq_bot_of_odd_of_isPGroup_two (U := B.U)
      (S := Work.GW2.pCoreIn 2 B.Hhat) (Work.CORE2A.bSetup_U_odd B)
      (Work.CORE2A.thm26Concl_isPGroup_O2 h26)
  have h1 : v ^ 2 * u ^ 2 = 1 := by
    have h := ((commute_iff_eq v u).mpr hcomm).mul_pow 2
    rw [← h, ← hseq, pow_two]
    exact hs2
  have huinv : u ^ 2 = (v ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right h1
  have hmem : u ^ 2 ∈ Work.GW2.pCoreIn 2 B.Hhat ⊓ B.U :=
    ⟨by rw [huinv]; exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hv 2),
      Subgroup.pow_mem _ hu 2⟩
  rw [hVUbot] at hmem
  have hu2one : u ^ 2 = 1 := Subgroup.mem_bot.mp hmem
  have hu1 : u = 1 := by
    have hd2 : orderOf u ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hu2one
    have hoddu : Odd (orderOf u) :=
      Odd.of_dvd_nat (Work.CORE2A.bSetup_U_odd B) (Subgroup.orderOf_dvd_natCard B.U hu)
    exact orderOf_eq_one_iff.mp (hoddu.coprime_two_right.eq_one_of_dvd hd2)
  rw [hseq, hu1, mul_one]
  exact hv

/-! ## The main lemma -/

theorem SevenNoInvolCentralizer (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) {y : G} (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat)
    {X : Subgroup G} (hXH : X ≤ B.Hhat) (hXne : X ≠ ⊥) (hXodd : Odd (Nat.card X))
    (hinv : ∀ x ∈ X, y * x * y⁻¹ = x⁻¹) :
    ¬ ∃ s : G, s ∈ B.Hhat ∧ orderOf s = 2 ∧ ∀ x ∈ X, s * x = x * s := by
  classical
  rintro ⟨s, hsH, hs2, hcent⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h26 : Work.GW2.Thm26Concl B := I.h26 G I.T.ft hBc B
  -- ### an element `x ∈ X` of odd order with `x ≠ 1`
  obtain ⟨x, hxne1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hXne
  have hxmem : (x : G) ∈ X := x.2
  have hxG1 : (x : G) ≠ 1 := fun h => hxne1 (Subtype.ext h)
  have hxH : (x : G) ∈ B.Hhat := hXH hxmem
  have hxy : y * (x : G) * y⁻¹ = (x : G)⁻¹ := hinv x hxmem
  have hxs : s * (x : G) = (x : G) * s := hcent x hxmem
  have hs1 : s ≠ 1 := by
    intro h; rw [h, orderOf_one] at hs2; exact absurd hs2 (by norm_num)
  have hxoddord : Odd (orderOf (x : G)) :=
    Odd.of_dvd_nat hXodd (Subgroup.orderOf_dvd_natCard X hxmem)
  -- ### `x ∉ U = O(Ĥ)` (Bender's (5))
  have hxU : (x : G) ∉ B.U := fun hxU =>
    Work.CORE3.not_invset_U_mem I G hBc B h1 D hxU hxG1 hy2 hyH hxy
  -- ### `x ∉ W = V ⊔ U`
  have hxVU : (x : G) ∉ Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U := fun h =>
    hxU (mem_oddCoreIn_of_mem_sup_VU_of_odd B h26 h hxoddord)
  -- ### `x ∉ C_G(V)`
  have hxnc : (x : G) ∉ Subgroup.centralizer
      ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) := by
    intro hc
    refine hxVU ?_
    have hmem : (x : G) ∈ Subgroup.centralizer
        ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) ⊓ B.Hhat := ⟨hc, hxH⟩
    rwa [Work.CORE3.CentralizerPcoreEqVU G I hBc B h1 D] at hmem
  -- ### `x ∈ N_G(V) = Ĥ`
  have hxN : (x : G) ∈ Subgroup.normalizer
      ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) := by
    rw [Work.CORE3.NormalizerPcoreEqHhat G hBc B D.four]
    exact hxH
  -- ### the quotient `Q = Ĥ/W`
  set W : Subgroup G := Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U with hW
  have hWnorm : (W.subgroupOf B.Hhat).Normal := by
    rw [hW]; exact Work.CORE3.normal_VU_subgroupOf G I hBc B h1 D
  have hWindex : (W.subgroupOf B.Hhat).index = 6 := by
    rw [hW]; exact Work.CORE3.relIndex_VU_Hhat G I hBc B h1 D
  haveI : (W.subgroupOf B.Hhat).Normal := hWnorm
  have hQcard : Nat.card (↥B.Hhat ⧸ (W.subgroupOf B.Hhat)) = 6 := by
    rw [← Subgroup.index_eq_card (W.subgroupOf B.Hhat), hWindex]
  -- `Q` is not abelian, by the third alternative of Theorem 2.6
  have hQnab : ¬ IsMulCommutative (↥B.Hhat ⧸ (W.subgroupOf B.Hhat)) := by
    intro hcomm
    have hdata : ∃ a b : G, a ∈ B.Hhat ∧ b ∈ B.Hhat ∧ a * b * a⁻¹ * b⁻¹ ∉ W := by
      rcases h26.2.2 with ⟨hle, -⟩ | ⟨-, -, a, ha, b, hb, hab⟩
      · exact absurd (Work.CORE3.isCyclic_of_le_of_isCyclic' hle B.S0_cyclic)
          (Work.CORE3.not_isCyclic_of_isFourGroup' D.four)
      · rw [hW]; exact ⟨a, b, ha, hb, hab⟩
    obtain ⟨a, b, ha, hb, hab⟩ := hdata
    set g : ↥B.Hhat := ⟨a * b * a⁻¹ * b⁻¹,
      B.Hhat.mul_mem (B.Hhat.mul_mem (B.Hhat.mul_mem ha hb) (B.Hhat.inv_mem ha))
        (B.Hhat.inv_mem hb)⟩ with hg
    have h1 : (QuotientGroup.mk' (W.subgroupOf B.Hhat)) g = 1 := by
      have heq : g = (⟨a, ha⟩ : ↥B.Hhat) * ⟨b, hb⟩ * (⟨a, ha⟩ : ↥B.Hhat)⁻¹ *
          (⟨b, hb⟩ : ↥B.Hhat)⁻¹ := by
        apply Subtype.ext
        simp [hg]
      rw [heq, map_mul, map_mul, map_mul, map_inv, map_inv]
      have hcab : (QuotientGroup.mk' (W.subgroupOf B.Hhat)) ⟨a, ha⟩ *
          (QuotientGroup.mk' (W.subgroupOf B.Hhat)) ⟨b, hb⟩ =
          (QuotientGroup.mk' (W.subgroupOf B.Hhat)) ⟨b, hb⟩ *
          (QuotientGroup.mk' (W.subgroupOf B.Hhat)) ⟨a, ha⟩ :=
        hcomm.is_comm.comm _ _
      rw [hcab]
      group
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    refine hab ?_
    have := Subgroup.mem_subgroupOf.mp h1
    simpa [hg] using this
  -- ### the image of `x` in `Q` is nontrivial of order `3`
  have hxq_ne : (QuotientGroup.mk' (W.subgroupOf B.Hhat)) (⟨x, hxH⟩ : ↥B.Hhat) ≠ 1 := by
    intro h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    refine hxVU ?_
    have := Subgroup.mem_subgroupOf.mp h
    simpa [hW] using this
  have hxdiv : orderOf ((QuotientGroup.mk' (W.subgroupOf B.Hhat)) (⟨x, hxH⟩ : ↥B.Hhat)) ∣ 6 := by
    have h := orderOf_dvd_natCard ((QuotientGroup.mk' (W.subgroupOf B.Hhat)) (⟨x, hxH⟩ : ↥B.Hhat))
    rwa [hQcard] at h
  have hxoddq : Odd (orderOf ((QuotientGroup.mk' (W.subgroupOf B.Hhat)) (⟨x, hxH⟩ : ↥B.Hhat))) := by
    refine Odd.of_dvd_nat hxoddord ?_
    have h := orderOf_map_dvd (QuotientGroup.mk' (W.subgroupOf B.Hhat)) (⟨x, hxH⟩ : ↥B.Hhat)
    rwa [← Subgroup.orderOf_coe (⟨x, hxH⟩ : ↥B.Hhat)] at h
  have hxq3 : orderOf ((QuotientGroup.mk' (W.subgroupOf B.Hhat)) (⟨x, hxH⟩ : ↥B.Hhat)) = 3 := by
    have hdvd3 : orderOf ((QuotientGroup.mk' (W.subgroupOf B.Hhat)) (⟨x, hxH⟩ : ↥B.Hhat)) ∣ 3 :=
      hxoddq.coprime_two_right.dvd_of_dvd_mul_left (by
        rw [show (2 : ℕ) * 3 = 6 from rfl]; exact hxdiv)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hxq_ne
    · exact h
  -- ### the image of `s` in `Q` is trivial
  have hs2' : s * s = 1 := by
    have h : s ^ orderOf s = 1 := pow_orderOf_eq_one s
    rw [hs2] at h
    simpa [pow_two] using h
  have hsq : (QuotientGroup.mk' (W.subgroupOf B.Hhat)) (⟨s, hsH⟩ : ↥B.Hhat) *
      (QuotientGroup.mk' (W.subgroupOf B.Hhat)) (⟨s, hsH⟩ : ↥B.Hhat) = 1 := by
    have hsub : (⟨s, hsH⟩ : ↥B.Hhat) * ⟨s, hsH⟩ = 1 := by
      apply Subtype.ext
      show s * s = 1
      exact hs2'
    rw [← map_mul, hsub, map_one]
  have hsq1 : (QuotientGroup.mk' (W.subgroupOf B.Hhat)) (⟨s, hsH⟩ : ↥B.Hhat) = 1 := by
    have hdvd : orderOf ((QuotientGroup.mk' (W.subgroupOf B.Hhat)) (⟨s, hsH⟩ : ↥B.Hhat)) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hsq)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact orderOf_eq_one_iff.mp h
    · exfalso
      have hcommq : (QuotientGroup.mk' (W.subgroupOf B.Hhat)) (⟨s, hsH⟩ : ↥B.Hhat) *
          (QuotientGroup.mk' (W.subgroupOf B.Hhat)) (⟨x, hxH⟩ : ↥B.Hhat) =
          (QuotientGroup.mk' (W.subgroupOf B.Hhat)) (⟨x, hxH⟩ : ↥B.Hhat) *
          (QuotientGroup.mk' (W.subgroupOf B.Hhat)) (⟨s, hsH⟩ : ↥B.Hhat) := by
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext hxs
      have hres := involution_commute_order_three_card_six hQcard hQnab hsq hxq3 hcommq
      rw [hres, orderOf_one] at h
      exact absurd h (by norm_num)
  -- ### hence `s ∈ W`, and being an involution, `s ∈ V`
  have hsWsub : (⟨s, hsH⟩ : ↥B.Hhat) ∈ W.subgroupOf B.Hhat := by
    rw [QuotientGroup.mk'_apply] at hsq1
    exact (QuotientGroup.eq_one_iff _).mp hsq1
  have hsVU : s ∈ W := by
    have := Subgroup.mem_subgroupOf.mp hsWsub
    simpa using this
  have hsV : s ∈ Work.GW2.pCoreIn 2 B.Hhat := by
    rw [hW] at hsVU
    exact mem_pCoreIn_of_mem_sup_VU_of_mul_self B h26 hsVU hs2'
  -- ### contradiction: `x` fixes no nontrivial element of the four-group `V`
  exact hs1 (fourGroup_no_fixed_of_odd D.four hxN hxoddord hxnc s hsV hxs.symm)

end Work.CORE3
