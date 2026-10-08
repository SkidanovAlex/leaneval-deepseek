import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.SevenConjU
import Submission.Work.CORE3.J4.J4U3
import Submission.Work.CORE3.J4.ExistsConjEqInvOrderThree
import Submission.Work.CORE3.OrderThreeLeCentralizer
import Submission.Work.CORE3.SevenNoInvolCentralizer
import Submission.Work.CORE3.CentralizerPcoreEqVU
import Submission.Work.CORE3.NormalizerPcoreEqHhat
import Submission.Work.CORE3.VUInvSetTrivial
import Submission.Work.CORE3.CosetInvCountLeSix
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.lemma24
import Submission.Work.BSW.Cases.K4.CardSup
import Submission.Work.CORE3.FreeAux.NormalizerU3
import Submission.Work.CORE3.FreeAux.CardHhat72
import Submission.Work.CORE3.FreeAux.EvenOrderOfIndexTwo

open Subgroup
open Work.GW2
open scoped Pointwise

namespace Work.CORE3

set_option maxHeartbeats 1000000

/-- **Bender 1981 §3, p. 224, item (7), the fourth involution of the coset `yĤ`.**

In Case (1) of Bender's Theorem 2.10, subcase `V = O₂(Ĥ)` of type `(2,2)` with `|U| = 3`
(`U = O(Ĥ) = O(H)`), let `y ∉ Ĥ` be an involution inverting a non-trivial odd-order subgroup
`X ≤ Ĥ` whose `G`-centralizer has even order.  Then the coset `yĤ` carries at least four
involutions, i.e. `4 ≤ cosetInvCount Ĥ y`.

Proof (the "factorisation" route; no use of `J4.J4SevenNeThree`, which is cycle-blocked for the
`Case1bSeven` assembly):

* `H8`/`J4.exists_zpowers_eq`: `X = ⟨x⟩` with `orderOf x = 3` and `x ∉ VU = O₂(Ĥ)·O(Ĥ)`;
  `SevenConjU`: `X = U^g` for some `g`, so `N_G(U) = Ĥ`
  (`FreeAux.NormalizerU3`, from maximality of `Ĥ`) gives `N_G(X) = Ĥ^g =: Hg`; `y ∈ Hg`.
* `Vg := (O₂(Ĥ))^g` centralizes `X = U^g` (because `U` centralizes `O₂(Ĥ)`, `CentralizerPcoreEqVU`)
  and has only involutions, so `Vg ⊓ Ĥ = ⊥` (`SevenNoInvolCentralizer`).
* `P := ⟨x⟩ ⊔ U` has order `9` (as `X ⊓ VU = ⊥`) and lies in `Hg` — `U ≤ C_G(x)` because
  `x ∈ N_G(U)` and `|U| = 3` (`OrderThreeLeCentralizer`, as `U ≅ ℤ/3` has `Aut` of order `2`).
* Hence `9 ∣ |Ĥ ⊓ Hg|` and `4·|Ĥ ⊓ Hg| = |Vg ⊔ (Ĥ ⊓ Hg)| ≤ |Hg| = 72`
  (`FreeAux.CardHhat72`), so `|Ĥ ⊓ Hg| ∈ {9,18}`; `|Ĥ ⊓ Hg| ≠ 9` since some `h ∈ Ĥ` inverts
  `x` (`ExistsConjEqInvOrderThree`), hence lies in `Ĥ ⊓ Hg = P ≤ C_G(x)`.  So
  `|Ĥ ⊓ Hg| = 18` and `Hg = Vg ⊔ (Ĥ ⊓ Hg)` with `Vg ⊓ (Ĥ ⊓ Hg) = ⊥`.
* Writing `y = v · d` with `v ∈ Vg`, `d ∈ Ĥ ⊓ Hg` (set product), one has `y d y⁻¹ = d⁻¹`
  (as `v² = d² = ... `: `vd = (vd)⁻¹ = d⁻¹v`).  Also `d ∉ P` (else `y = vd` centralizes `x`),
  and `|Ĥ ⊓ Hg| = 2|P|` gives `Even (orderOf d)` (`FreeAux.EvenOrderOfIndexTwo`).
* With `orderOf d = 2k`, `u := d^k` is an involution of `Ĥ`, `u ≠ 1`, centralized by `y`
  (since `y` inverts `d` and `2k = orderOf d`); hence `u ∈ I_Ĥ(y) = invSetIn Ĥ y`, and `u ∉ X`
  (which has odd order).  So `X ∪ {u} ⊆ I_Ĥ(y)` has four elements, and
  `ncard_invSetIn_eq_cosetInvCount` gives `4 ≤ cosetInvCount Ĥ y`. -/
theorem Case1bSevenInvInI (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) (hU3 : Nat.card B.U = 3) {y : G} (hy2 : orderOf y = 2)
    (hyH : y ∉ B.Hhat) {X : Subgroup G} (hXH : X ≤ B.Hhat) (hXne : X ≠ ⊥)
    (hXodd : Odd (Nat.card X)) (hinv : ∀ x ∈ X, y * x * y⁻¹ = x⁻¹)
    (hC : Even (Nat.card (Subgroup.centralizer (X : Set G)))) :
    4 ≤ Work.GW2.cosetInvCount B.Hhat y := by
  classical
  have hy1 : y * y = 1 := (orderOf_eq_two_iff_mul_self y).mp hy2 |>.1
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy1
  -- ## (1) `X = ⟨x⟩` with `x` of order `3` outside `VU`
  obtain ⟨x, hxX, hx3, hXeqz, hxVU⟩ :=
    Work.CORE3.J4.exists_zpowers_eq I hBc B h1 D hy2 hyH hXH hXne hXodd hinv
  have hxH : x ∈ B.Hhat := hXH hxX
  have hXcard : Nat.card X = 3 :=
    Work.CORE3.J4.card_X_eq_three I hBc B h1 D hy2 hyH hXH hXne hXodd hinv
  -- ## (2) `X = U^g`
  obtain ⟨g, hXg⟩ := Work.CORE3.SevenConjU G I hBc B h1 D hU3 hy2 hyH hXH hXne hXodd hinv hC
  set Hg : Subgroup G := Work.GW2.conjSub g B.Hhat with hHg
  set Vg : Subgroup G := Work.GW2.conjSub g (Work.GW2.pCoreIn 2 B.Hhat) with hVg
  -- ## (3) `N_G(U) = Ĥ`, hence `N_G(X) = Ĥ^g`
  have hNU : Subgroup.normalizer (B.U : Set G) = B.Hhat := Work.CORE3.FreeAux.NormalizerU3 G I hBc B h1 D hU3
  have hNX : Subgroup.normalizer (X : Set G) = Hg := by
    rw [hHg, hXg, Work.CORE2A.normalizer_conjSub, hNU]
  have hyN : y ∈ Subgroup.normalizer (X : Set G) := Work.CORE2A.inverts_normalizes hinv hy1
  have hyHg : y ∈ Hg := by rw [← hNX]; exact hyN
  -- ## (4) `V^g ≤ C_G(X)` and `V^g ⊓ Ĥ = ⊥`
  have hUcV : B.U ≤ Subgroup.centralizer (Work.GW2.pCoreIn 2 B.Hhat : Set G) := by
    intro w hw
    have hmem : w ∈ Subgroup.centralizer
        ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) ⊓ B.Hhat := by
      rw [Work.CORE3.CentralizerPcoreEqVU G I hBc B h1 D]
      exact Subgroup.mem_sup_right hw
    exact hmem.1
  have hVgC : Vg ≤ Subgroup.centralizer (X : Set G) := by
    rw [hVg, hXg]
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    rw [Work.CORE2A.conjSub_eq_map] at hv hu
    obtain ⟨v₀, hv₀, rfl⟩ := Subgroup.mem_map.mp hv
    obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.mp hu
    have hcomm : v₀ * u₀ = u₀ * v₀ := (Subgroup.mem_centralizer_iff.mp (hUcV hu₀)) v₀ hv₀
    rw [← map_mul, ← map_mul, hcomm]
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
  have hVgInfH : Vg ⊓ B.Hhat = ⊥ := by
    refine le_bot_iff.mp ?_
    intro w hw
    rw [Subgroup.mem_inf] at hw
    obtain ⟨hwV, hwH⟩ := hw
    rw [Subgroup.mem_bot]
    by_contra hw1
    exact Work.CORE3.SevenNoInvolCentralizer G I hBc B h1 D hy2 hyH hXH hXne hXodd hinv
      ⟨w, hwH, (Work.CORE3.orderOf_eq_two_iff_mul_self w).mpr ⟨hVgsq w hwV, hw1⟩,
        fun u hu => ((Subgroup.mem_centralizer_iff.mp (hVgC hwV)) u hu).symm⟩
  -- ## (5) `P = ⟨x⟩ ⊔ U` has order `9` and lies in `Ĥ ⊓ Ĥ^g`
  set P : Subgroup G := Subgroup.zpowers x ⊔ B.U with hP
  have hxNU : x ∈ Subgroup.normalizer (B.U : Set G) := by
    rw [hNU]; exact hxH
  have hUcX : B.U ≤ Subgroup.centralizer ({x} : Set G) :=
    Work.CORE3.OrderThreeLeCentralizer hxNU hx3 hU3
  have hUleNorm : B.U ≤ Subgroup.normalizer (X : Set G) := by
    have h1' : B.U ≤ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
      rw [← Work.CORE3.J4.centralizer_zpowers_eq (x := x)]
      exact hUcX
    rw [hXeqz]
    exact h1'.trans (Subgroup.centralizer_le_normalizer ((Subgroup.zpowers x : Subgroup G) : Set G))
  have hPcard : Nat.card P = 9 := by
    have hdisj : Subgroup.zpowers x ⊓ B.U = ⊥ := by
      refine le_bot_iff.mp ?_
      intro w hw
      rw [Subgroup.mem_inf] at hw
      obtain ⟨hwz, hwU⟩ := hw
      have hwX : w ∈ X := by rw [hXeqz]; exact hwz
      have hmem : w ∈ X ⊓ (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) :=
        ⟨hwX, Subgroup.mem_sup_right hwU⟩
      rwa [Work.CORE3.J4.X_inf_VU_eq_bot I hBc B h1 D hy2 hyH hXH hinv] at hmem
    have hun : B.U ≤ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
      rw [← hXeqz]
      exact hUleNorm
    have h := Work.BSW.Cases.K4.card_sup_of_le_normalizer_of_inf_eq_bot
      (H := Subgroup.zpowers x) (K := B.U) hun hdisj
    rw [hP, h, Nat.card_zpowers, hx3, hU3]
  have hUleH : B.U ≤ B.Hhat := Work.CORE2A.thm26Concl_U_le_Hhat (I.h26 G I.T.ft hBc B)
  have hPleD : P ≤ B.Hhat ⊓ Hg := by
    refine le_inf ?_ ?_
    · rw [hP]
      exact sup_le (Subgroup.zpowers_le.mpr hxH) hUleH
    · rw [hP, ← hNX]
      exact sup_le (by rw [← hXeqz]; exact Subgroup.le_normalizer) hUleNorm
  -- ## (6) `|Ĥ ⊓ Ĥ^g| = 18`
  have hcardVg : Nat.card Vg = 4 := by
    rw [hVg, Work.CORE2A.card_conjSub]; exact D.four.1
  have hcardHg : Nat.card Hg = 72 := by
    rw [hHg, Work.CORE2A.card_conjSub, Work.CORE3.FreeAux.CardHhat72 G I hBc B h1 D hU3]
  have hDnorm : B.Hhat ⊓ Hg ≤ Subgroup.normalizer (Vg : Set G) := by
    have hNg : Subgroup.normalizer (Vg : Set G) = Hg := by
      rw [hVg, hHg, Work.CORE2A.normalizer_conjSub,
        Work.CORE3.NormalizerPcoreEqHhat G hBc B D.four]
    rw [hNg]
    exact inf_le_right
  have hle1 : Vg ⊔ (B.Hhat ⊓ Hg) ≤ Hg := by
    refine sup_le ?_ inf_le_right
    rw [hVg, hHg]
    exact Work.CORE2A.conjSub_mono (Subgroup.map_subtype_le _) g
  have hinf : Vg ⊓ (B.Hhat ⊓ Hg) = ⊥ := by
    refine le_bot_iff.mp ?_
    intro w hw
    rw [Subgroup.mem_inf] at hw
    exact (le_bot_iff.mpr hVgInfH) ⟨hw.1, hw.2.1⟩
  have hDcard : Nat.card ↥(B.Hhat ⊓ Hg) = 18 := by
    have h9 : 9 ∣ Nat.card ↥(B.Hhat ⊓ Hg) := by
      rw [← hPcard]
      exact Subgroup.card_dvd_of_le hPleD
    have h4 : Nat.card ↥(Vg ⊔ (B.Hhat ⊓ Hg)) = 4 * Nat.card ↥(B.Hhat ⊓ Hg) := by
      have h := Work.BSW.Cases.K4.card_sup_of_le_normalizer_of_inf_eq_bot
        (H := Vg) (K := B.Hhat ⊓ Hg) hDnorm hinf
      rw [h, hcardVg]
    have hcardle : Nat.card ↥(Vg ⊔ (B.Hhat ⊓ Hg)) ≤ Nat.card Hg := by
      have h := Subgroup.card_le_card_group ((Vg ⊔ (B.Hhat ⊓ Hg)).subgroupOf Hg)
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle1).toEquiv] at h
    have hle18 : Nat.card ↥(B.Hhat ⊓ Hg) ≤ 18 := by omega
    have hne9 : Nat.card ↥(B.Hhat ⊓ Hg) ≠ 9 := by
      intro h9'
      have hDeq : B.Hhat ⊓ Hg = P :=
        (Subgroup.eq_of_le_of_card_ge hPleD (by rw [h9', hPcard])).symm
      -- some element of `Ĥ` inverts `x`
      obtain ⟨h, hhH, hhinv⟩ :=
        Work.CORE3.J4.ExistsConjEqInvOrderThree I hBc B h1 D hU3 hxH hx3 hxVU
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
      have hhD : h ∈ B.Hhat ⊓ Hg := ⟨hhH, by rw [← hNX]; exact hhN⟩
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
      have hz : Nat.card ↥(B.Hhat ⊓ Hg) = 0 := by rw [hm, h0, mul_zero]
      exact (Nat.card_pos (α := ↥(B.Hhat ⊓ Hg))).ne' hz
    have hmne1 : m ≠ 1 := by
      intro h1'
      rw [h1', mul_one] at hm
      exact hne9 hm
    omega
  have hsup : Vg ⊔ (B.Hhat ⊓ Hg) = Hg := by
    have h := Work.BSW.Cases.K4.card_sup_of_le_normalizer_of_inf_eq_bot
      (H := Vg) (K := B.Hhat ⊓ Hg) hDnorm hinf
    have hcard : Nat.card ↥(Vg ⊔ (B.Hhat ⊓ Hg)) = Nat.card Hg := by
      rw [h, hDcard, hcardVg, hcardHg]
    exact Subgroup.eq_of_le_of_card_ge hle1 (le_of_eq hcard.symm)
  -- ## (7) `y = v * d` with `v ∈ V^g`, `d ∈ Ĥ ⊓ Ĥ^g`
  have hcoe : ((Vg ⊔ (B.Hhat ⊓ Hg) : Subgroup G) : Set G) =
      (Vg : Set G) * ((B.Hhat ⊓ Hg : Subgroup G) : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left Vg (B.Hhat ⊓ Hg) hDnorm
  obtain ⟨v, hvV, d, hdD, hvd⟩ : ∃ v ∈ Vg, ∃ d ∈ B.Hhat ⊓ Hg, v * d = y := by
    have hymem : y ∈ ((Vg ⊔ (B.Hhat ⊓ Hg) : Subgroup G) : Set G) := by
      rw [hsup]; exact hyHg
    rw [hcoe, Set.mem_mul] at hymem
    exact hymem
  have hdH : d ∈ B.Hhat := hdD.1
  have hvv : v * v = 1 := hVgsq v hvV
  have hyVg : y ∉ Vg := by
    intro hyv
    have hxy : y * x = x * y :=
      ((Subgroup.mem_centralizer_iff.mp (hVgC hyv)) x hxX).symm
    have hthis : y * x * y⁻¹ = x := by rw [hxy, mul_assoc, mul_inv_cancel, mul_one]
    rw [hinv x hxX] at hthis
    have hx2 : x * x = 1 := by
      have h2 : x⁻¹ = x := hthis
      calc x * x = x⁻¹ * x := by rw [h2]
        _ = 1 := inv_mul_cancel x
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hx2)
    rw [hx3] at hdvd
    norm_num at hdvd
  -- ## (8) `d ∉ P`, so `orderOf d` is even
  have hdleC : P ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [hP]
    exact sup_le (Subgroup.zpowers_le.mpr
      (Subgroup.mem_centralizer_singleton_iff.mpr rfl)) hUcX
  have hdP : d ∉ P := by
    intro hdPin
    have hdx : d * x = x * d := Subgroup.mem_centralizer_singleton_iff.mp (hdleC hdPin)
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
  have heven : Even (orderOf d) :=
    Work.CORE3.FreeAux.EvenOrderOfIndexTwo hPleD (by rw [hDcard, hPcard]) hdD hdP
  -- ## (9) the fourth involution `u = d ^ k ∈ I_Ĥ(y)`
  obtain ⟨k, hk⟩ := heven
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso
      rw [h0, add_zero] at hk
      have hpos := orderOf_pos d
      omega
    · exact h0
  set u : G := d ^ k with hu
  have huH : u ∈ B.Hhat := by rw [hu]; exact Subgroup.pow_mem _ hdH k
  have hu1 : u ≠ 1 := by
    intro h0
    have hdvd : orderOf d ∣ k := by rw [hu] at h0; exact orderOf_dvd_iff_pow_eq_one.mpr h0
    have hle : orderOf d ≤ k := Nat.le_of_dvd hkpos hdvd
    omega
  have husq : u * u = 1 := by
    rw [hu, ← pow_two, ← pow_mul]
    have h2k : k * 2 = orderOf d := by omega
    rw [h2k, pow_orderOf_eq_one]
  have hvv1 : v * d = d⁻¹ * v := by
    have h2 : (v * d) * (v * d) = 1 := by rw [hvd, hy1]
    have h3 : v * d = (v * d)⁻¹ := eq_inv_of_mul_eq_one_right h2
    calc v * d = (v * d)⁻¹ := h3
      _ = d⁻¹ * v⁻¹ := mul_inv_rev v d
      _ = d⁻¹ * v := by rw [inv_eq_of_mul_eq_one_right hvv]
  have hyd : y * d * y⁻¹ = d⁻¹ := by
    rw [hyinv, ← hvd]
    have h4 : d * (v * d) = v := by
      calc d * (v * d) = d * (d⁻¹ * v) := by rw [hvv1]
        _ = v := by group
    calc (v * d) * d * (v * d) = (v * d) * (d * (v * d)) := by group
      _ = (v * d) * v := by rw [h4]
      _ = d⁻¹ := by rw [hvv1, mul_assoc, hvv, mul_one]
  have huy : y * u * y⁻¹ = u := by
    rw [hu]
    calc y * d ^ k * y⁻¹ = (y * d * y⁻¹) ^ k := by
          rw [← MulAut.conj_apply y (d ^ k), map_pow, MulAut.conj_apply]
      _ = (d⁻¹) ^ k := by rw [hyd]
      _ = (d ^ k)⁻¹ := inv_pow d k
      _ = d ^ k := inv_eq_of_mul_eq_one_right husq
  -- `u ∉ X` (it has order two, `X` has odd order)
  have huord : orderOf u = 2 := (Work.CORE3.orderOf_eq_two_iff_mul_self u).mpr ⟨husq, hu1⟩
  have huX : u ∉ X := by
    intro huX'
    have hdvd : orderOf u ∣ Nat.card X := Subgroup.orderOf_dvd_natCard X huX'
    rw [huord, hXcard] at hdvd
    norm_num at hdvd
  -- ## (10) the count
  have hXu : ((X : Set G) ∪ {u}) ⊆ Work.CORE3.invSetIn B.Hhat y := by
    intro w hw
    rcases hw with hwX | hwu
    · exact ⟨hXH hwX, by simpa [hyinv] using hinv w hwX⟩
    · rw [Set.mem_singleton_iff] at hwu
      subst hwu
      refine ⟨huH, ?_⟩
      have h2 : y * u * y = u := by simpa [hyinv] using huy
      rw [h2, inv_eq_of_mul_eq_one_right husq]
  have hunion : ((X : Set G) ∪ {u}).ncard = 4 := by
    rw [Set.ncard_union_eq (Set.disjoint_singleton_right.mpr huX) (Set.toFinite _),
      Set.ncard_singleton]
    have hXnc : (X : Set G).ncard = Nat.card X := (Nat.card_coe_set_eq (X : Set G)).symm
    rw [hXnc, hXcard]
  have hge4 : 4 ≤ (Work.CORE3.invSetIn B.Hhat y).ncard := by
    calc (4 : ℕ) = ((X : Set G) ∪ {u}).ncard := hunion.symm
      _ ≤ (Work.CORE3.invSetIn B.Hhat y).ncard := Set.ncard_le_ncard hXu (Set.toFinite _)
  rw [← Work.CORE3.ncard_invSetIn_eq_cosetInvCount B.Hhat y hy1 hyH]
  exact hge4

end Work.CORE3
