import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.ASM.Defs
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE3.Case1bDStructure
import Submission.Work.CORE3.SixInvSetElements
import Submission.Work.CORE3.SixInvSetMulTable
import Submission.Work.CORE3.InvSetVUSingleton
import Submission.Work.CORE3.CosetInvCountBasic
import Submission.Work.CORE3.CosetInvCountLeSix
import Submission.Work.CORE3.CentralizerPcoreEqVU
import Submission.Work.CORE3.OrderThreeLeCentralizer
import Submission.Work.CORE3.exists_mul_of_mem_sup_of_normal
import Submission.Work.CORE3.LeFourAux.FixFour
import Submission.Work.CORE3.LeFourAux.SplitQuotient
import Submission.Work.CORE3.LeFourAux.ConjInvOfMul
import Submission.Work.CORE3.LeFourAux.ConjEqOfDecomp

/-!
# `Work.CORE3.Case1bLeFourSplit`

Bender 1981 §3, pp. 223–224, Case (1), subcase `V = O₂(Ĥ)` of type `(2,2)`, with `|U| = 3`.

Assume a coset of `Ĥ` whose non-`Ĥ` involutions number six (`h6`), and let `a ∈ I_Ĥ(y)` have
order `3`, `b₁, b₂ ∈ I_Ĥ(y)` be distinct involutions (`I_Ĥ(y) = invSetIn Ĥ y`).  Writing
`V = O₂(Ĥ)`, `U = O(Ĥ)`, `VU = V ⊔ U` and `D = Ĥ ⊓ Ĥ^y`, the inverted set `I_Ĥ(y)` has six
elements and injects into `Ĥ/VU` (Bender (5)), so `D/M` (`M = D ⊓ VU`) is `S₃` and `I_Ĥ(y)` is a
transversal.  The product `b₁b₂` therefore lies in the coset of `⟨a⟩` modulo `VU`: there are
`h ∈ {a, a²}` and `v ∈ D ⊓ VU` with `b₁b₂ = h·v`.

Moreover the `V`-component of `v` is trivial.  Indeed if `v ≠ 1` had a nontrivial
`V = C₂ × C₂` component `v₂`, then (i) `b₁ v b₁ = b₂ v b₂ = h v⁻¹ h⁻¹` (because
`b₁(b₁b₂)b₁ = b₂b₁ = (b₁b₂)⁻¹`), which — using that `b₁`, `b₂` invert `U` elementwise and `h`
centralizes `U` — forces `b₁v₂b₁ = b₂v₂b₂ = hv₂h⁻¹`; and (ii) `h v h⁻¹ = (b₁b₂) v (b₁b₂)⁻¹`
because `v ∈ VU = C_Ĥ(V)`.  Combining these, `b₁` and `b₂` induce the same (nontrivial)
automorphism of the four-group `V`, so `b₁b₂` centralizes `V`, i.e. `b₁b₂ ∈ C_Ĥ(V) = VU`,
contradicting `b₁ ≠ b₂` (the injectivity of `I_Ĥ(y) → Ĥ/VU`).  Hence `v ∈ U`, and then `h`
centralizes `v` because `|U| = 3` and `orderOf h = 3` (`OrderThreeLeCentralizer`).
-/

namespace Work.CORE3

open Subgroup
open Work.GW2

/-- If `b * b = 1` then conjugation by `b` is an involution, so
`b * (b * x * b⁻¹) * b⁻¹ = x`. -/
private lemma mul_inj_sandwich {G : Type} [Group G] {b x : G} (hb : b * b = 1) :
    b * (b * x * b⁻¹) * b⁻¹ = x := by
  have e : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  rw [show b * (b * x * b⁻¹) * b⁻¹ = (b * b) * x * (b⁻¹ * b⁻¹) from by group, hb, e, hb]
  group

theorem Case1bLeFourSplit (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) (hU3 : Nat.card B.U = 3)
    {y : G} (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat)
    (h6 : Work.GW2.cosetInvCount B.Hhat y = 6)
    {a b1 b2 : G} (ha : a ∈ Work.CORE3.invSetIn B.Hhat y) (ha3 : orderOf a = 3)
    (hb1 : b1 ∈ Work.CORE3.invSetIn B.Hhat y) (hb1o : orderOf b1 = 2)
    (hb2 : b2 ∈ Work.CORE3.invSetIn B.Hhat y) (hb2o : orderOf b2 = 2) (h12 : b1 ≠ b2) :
    ∃ h : G, (h = a ∨ h = a * a) ∧
      ∃ v ∈ (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat) ⊓ (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U),
        b1 * b2 = h * v ∧ (v ≠ 1 → (v ∈ B.U ∧ h * v = v * h)) := by
  classical
  -- ## Basic data
  have hy : y * y = 1 := ((orderOf_eq_two_iff_mul_self y).mp hy2).1
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have h26 : Work.GW2.Thm26Concl B := I.h26 G I.T.ft hBc B
  have hVle : Work.GW2.pCoreIn 2 B.Hhat ≤ B.Hhat := Work.CORE2A.thm26Concl_O2_le_Hhat h26
  have hUle : B.U ≤ B.Hhat := Work.CORE2A.thm26Concl_U_le_Hhat h26
  have hVUle : Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U ≤ B.Hhat := sup_le hVle hUle
  have hVUn : ((Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U).subgroupOf B.Hhat).Normal :=
    normal_VU_subgroupOf G I hBc B h1 D
  have hVUrel : (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U).relIndex B.Hhat = 6 :=
    relIndex_VU_Hhat G I hBc B h1 D
  have hCV : Subgroup.centralizer ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) ⊓ B.Hhat
      = Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U := CentralizerPcoreEqVU G I hBc B h1 D
  -- Bender (5), in both the `orderOf` and the `mul_self` shape
  have h5o : ∀ z : G, orderOf z = 2 → z ∉ B.Hhat →
      Work.GW2.invSet (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) z = {1} :=
    fun z hz hzH => InvSetVUSingleton G I hBc B h1 D z hz hzH
  have h5 : ∀ z : G, z * z = 1 → z ∉ B.Hhat →
      Work.GW2.invSet (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) z = {1} := by
    intro z hz hzH
    refine h5o z ?_ hzH
    exact (orderOf_eq_two_iff_mul_self z).mpr
      ⟨hz, fun h1z => hzH (by rw [h1z]; exact B.Hhat.one_mem)⟩
  -- the normalizer of `V` and of `U` inside `Ĥ`
  have hVnorm : ∀ s ∈ B.Hhat, ∀ w ∈ Work.GW2.pCoreIn 2 B.Hhat,
      s * w * s⁻¹ ∈ Work.GW2.pCoreIn 2 B.Hhat := by
    intro s hs w hw
    exact ((Subgroup.mem_normalizer_iff.mp
      (le_normalizer_map_subtype B.Hhat (Work.GW2.pCore 2 ↥B.Hhat) hs)) w).mp hw
  have hUnorm : ∀ s ∈ B.Hhat, ∀ u ∈ B.U, s * u * s⁻¹ ∈ B.U := by
    intro s hs u hu
    have h1' : B.Hhat ≤ Subgroup.normalizer (B.U : Set G) := by
      rw [← Work.CORE2A.thm26Concl_oddCore_eq h26]
      simpa [Work.GW2.oddCoreIn] using
        le_normalizer_map_subtype B.Hhat (Work.GW2.oddCore ↥B.Hhat)
    exact ((Subgroup.mem_normalizer_iff.mp (h1' hs)) u).mp hu
  have hHhatNormU : B.Hhat ≤ Subgroup.normalizer (B.U : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro u
    exact ⟨fun hu => hUnorm s hs u hu, fun hu => by
      have h2 := hUnorm s⁻¹ (B.Hhat.inv_mem hs) (s * u * s⁻¹) hu
      have h3 : s⁻¹ * (s * u * s⁻¹) * (s⁻¹)⁻¹ = u := by group
      rwa [h3] at h2⟩
  -- ## The structure of `D = Ĥ ⊓ Ĥ^y`
  have hstruct := Case1bDStructure G I hBc B h1 D y hy2 hyH (by rw [h6]; norm_num)
  have hsub : invSetIn B.Hhat y ⊆ B.Hhat ⊓ Work.GW2.conjSub y B.Hhat := hstruct.2.2
  have haD : a ∈ B.Hhat ⊓ Work.GW2.conjSub y B.Hhat := hsub ha
  have hb1D : b1 ∈ B.Hhat ⊓ Work.GW2.conjSub y B.Hhat := hsub hb1
  have hb2D : b2 ∈ B.Hhat ⊓ Work.GW2.conjSub y B.Hhat := hsub hb2
  have hb1sq : b1 * b1 = 1 := ((orderOf_eq_two_iff_mul_self b1).mp hb1o).1
  have hb2sq : b2 * b2 = 1 := ((orderOf_eq_two_iff_mul_self b2).mp hb2o).1
  have hb1ne1 : b1 ≠ 1 := ((orderOf_eq_two_iff_mul_self b1).mp hb1o).2
  have hb2ne1 : b2 ≠ 1 := ((orderOf_eq_two_iff_mul_self b2).mp hb2o).2
  have hane1 : a ≠ 1 := by
    intro hcon; rw [hcon, orderOf_one] at ha3; exact absurd ha3 (by norm_num)
  -- nothing of `{a, b₁, b₂}` lies in `VU`
  have ha_notVU : a ∉ Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U := by
    intro hmem
    have hmemI : a ∈ Work.GW2.invSet (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) y :=
      ⟨hmem, by rw [hyinv]; exact ha.2⟩
    rw [h5o y hy2 hyH] at hmemI
    exact hane1 (by simpa using hmemI)
  have hb1_notVU : b1 ∉ Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U := by
    intro hmem
    have hmemI : b1 ∈ Work.GW2.invSet (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) y :=
      ⟨hmem, by rw [hyinv]; exact hb1.2⟩
    rw [h5o y hy2 hyH] at hmemI
    exact hb1ne1 (by simpa using hmemI)
  have hb2_notVU : b2 ∉ Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U := by
    intro hmem
    have hmemI : b2 ∈ Work.GW2.invSet (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) y :=
      ⟨hmem, by rw [hyinv]; exact hb2.2⟩
    rw [h5o y hy2 hyH] at hmemI
    exact hb2ne1 (by simpa using hmemI)
  have hb1_notV : b1 ∉ Work.GW2.pCoreIn 2 B.Hhat := fun h => hb1_notVU (Subgroup.mem_sup_left h)
  have hb2_notV : b2 ∉ Work.GW2.pCoreIn 2 B.Hhat := fun h => hb2_notVU (Subgroup.mem_sup_left h)
  have hb1b2_notVU : b1 * b2 ∉ Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U := by
    intro hmem
    have hfg : b1 * b2⁻¹ ∈ Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U := by
      rw [inv_eq_of_mul_eq_one_right hb2sq]; exact hmem
    exact h12 (invSetIn_eq_of_mul_inv_mem hVUle h5 hy hyH hb1 hb2 hfg)
  -- Bender's multiplication table (with `b₁ ↔ b₂` for the second inversion)
  have hmul1 := SixInvSetMulTable G I hBc B h1 D h5o y hy2 hyH h6 a b1 b2 ha ha3 hb1 hb1o hb2 hb2o h12
  have hb1a : b1 * a * b1 = a⁻¹ := hmul1.1
  have hcube : (b1 * b2) ^ 3 = 1 := hmul1.2
  have hmul2 := SixInvSetMulTable G I hBc B h1 D h5o y hy2 hyH h6 a b2 b1 ha ha3 hb2 hb2o hb1 hb1o h12.symm
  have hb2a : b2 * a * b2 = a⁻¹ := hmul2.1
  have hb1aa : b1 * (a * a) * b1 = (a * a)⁻¹ := by
    have h : (b1 * a * b1) * (b1 * a * b1) = b1 * (a * a) * b1 := by
      rw [show (b1 * a * b1) * (b1 * a * b1) = b1 * a * (b1 * b1) * a * b1 from by group,
        hb1sq]
      group
    rw [← h, hb1a]; group
  have hb2aa : b2 * (a * a) * b2 = (a * a)⁻¹ := by
    have h : (b2 * a * b2) * (b2 * a * b2) = b2 * (a * a) * b2 := by
      rw [show (b2 * a * b2) * (b2 * a * b2) = b2 * a * (b2 * b2) * a * b2 from by group,
        hb2sq]
      group
    rw [← h, hb2a]; group
  have haa3 : orderOf (a * a) = 3 := by
    have h3 : a ^ 3 = 1 := by rw [← ha3]; exact pow_orderOf_eq_one a
    have hcube' : (a * a) ^ 3 = 1 := by
      have h6' : (a * a) ^ 3 = (a ^ 3) ^ 2 := by
        have e1 : (a * a) ^ 3 = a ^ 6 := by
          rw [← pow_two a, ← pow_mul]
        have e2 : (a ^ 3) ^ 2 = a ^ 6 := by
          rw [← pow_mul]
        rw [e1, e2]
      rw [h6', h3]; norm_num
    have hdvd : orderOf (a * a) ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hcube'
    have hne : orderOf (a * a) ≠ 1 := by
      intro hcon
      have h1' : a * a = 1 := orderOf_eq_one_iff.mp hcon
      have h2' : orderOf a ∣ 2 := by
        rw [orderOf_dvd_iff_pow_eq_one, pow_two]; exact h1'
      rw [ha3] at h2'
      exact absurd h2' (by norm_num)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h hne
    · exact h
  -- ## The split: `b₁b₂ = h·v` with `h ∈ {a, a²}` and `v ∈ VU`
  obtain ⟨h, hhc, hvsplit⟩ :=
    Work.CORE3.LeFourAux.SplitQuotient hVUle hVUn hVUrel ha.1 hb1.1 hb2.1 ha3 ha_notVU
      hb1b2_notVU hcube
  set v : G := h⁻¹ * (b1 * b2) with hvdef
  have hprod : b1 * b2 = h * v := by rw [hvdef]; group
  have hvVU : v ∈ Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U := hvsplit
  have hhH : h ∈ B.Hhat := by
    rcases hhc with rfl | rfl
    · exact ha.1
    · exact B.Hhat.mul_mem ha.1 ha.1
  have hh3 : orderOf h = 3 := by
    rcases hhc with rfl | rfl
    · exact ha3
    · exact haa3
  have hb1h : b1 * h * b1 = h⁻¹ := by
    rcases hhc with rfl | rfl
    · exact hb1a
    · exact hb1aa
  have hb2h : b2 * h * b2 = h⁻¹ := by
    rcases hhc with rfl | rfl
    · exact hb2a
    · exact hb2aa
  have hhD : h ∈ B.Hhat ⊓ Work.GW2.conjSub y B.Hhat := by
    rcases hhc with rfl | rfl
    · exact haD
    · exact (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat).mul_mem haD haD
  have hvD : v ∈ B.Hhat ⊓ Work.GW2.conjSub y B.Hhat :=
    (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat).mul_mem
      ((B.Hhat ⊓ Work.GW2.conjSub y B.Hhat).inv_mem hhD)
      ((B.Hhat ⊓ Work.GW2.conjSub y B.Hhat).mul_mem hb1D hb2D)
  -- ## `v` lies in `U`
  have hvU : v ∈ B.U := by
    by_contra hvnotU
    obtain ⟨v2, hv2, v3, hv3, hvdec⟩ :=
      exists_mul_of_mem_sup_of_normal hVle hUle hVnorm hUnorm v hvVU
    have hv2ne : v2 ≠ 1 := by
      intro hcon
      exact hvnotU (by rw [hvdec, hcon, one_mul]; exact hv3)
    have hv22 : v2 * v2 = 1 := by
      have h := D.four.2 v2 hv2
      simpa [pow_two] using h
    -- `U` commutes with `V` elementwise, since `VU = C_Ĥ(V)`
    have hcommUV : ∀ u ∈ B.U, ∀ w ∈ Work.GW2.pCoreIn 2 B.Hhat, u * w = w * u := by
      intro u hu w hw
      have hmem : u ∈ Subgroup.centralizer ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G)
          ⊓ B.Hhat := by
        rw [hCV]; exact Subgroup.mem_sup_right hu
      exact (Subgroup.mem_centralizer_iff.mp hmem.1 w hw).symm
    -- `b₁ v b₁ = b₂ v b₂ = h v⁻¹ h⁻¹`
    obtain ⟨hconj1, hconj2⟩ :=
      Work.CORE3.LeFourAux.ConjInvOfMul hb1sq hb2sq hb1h hb2h hprod
    -- `b₁`, `b₂` invert `U` elementwise (`D.K = U` and Bender's `Case1bData.inv`)
    have hKU : D.K = B.U := by
      have hKle : D.K ≤ B.U := le_trans D.hall.1 (Subgroup.map_subtype_le _)
      refine Subgroup.eq_of_le_of_card_ge hKle ?_
      have hdvd : Nat.card D.K ∣ 3 := by
        have h := Subgroup.card_dvd_of_le hKle
        rwa [hU3] at h
      have hne : Nat.card D.K ≠ 1 := by
        intro hcon
        exact D.ne (Subgroup.eq_bot_of_card_eq (H := D.K) hcon)
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with hh | hh
      · exact absurd hh hne
      · rw [hh, hU3]
    have hinvU : ∀ s : G, s ∈ B.Hhat → orderOf s = 2 → s ∉ Work.GW2.pCoreIn 2 B.Hhat →
        ∀ u ∈ B.U, s * u * s⁻¹ = u⁻¹ := by
      intro s hsH hs2 hsV u hu
      have hKset : ((D.K : Subgroup G) : Set G) = Work.GW2.invSet B.U s := D.inv s hsH hs2 hsV
      have hmem : u ∈ Work.GW2.invSet B.U s := by
        rw [← hKset, hKU]; exact hu
      exact hmem.2
    have hb1U : b1 * v3 * b1 = v3⁻¹ := by
      have h := hinvU b1 hb1.1 hb1o hb1_notV v3 hv3
      rwa [inv_eq_of_mul_eq_one_right hb1sq] at h
    have hb2U : b2 * v3 * b2 = v3⁻¹ := by
      have h := hinvU b2 hb2.1 hb2o hb2_notV v3 hv3
      rwa [inv_eq_of_mul_eq_one_right hb2sq] at h
    -- `h` centralizes `U`
    have hhN : h ∈ Subgroup.normalizer (B.U : Set G) := hHhatNormU hhH
    have hhU : h * v3 * h⁻¹ = v3 := by
      have hcent : B.U ≤ Subgroup.centralizer ({h} : Set G) :=
        OrderThreeLeCentralizer hhN hh3 hU3
      have hcomm := Subgroup.mem_centralizer_singleton_iff.mp (hcent hv3)
      rw [← hcomm]; group
    have hA : b1 * v2 * b1 ∈ Work.GW2.pCoreIn 2 B.Hhat := by
      have h := hVnorm b1 hb1.1 v2 hv2
      rwa [inv_eq_of_mul_eq_one_right hb1sq] at h
    have hB : b2 * v2 * b2 ∈ Work.GW2.pCoreIn 2 B.Hhat := by
      have h := hVnorm b2 hb2.1 v2 hv2
      rwa [inv_eq_of_mul_eq_one_right hb2sq] at h
    obtain ⟨hfixA, hfixB⟩ :=
      Work.CORE3.LeFourAux.ConjEqOfDecomp hcommUV hv2 hv3 hvdec hv22 hb1sq hb2sq hA hB
        hconj1 hconj2 hb1U hb2U hhU
    have hB1 : b1 * v2 * b1⁻¹ = h * v2 * h⁻¹ := by
      rw [inv_eq_of_mul_eq_one_right hb1sq]; exact hfixA
    have hB2 : b2 * v2 * b2⁻¹ = h * v2 * h⁻¹ := by
      rw [inv_eq_of_mul_eq_one_right hb2sq]; exact hfixB
    -- `v ∈ VU = C_Ĥ(V)`, so `h` and `b₁b₂` induce the same automorphism of `V`
    have hvcent : v ∈ Subgroup.centralizer
        ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) := by
      have hmem : v ∈ Subgroup.centralizer ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G)
          ⊓ B.Hhat := by
        rw [hCV]; exact hvVU
      exact hmem.1
    have hvconj : ∀ x ∈ Work.GW2.pCoreIn 2 B.Hhat, v * x * v⁻¹ = x := by
      intro x hx
      have hcomm := Subgroup.mem_centralizer_iff.mp hvcent x hx
      rw [← hcomm]; group
    have hconjh : ∀ x ∈ Work.GW2.pCoreIn 2 B.Hhat,
        h * x * h⁻¹ = (b1 * b2) * x * (b1 * b2)⁻¹ := by
      intro x hx
      calc h * x * h⁻¹ = h * (v * x * v⁻¹) * h⁻¹ := by rw [hvconj x hx]
        _ = (h * v) * x * (h * v)⁻¹ := by group
        _ = (b1 * b2) * x * (b1 * b2)⁻¹ := by rw [hprod]
    have hphi : (b1 * b2) * v2 * (b1 * b2)⁻¹ = h * v2 * h⁻¹ := (hconjh v2 hv2).symm
    have hphi' : (b1 * b2) * v2 * (b1 * b2)⁻¹ = v2 := by
      have h1' : (b1 * b2) * v2 * (b1 * b2)⁻¹ = b1 * (b2 * v2 * b2⁻¹) * b1⁻¹ := by group
      rw [h1', hB2, ← hB1]
      exact mul_inj_sandwich hb1sq
    have hv2fix : h * v2 * h⁻¹ = v2 := by rw [← hphi, hphi']
    have hfix1 : b1 * v2 * b1⁻¹ = v2 := by rw [hB1, hv2fix]
    have hfix2 : b2 * v2 * b2⁻¹ = v2 := by rw [hB2, hv2fix]
    -- `b₁` and `b₂` induce the same automorphism of `V`
    have hb1N : b1 ∈ Subgroup.normalizer ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) :=
      Subgroup.le_normalizer_iff.mpr hVnorm hb1.1
    have hb2N : b2 ∈ Subgroup.normalizer ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) :=
      Subgroup.le_normalizer_iff.mpr hVnorm hb2.1
    have hb1C : b1 ∉ Subgroup.centralizer
        ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) := fun hmem =>
      hb1_notVU (by rw [← hCV]; exact ⟨hmem, hb1.1⟩)
    have hb2C : b2 ∉ Subgroup.centralizer
        ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) := fun hmem =>
      hb2_notVU (by rw [← hCV]; exact ⟨hmem, hb2.1⟩)
    have hagree : ∀ w : G, w ∈ Work.GW2.pCoreIn 2 B.Hhat →
        b1 * w * b1⁻¹ = b2 * w * b2⁻¹ :=
      Work.CORE3.LeFourAux.FixFour D.four hv2 hv2ne hfix1 hfix2 hb1N hb2N hb1C hb2C
    -- hence `b₁b₂` centralizes `V`, i.e. `b₁b₂ ∈ VU = C_Ĥ(V)`: contradiction
    have hcentb12 : (b1 * b2) ∈ Subgroup.centralizer
        ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hconj : (b1 * b2) * x * (b1 * b2)⁻¹ = x := by
        have h1' : (b1 * b2) * x * (b1 * b2)⁻¹ = b1 * (b2 * x * b2⁻¹) * b1⁻¹ := by group
        rw [h1', ← hagree x hx]
        exact mul_inj_sandwich hb1sq
      have h2' : (b1 * b2) * x = x * (b1 * b2) := by
        have := congrArg (fun t => t * (b1 * b2)) hconj
        simpa [mul_assoc] using this
      exact h2'.symm
    have hmemVU : b1 * b2 ∈ Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U := by
      have hmem : (b1 * b2) ∈ Subgroup.centralizer
          ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) ⊓ B.Hhat :=
        ⟨hcentb12, B.Hhat.mul_mem hb1.1 hb2.1⟩
      rwa [hCV] at hmem
    exact hb1b2_notVU hmemVU
  -- ## Conclusion
  have hcommhv : h * v = v * h := by
    have hcent : B.U ≤ Subgroup.centralizer ({h} : Set G) :=
      OrderThreeLeCentralizer (hHhatNormU hhH) hh3 hU3
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hcent hvU)).symm
  exact ⟨h, hhc, v, ⟨hvD, hvVU⟩, hprod, fun _ => ⟨hvU, hcommhv⟩⟩

end Work.CORE3
