import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.CountSetup
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2SevenAux
import Submission.Work.CORE4.Case2Seven
import Submission.Work.CORE4.SevenX.piFU_le_pi_K0F
import Submission.Work.CORE4.Case2K1_ne_bot
import Submission.Work.CORE4.A7V
import Submission.Work.CORE4.Case2S0_comm_U
import Submission.Work.CORE4.Case2SevenCentralizer
import Submission.Work.CORE4.SevenX.sevenX_le_centralizer_of_isNilpotent
import Submission.Work.CORE4.SevenX.sevenX_fittingIn_inf_centralizer_sup_le
import Submission.Work.CORE4.SixThree

open Work.GW2 Subgroup

set_option linter.style.haveILetI false

namespace Work.CORE4

/-- **Bender 1981, §4 (7), first conjunct, p. 225: `O₂(H ⊓ M) = O₂(H)`.**

(The paper writes `O₂`, not `O_{2'}`: compare the later uses `V := O₂(H∩M) = O₂(H)` "is of type
(2,2)" and p. 227.  The odd-core reading is false.)

At the `Case2Ctx` level, where `S ≤ E(M)` by §4 (9) and `H ⊓ M = (U ⊓ M) ⊔ S`
(`Case2Ctx.inter_H_M`), the two inclusions are:

* `O₂(H ⊓ M) ≤ S₀`:  `O₂(H ⊓ M)` is a normal 2-subgroup of `H ⊓ M`, hence lies in the Sylow
  2-subgroup `S ≤ H ⊓ M`; and `O₂(H ⊓ M) ⊓ (U ⊓ M) ≤ S ⊓ U ⊓ M ≤ S ⊓ K = 1`, so
  `[O₂(H ⊓ M), U ⊓ M] = 1` and hence `O₂(H ⊓ M) ≤ C_S(U ⊓ M) ⊆ C_S(K) = S₀`
  (`Work.CORE4.S0CentK` proves `⁅K, S₀⁆ = ⊥`, i.e. `S₀ ≤ C_S(K)`; the reverse inclusion is the
  Bender p. 224 dihedral computation in `Case2S0_comm_U.lean`).
* `S₀ ≤ O₂(H ⊓ M)`:  `S₀ ⊴ S` (index two) and `U ⊓ M ≤ C_G(S₀)` (`Case2Pre` gives
  `U ⊓ M = K ⊔ B₀`; `⁅K, S₀⁆ = ⊥` by `Work.CORE4.S0CentK`, and `B₀ = C_{U⊓M}(s) ≤ C_G(S ⊓ E)`
  by Bender's (2)), so `S₀ ⊴ H ⊓ M` and `S₀ ≤ O₂(H ⊓ M)`.
* Hence `O₂(H ⊓ M) = S₀ = C_S(K)`.  Also `O₂(H) ≤ C_S(K)`: `O₂(H) ⊓ U = 1` (`O₂(H)` a 2-group,
  `U` odd, both normal in `H`) gives `[O₂(H), U] = 1`, so `O₂(H) ≤ C_S(U) ⊆ C_S(K)`.
* Finally `S₀ ≤ O₂(H)` needs `S₀ ⊴ H` (equivalently `U ≤ N_G(S₀)`; this is the crux).  Bender's
  pp. 224–225 route: every `π'`-subgroup of `H` centralizing `K₀F = N_{F(U)}(F)` lies in
  `C_H(F(U)) = O₂(H) × Z(F(U))` — `I.toolkit.c11iv` with `K₀ = F(U) ⊓ K` and `π = π(F(U))`;
  since `O₂(H ⊓ M) ≤ C_G(U ⊓ M) ⊇ C_G(K₀F)`, this gives `O₂(H ⊓ M) ≤ O₂(H)`, and then
  `O₂(H ⊓ M) = S₀ ≤ O₂(H)`.

The statement is Bender's (7) conjunct 1; `Case2Ctx` carries §4 (1)–(6) and (9), and
`Case2SevenFacts` is the conjunction of this with five `π`-statements.  The older docstring in
`Submission/Work/CORE4/Case2SevenRemainingOfCtx.lean` claims `O₂(H ⊓ M) = S` (the whole Sylow),
which is mathematically wrong for `PSL(2,q)`; `S₀` is correct.

PROOF (added by the prover; it does *not* go through `S₀`, and so avoids the circularity of
`Case2S0_comm_U`, which assumes `Case2SevenFacts`).  Everything is Bender's own argument, run in
the reverse order, and both inclusions are cheap once the right auxiliary objects are recognised.

* `O₂(H) = S ⊓ C_G(U)`: the middle conjunct of Bender's Theorem 2.6 (`I.thm26`) combined with
  `A7V_pCoreIn_Hhat_eq_pCoreIn_H` (which turns `O₂(Ĥ)` into `O₂(H)` from that conjunct alone).
* `P := O₂(H ⊓ M) ≤ S` and `[P, U ⊓ M] = 1` (normal subgroups of `H ⊓ M` of coprime order), so
  `P ≤ C_G(U ⊓ M)`.
* Bender 1.1(iv) with `K = F(U)`, `K₁ = F(U) ⊓ M = K₀ ⊔ F = N_{F(U)}(F)`: `F(U)` is nilpotent,
  `C_{F(U)}(K₁) ≤ K₁` (`sevenX_fittingIn_inf_centralizer_sup_le`), so `P ≤ C_G(F(U))`.  This uses
  `SevenX.sevenX_le_centralizer_of_isNilpotent` (the nilpotent form of 1.1(iv), which needs no
  normality of `K₁` in `F(U)`).
* 1.1(iv) a second time, now with `K = U`, `K₁ = F(U)`: `F(U) ⊴ U`, `C_U(F(U)) ≤ F(U)` (P. Hall /
  Bender 1.2 for the solvable odd-order group `U`, `sevenX_centralizer_fittingIn_inf_le_fittingIn`)
  and `P ≤ C_G(F(U))`, so `P ≤ C_G(U)`.  Hence `P ≤ S ⊓ C_G(U) = O₂(H)`.
* Conversely `O₂(H) ≤ P`: `O₂(H) ≤ S ≤ H ⊓ M`, and `O₂(H) ⊴ H ⊓ M` because
  `H ⊓ M = (U ⊓ M) ⊔ S`, `S ≤ N_G(O₂(H))` (as `O₂(H) ⊴ H`) and `U ≤ C_G(O₂(H))` (from
  `O₂(H) ≤ C_G(U)`); as a normal 2-subgroup of `H ⊓ M` it lies in `O₂(H ⊓ M)`. -/
theorem SevenO2HM (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        Work.GW2.pCoreIn 2 (B.H ⊓ h.D.M) = Work.GW2.pCoreIn 2 B.H := by
  intro G _ _ hbc B h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- ## Step 0. Bender's Theorem 2.6: `O₂(H) = S ⊓ C_G(U)`
  have h26 : (B.S : Subgroup G) ⊓ Subgroup.centralizer (B.U : Set G) =
      Work.GW2.pCoreIn 2 B.Hhat := (I.thm26 G I.toolkit.ft hbc B).2.1
  have hA7 : Work.GW2.pCoreIn 2 B.Hhat = Work.GW2.pCoreIn 2 B.H :=
    A7V_pCoreIn_Hhat_eq_pCoreIn_H
      (fun B' => (I.thm26 G I.toolkit.ft hbc B').2.1) B
  have hO2 : Work.GW2.pCoreIn 2 B.H =
      (B.S : Subgroup G) ⊓ Subgroup.centralizer (B.U : Set G) := (h26.trans hA7).symm
  have hO2leC : Work.GW2.pCoreIn 2 B.H ≤ Subgroup.centralizer (B.U : Set G) :=
    hO2.le.trans inf_le_right
  have hO2leS : Work.GW2.pCoreIn 2 B.H ≤ (B.S : Subgroup G) := hO2.le.trans inf_le_left
  -- ## Step 1. `P := O₂(H ⊓ M)` is a normal 2-subgroup of `H ⊓ M`, hence `P ≤ S`
  set X : Subgroup G := B.H ⊓ h.D.M with hX
  set P : Subgroup G := Work.GW2.pCoreIn 2 X with hP
  have hSleX : (B.S : Subgroup G) ≤ X := by
    rw [hX]; exact le_inf B.S_le_H h.S_le_M
  have hPleX : P ≤ X := by rw [hP]; exact Subgroup.map_subtype_le _
  have hPleH : P ≤ B.H := hPleX.trans inf_le_left
  have hPp : IsPGroup 2 P := by rw [hP]; exact A7V_isPGroup_pCoreIn 2 X
  have hPn : (P.subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hPleX]
    intro n a hn ha
    rw [hP] at hn
    exact hP ▸ (A7V_conj_mem_pCoreIn 2 X ha hn)
  have hPleS : P ≤ (B.S : Subgroup G) := by
    have hPpX : IsPGroup 2 (P.subgroupOf X) :=
      hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPleX).symm
    haveI := hPn
    have h1 := IsPGroup.le_sylow_of_normal hPpX ((B.S).subtype hSleX)
    intro x hx
    have h2 := h1 (Subgroup.mem_subgroupOf.mpr hx :
      (⟨x, hPleX hx⟩ : ↥X) ∈ P.subgroupOf X)
    exact Subgroup.mem_subgroupOf.mp h2
  -- ## Step 2. `[P, U ⊓ M] = 1`
  have hUn : ((B.U ⊓ h.D.M).subgroupOf X).Normal := by
    have hXM : h.D.M ⊓ B.H = X := by rw [hX, inf_comm]
    rw [← hXM]; exact h.U_inf_M_normal
  have hPinf : P ⊓ (B.U ⊓ h.D.M) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxP, hxUM⟩ := Subgroup.mem_inf.mp hx
    have h1 : x ∈ B.U ⊓ (B.S : Subgroup G) :=
      Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hxUM).1, hPleS hxP⟩
    rw [B.U_inf_S] at h1
    exact Subgroup.mem_bot.mp h1
  have hPleCUM : P ≤ Subgroup.centralizer (((B.U ⊓ h.D.M) : Subgroup G) : Set G) :=
    A7V_le_centralizer_of_normal_inf_eq_bot hPleX
      (le_inf (le_trans inf_le_left B.U_le_H) inf_le_right) hPn hUn hPinf
  -- ## Step 3. Bender 1.1(iv) with `K = F(U)`, `K₁ = F(U) ⊓ M`: `P ≤ C_G(F(U))`
  have hSix : Work.GW2.fittingIn B.U ⊓ h.D.M = h.D.K0 ⊔ h.D.F :=
    SixThree I G hbc B h.D h.pre
  have hK0Fle_FU : h.D.K0 ⊔ h.D.F ≤ Work.GW2.fittingIn B.U := by
    rw [← hSix]; exact inf_le_left
  have hK0Fle_UM : h.D.K0 ⊔ h.D.F ≤ B.U ⊓ h.D.M := by
    rw [← hSix]
    exact le_inf (le_trans inf_le_left (Subgroup.map_subtype_le _)) inf_le_right
  have hFUodd : Odd (Nat.card ↥(Work.GW2.fittingIn B.U)) :=
    Odd.of_dvd_nat B.U_odd (Subgroup.card_dvd_of_le (Subgroup.map_subtype_le _))
  have hPN : P ≤ Subgroup.normalizer (Work.GW2.fittingIn B.U : Set G) :=
    hPleH.trans (BenderSetup.H_le_normalizer_fittingIn B)
  have hPC : P ≤ Subgroup.centralizer ((h.D.K0 ⊔ h.D.F : Subgroup G) : Set G) :=
    hPleCUM.trans (Subgroup.centralizer_le hK0Fle_UM)
  have hsc : Work.GW2.fittingIn B.U ⊓
      Subgroup.centralizer ((h.D.K0 ⊔ h.D.F : Subgroup G) : Set G) ≤ h.D.K0 ⊔ h.D.F :=
    SevenX.sevenX_fittingIn_inf_centralizer_sup_le B h.D h.pre hSix
  have hPleCFU : P ≤ Subgroup.centralizer (Work.GW2.fittingIn B.U : Set G) :=
    SevenX.sevenX_le_centralizer_of_isNilpotent I.toolkit.c11iv
      (Work.GW2.fittingIn B.U) (h.D.K0 ⊔ h.D.F) P
      (SevenX.PiFU.isNilpotent_fittingIn B.U) hK0Fle_FU hsc
      Nat.prime_two hPp (Nat.coprime_two_left.mpr hFUodd) hPN hPC
  -- ## Step 4. Bender 1.1(iv) with `K = U`, `K₁ = F(U)`: `P ≤ C_G(U)`
  have hUsolv : Group.IsSolvable ↥B.U := I.toolkit.ft ↥B.U B.U_odd
  have hscU : B.U ⊓ Subgroup.centralizer (Work.GW2.fittingIn B.U : Set G) ≤
      Work.GW2.fittingIn B.U := by
    rw [inf_comm]
    exact sevenX_centralizer_fittingIn_inf_le_fittingIn B.U hUsolv
  have hPNU : P ≤ Subgroup.normalizer (B.U : Set G) :=
    hPleH.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer B.U_le_H).mp B.U_normal)
  have hPleCU : P ≤ Subgroup.centralizer (B.U : Set G) :=
    I.toolkit.c11iv G 2 P B.U (Work.GW2.fittingIn B.U) hPp
      (Nat.coprime_two_left.mpr B.U_odd) hPNU (Subgroup.map_subtype_le _)
      (fittingIn_subgroupOf_normal B.U) hPleCFU hscU
  -- ## Step 5. `P ≤ O₂(H) = S ⊓ C_G(U)`
  have hPleO2 : P ≤ Work.GW2.pCoreIn 2 B.H := by
    rw [hO2]; exact le_inf hPleS hPleCU
  -- ## Step 6. `O₂(H) ≤ P`: `O₂(H)` is a normal 2-subgroup of `H ⊓ M`
  have hO2leP : Work.GW2.pCoreIn 2 B.H ≤ P := by
    have hleX : Work.GW2.pCoreIn 2 B.H ≤ X := hO2leS.trans hSleX
    have hHleN : B.H ≤ Subgroup.normalizer ((Work.GW2.pCoreIn 2 B.H : Subgroup G) : Set G) := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp ?_
      rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_subtype_le _)]
      intro n a hn ha
      exact A7V_conj_mem_pCoreIn 2 B.H ha hn
    have hUcen : B.U ≤ Subgroup.centralizer ((Work.GW2.pCoreIn 2 B.H : Subgroup G) : Set G) := by
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact ((Subgroup.mem_centralizer_iff.mp (hO2leC hx)) u hu).symm
    have hNn : ((Work.GW2.pCoreIn 2 B.H).subgroupOf X).Normal := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hleX).mpr ?_
      have hXM : X = (B.U ⊓ h.D.M) ⊔ (B.S : Subgroup G) := by
        have h' : h.D.M ⊓ B.H = X := by rw [hX, inf_comm]
        rw [← h']; exact h.inter_H_M I
      rw [hXM]
      exact sup_le ((le_trans inf_le_left hUcen).trans (Subgroup.centralizer_le_normalizer _))
        (B.S_le_H.trans hHleN)
    have hPg : IsPGroup 2 ((Work.GW2.pCoreIn 2 B.H).subgroupOf X) :=
      (A7V_isPGroup_pCoreIn 2 B.H).of_equiv (Subgroup.subgroupOfEquivOfLe hleX).symm
    have h1 := le_pCoreIn_of_normal_isPGroup_s0 hleX hNn hPg
    rw [← hP] at h1
    exact h1
  exact le_antisymm hPleO2 hO2leP

end Work.CORE4
