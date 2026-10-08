import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2SevenAux
import Submission.Work.CORE4.SixThree
import Submission.Work.CORE4.SevenX.piFU_le_pi_K0F
import Submission.Work.CORE4.SevenX.sevenX_le_centralizer_of_isNilpotent
import Submission.Work.CORE4.SevenX.sevenX_fittingIn_inf_centralizer_sup_le
import Submission.Work.CORE4.Case2SevenCentralizer
import Submission.Work.CORE4.A7V

namespace Work.CORE4.SevenNine

open Work.GW2 Subgroup

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- `H ≤ N_G(F(U))`: `U ⊴ H` and `F(U)` is characteristic in `U` (via `conjSub_fittingIn`).

This is `Work.GW2.BenderSetup.H_le_normalizer_fittingIn` (`CORE4/Case2K1_ne_bot.lean`),
reproved here so that this file does not import a module whose closure contains a `sorry`. -/
private theorem o2hm_H_le_normalizer_fittingIn {G : Type} [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) :
    B.H ≤ Subgroup.normalizer ((Work.GW2.fittingIn B.U : Subgroup G) : Set G) := by
  intro g hg
  have hU : Work.GW2.conjSub g B.U = B.U :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normal_subgroupOf_iff_le_normalizer B.U_le_H).mp B.U_normal hg)
  have hA : Work.GW2.conjSub g (Work.GW2.fittingIn B.U) = Work.GW2.fittingIn B.U := by
    rw [Work.CORE4.conjSub_fittingIn, hU]
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact hA

/-- Bender 1981, §4 (7) (p. 225), first conjunct: `O₂(H ⊓ M) = O₂(H)`, at the design-pass-9
`Case2Ctx6` level (§4 (1)–(6) data plus Bender's Sylow choice `S ⊓ M ∈ Syl₂(M)` and (1),(2)).

`O₂(X) = Work.GW2.pCoreIn 2 X`, `H = C_G(t)`, `B.U = O(H)`, `S` = the Sylow 2-subgroup of `B`.

NOTE for the prover: `Submission/Work/CORE4/SevenO2HM.lean` proves this at the *stronger*
`Case2Ctx` level (where §4 (9) `S ≤ E(M) ≤ M` is available); that proof uses `S ≤ M` and so does
NOT apply here.  A complete route at `Case2Ctx6` is:

* reverse inclusion `O₂(H) ≤ O₂(H ⊓ M)`: `O₂(H) ≤ H` is normal in `H`, so `H ⊓ M ≤ H ≤ N_G(O₂(H))`
  gives `O₂(H) ⊴ H ⊓ M`; and `O₂(H) ≤ C.D.M` because `O₂(H) ≤ C_G(F(U)) ≤ C_G(X) ≤ N_G(X) ≤ M`
  (`O₂(H)` and `F(U)` are normal subgroups of `H` of coprime order, `X ≤ F(U)` is `Case2Data.X_le`
  and `Case2Data.NX_le`); so `O₂(H) ≤ H ⊓ M` and
  `le_pCoreIn_of_normal_isPGroup` (or `A7V_le_pCoreIn_of_normal_isPGroup`) finishes.
* forward inclusion `P := O₂(H ⊓ M) ≤ O₂(H)`:
  - `P ≤ B.S ⊓ C.D.M`: `P ⊴ H ⊓ M` and `B.S ⊓ C.D.M ≤ H ⊓ M` (`B.S ≤ B.H`); `P` and `B.S ⊓ C.D.M`
    are 2-subgroups of `C.D.M`, and `B.S ⊓ C.D.M ∈ Syl₂(C.D.M)` by `hplus.1`
    (`¬ 2 ∣ (B.S ⊓ C.D.M).relIndex C.D.M`), so `(B.S ⊓ C.D.M) ⊔ P` is a 2-subgroup of `C.D.M`
    containing a Sylow, whence `P ≤ B.S ⊓ C.D.M ≤ B.S`.
  - `[P, B.U ⊓ C.D.M] = ⋯ = ⊥` (both are normal in `H ⊓ M` and of coprime order), hence
    `P ≤ C_G(B.U ⊓ C.D.M)`; as `Work.GW2.Case2Data.K0 C.D ⊔ C.D.F ≤ B.U ⊓ C.D.M` also
    `P ≤ C_G(K₀ ⊔ F)`.
  - `SevenX.sevenX_le_centralizer_of_isNilpotent` with `K = B.U`, `K₀ = F(U)` (using
    `SevenX.sevenX_fittingIn_inf_centralizer_sup_le`, `SixThree`, P. Hall
    `sevenX_centralizer_fittingIn_inf_le_fittingIn`, `I.toolkit.ft`)
    gives `P ≤ C_G(B.U)` — exactly as in `SevenO2HM` steps 3–4, none of which uses `S ≤ M`.
  - `O₂(H) = B.S ⊓ C_G(B.U)` by `I.thm26` + `A7V_pCoreIn_Hhat_eq_pCoreIn_H`.

Do NOT use `Work.CORE4.Case2Seven`, `Work.CORE4.SevenO2HM` or anything depending on `sorryAx`.

PROOF (added by the prover; it follows the route above, with one simplification: `O₂(H) ≤ M` is
obtained from `O₂(H) = S ⊓ C_G(U) = S ⊓ C_G(B.U)` (Theorem 2.6 + `A7V_pCoreIn_Hhat_eq_pCoreIn_H`,
already needed for the forward inclusion) together with `X ≤ U`, `C_G(U) ≤ C_G(X) ≤ N_G(X) ≤ M`,
rather than by first passing through `C_G(F(U))`).

The only place where `hplus.1` (`S ⊓ M ∈ Syl₂(M)`) enters is `P ≤ S`: `P` is a 2-subgroup of
`H ⊓ M` normal in `H ⊓ M`, and `S ⊓ M ≤ H ⊓ M` normalizes `P`; hence `(S ⊓ M) ⊔ P` is a 2-subgroup
of `M` containing the Sylow `S ⊓ M` of `M` (a Sylow object of `↥M` is built from `hplus.1` via
`IsPGroup.toSylow`), so by maximality `(S ⊓ M) ⊔ P = S ⊓ M` and `P ≤ S`. -/
theorem O2_HM_eq_O2_H {G : Type} [Group G] [Finite G] (I : Work.GW2.C4Inputs)
    (hbc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h2 : Work.GW2.Case2 B)
    (C : Work.GW2.Case2Ctx6 B) (hplus : Work.GW2.Case2PrePlus B C.D) :
    Work.GW2.pCoreIn 2 (B.H ⊓ C.D.M) = Work.GW2.pCoreIn 2 B.H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D : Work.GW2.Case2Data B := C.D with hD
  have hpre : Work.GW2.Case2Pre B D := C.pre
  -- ## Step 0. Bender's Theorem 2.6: `O₂(H) = S ⊓ C_G(U)`
  have h26 : ((B.S : Subgroup G) ⊓ Subgroup.centralizer (B.U : Set G) =
      Work.GW2.pCoreIn 2 B.Hhat) := (I.thm26 G I.toolkit.ft hbc B).2.1
  have hA7 : Work.GW2.pCoreIn 2 B.Hhat = Work.GW2.pCoreIn 2 B.H :=
    Work.CORE4.A7V_pCoreIn_Hhat_eq_pCoreIn_H
      (fun B' => (I.thm26 G I.toolkit.ft hbc B').2.1) B
  have hO2 : Work.GW2.pCoreIn 2 B.H =
      (B.S : Subgroup G) ⊓ Subgroup.centralizer (B.U : Set G) := (h26.trans hA7).symm
  have hO2leC : Work.GW2.pCoreIn 2 B.H ≤ Subgroup.centralizer (B.U : Set G) :=
    hO2.le.trans inf_le_right
  -- ## Step 1. reverse inclusion: `O₂(H) ≤ O₂(H ⊓ M)`
  have hO2leM : Work.GW2.pCoreIn 2 B.H ≤ D.M := by
    refine (hO2leC.trans ?_).trans D.NX_le
    exact (Subgroup.centralizer_le D.X_le_U).trans
      (Subgroup.centralizer_le_normalizer (D.X : Set G))
  have hO2leX : Work.GW2.pCoreIn 2 B.H ≤ B.H ⊓ D.M :=
    le_inf (Subgroup.map_subtype_le _) hO2leM
  have hO2n : ((Work.GW2.pCoreIn 2 B.H).subgroupOf (B.H ⊓ D.M)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hO2leX]
    intro a b ha hb
    exact Work.CORE4.A7V_conj_mem_pCoreIn 2 B.H (Subgroup.mem_inf.mp hb).1 ha
  have hO2p : IsPGroup 2 ((Work.GW2.pCoreIn 2 B.H).subgroupOf (B.H ⊓ D.M)) :=
    (Work.CORE4.A7V_isPGroup_pCoreIn 2 B.H).of_equiv
      (Subgroup.subgroupOfEquivOfLe hO2leX).symm
  have hO2leP : Work.GW2.pCoreIn 2 B.H ≤ Work.GW2.pCoreIn 2 (B.H ⊓ D.M) :=
    Work.CORE4.A7V_le_pCoreIn_of_normal_isPGroup 2 (B.H ⊓ D.M) hO2leX hO2n hO2p
  -- ## forward inclusion: `P := O₂(H ⊓ M) ≤ O₂(H)`
  set X : Subgroup G := B.H ⊓ D.M with hX
  have hPleX : Work.GW2.pCoreIn 2 X ≤ X := Subgroup.map_subtype_le _
  have hPleH : Work.GW2.pCoreIn 2 X ≤ B.H := hPleX.trans inf_le_left
  have hPleM : Work.GW2.pCoreIn 2 X ≤ D.M := hPleX.trans inf_le_right
  have hPp : IsPGroup 2 (Work.GW2.pCoreIn 2 X) := Work.CORE4.A7V_isPGroup_pCoreIn 2 X
  have hPn : ((Work.GW2.pCoreIn 2 X).subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hPleX]
    intro a b ha hb
    exact Work.CORE4.A7V_conj_mem_pCoreIn 2 X hb ha
  -- ## Step 2. `P ≤ S`, using Bender's Sylow choice `S ⊓ M ∈ Syl₂(M)`
  have hSmleX : (B.S : Subgroup G) ⊓ D.M ≤ X := by
    rw [hX]; exact le_inf (le_trans inf_le_left B.S_le_H) inf_le_right
  have hXleNP : X ≤ Subgroup.normalizer ((Work.GW2.pCoreIn 2 X : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPleX).mp hPn
  set J : Subgroup G := ((B.S : Subgroup G) ⊓ D.M) ⊔ Work.GW2.pCoreIn 2 X with hJ
  have hJleNP : ((B.S : Subgroup G) ⊓ D.M) ≤
      Subgroup.normalizer (Work.GW2.pCoreIn 2 X : Set G) :=
    hSmleX.trans hXleNP
  have hJp : IsPGroup 2 J :=
    ((B.S).isPGroup'.to_inf_left).to_sup_of_normal_right' hPp hJleNP
  have hSmP : IsPGroup 2 ((B.S).subgroupOf D.M) := (B.S).isPGroup'.comap_subtype
  have hSmIdx : ¬ 2 ∣ ((B.S).subgroupOf D.M).index := by
    simpa [Subgroup.relIndex, Subgroup.inf_subgroupOf_right] using hplus.1
  have hJpM : IsPGroup 2 (J.subgroupOf D.M) := hJp.comap_subtype
  have hmax : J.subgroupOf D.M = (B.S).subgroupOf D.M := by
    refine (hSmP.toSylow hSmIdx).is_maximal' hJpM ?_
    intro x hx
    have hxg : (x : G) ∈ (B.S : Subgroup G) := Subgroup.mem_subgroupOf.mp hx
    have hxJ : (x : G) ∈ ((B.S : Subgroup G) ⊓ D.M) ⊔ Work.GW2.pCoreIn 2 X :=
      Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hxg, x.2⟩)
    rw [← hJ] at hxJ
    exact Subgroup.mem_subgroupOf.mpr hxJ
  have hPleS : Work.GW2.pCoreIn 2 X ≤ (B.S : Subgroup G) := by
    intro x hx
    have hxM : x ∈ D.M := hPleM hx
    have h1 : (⟨x, hxM⟩ : ↥D.M) ∈ J.subgroupOf D.M :=
      Subgroup.mem_subgroupOf.mpr (by rw [hJ]; exact Subgroup.mem_sup_right hx)
    rw [hmax] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  -- ## Step 3. `[P, U ⊓ M] = 1`, hence `P ≤ C_G(U ⊓ M)`
  have hUMleX : B.U ⊓ D.M ≤ X := by
    rw [hX]; exact le_inf (le_trans inf_le_left B.U_le_H) inf_le_right
  have hUn : ((B.U ⊓ D.M).subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hUMleX]
    intro a b ha hb
    obtain ⟨haU, haM⟩ := Subgroup.mem_inf.mp ha
    obtain ⟨hbH, hbM⟩ := Subgroup.mem_inf.mp (by rw [hX] at hb; exact hb)
    exact Subgroup.mem_inf.mpr
      ⟨(Subgroup.normal_subgroupOf_iff B.U_le_H).mp B.U_normal a b haU hbH,
        D.M.mul_mem (D.M.mul_mem hbM haM) (D.M.inv_mem hbM)⟩
  have hPinf : Work.GW2.pCoreIn 2 X ⊓ (B.U ⊓ D.M) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxP, hxUM⟩ := Subgroup.mem_inf.mp hx
    have h1 : x ∈ B.U ⊓ (B.S : Subgroup G) :=
      Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hxUM).1, hPleS hxP⟩
    rw [B.U_inf_S] at h1
    exact Subgroup.mem_bot.mp h1
  have hPleCUM : Work.GW2.pCoreIn 2 X ≤
      Subgroup.centralizer (((B.U ⊓ D.M) : Subgroup G) : Set G) :=
    Work.CORE4.A7V_le_centralizer_of_normal_inf_eq_bot hPleX hUMleX hPn hUn hPinf
  -- ## Step 4. Bender 1.1(iv) with `K = F(U)`, `K₁ = K₀ ⊔ F`: `P ≤ C_G(F(U))`
  have hSix : Work.GW2.fittingIn B.U ⊓ D.M = D.K0 ⊔ D.F :=
    Work.CORE4.SixThree I G hbc B D hpre
  have hK0Fle_FU : D.K0 ⊔ D.F ≤ Work.GW2.fittingIn B.U := by
    rw [← hSix]; exact inf_le_left
  have hK0Fle_UM : D.K0 ⊔ D.F ≤ B.U ⊓ D.M := by
    rw [← hSix]; exact le_inf (le_trans inf_le_left (Subgroup.map_subtype_le _)) inf_le_right
  have hFUodd : Odd (Nat.card ↥(Work.GW2.fittingIn B.U)) :=
    Odd.of_dvd_nat B.U_odd (Subgroup.card_dvd_of_le (Subgroup.map_subtype_le _))
  have hPN : Work.GW2.pCoreIn 2 X ≤ Subgroup.normalizer (Work.GW2.fittingIn B.U : Set G) :=
    hPleH.trans (o2hm_H_le_normalizer_fittingIn B)
  have hPC : Work.GW2.pCoreIn 2 X ≤
      Subgroup.centralizer ((D.K0 ⊔ D.F : Subgroup G) : Set G) :=
    hPleCUM.trans (Subgroup.centralizer_le hK0Fle_UM)
  have hsc : Work.GW2.fittingIn B.U ⊓
      Subgroup.centralizer ((D.K0 ⊔ D.F : Subgroup G) : Set G) ≤ D.K0 ⊔ D.F :=
    Work.CORE4.SevenX.sevenX_fittingIn_inf_centralizer_sup_le B D hpre hSix
  have hPleCFU : Work.GW2.pCoreIn 2 X ≤
      Subgroup.centralizer (Work.GW2.fittingIn B.U : Set G) :=
    Work.CORE4.SevenX.sevenX_le_centralizer_of_isNilpotent I.toolkit.c11iv
      (Work.GW2.fittingIn B.U) (D.K0 ⊔ D.F) (Work.GW2.pCoreIn 2 X)
      (Work.CORE4.SevenX.PiFU.isNilpotent_fittingIn B.U) hK0Fle_FU hsc
      Nat.prime_two hPp (Nat.coprime_two_left.mpr hFUodd) hPN hPC
  -- ## Step 5. Bender 1.1(iv) with `K = U`, `K₁ = F(U)`: `P ≤ C_G(U)`
  have hUsolv : Group.IsSolvable ↥B.U := I.toolkit.ft ↥B.U B.U_odd
  have hscU : B.U ⊓ Subgroup.centralizer (Work.GW2.fittingIn B.U : Set G) ≤
      Work.GW2.fittingIn B.U := by
    rw [inf_comm]
    exact Work.CORE4.sevenX_centralizer_fittingIn_inf_le_fittingIn B.U hUsolv
  have hPNU : Work.GW2.pCoreIn 2 X ≤ Subgroup.normalizer (B.U : Set G) :=
    hPleH.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer B.U_le_H).mp B.U_normal)
  have hPleCU : Work.GW2.pCoreIn 2 X ≤ Subgroup.centralizer (B.U : Set G) :=
    I.toolkit.c11iv G 2 (Work.GW2.pCoreIn 2 X) B.U (Work.GW2.fittingIn B.U) hPp
      (Nat.coprime_two_left.mpr B.U_odd) hPNU (Subgroup.map_subtype_le _)
      (Work.CORE4.fittingIn_subgroupOf_normal B.U) hPleCFU hscU
  -- ## Assembly
  have hPleO2 : Work.GW2.pCoreIn 2 X ≤ Work.GW2.pCoreIn 2 B.H := by
    rw [hO2]; exact le_inf hPleS hPleCU
  exact le_antisymm hPleO2 hO2leP

end Work.CORE4.SevenNine
