import Mathlib
import Submission.Work.CORE2B.HallPerPrime_case2
import Submission.Work.CORE2B.CentralizesNormalizer
import Submission.Work.CORE2B.Core18IsPGroupPCoreIn
import Submission.Work.CORE2B.Core18HPPNotLeH
import Submission.Work.CORE2B.Core18PairNormalizerLeNormalizerPX
import Submission.Work.CORE2B.Core18L27HypOfPairNormalizer
import Submission.Work.CORE2B.Core18PGroupLeFittingPiComplEqBot
import Submission.Work.CORE2B.Core18PrimeMemPrimesOf
import Submission.Work.CORE2B.Core18CommTMemPCoreTwoHhat

/-!
# GW design 18, item A′: the per-prime step of Theorem 2.10 (assembly, no `sorry` here)

Exactly the signature of `Work.CORE2B.HallPerPrimeCase2` (`CORE2B/HallPerPrimeCase2.lean`).
`HallPerPrime`'s odd case is NOT "underivable" (`HallPerPrime.lean` docstring): Lemma 2.7's
conclusion `[M,t] ≤ F_{π'}(M)` is exactly what Bender contradicts, with the nontrivial
`p`-element `[y,t]`, `y ∈ N_P(X)`, `p ∈ π`.  The only missing piece in the area was
Lemma 2.7's hypothesis list for `M ⊇ N_G(X)` *without* `S ≤ M`: Bender uses
`N_S(⟨t,s⟩) ≤ M` (leaves H2/H3).

Bender p. 222, in order:
1. `X = O_p(U) ∩ C(s) ≤ O(C(s))` (`HallPerPrime_Xodd`), `t`-invariant Sylow `P ⊇ X` of
   `O(C(s))` (`HallPerPrime_tSylow`, 1.1(ii));
2. `P ⊄ C(t)` (H1), so by 1.1(iv) (`CentralizesNormalizer`) some `y ∈ N_P(X)` has `[y,t] ≠ 1`;
3. `M` a coatom `⊇ N_G(X)`; `t ∉ E(M)` (¬Case 2); `Ĥ ⇝ M` via `X ≤ F(Ĥ)`; `M ⊄ Ĥ` (H6: else
   `[y,t] ∈ P ∩ O₂(Ĥ) = 1`); `N_S(⟨t,s⟩) ≤ N_G(X) ≤ M` (H2) gives `L27Hyp B M` (H3);
4. Lemma 2.7: `[y,t] ∈ [M,t] ≤ F_{π'}(M)`, a `p`-element with `p ∈ π` (H5) — trivial (H4).
-/

namespace Work.GW18

open Subgroup Work.CORE2B

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

theorem Core18HallPerPrimeCase2 (T : Work.GW2.LocalToolkit) (h26 : Work.GW2.Thm26Prop)
    (h27 : Work.GW2.Lemma27Prop) (h28 : Work.GW2.Lemma28Prop) (G : Type) [Group G] [Finite G]
    (hFT : Work.GW2.FeitThompsonProp) (hCtx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (hnot1 : ¬ Work.GW2.Case1 B) (hnot2 : ¬ Work.GW2.Case2 B)
    (s : G) (hs : s ∈ (B.S : Subgroup G)) (hs0 : s ∉ B.S0) (p : ℕ) (hp : Nat.Prime p)
    (hXne : Work.GW2.pCoreIn p B.U ⊓ Subgroup.centralizer ({s} : Set G) ≠ ⊥)
    (hXlt : ¬ Work.GW2.pCoreIn p B.U ≤ Subgroup.centralizer ({s} : Set G)) :
    Work.GW2.Case2 B := by
  classical
  exfalso
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsSimpleGroup G := hCtx.simple
  set X : Subgroup G := pX B s p with hXdef
  -- `p` is odd
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hXlt (by rw [pCoreIn_two_eq_bot B]; exact bot_le)
  -- step 1: the `t`-invariant Sylow `P`
  obtain ⟨P, hXP, hPK, hPp, hPsyl, hPt⟩ :=
    HallPerPrime_tSylow T G B s hs hs0 p hp (HallPerPrime_Xodd T G hCtx B s hs hs0 p hp)
  have hPnot : ¬ P ≤ Subgroup.centralizer ({B.t} : Set G) :=
    Core18HPPNotLeH T G hCtx B s hs hs0 p hp P hPK hPp hPsyl hXlt
  have htNP : B.t ∈ Subgroup.normalizer (P : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hPt
  have ht2 : IsPGroup 2 (Subgroup.zpowers B.t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, B.t_order]; norm_num)
  -- step 2: 1.1(iv) gives `y ∈ N_P(X)` not commuting with `t`
  have hnot : ¬ P ⊓ Subgroup.normalizer (X : Set G) ≤ Subgroup.centralizer ({B.t} : Set G) :=
    fun h => hPnot (CentralizesNormalizer p hp2 P X B.t hPp ht2 htNP hXP h)
  obtain ⟨y, hyPN, hyC⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  have hyP : y ∈ P := hyPN.1
  have hyN : y ∈ Subgroup.normalizer (X : Set G) := hyPN.2
  set c : G := y * B.t * y⁻¹ * B.t⁻¹ with hcdef
  have hc1 : c ≠ 1 := by
    intro h
    apply hyC
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have h' : y * B.t * y⁻¹ = B.t := by
      calc y * B.t * y⁻¹ = c * B.t := by rw [hcdef]; group
        _ = B.t := by rw [h, one_mul]
    calc B.t * y = (y * B.t * y⁻¹) * y := by rw [h']
      _ = y * B.t := by group
  have hcP : c ∈ P := by
    have h1 : B.t * y⁻¹ * B.t⁻¹ ∈ P := by
      have := (Subgroup.mem_normalizer_iff.mp htNP y⁻¹).mp (P.inv_mem hyP)
      exact this
    have : c = y * (B.t * y⁻¹ * B.t⁻¹) := by rw [hcdef]; group
    rw [this]
    exact P.mul_mem hyP h1
  -- step 3: the coatom `M ⊇ N_G(X)`
  have hXFU : X ≤ Work.GW2.fittingIn B.U := pX_le_fittingIn_U B s p
  have hXFH : X ≤ Work.GW2.fittingIn B.Hhat := pX_le_fittingIn_Hhat h26 G hFT hCtx B s p
  have hXHhat : X ≤ B.Hhat := hXFH.trans (in_le_self B.Hhat 2 B.pi).2.2.1
  have hNne : Subgroup.normalizer (X : Set G) ≠ ⊤ := by
    intro htopN
    haveI : X.Normal := Subgroup.normalizer_eq_top_iff.mp htopN
    rcases Subgroup.Normal.eq_bot_or_eq_top X with hbot | htopX
    · exact hXne hbot
    · exact B.Hhat_coatom.ne_top (top_le_iff.mp (htopX ▸ hXHhat))
  obtain ⟨M, hM, hNM⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.normalizer (X : Set G))).resolve_left hNne
  have hyM : y ∈ M := hNM hyN
  have htE : B.t ∉ Work.GW2.layerIn M := fun ht => hnot2 ⟨M, hM, ht, X, hXne, hXFU, hNM⟩
  have hrel : Work.GW2.BRel B.Hhat M := ⟨X, hXFH, le_trans inf_le_left hNM⟩
  have hnle : ¬ M ≤ B.Hhat := by
    intro hMH
    have hcO2 : c ∈ Work.GW2.pCoreIn 2 B.Hhat :=
      Core18CommTMemPCoreTwoHhat h26 G hFT hCtx B y (hMH hyM)
    have hdisj : Disjoint P (Work.GW2.pCoreIn 2 B.Hhat) :=
      IsPGroup.disjoint_of_ne p 2 hp2 P _ hPp (Core18IsPGroupPCoreIn 2 B.Hhat)
    exact hc1 (Subgroup.mem_bot.mp (hdisj.le_bot ⟨hcP, hcO2⟩))
  have hNpair : (B.S : Subgroup G) ⊓
      Subgroup.normalizer ((Subgroup.closure ({B.t, s} : Set G) : Subgroup G) : Set G) ≤ M :=
    (Core18PairNormalizerLeNormalizerPX hCtx B s hs hs0 p).trans hNM
  have hD : L27Hyp B M :=
    Core18L27HypOfPairNormalizer hCtx B s hs hs0 M hM.ne_top hrel hnle htE hNpair
  -- step 4: Lemma 2.7
  have h27c := (h27 G hFT hCtx B M hD.M_ne_top hD.rel hD.not_le hD.t_mem hD.t_not_layer
    hD.sylow_nc hD.size).1
  have hcMt : c ∈ ⁅M, Subgroup.zpowers B.t⁆ := by
    have := Subgroup.commutator_mem_commutator hyM (Subgroup.mem_zpowers B.t)
    simpa [commutatorElement_def, hcdef] using this
  have hcF : c ∈ Work.GW2.fittingPiIn B.piᶜ M := h27c hcMt
  have hXp : IsPGroup p X := (Core18IsPGroupPCoreIn p B.U).to_le inf_le_left
  have hpπ : p ∈ B.pi := Core18PrimeMemPrimesOf p X _ hXFH hXne hXp
  have hzp : IsPGroup p (Subgroup.zpowers c) :=
    hPp.to_le ((Subgroup.zpowers_le).mpr hcP)
  have hbot := Core18PGroupLeFittingPiComplEqBot M B.pi p hpπ (Subgroup.zpowers c) hzp
    ((Subgroup.zpowers_le).mpr hcF)
  exact hc1 (Subgroup.zpowers_eq_bot.mp hbot)

end Work.GW18
