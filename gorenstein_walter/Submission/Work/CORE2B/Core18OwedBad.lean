import Mathlib
import Submission.Work.CORE2B.Thm210_hall_and_normal
import Submission.Work.CORE2B.Core18SNormalizesOfScalar

/-!
# GW design pass 18, item A: `owed_bad` (the "bad configuration" of Theorem 2.10) is vacuous

Exactly the signature of `Work.CORE2B.owed_bad` (`CORE2B/Thm210_contra_proved.lean`).

Bender's printed proof (p. 222) — "By Lemma 2.8, `t ∈ E(M)` for `M ⊇ N_G(X)`" — needs `S ≤ M`,
and it has it: the first half of the proof shows that every `s ∈ S − S₀` centralizes or
inverts every `O_p(U)` (`HallPerPrime` + `centralizes_or_inverts_of_dichotomy`), hence every
element of `S` acts on `F(U) = ∏ O_p(U)` by a "scalar" on each Sylow, hence **every subgroup of
`F(U)` is `S`-invariant** (`Core18SNormalizesOfScalar`).  So `S ≤ N_G(X) ≤ M` for every coatom
`M ⊇ N_G(X)`, and `hbad` is contradictory.  (The `S`-closure route `⟨X^S⟩ ⊴ G` is false in
general — `F₃⁶ ⋊ A₅` — and is not needed.)
-/

namespace Work.GW18

open Subgroup Work.CORE2B

theorem Core18OwedBad (T : Work.GW2.LocalToolkit) (h26 : Work.GW2.Thm26Prop)
    (h27 : Work.GW2.Lemma27Prop) (h28 : Work.GW2.Lemma28Prop) (G : Type) [Group G] [Finite G]
    (hFT : Work.GW2.FeitThompsonProp) (hCtx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (hnot1 : ¬ Work.GW2.Case1 B) (hnot2 : ¬ Work.GW2.Case2 B)
    (X : Subgroup G) (hXne : X ≠ ⊥) (hXle : X ≤ Work.GW2.fittingIn B.U)
    (hXnorm : ¬ Subgroup.normalizer (X : Set G) ≤ B.Hhat)
    (hbad : ∀ M : Subgroup G, IsCoatom M → Subgroup.normalizer (X : Set G) ≤ M →
      ¬ (B.S : Subgroup G) ≤ M) : Work.GW2.Case2 B := by
  exfalso
  haveI : IsSimpleGroup G := hCtx.simple
  -- the per-prime dichotomy, in "centralizes or inverts" form, for every `s ∈ S − S₀`
  have hact : ∀ s ∈ (B.S : Subgroup G), s ∉ B.S0 → ∀ p : ℕ, p.Prime →
      (∀ z ∈ Work.GW2.pCoreIn p B.U, s * z * s⁻¹ = z) ∨
        (∀ z ∈ Work.GW2.pCoreIn p B.U, s * z * s⁻¹ = z⁻¹) := by
    intro s hs hs0 p hp
    haveI : Fact p.Prime := ⟨hp⟩
    have hs2 : orderOf s = 2 := orderOf_eq_two_of_mem_S_notMem_S0 hCtx B hs hs0
    have hss : s * s = 1 := by
      have h := pow_orderOf_eq_one s
      rw [hs2] at h
      simpa [pow_two] using h
    exact centralizes_or_inverts_of_dichotomy (Work.GW2.pCoreIn p B.U) s hss
      (Subgroup.mem_normalizer_iff_map_conj_eq.mpr
        (map_conj_pCoreIn (U := B.U) (p := p) (mem_normalizer_U_of_mem_S B hs)))
      (HallPerPrime T h26 h27 h28 G hFT hCtx B hnot1 hnot2 s hs hs0 p hp)
  have hSN : (B.S : Subgroup G) ≤ Subgroup.normalizer (X : Set G) :=
    Core18SNormalizesOfScalar B hact X hXle
  -- `N_G(X)` is proper: `X ≠ 1` lies in the proper subgroup `Ĥ` of the simple group `G`
  have hXHhat : X ≤ B.Hhat :=
    hXle.trans ((in_le_self B.U 2 B.pi).2.2.1.trans
      ((in_le_self B.H 2 B.pi).1.trans B.H_le_Hhat))
  have hNne : Subgroup.normalizer (X : Set G) ≠ ⊤ := by
    intro htopN
    haveI : X.Normal := Subgroup.normalizer_eq_top_iff.mp htopN
    rcases Subgroup.Normal.eq_bot_or_eq_top X with hbot | htopX
    · exact hXne hbot
    · exact B.Hhat_coatom.ne_top (top_le_iff.mp (htopX ▸ hXHhat))
  obtain ⟨M, hM, hle⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.normalizer (X : Set G))).resolve_left hNne
  exact hbad M hM hle (hSN.trans hle)

end Work.GW18
