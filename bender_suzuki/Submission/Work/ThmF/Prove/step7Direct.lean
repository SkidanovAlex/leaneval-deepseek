import Mathlib
import Submission.Work.ThmF.ChV3.NearField
import Submission.Work.ThmF.ChV3.Ctx
import Submission.Work.ThmF.Prove.step7

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.Prove.step7Direct` — Peterfalvi II, Ch. V §3 step (7) without the circular input (6)

The design's step (7) (`Work.ThmF.Prove.step7`) concludes `Ker H Q P t = P` from the outputs of
steps (1), (2), (4), (5) **and (6)**.  But `Prove/step6.lean` derives (6) *from* (7) (`h7 : Ker = P`
is one of its hypotheses), so the pair `step6`/`step7` is circular, and `ChV3/step6.lean` records
that (6) is not derivable from its own hypotheses.  This file removes the circularity.

The whole content is the single fact

`hSigKbot : Σ ⊓ C_G(C_Q(P)) = 1`, where `Σ = Sig H t P = C_W(P)`,

from which `Ker ≤ P` follows at once from hypothesis (1)
(`D ⊓ C_G(P) = Σ ⊔ P = Σ · P`, as `Σ ≤ C_G(P) ≤ N_G(P)`): if `x = y z ∈ Ker` with `y ∈ Σ`,
`z ∈ P`, then `y = x z⁻¹` centralises `C_Q(P)`, so `y ∈ Σ ⊓ C_G(C_Q(P)) = 1` and `x = z ∈ P`.
The reverse inclusion `P ≤ Ker` is immediate from `CtxF` (`P ≤ D` by `P ≤ V`, and `P` abelian
of prime order).  Together with `W ⊓ P = 1` (step (1)) this is the source's argument.

`hSigKbot` is proved in two cases:

* **`C_Q(P)` non-commutative** (`W_inf_eq_bot_of_noncomm`, the source's main line): (5) gives
  `|C_Q(P)| = 8`, (2) forces `f = o(st) = 3`, (4) makes `Q` a `2`-group, and if `1 ≠ x ∈ W`
  centralised `C_Q(P)` a prime-order power `x'` of `x` would have `Q₀ ≤ C_G(x')` (Ch. II §4
  Prop. 4), so the §2 Lemma 2 (c) trichotomy for `P' = ⟨x'⟩` (`Prove/trichotomySingle.lean`, its
  `PSU3Hyp` hypothesis (F1) being false at `P`) leaves only `|C_Q(x')| = |Q₀|³ = |Q|`, whence
  `x'` centralises the regular `Q` and fixes all of `Ω = G ⧸ H`, i.e. `x' ∈ H.normalCore = 1`
  (`G` is simple).  This is verbatim the crux of `Prove/step7.lean`, whose only remaining
  hypotheses are (1) and (6); here we keep its proof and drop the other inputs.
* **`C_Q(P)` commutative** (`Sig_inf_eq_bot_of_comm`): by App. XI Prop. 1 (2) b)
  (`NearFieldFieldProp`) the near-field `F` of (2) is a field with `|F| = f^m = |C_Q(P)| + 1`,
  `Σ` embeds in `Aut F` and `|C_F(w)| = |C_{C_Q(P)}(w)| + 1` for `w ≠ 1`; an element of `Σ`
  centralising `C_Q(P)` fixes all of `F^×`, hence all of `F`, hence lies in the kernel of the
  embedding.  This *replaces* the step (6) input `Σ = 1` of the commutative branch of `step7`,
  which is exactly the input that would have come from the circular `step6`.

`hFT`, `hTh`, `hNF`, `hnil` are kept because the caller threads them; the proof uses `hFT`
(through step (1)), `hC4` (Ch. II §4), `hnil` (Ch. V §1 Prop. 1 c) and the (2)/(4)/(5) hypotheses.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open Classical
open Submission.Blueprint
open scoped Pointwise

namespace Work.ThmF.Prove

/-- **Ch. V §3 step (7), non-commutative branch.**  If `C_Q(P)` is not commutative then
`W ⊓ C_G(C_Q(P)) = 1`.  (Hypotheses (2), (4), (5) of the design and the standing context; this is
the source's argument, cited from `Prove/step7.lean` where it is the `hKbot` crux.) -/
theorem W_inf_eq_bot_of_noncomm {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hnil : Group.IsNilpotent ↥Q)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P)
    (h2 : ∃ (m : ℕ) (R : Subgroup G), 1 ≤ m ∧ (orderOf (s * t)).Prime ∧
      Work.ThmF.ChV3.Ker H Q P t ≤ R ∧ R ≤ Subgroup.centralizer (P : Set G) ∧
      Subgroup.centralizer (P : Set G) ≤ Subgroup.normalizer (R : Set G) ∧
      Nat.card R = Nat.card ↥(Work.ThmF.ChV3.Ker H Q P t) * orderOf (s * t) ^ m ∧
      Nat.card ↥(Work.ThmF.ChV3.CQ Q P) + 1 = orderOf (s * t) ^ m ∧
      ∀ x ∈ R, x ∉ Work.ThmF.ChV3.Ker H Q P t → ∀ y ∈ Work.ThmF.ChV3.CQ Q P,
        y * x * y⁻¹ * x⁻¹ ∈ Work.ThmF.ChV3.Ker H Q P t → y = 1)
    (h4 : Nat.card Q = Nat.card ↥(Work.ThmF.ChV3.CQ Q P) ^ Nat.card P)
    (h5 : ¬ IsMulCommutative ↥(Work.ThmF.ChV3.CQ Q P) →
      Nat.card ↥(Work.ThmF.ChV3.CQ Q P) = 8 ∧ Work.ThmF.oddPart Q = ⊥)
    (hnc : ¬ IsMulCommutative ↥(Work.ThmF.ChV3.CQ Q P)) :
    Work.ThmF.W H t ⊓ Subgroup.centralizer ((Work.ThmF.ChV3.CQ Q P : Subgroup G) : Set G) = ⊥ := by
  classical
  haveI : IsSimpleGroup G := c.simple
  obtain ⟨_, _, hQ0card, _, _⟩ := Work.ThmF.Prove.step1 hFT hC4 c
  obtain ⟨hCQ8, _hoddQ⟩ := h5 hnc
  -- `f = orderOf (s * t) = 3` from `|C_Q(P)| + 1 = f^m = 9`
  obtain ⟨m, _R, hm1, hfprime, _hKR, _hRC, _hCRn, _hRcard, hCQcard, _hfpf⟩ := h2
  have hf3 : orderOf (s * t) = 3 := by
    have h9 : orderOf (s * t) ^ m = 9 := by rw [← hCQcard, hCQ8]
    have hm0 : m ≠ 0 := by omega
    have hdvd : orderOf (s * t) ∣ 3 ^ 2 := by
      have h := dvd_pow_self (orderOf (s * t)) hm0
      rw [h9] at h
      simpa using h
    have hdvd3 : orderOf (s * t) ∣ 3 := hfprime.dvd_of_dvd_pow hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h | h
    · exact absurd h hfprime.ne_one
    · exact h
  -- `Q` is a `2`-group: `|Q| = |C_Q(P)|^{|P|} = 8^{|P|} = 2^{3|P|}`
  have hQ2 : IsPGroup 2 Q := by
    refine IsPGroup.of_card (n := 3 * Nat.card P) ?_
    have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
    rw [h4, hCQ8, h8, pow_mul]
  -- ## the crux: `W ⊓ C_G(C_Q(P)) = 1`
  set K : Subgroup G := Work.ThmF.W H t ⊓
    Subgroup.centralizer ((Work.ThmF.ChV3.CQ Q P : Subgroup G) : Set G) with hKdef
  refine le_antisymm ?_ bot_le
  intro x hxK
  rw [Subgroup.mem_bot]
  by_contra hxne
  -- a prime-order element `x'` of `K` (Cauchy)
  have hKne : K ≠ ⊥ := by
    intro hbot
    rw [hbot] at hxK
    exact hxne (Subgroup.mem_bot.mp hxK)
  have hcardK : Nat.card ↥K ≠ 1 := fun h1 => hKne (Subgroup.card_eq_one.mp h1)
  obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd hcardK
  haveI : Fact p.Prime := ⟨hpprime⟩
  haveI : Fintype ↥K := Fintype.ofFinite _
  have hpdvd' : p ∣ Fintype.card ↥K := by rwa [← Nat.card_eq_fintype_card]
  obtain ⟨zg, hzgorder⟩ := exists_prime_orderOf_dvd_card p hpdvd'
  set x' : G := (zg : G) with hx'def
  have hx'K : x' ∈ K := zg.2
  have hx'order : orderOf x' = p := by
    rw [hx'def]
    exact (Subgroup.orderOf_coe zg).trans hzgorder
  have hx'W : x' ∈ Work.ThmF.W H t := (Subgroup.mem_inf.mp hx'K).1
  have hx'CQ : x' ∈ Subgroup.centralizer ((Work.ThmF.ChV3.CQ Q P : Subgroup G) : Set G) :=
    (Subgroup.mem_inf.mp hx'K).2
  have hx'ne : x' ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx'order
    exact hpprime.ne_one hx'order.symm
  have hx'V : x' ∈ Submission.Blueprint.centD H t := Work.ThmF.W_le_centD H t hx'W
  have hx'H : x' ∈ H := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx'V).1).1
  have hx't : x' * t = t * x' :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx'V).2
  -- the centraliser of `⟨x'⟩` is the centraliser of `x'`
  have hcent_eq : Subgroup.centralizer ((Subgroup.zpowers x' : Subgroup G) : Set G) =
      Subgroup.centralizer ({x'} : Set G) := by
    refine le_antisymm ?_ ?_
    · intro y hy
      rw [Subgroup.mem_centralizer_iff] at hy ⊢
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hy x' (Subgroup.mem_zpowers x')
    · intro y hy
      rw [Subgroup.mem_centralizer_iff] at hy ⊢
      intro z hz
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact Commute.zpow_left ((Subgroup.mem_centralizer_iff.mp hy) x'
        (Set.mem_singleton_iff.mpr rfl)) n
  -- `Q₀ = Q0sub H ≤ C_G(x')`: `W = C_D(Inv H)` (Ch. II §4 Prop. 4)
  have hQ0le : Work.ThmF.Q0sub H ≤
      Subgroup.centralizer ((Subgroup.zpowers x' : Subgroup G) : Set G) := by
    rw [hcent_eq]
    refine (Subgroup.closure_le _).mpr ?_
    intro u hu
    rw [Work.ThmF.mem_Q0_iff] at hu
    rcases hu with ⟨huH, hu2⟩ | rfl
    · have hWeq := Work.ThmF.ChV3.W_eq_inf_centralizer_involutions c.sit hC4 c.split
      have hx'Cinv : x' ∈ Subgroup.centralizer
          ((involutions (H : Set G))) := by
        have h := hx'W
        rw [hWeq] at h
        exact (Subgroup.mem_inf.mp h).2
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp hx'Cinv) u ⟨huH, hu2⟩)
    · exact Subgroup.one_mem _
  -- involutions of `H` commute, so `Q₀` is elementary abelian
  have ht2 : orderOf t = 2 := c.split.invol
  have htH : t ∉ H := c.split.not_mem
  have hDtr := Work.ThmF.Bender.DTransitiveInv c.split.stronglyEmbedded ht2 htH
  have hcentQ := Work.ThmF.ChV12.prop1c c.sit H Q t c.split hDtr hnil
  have hcommH : ∀ u ∈ Submission.Blueprint.involutions (H : Set G),
      ∀ v ∈ Submission.Blueprint.involutions (H : Set G), u * v = v * u := by
    intro u hu v hv
    have h1 := (Work.ThmF.mem_centerOf (Q := Q)).mp (hcentQ u hu)
    have h2 := (Work.ThmF.mem_centerOf (Q := Q)).mp (hcentQ v hv)
    exact h1.2 v h2.1
  have hQ0el := Work.ThmF.ChV12.Q0sub_elementary H hcommH
  -- two distinct commuting involutions in `C_G(x')`
  have hcard4 : 4 ≤ Nat.card ↥(Work.ThmF.Q0sub H) := by
    rw [hQ0card]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ Nat.card P := Nat.pow_le_pow_right (by norm_num) c.P_prime.two_le
  have hexa : ∃ a ∈ Work.ThmF.Q0sub H, a ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hbot : Work.ThmF.Q0sub H = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    rw [hbot] at hcard4
    simp at hcard4
  obtain ⟨a, haQ0, ha1⟩ := hexa
  have ha2 : a * a = 1 := hQ0el.1 a haQ0
  have haorder : orderOf a = 2 := by
    have hdvd : orderOf a ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact ha2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ha1
    · exact h
  have hexb : ∃ b ∈ Work.ThmF.Q0sub H, b ∉ Subgroup.zpowers a := by
    by_contra hcon
    push_neg at hcon
    have hdvd := Subgroup.card_dvd_of_le (hcon : Work.ThmF.Q0sub H ≤ Subgroup.zpowers a)
    rw [Nat.card_zpowers, haorder] at hdvd
    have hle2 : Nat.card ↥(Work.ThmF.Q0sub H) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  obtain ⟨b, hbQ0, hbz⟩ := hexb
  have hb1 : b ≠ 1 := fun h => hbz (by rw [h]; exact Subgroup.one_mem _)
  have hba : b ≠ a := fun h => hbz (by rw [h]; exact Subgroup.mem_zpowers a)
  have hb2 : b * b = 1 := hQ0el.1 b hbQ0
  have hborder : orderOf b = 2 := by
    have hdvd : orderOf b ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hb2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hb1
    · exact h
  have hab : a * b = b * a := hQ0el.2.1 a haQ0 b hbQ0
  have hB3 : HasFourGroup ↥(Subgroup.centralizer
      ((Subgroup.zpowers x' : Subgroup G) : Set G)) := by
    refine ⟨⟨a, hQ0le haQ0⟩, ⟨b, hQ0le hbQ0⟩, ?_, ?_, ?_, ?_⟩
    · rw [← Subgroup.orderOf_coe]; exact haorder
    · rw [← Subgroup.orderOf_coe]; exact hborder
    · intro h
      exact hba (Subtype.ext_iff.mp h).symm
    · refine Subtype.ext ?_
      push_cast
      exact hab
  -- §2 Lemma 2 (c) for the prime-order subgroup `⟨x'⟩ ≤ V`
  have hPleV : Subgroup.zpowers x' ≤ Submission.Blueprint.centD H t :=
    Subgroup.zpowers_le.mpr hx'V
  have hPprime' : (Nat.card ↥(Subgroup.zpowers x')).Prime := by
    rw [Nat.card_zpowers, hx'order]
    exact hpprime
  have htri := trichotomy_of_prime (P := Subgroup.zpowers x') c.sit c.simple c.split hC4
    hQ2 hB3 c.s_mem c.s_inv c.r_mem c.sid hPleV hPprime'
  dsimp only at htri
  have hℓ : Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer
      ((Subgroup.zpowers x' : Subgroup G) : Set G)) = 2 ^ Nat.card P := by
    rw [inf_eq_left.mpr hQ0le, hQ0card]
  -- `C_Q(P) ≤ C_Q(x')`
  have hCQleC : Work.ThmF.ChV3.CQ Q P ≤
      Q ⊓ Subgroup.centralizer ((Subgroup.zpowers x' : Subgroup G) : Set G) := by
    intro y hy
    refine ⟨(Subgroup.mem_inf.mp hy).1, ?_⟩
    show y ∈ Subgroup.centralizer ((Subgroup.zpowers x' : Subgroup G) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [Subgroup.mem_centralizer_iff] at hx'CQ
    exact ((Commute.zpow_right (hx'CQ y hy) n)).symm
  rcases htri with ⟨hord, habC, hcardC⟩ | ⟨hord5, _hnab, _hcard5, _hsq⟩ |
    ⟨hord3, hcard3, _hxcl⟩
  · -- branch `f = 3`, `C_Q(x')` abelian: impossible, `C_Q(P)` is not abelian
    exact hnc (by
      rw [isMulCommutative_iff]
      intro u v
      refine Subtype.ext ?_
      have h := habC (u : G) (hCQleC u.2) (v : G) (hCQleC v.2)
      simpa using h)
  · -- branch `f = 5`: contradicts `f = 3`
    exact absurd hord5 (by rw [hf3]; norm_num)
  · -- branch `|C_Q(x')| = ℓ^3 = |Q|`: `x'` centralises `Q`
    have hCeq : Q ⊓ Subgroup.centralizer ((Subgroup.zpowers x' : Subgroup G) : Set G) = Q := by
      refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
      rw [hcard3, hℓ, h4, hCQ8]
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_mul,
        Nat.mul_comm (Nat.card P) 3]
    have hQleC : Q ≤ Subgroup.centralizer ((Subgroup.zpowers x' : Subgroup G) : Set G) := by
      intro y hy
      have h : y ∈ Q ⊓ Subgroup.centralizer
          ((Subgroup.zpowers x' : Subgroup G) : Set G) := by
        rw [hCeq]
        exact hy
      exact h.2
    have hx'Q : ∀ q ∈ Q, q * x' = x' * q := by
      intro q hq
      exact ((Subgroup.mem_centralizer_iff.mp (hQleC hq)) x'
        (Subgroup.mem_zpowers x')).symm
    -- `x'` fixes every point of `Ω = G ⧸ H`
    have hfixpt : x' • Work.DoubleTransitivity.pt H = Work.DoubleTransitivity.pt H := by
      rw [Work.DoubleTransitivity.smul_pt, Work.DoubleTransitivity.mk_one_eq_iff]
      exact hx'H
    have hfixall : ∀ ω : Work.DoubleTransitivity.Omega H, x' • ω = ω := by
      intro ω
      by_cases hω : ω = Work.DoubleTransitivity.pt H
      · rw [hω]; exact hfixpt
      · obtain ⟨q, hqQ, hqω⟩ := Work.RankOneUniqueness.qPt_surjective c.split hω
        rw [← hqω, Work.RankOneUniqueness.qPt_eq_smul]
        calc x' • (q • (t • Work.DoubleTransitivity.pt H))
            = (x' * q) • (t • Work.DoubleTransitivity.pt H) := by rw [mul_smul]
          _ = (q * x') • (t • Work.DoubleTransitivity.pt H) := by rw [← hx'Q q hqQ]
          _ = q • (x' • (t • Work.DoubleTransitivity.pt H)) := by rw [mul_smul]
          _ = q • ((x' * t) • Work.DoubleTransitivity.pt H) := by rw [mul_smul]
          _ = q • (t • (x' • Work.DoubleTransitivity.pt H)) := by
                rw [hx't, mul_smul]
          _ = q • (t • Work.DoubleTransitivity.pt H) := by rw [hfixpt]
    -- hence `x'` lies in the core `H.normalCore = 1`
    have hmem_nc : x' ∈ H.normalCore := by
      rw [Subgroup.normalCore_eq_iInf_map_conj]
      rw [Subgroup.mem_iInf]
      intro g
      show x' ∈ Submission.Blueprint.conj g H
      rw [Work.DoubleTransitivity.mem_conj]
      have hfix := hfixall (g • Work.DoubleTransitivity.pt H)
      have h2 : ((g⁻¹ * x' * g : G) : G ⧸ H) = Work.DoubleTransitivity.pt H := by
        rw [← Work.DoubleTransitivity.smul_pt (g⁻¹ * x' * g) H]
        rw [show g⁻¹ * x' * g = g⁻¹ * (x' * g) from by group, mul_smul, mul_smul, hfix,
          ← mul_smul, inv_mul_cancel, one_smul]
      exact Work.DoubleTransitivity.mk_one_eq_iff.mp h2
    have hbot : H.normalCore = ⊥ := by
      rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ _ H.normalCore
        (Subgroup.normalCore_normal H) with h | h
      · exact h
      · exfalso
        have htop : H = ⊤ := by
          rw [eq_top_iff]
          rw [← h]
          exact Subgroup.normalCore_le H
        exact c.split.stronglyEmbedded.1 htop
    rw [hbot] at hmem_nc
    exact hx'ne (Subgroup.mem_bot.mp hmem_nc)

/-- **Ch. V §3 step (7), commutative branch.**  If `C_Q(P)` is commutative, App. XI Prop. 1 (2) b)
(recorded as the external input `NearFieldFieldProp`) supplies a finite field `F` with
`|F| = f^m = |C_Q(P)| + 1` together with an *injective* action `act : ↥Σ →* (F ≃+* F)` such that
`|C_F(w)| = |C_{C_Q(P)}(w)| + 1` for every `w ≠ 1`.  An element `x ∈ Σ` centralising `C_Q(P)`
therefore satisfies `C_Q(P) ⊓ C_G({x}) = C_Q(P)`, whence `act x` fixes `|C_Q(P)| + 1 = |F|` points
of `F`, i.e. all of them; so `act x = 1 = act 1`, and injectivity gives `x = 1`. -/
theorem Sig_inf_eq_bot_of_comm {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    {P : Subgroup G} {m : ℕ}
    (c : Work.ThmF.ChV3.CtxF H Q t s r P)
    (hm : 1 ≤ m)
    (hcq : Nat.card ↥(Work.ThmF.ChV3.CQ Q P) + 1 = orderOf (s * t) ^ m)
    (hNFF : Work.ThmF.ChV3.NearFieldFieldProp)
    (hcomm : IsMulCommutative ↥(Work.ThmF.ChV3.CQ Q P)) :
    Work.ThmF.ChV3.Sig H t P ⊓
        Subgroup.centralizer ((Work.ThmF.ChV3.CQ Q P : Subgroup G) : Set G) = ⊥ := by
  obtain ⟨F, hFfield, hFfintype, _hFchar, _hFfact, act, hFcard, hinj, hfix⟩ :=
    hNFF c hm hcq hcomm
  -- `hFfield : Field F` and `hFfintype : Fintype F` are registered as local instances by `obtain`.
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hxne
  have hxne' : (⟨x, hx.1⟩ : ↥(Work.ThmF.ChV3.Sig H t P)) ≠ 1 := by
    intro h
    exact hxne (by simpa using congrArg Subtype.val h)
  have hCQle : Work.ThmF.ChV3.CQ Q P ≤ Subgroup.centralizer ({x} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hx.2 y hy
  have hinf : Work.ThmF.ChV3.CQ Q P ⊓ Subgroup.centralizer ({x} : Set G) =
      Work.ThmF.ChV3.CQ Q P := inf_eq_left.mpr hCQle
  have hfx := hfix ⟨x, hx.1⟩ hxne'
  rw [hinf] at hfx
  have hcard : Nat.card (Function.fixedPoints (act ⟨x, hx.1⟩)) = Nat.card F := by
    rw [hfx, hFcard]
    exact hcq
  have huniv : Function.fixedPoints (act ⟨x, hx.1⟩) = Set.univ :=
    (Set.eq_univ_iff_ncard _).mpr hcard
  have hact1 : act ⟨x, hx.1⟩ = 1 := by
    refine RingEquiv.ext (fun z => ?_)
    have hz : z ∈ Function.fixedPoints (act ⟨x, hx.1⟩) := by
      rw [huniv]; exact Set.mem_univ z
    simpa [Function.mem_fixedPoints, Function.IsFixedPt] using hz
  exact hxne' (hinj (by rw [hact1, map_one]))

/-- **Peterfalvi II, Ch. V §3, step (7).**  In the standing context `CtxF H Q t s r P`, with the
outputs (1) (`h1`), (2) (`h2`), (4) (`h4`) and (5) (`h5`) of the design and the field half of
App. XI Prop. 1 (`hNFF`) in place, the kernel `N = D ⊓ C_G(C_Q(P)) ⊓ C_G(P)` of step (2) is exactly
`P`. -/
theorem step7Direct {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G} {m : ℕ}
    (hFT : Submission.Blueprint.FeitThompsonProp)
    (hTh : Submission.Blueprint.ThompsonFrobeniusProp)
    (hNF : Work.ThmF.ChV3.NearFieldAppXIProp)
    (hNFF : Work.ThmF.ChV3.NearFieldFieldProp)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hnil : Group.IsNilpotent ↥Q)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P)
    (h1 : Submission.Blueprint.twoPoint H t ⊓ Subgroup.centralizer (P : Set G) =
      Work.ThmF.ChV3.Sig H t P ⊔ P)
    (h2 : ∃ (m : ℕ) (R : Subgroup G), 1 ≤ m ∧ (orderOf (s * t)).Prime ∧
      Work.ThmF.ChV3.Ker H Q P t ≤ R ∧ R ≤ Subgroup.centralizer (P : Set G) ∧
      Subgroup.centralizer (P : Set G) ≤ Subgroup.normalizer (R : Set G) ∧
      Nat.card R = Nat.card ↥(Work.ThmF.ChV3.Ker H Q P t) * orderOf (s * t) ^ m ∧
      Nat.card ↥(Work.ThmF.ChV3.CQ Q P) + 1 = orderOf (s * t) ^ m ∧
      ∀ x ∈ R, x ∉ Work.ThmF.ChV3.Ker H Q P t → ∀ y ∈ Work.ThmF.ChV3.CQ Q P,
        y * x * y⁻¹ * x⁻¹ ∈ Work.ThmF.ChV3.Ker H Q P t → y = 1)
    (h4 : Nat.card Q = Nat.card ↥(Work.ThmF.ChV3.CQ Q P) ^ Nat.card P)
    (h5 : ¬ IsMulCommutative ↥(Work.ThmF.ChV3.CQ Q P) →
      Nat.card ↥(Work.ThmF.ChV3.CQ Q P) = 8 ∧ Work.ThmF.oddPart Q = ⊥)
    (hm : 1 ≤ m)
    (hcq : Nat.card ↥(Work.ThmF.ChV3.CQ Q P) + 1 = orderOf (s * t) ^ m) :
    Work.ThmF.ChV3.Ker H Q P t = P := by
  classical
  haveI : IsSimpleGroup G := c.simple
  -- ## the crux `Σ ⊓ C_G(C_Q(P)) = 1`, in the two branches
  have hNoncomm := W_inf_eq_bot_of_noncomm hFT hC4 hnil c h2 h4 h5
  have hComm := Sig_inf_eq_bot_of_comm c hm hcq hNFF
  -- ## standing facts
  have hPleD : P ≤ Submission.Blueprint.twoPoint H t :=
    fun p hp => Work.ThmF.centD_le_twoPoint t (c.P_le hp)
  have hPleCP : P ≤ Subgroup.centralizer (P : Set G) := by
    haveI : Fact (Nat.card P).Prime := ⟨c.P_prime⟩
    haveI : IsCyclic ↥P := isCyclic_of_prime_card rfl
    haveI : IsMulCommutative ↥P := IsCyclic.isMulCommutative
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact congrArg Subtype.val (isMulCommutative_iff.mp inferInstance ⟨q, hq⟩ ⟨p, hp⟩)
  have hPleCQ : P ≤ Subgroup.centralizer ((Work.ThmF.ChV3.CQ Q P : Subgroup G) : Set G) := by
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).2) p hp).symm
  have hPKer : P ≤ Work.ThmF.ChV3.Ker H Q P t :=
    fun p hp => ⟨⟨hPleD hp, hPleCQ hp⟩, hPleCP hp⟩
  have hSigW : Work.ThmF.ChV3.Sig H t P ≤ Work.ThmF.W H t := inf_le_left
  have hSigN : Work.ThmF.ChV3.Sig H t P ≤ Subgroup.normalizer (P : Set G) :=
    le_trans inf_le_right (Subgroup.centralizer_le_normalizer (P : Set G))
  -- ## the crux
  have hSigKbot : Work.ThmF.ChV3.Sig H t P ⊓
      Subgroup.centralizer ((Work.ThmF.ChV3.CQ Q P : Subgroup G) : Set G) = ⊥ := by
    by_cases hcomm : IsMulCommutative ↥(Work.ThmF.ChV3.CQ Q P)
    · exact hComm hcomm
    · have hW := hNoncomm hcomm
      have hle : Work.ThmF.ChV3.Sig H t P ⊓
          Subgroup.centralizer ((Work.ThmF.ChV3.CQ Q P : Subgroup G) : Set G) ≤
          Work.ThmF.W H t ⊓
          Subgroup.centralizer ((Work.ThmF.ChV3.CQ Q P : Subgroup G) : Set G) :=
        le_inf (inf_le_left.trans hSigW) inf_le_right
      exact le_antisymm (hle.trans hW.le) bot_le
  -- ## `Ker ≤ P`
  have hKerP : Work.ThmF.ChV3.Ker H Q P t ≤ P := by
    intro x hx
    obtain ⟨⟨hxD, hxCQ⟩, hxCP⟩ := hx
    have hx1 : x ∈ Submission.Blueprint.twoPoint H t ⊓ Subgroup.centralizer (P : Set G) :=
      ⟨hxD, hxCP⟩
    rw [h1] at hx1
    have hprod : ((Work.ThmF.ChV3.Sig H t P ⊔ P : Subgroup G) : Set G)
        = (Work.ThmF.ChV3.Sig H t P : Set G) * (P : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right _ _ hSigN
    have hx2 : x ∈ (Work.ThmF.ChV3.Sig H t P : Set G) * (P : Set G) := by
      rw [← hprod]
      exact hx1
    rw [Set.mem_mul] at hx2
    obtain ⟨y, hySig, z, hzP, hyz⟩ := hx2
    have hyK : y ∈ Work.ThmF.ChV3.Sig H t P ⊓
        Subgroup.centralizer ((Work.ThmF.ChV3.CQ Q P : Subgroup G) : Set G) := by
      refine ⟨hySig, ?_⟩
      have hyC : y = x * z⁻¹ := by rw [← hyz]; group
      rw [hyC]
      exact Subgroup.mul_mem _ hxCQ (Subgroup.inv_mem _ (hPleCQ hzP))
    rw [hSigKbot] at hyK
    have hy1 : y = 1 := Subgroup.mem_bot.mp hyK
    have hxz : x = z := by rw [← hyz, hy1, one_mul]
    rw [hxz]
    exact hzP
  show Work.ThmF.ChV3.Ker H Q P t = P
  exact le_antisymm hKerP hPKer

end Work.ThmF.Prove
