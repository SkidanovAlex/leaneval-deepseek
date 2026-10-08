import Mathlib
import Submission.Work.ThmF.ChV3.Ctx
import Submission.Work.ThmF.Prove.cQNormalizerIsPGroupTwo
import Submission.Work.ThmF.Prove.trichotomyOfPrimeNil
import Submission.Work.ThmF.ChV3.l2cCentralizerOddPart

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.Prove.sigLemma2c` — Peterfalvi II, Ch. V §2 Lemma 2 (c) at `w ∈ Σ#`

For `w ∈ Σ = C_W(P)` non-trivial in the standing context of §3 (`CtxF H Q t s r P`) with
`|Q₀| = 2^{|P|}` and `Q` nilpotent, the centraliser `C_Q(w)` is a `2`-group and the trichotomy
value `o(st)` is `3` or `5`:

  `IsPGroup 2 (Q ⊓ C_G(w)) ∧ (o(st) = 3 ∨ o(st) = 5)`.

The proof uses the "Lemma 2 (c) recursion" of `NOTES_LEAD_bs_pass12.md` §1: a suitable
prime-order power `w'` of `w` spans `X = ⟨w'⟩ ≤ W = C_D(Inv H)`, so `Q₀ ≤ C_G(X)` and
`C_G(X)` has 2-rank `≥ 2` (the `hB3` block of `Prove/step7Direct.lean`).  Ch. II §4 Prop. 3 then
supplies `N_K(X) ≠ 1` (`exists_k_normalizing`), and

* `Prove/cQNormalizerIsPGroupTwo` makes `Q ⊓ N_G(X)` a `2`-group, whence `Q ⊓ C_G(w)` is one
  (`C_G(w) ≤ N_G(⟨w'⟩)` because `w'` is a power of `w`);
* `Prove/trichotomyOfPrimeNil` at `P := ⟨w'⟩` gives the trichotomy, whose three branches all
  contain `o(st) = 3` or `o(st) = 5`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open Submission.Blueprint

namespace Work.ThmF.Prove

/-- `C_G(w) ≤ N_G(⟨w'⟩)` whenever `w'` is a power of `w`. -/
private lemma centralizer_le_normalizer_zpowers {G : Type} [Group G] {w w' : G}
    (hw' : w' ∈ Subgroup.zpowers w) :
    Subgroup.centralizer ({w} : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers w' : Subgroup G) : Set G) := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hw'
  intro y hy
  have hyw : Commute y w := Subgroup.mem_centralizer_singleton_iff.mp hy
  have hyw' : Commute y w' := by rw [← hn]; exact hyw.zpow_right n
  have hy_cent_zp : y ∈ Subgroup.centralizer ((Subgroup.zpowers w' : Subgroup G) : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro z hz
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (hyw'.zpow_right m).eq.symm
  exact Subgroup.centralizer_le_normalizer _ hy_cent_zp

theorem sigLemma2c {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    {P : Subgroup G} (hC4 : Submission.Blueprint.ChIIFourProp) (hnil : Group.IsNilpotent ↥Q)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P)
    (hQ0 : Nat.card ↥(Work.ThmF.Q0sub H) = 2 ^ Nat.card P)
    {w : G} (hw : w ∈ Work.ThmF.ChV3.Sig H t P) (hw1 : w ≠ 1) :
    IsPGroup 2 ↥(Q ⊓ Subgroup.centralizer ({w} : Set G)) ∧
      (orderOf (s * t) = 3 ∨ orderOf (s * t) = 5) := by
  classical
  -- ## 0. the standing context
  have hSit : Submission.Blueprint.Situation G := c.sit
  have hsplit : Submission.Blueprint.IsSplitRankOne H Q t := c.split
  have hH := hsplit.stronglyEmbedded
  have ht2 : orderOf t = 2 := hsplit.invol
  have htH : t ∉ H := hsplit.not_mem
  have hDodd : Odd (Nat.card ↥(Submission.Blueprint.twoPoint H t)) :=
    hsplit.stronglyEmbedded.2.2 t htH
  -- ## 1. `w ∈ Σ = W ⊓ C_G(P)`; `o(w)` is odd and `≠ 1`
  have hwW : w ∈ Work.ThmF.W H t := (Subgroup.mem_inf.mp hw).1
  have hwD : w ∈ Submission.Blueprint.twoPoint H t :=
    (Subgroup.mem_inf.mp (Work.ThmF.W_le_centD H t hwW)).1
  have hworddvd : orderOf w ∣ Nat.card ↥(Submission.Blueprint.twoPoint H t) :=
    Subgroup.orderOf_dvd_natCard _ hwD
  have hwordd : Odd (orderOf w) := hDodd.of_dvd_nat hworddvd
  have hwordne : orderOf w ≠ 1 := fun h => hw1 (orderOf_eq_one_iff.mp h)
  -- ## 2. a prime-order power `w'` of `w`, and `X = ⟨w'⟩`
  obtain ⟨ℓ, hℓprime, hℓdvd⟩ := Nat.exists_prime_and_dvd hwordne
  haveI : Fact ℓ.Prime := ⟨hℓprime⟩
  have hℓdvd' : ℓ ∣ Nat.card ↥(Subgroup.zpowers w) := by
    rw [Nat.card_zpowers]; exact hℓdvd
  obtain ⟨w'₀, hw'₀ord⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.zpowers w)) ℓ hℓdvd'
  set w' : G := (w'₀ : G) with hw'def
  have hw'w : w' ∈ Subgroup.zpowers w := w'₀.2
  have hw'ord : orderOf w' = ℓ := (Subgroup.orderOf_coe w'₀).trans hw'₀ord
  have hw'1 : w' ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hw'ord
    exact hℓprime.ne_one hw'ord.symm
  have hXprime : Nat.Prime (Nat.card ↥(Subgroup.zpowers w')) := by
    rw [Nat.card_zpowers, hw'ord]; exact hℓprime
  have hw'W : w' ∈ Work.ThmF.W H t := Subgroup.zpowers_le.mpr hwW hw'w
  have hw'V : w' ∈ Submission.Blueprint.centD H t := Work.ThmF.W_le_centD H t hw'W
  have hXV : (Subgroup.zpowers w' : Subgroup G) ≤ Submission.Blueprint.centD H t :=
    Subgroup.zpowers_le.mpr hw'V
  have hXne : (Subgroup.zpowers w' : Subgroup G) ≠ ⊥ :=
    fun h => hw'1 (Subgroup.zpowers_eq_bot.mp h)
  -- ## 3. `Q₀ ≤ C_G(X)`: `w' ∈ W = D ⊓ C_G(Inv H)` (Ch. II §4 Prop. 4)
  have hWeq : Work.ThmF.W H t = Submission.Blueprint.twoPoint H t ⊓
      Subgroup.centralizer (Submission.Blueprint.involutions (H : Set G)) := by
    have hP4 := (hC4 G hSit H hH t ht2 htH).2.2.2.2.1
    simpa only [Work.ThmF.W, Work.ThmF.Kset] using hP4
  have hw'Cinv : w' ∈ Subgroup.centralizer
      (Submission.Blueprint.involutions (H : Set G)) := by
    rw [hWeq] at hw'W
    exact (Subgroup.mem_inf.mp hw'W).2
  have hQ0le : Work.ThmF.Q0sub H ≤
      Subgroup.centralizer ((Subgroup.zpowers w' : Subgroup G) : Set G) := by
    rw [Work.ThmF.Q0sub]
    refine (Subgroup.closure_le _).mpr ?_
    intro u hu
    rw [Work.ThmF.mem_Q0_iff] at hu
    rcases hu with ⟨huH, hu2⟩ | h1
    · refine Subgroup.mem_centralizer_iff.mpr ?_
      intro z hz
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have huc : Commute u w' := (Subgroup.mem_centralizer_iff.mp hw'Cinv) u ⟨huH, hu2⟩
      exact (huc.zpow_right m).eq.symm
    · subst h1
      exact Subgroup.one_mem _
  -- ## 4. `HasFourGroup (C_G(X))`, the `hB3` block of `Prove/step7Direct.lean`
  have hDtr := Work.ThmF.Bender.DTransitiveInv hH ht2 htH
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcentQ : ∀ u ∈ Submission.Blueprint.involutions (H : Set G), u ∈ Work.ThmF.centerOf Q :=
    Work.ThmF.ChV12.prop1c hSit H Q t hsplit hDtr hnil
  have hcommH : ∀ u ∈ Submission.Blueprint.involutions (H : Set G),
      ∀ v ∈ Submission.Blueprint.involutions (H : Set G), u * v = v * u := by
    intro u hu v hv
    have h1 := (Work.ThmF.mem_centerOf (Q := Q)).mp (hcentQ u hu)
    have h2 := (Work.ThmF.mem_centerOf (Q := Q)).mp (hcentQ v hv)
    exact h1.2 v h2.1
  have hQ0el := Work.ThmF.ChV12.Q0sub_elementary H hcommH
  have hcard4 : 4 ≤ Nat.card ↥(Work.ThmF.Q0sub H) := by
    rw [hQ0]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ Nat.card P := Nat.pow_le_pow_right (by norm_num) c.P_prime.two_le
  have hfour : Submission.Blueprint.HasFourGroup
      ↥(Subgroup.centralizer ((Subgroup.zpowers w' : Subgroup G) : Set G)) := by
    have hexa : ∃ a ∈ Work.ThmF.Q0sub H, a ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      have hbot : Work.ThmF.Q0sub H = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
      rw [hbot] at hcard4
      simp at hcard4
    obtain ⟨a, haQ0, ha1⟩ := hexa
    have haorder : orderOf a = 2 := (hQ0el.2.2.2 a haQ0 ha1).2
    have hexb : ∃ b ∈ Work.ThmF.Q0sub H, b ∉ Subgroup.zpowers a := by
      by_contra hcon
      push_neg at hcon
      have hdvd : Nat.card ↥(Work.ThmF.Q0sub H) ∣ Nat.card ↥(Subgroup.zpowers a) :=
        Subgroup.card_dvd_of_le hcon
      rw [Nat.card_zpowers, haorder] at hdvd
      have hle2 : Nat.card ↥(Work.ThmF.Q0sub H) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
      omega
    obtain ⟨b, hbQ0, hbz⟩ := hexb
    have hb1 : b ≠ 1 := fun h => hbz (by rw [h]; exact Subgroup.one_mem _)
    have hborder : orderOf b = 2 := (hQ0el.2.2.2 b hbQ0 hb1).2
    have hba : b ≠ a := fun h => hbz (by rw [h]; exact Subgroup.mem_zpowers a)
    have hab : a * b = b * a := hQ0el.2.1 a haQ0 b hbQ0
    refine ⟨⟨a, hQ0le haQ0⟩, ⟨b, hQ0le hbQ0⟩, ?_, ?_, ?_, ?_⟩
    · rw [← Subgroup.orderOf_coe]; exact haorder
    · rw [← Subgroup.orderOf_coe]; exact hborder
    · intro h
      exact hba (Subtype.ext_iff.mp h).symm
    · refine Subtype.ext ?_
      push_cast
      exact hab
  -- ## 5. `N_K(X) ≠ 1` (Ch. II §4 Prop. 3's hypothesis, `exists_k_normalizing`)
  have hX3 : 3 ≤ (Submission.Blueprint.fixedPts H (Subgroup.zpowers w')).ncard :=
    Work.ThreePoints.P3NeBot.three_le_ncard_fixedPts_of_le_centD hH ht2 htH hXV
  have hP1b := (hC4 G hSit H hH t ht2 htH).1
  obtain ⟨k, hkK, hk1, hkN⟩ :=
    Work.ThmF.ChV12.exists_k_normalizing hH ht2 htH hXV hX3 hfour hP1b
  -- ## 6. `Q ⊓ N_G(X)` is a `2`-group, hence so is `Q ⊓ C_G(w)`
  have hP2 : IsPGroup 2 ↥(Q ⊓ Subgroup.normalizer
      ((Subgroup.zpowers w' : Subgroup G) : Set G)) :=
    cQNormalizerIsPGroupTwo hSit hC4 hsplit hXV hXne ⟨k, hkK, hk1, hkN⟩
  have hCW_le : (Q ⊓ Subgroup.centralizer ({w} : Set G)) ≤
      (Q ⊓ Subgroup.normalizer ((Subgroup.zpowers w' : Subgroup G) : Set G)) :=
    le_inf inf_le_left (inf_le_right.trans (centralizer_le_normalizer_zpowers hw'w))
  refine ⟨hP2.to_le hCW_le, ?_⟩
  -- ## 7. the trichotomy at `P := ⟨w'⟩`: `o(st) ∈ {3, 5}`
  have htri := trichotomyOfPrimeNil (P := Subgroup.zpowers w') hSit c.simple hsplit hC4 hnil
    hfour c.s_mem c.s_inv c.r_mem c.sid hXV hXprime
  dsimp only at htri
  rcases htri with h1 | h2 | h3
  · exact Or.inl h1.1
  · exact Or.inr h2.1
  · exact Or.inl h3.1

end Work.ThmF.Prove
