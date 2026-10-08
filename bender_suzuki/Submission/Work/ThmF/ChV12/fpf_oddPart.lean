import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.ChV12.Basic
import Submission.Work.ThmF.Bender.Basic
import Submission.Work.ThmF.Bender.DTransitiveInv
import Submission.Work.ThmF.Bender.cardKsetEqInv
import Submission.Work.ThmF.Bender.cardInvGeTwo
import Submission.Work.ThmG.nilpotent_two_odd_split
import Submission.Work.ThmG.oddPart_le_normalizer
import Submission.Work.ThmG.rankOne_index
import Submission.Work.NormalComplement.case1_normalizer_le
import Submission.Work.NormalComplement.prop2b_conj_into_centD
import Submission.Work.ThreePoints.BenderPrelim
import Submission.Work.PGroup.card_sup_mul_card_inf_of_le_normalizer
import Submission.Work.ThmF.ChV12.exists_k_normalizing
import Submission.Work.ThmF.ChV12.oddPart_inf_centralizer_eq_bot
import Submission.Work.ThmG.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV12.fpf_oddPart` — Peterfalvi II, Ch. V §2 Lemma 2 (c)

`D = H ⊓ H^t` acts fixed-point-freely on `Q₁ = O_{2'}(Q) = oddPart Q`:

`∀ d ∈ D, d ≠ 1 → ∀ x ∈ Q₁, d * x * d⁻¹ = x → x = 1`.

This is the hypothesis `N_K(X) ≠ 1`/`C_{Q₁}(X) = 1` chain used in Théorème G (Ch. VI §1, p. 257):
"D acts fixed-point-freely on `Q₁`".  The design of the argument is recorded in
`NOTES_fpf_oddPart.md`; the two structural inputs about `X ≤ V = C_D(t)` that it consumes are
delegated to the sibling files `exists_k_normalizing` and `oddPart_inf_centralizer_eq_bot`.

Main steps:

* reduce `d ∈ D#` to a prime-order `P = ⟨z⟩ ≤ D` (`z = d^(orderOf d / p)`, `p ∣ orderOf d`), which
  still centralises `x`;
* `P` fixes the two points `H` and `tH` of `Ω = G ⧸ H`; if these are *all* its fixed points then
  `C_H(P) ≤ D` (an element of `H` centralising `P` permutes the fixed points and fixes `H`), and
  `x ∈ C_H(P) ⊓ Q ≤ Q ⊓ D = ⊥`;
* otherwise `3 ≤ |Ω_P|`, and Peterfalvi I Ch. II §4 Prop. 2 (b)
  (`Work.NormalComplement.prop2b_conj_into_centD`, proved) conjugates `P` into `V = C_D(t)`;
  hypothesis (B3) supplies a four-group in `C_G(P)`, which yields a non-trivial `k ∈ K = J(D,t)`
  normalising `P` (`exists_k_normalizing`), the hypothesis of Ch. II §4 Prop. 3 (the P3 clause of
  `ChIIFourProp`); its 2-subgroup `S` with `S ⊔ (D ⊓ N_G(P)) = H ⊓ N_G(P)` then forces every
  centraliser of odd order to be trivial (`oddPart_inf_centralizer_eq_bot`).
-/

set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.ThmF.ChV12

open Submission.Blueprint Work.ThmF

variable {G : Type} [Group G] [Finite G]

/-! ## Fixed points under conjugation -/

/-- Conjugation transports fixed points: `|Ω_{X^g}| = |Ω_X|`. -/
theorem ncard_fixedPts_map_conj (H X : Subgroup G) (g : G) :
    (fixedPts H (X.map (MulAut.conj g).toMonoidHom)).ncard = (fixedPts H X).ncard := by
  have hset : fixedPts H (X.map (MulAut.conj g).toMonoidHom) =
      (fun ω : G ⧸ H => g • ω) '' fixedPts H X := by
    ext ω
    constructor
    · intro hω
      refine ⟨g⁻¹ • ω, ?_, ?_⟩
      · intro x hx
        have h1 : (g * x * g⁻¹) • ω = ω := by
          have h2 := hω (g * x * g⁻¹)
            (Subgroup.mem_map.mpr ⟨x, hx, by simp [MulAut.conj_apply]⟩)
          simpa [MulAut.conj_apply] using h2
        have h2 : g • (x • (g⁻¹ • ω)) = g • (g⁻¹ • ω) := by
          calc g • (x • (g⁻¹ • ω)) = (g * x * g⁻¹) • ω := by rw [← mul_smul, ← mul_smul]
            _ = ω := h1
            _ = g • (g⁻¹ • ω) := by rw [← mul_smul, mul_inv_cancel, one_smul]
        have h3 := congrArg (fun ω : G ⧸ H => g⁻¹ • ω) h2
        simpa [← mul_smul] using h3
      · dsimp only
        rw [← mul_smul, mul_inv_cancel, one_smul]
    · rintro ⟨ω, hω, rfl⟩
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      show (g * x * g⁻¹) • (g • ω) = g • ω
      calc (g * x * g⁻¹) • (g • ω) = g • (x • ω) := by rw [mul_smul, mul_smul, inv_smul_smul]
        _ = g • ω := by rw [hω x hx]
  rw [hset]
  exact Set.InjOn.ncard_image (f := fun ω : G ⧸ H => g • ω) (s := fixedPts H X)
    (fun a _ b _ h => by
      have h' := congrArg (fun ω : G ⧸ H => g⁻¹ • ω) h
      simpa [← mul_smul] using h')

/-! ## The two fixed points of a subgroup of `D` -/

/-- Every subgroup `P ≤ D = H ⊓ H^t` fixes at least the two points `H` and `tH` of `Ω = G ⧸ H`
(they are distinct because `t ∉ H`). -/
theorem two_le_ncard_fixedPts_of_le_twoPoint {H P : Subgroup G} {t : G} (htH : t ∉ H)
    (hP : P ≤ twoPoint H t) : 2 ≤ (fixedPts H P).ncard := by
  have h1 : ((1 : G) : G ⧸ H) ∈ fixedPts H P := by
    intro p hp
    change ((p * 1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H)
    rw [mul_one, QuotientGroup.eq]
    simpa using H.inv_mem ((Subgroup.mem_inf.mp (hP hp)).1)
  have ht : ((t : G) : G ⧸ H) ∈ fixedPts H P := by
    intro p hp
    change ((p * t : G) : G ⧸ H) = ((t : G) : G ⧸ H)
    rw [QuotientGroup.eq]
    have hpt : t⁻¹ * p * t ∈ H :=
      Work.Models.mem_conj_iff.mp (Subgroup.mem_inf.mp (hP hp)).2
    have : (p * t)⁻¹ * t = (t⁻¹ * p * t)⁻¹ := by group
    rw [this]
    exact H.inv_mem hpt
  have hne : ((1 : G) : G ⧸ H) ≠ ((t : G) : G ⧸ H) := by
    intro hcon
    have h1 : (1 : G)⁻¹ * t ∈ H := QuotientGroup.eq.mp hcon
    exact htH (by simpa using h1)
  have hsub : ({((1 : G) : G ⧸ H), ((t : G) : G ⧸ H)} : Set (G ⧸ H)) ⊆ fixedPts H P := by
    intro ω hω
    rw [Set.mem_insert_iff] at hω
    rcases hω with hω | hω
    · rw [hω]
      exact h1
    · rw [Set.mem_singleton_iff] at hω
      rw [hω]
      exact ht
  have hle := Set.ncard_le_ncard hsub
  rwa [Set.ncard_pair hne] at hle

/-! ## The case `|Ω_P| = 2` -/

/-- If `X ≤ D` has exactly two fixed points on `Ω = G ⧸ H`, then every element of `H` centralising
`X` lies in `D` (it fixes `H` and permutes the two fixed points `{H, tH}`).  Consequently
`C_{Q₁}(X) = 1` because `Q ⊓ D = ⊥`. -/
theorem oddPart_inf_centralizer_eq_bot_of_ncard_two {H Q X : Subgroup G} {t : G}
    (hH : IsStronglyEmbedded H) (ht : orderOf t = 2) (htH : t ∉ H)
    (hQH : Q ≤ H) (hQD : Q ⊓ twoPoint H t = ⊥)
    (hX : X ≤ twoPoint H t) (h2 : (fixedPts H X).ncard = 2) :
    oddPart Q ⊓ Subgroup.centralizer (X : Set G) = ⊥ := by
  have hCD : Subgroup.centralizer (X : Set G) ⊓ H ≤ twoPoint H t := by
    have h1 : Subgroup.normalizer (X : Set G) ⊓ H ≤ H ⊓ twoPoint H t :=
      Work.NormalComplement.case1_normalizer_le G hH ht htH (W := H) le_rfl
        (le_inf (le_trans hX inf_le_left) hX) h2
    intro c hc
    exact (h1 ⟨Subgroup.centralizer_le_normalizer (X : Set G) hc.1, hc.2⟩).2
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hyQ, hyC⟩ := Subgroup.mem_inf.mp hy
  have hyD : y ∈ twoPoint H t := hCD ⟨hyC, hQH (oddPart_le Q hyQ)⟩
  have hybot : y ∈ Q ⊓ twoPoint H t := ⟨oddPart_le Q hyQ, hyD⟩
  rw [hQD] at hybot
  exact hybot

/-! ## Reduction to a prime-order subgroup of `D` -/

/-- An element `≠ 1` of a finite group has a power of prime order of which it is itself a power
(so that any element commuting with `d` commutes with `z`). -/
theorem exists_primeOrder_mem_zpowers {d : G} (hd1 : d ≠ 1) :
    ∃ z ∈ Subgroup.zpowers d, z ≠ 1 ∧ (orderOf z).Prime := by
  set o : ℕ := orderOf d with ho
  have ho_pos : 0 < o := by rw [ho]; exact orderOf_pos d
  have ho1 : o ≠ 1 := by
    rw [ho]
    exact fun hc => hd1 (orderOf_eq_one_iff.mp hc)
  obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd ho1
  have hmain : o / (o / p) = p := Nat.div_div_self hpdvd ho_pos.ne'
  have hzo : orderOf (d ^ (o / p)) = p := by
    rw [orderOf_pow]
    have hgcd : (orderOf d).gcd (o / p) = o / p := by
      rw [ho.symm]
      exact Nat.gcd_eq_right (Nat.div_dvd_of_dvd hpdvd)
    rw [hgcd, ← ho]
    exact hmain
  refine ⟨d ^ (o / p), ?_, ?_, ?_⟩
  · refine Subgroup.mem_zpowers_iff.mpr ⟨((o / p : ℕ) : ℤ), ?_⟩
    rw [zpow_natCast]
  · intro hc
    rw [hc, orderOf_one] at hzo
    exact hpprime.ne_one hzo.symm
  · rw [hzo]
    exact hpprime

/-- If `z` is a power of `d` and `d x d⁻¹ = x`, then `z x z⁻¹ = x`. -/
theorem conj_eq_of_mem_zpowers {d x z : G} (hz : z ∈ Subgroup.zpowers d)
    (h : d * x * d⁻¹ = x) : z * x * z⁻¹ = x := by
  have hdx : d * x = x * d := by
    have := congrArg (fun u => u * d) h
    simpa [mul_assoc] using this
  have hdC : d ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hdx
  have hzC : z ∈ Subgroup.centralizer ({x} : Set G) := (Subgroup.zpowers_le.mpr hdC) hz
  have hzx : z * x = x * z := Subgroup.mem_centralizer_singleton_iff.mp hzC
  rw [hzx]
  group

/-! ## The two structural inputs on `X ≤ V = C_D(t)`

These are the statements proved (for `ChIIFourProp`) in the sibling files
`Work.ThmF.ChV12.exists_k_normalizing` and `Work.ThmF.ChV12.oddPart_inf_centralizer_eq_bot`. -/

/-- Hypothesis form of `exists_k_normalizing`: the hypothesis `N_K(X) ≠ 1` of Ch. II §4 Prop. 3. -/
def KExistsProp (H : Subgroup G) (t : G) : Prop :=
  ∀ X : Subgroup G, X ≤ centD H t → 3 ≤ (fixedPts H X).ncard →
    HasFourGroup (Subgroup.centralizer (X : Set G)) →
    ∃ k ∈ invertedBy (twoPoint H t) t, k ≠ 1 ∧ k ∈ Subgroup.normalizer (X : Set G)

/-- Hypothesis form of `oddPart_inf_centralizer_eq_bot`: the `S`-clause of Ch. II §4 Prop. 3
forces `C_{Q₁}(X) = 1`. -/
def OddPartCentralizerProp (H Q : Subgroup G) (t : G) : Prop :=
  ∀ X : Subgroup G,
    (∃ S : Subgroup G, IsPGroup 2 S ∧ S ≤ Subgroup.normalizer (X : Set G) ∧ S ≤ H ∧
      S ⊓ twoPoint H t = ⊥ ∧
      S ⊔ (twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) =
        H ⊓ Subgroup.normalizer (X : Set G) ∧
      H ⊓ Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (S : Set G)) →
    oddPart Q ⊓ Subgroup.centralizer (X : Set G) = ⊥

open LeanEval.GroupTheory.Defs Submission.Blueprint Work.ThmF in theorem kExistsProp_of {G : Type} [Group G] [Finite G] {H : Subgroup G} {t : G} (hH : IsStronglyEmbedded H) (ht2 : orderOf t = 2) (htH : t ∉ H) (hP1b : ∀ X' F : Subgroup G, 3 ≤ (fixedPts H X').ncard → involutions (Subgroup.centralizer (X' : Set G) : Set G) ⊆ F → F ≤ Subgroup.normalizer (X' : Set G) → ∀ g : G, X' ≤ conj g H → IsStronglyEmbedded ((F ⊓ conj g H).subgroupOf F)) : KExistsProp H t := fun X hX h3 h4 => exists_k_normalizing hH ht2 htH hX h3 h4 hP1b

/-! ## The case `3 ≤ |Ω_P|` -/

/-- Peterfalvi II, Ch. V §2 Lemma 2 (c), in the case `3 ≤ |Ω_P|`: a subgroup `P ≤ D` of prime
order fixing at least three points of `Ω` is centralised by no non-trivial element of `Q₁`. -/
theorem oddPart_inf_centralizer_eq_bot_of_primeOrder_ge_three {H Q : Subgroup G} {t : G}
    (hS : Situation G) (hC4 : ChIIFourProp) (h : IsSplitRankOne H Q t)
    (hB3 : ∀ P : Subgroup G, P ≤ centD H t → (Nat.card P).Prime →
      HasFourGroup (Subgroup.centralizer (P : Set G)))
    (hnil : Group.IsNilpotent ↥Q)
    (hk_exists : KExistsProp H t) (hindex : OddPartCentralizerProp H Q t)
    {P : Subgroup G} (hPD : P ≤ twoPoint H t) (hPne : P ≠ ⊥) (hPprime : (Nat.card P).Prime)
    (hP3 : 3 ≤ (fixedPts H P).ncard) :
    oddPart Q ⊓ Subgroup.centralizer (P : Set G) = ⊥ := by
  -- (1) `P` is `D`-conjugate into `V = C_D(t)` (Peterfalvi I Ch. II §4 Prop. 2 (b))
  obtain ⟨d₀, hd₀D, hd₀V⟩ :=
    Work.NormalComplement.prop2b_conj_into_centD G hS Work.ThreePoints.benderPrelimProp hC4
      h.stronglyEmbedded h.invol h.not_mem hPD hP3
  set X : Subgroup G := P.map (MulAut.conj d₀).toMonoidHom with hXdef
  have hXV : X ≤ centD H t := hd₀V
  have hXcard : Nat.card ↥X = Nat.card ↥P := by
    rw [hXdef]
    exact Subgroup.card_map_of_injective (MulAut.conj d₀).injective
  have hXne : X ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥X = 1 := Subgroup.card_eq_one.mpr hbot
    rw [hXcard] at h1
    exact hPprime.ne_one h1
  have hX3 : 3 ≤ (fixedPts H X).ncard := by
    rw [hXdef, ncard_fixedPts_map_conj H P d₀]
    exact hP3
  -- (2) hypothesis (B3) for `X ≤ V`, and the element `k ∈ K#` normalising `X`
  have hfour : HasFourGroup (Subgroup.centralizer (X : Set G)) := by
    refine hB3 X hXV ?_
    rw [hXcard]
    exact hPprime
  obtain ⟨k, hkK, hk1, hkn⟩ := hk_exists X hXV hX3 hfour
  -- (3) Ch. II §4 Prop. 3 (the P3 clause of `ChIIFourProp`) applied to `X` and `k`
  have hP3c := (hC4 G hS H h.stronglyEmbedded t h.invol h.not_mem).2.2.2.1 X hXne hXV
    ⟨k, hkK, hk1, hkn⟩
  dsimp only at hP3c
  obtain ⟨S, hSp, hSFH, _hIdx, hSnorm, hSD, hSsup⟩ := hP3c.2.1
  have hSC : S ≤ Subgroup.centralizer (X : Set G) := by
    intro s hs
    have hmem : s ∈ (oddResidual (Subgroup.centralizer (X : Set G))).map
        (Subgroup.centralizer (X : Set G)).subtype := (Subgroup.mem_inf.mp (hSFH hs)).1
    obtain ⟨c, _hc, hcs⟩ := Subgroup.mem_map.mp hmem
    rw [← hcs]
    exact c.2
  have hSH : S ≤ H := fun s hs => (Subgroup.mem_inf.mp (hSFH hs)).2
  have hSN : S ≤ Subgroup.normalizer (X : Set G) :=
    hSC.trans (Subgroup.centralizer_le_normalizer (X : Set G))
  have hbotX : oddPart Q ⊓ Subgroup.centralizer (X : Set G) = ⊥ :=
    hindex X ⟨S, hSp, hSN, hSH, hSD, hSsup, hSnorm⟩
  -- (4) transfer back along `d₀`: `C_{Q₁}(P)^{d₀} = C_{Q₁}(P^{d₀}) = ⊥`
  have hQ₁norm : H ≤ Subgroup.normalizer ((oddPart Q : Subgroup G) : Set G) :=
    Work.ThmG.oddPart_le_normalizer h.normal
  have hd₀H : d₀ ∈ H := (Subgroup.mem_inf.mp hd₀D).1
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hyQ₁, hyP⟩ := Subgroup.mem_inf.mp hy
  have hydiv : d₀ * y * d₀⁻¹ ∈ (oddPart Q : Subgroup G) :=
    (Subgroup.mem_normalizer_iff.mp (hQ₁norm hd₀H) y).mp hyQ₁
  have hycent : d₀ * y * d₀⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hx
    have hpcomm : p * y = y * p := (Subgroup.mem_centralizer_iff.mp hyP) p hp
    have hpval : (MulAut.conj d₀).toMonoidHom p = d₀ * p * d₀⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hpval]
    calc (d₀ * p * d₀⁻¹) * (d₀ * y * d₀⁻¹) = d₀ * (p * y) * d₀⁻¹ := by group
      _ = d₀ * (y * p) * d₀⁻¹ := by rw [hpcomm]
      _ = (d₀ * y * d₀⁻¹) * (d₀ * p * d₀⁻¹) := by group
  have hybot : d₀ * y * d₀⁻¹ ∈ (⊥ : Subgroup G) := by
    rw [← hbotX]
    exact Subgroup.mem_inf.mpr ⟨hydiv, hycent⟩
  have hy1 : d₀ * y * d₀⁻¹ = 1 := Subgroup.mem_bot.mp hybot
  have hdy : d₀ * y = d₀ * 1 := by
    have := congrArg (fun u => u * d₀) hy1
    simpa [mul_assoc] using this
  exact mul_left_cancel hdy

/-- Peterfalvi II, Ch. V §2 Lemma 2 (c): a subgroup `P ≤ D` of prime order is centralised by no
non-trivial element of `Q₁ = O_{2'}(Q)`. -/
theorem oddPart_inf_centralizer_eq_bot_of_primeOrder {H Q : Subgroup G} {t : G}
    (hS : Situation G) (hC4 : ChIIFourProp) (h : IsSplitRankOne H Q t)
    (hB3 : ∀ P : Subgroup G, P ≤ centD H t → (Nat.card P).Prime →
      HasFourGroup (Subgroup.centralizer (P : Set G)))
    (hnil : Group.IsNilpotent ↥Q)
    (hk_exists : KExistsProp H t) (hindex : OddPartCentralizerProp H Q t)
    {P : Subgroup G} (hPD : P ≤ twoPoint H t) (hPne : P ≠ ⊥) (hPprime : (Nat.card P).Prime) :
    oddPart Q ⊓ Subgroup.centralizer (P : Set G) = ⊥ := by
  by_cases h2 : (fixedPts H P).ncard = 2
  · exact oddPart_inf_centralizer_eq_bot_of_ncard_two h.stronglyEmbedded h.invol h.not_mem
      h.le h.inf_eq hPD h2
  · refine oddPart_inf_centralizer_eq_bot_of_primeOrder_ge_three hS hC4 h hB3 hnil hk_exists
      hindex hPD hPne hPprime ?_
    have hle2 := two_le_ncard_fixedPts_of_le_twoPoint h.not_mem hPD
    omega


/-! ## Assembly -/

/-- The main theorem, with the two structural inputs (`exists_k_normalizing` and
`oddPart_inf_centralizer_eq_bot`) as hypotheses. -/
theorem fpf_oddPart_of {G : Type} [Group G] [Finite G] (hS : Situation G) (hC4 : ChIIFourProp)
    (H Q : Subgroup G) (t : G) (h : IsSplitRankOne H Q t)
    (hB3 : ∀ P : Subgroup G, P ≤ centD H t → (Nat.card P).Prime →
      HasFourGroup (Subgroup.centralizer (P : Set G)))
    (hnil : Group.IsNilpotent ↥Q)
    (hk_exists : KExistsProp H t) (hindex : OddPartCentralizerProp H Q t) :
    ∀ d ∈ twoPoint H t, d ≠ 1 → ∀ x ∈ oddPart Q, d * x * d⁻¹ = x → x = 1 := by
  intro d hdD hd1 x hxQ hdx
  -- a prime-order power `z` of `d`, still centralising `x`
  obtain ⟨z, hzmem, hz1, hzprime⟩ := exists_primeOrder_mem_zpowers hd1
  have hzD : z ∈ twoPoint H t := (Subgroup.zpowers_le.mpr hdD) hzmem
  set P : Subgroup G := Subgroup.zpowers z with hPdef
  have hPD : P ≤ twoPoint H t := Subgroup.zpowers_le.mpr hzD
  have hPprime : (Nat.card ↥P).Prime := by
    rw [hPdef, Nat.card_zpowers]
    exact hzprime
  have hPne : P ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥P = 1 := Subgroup.card_eq_one.mpr hbot
    exact hPprime.ne_one h1
  have hkey : oddPart Q ⊓ Subgroup.centralizer (P : Set G) = ⊥ :=
    oddPart_inf_centralizer_eq_bot_of_primeOrder hS hC4 h hB3 hnil hk_exists hindex hPD hPne
      hPprime
  -- `x` centralises `P = ⟨z⟩`
  have hmem : x ∈ oddPart Q ⊓ Subgroup.centralizer (P : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨hxQ, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro p hp
    have hzx : z * x = x * z := by
      have h := conj_eq_of_mem_zpowers hzmem hdx
      have h2 := congrArg (fun u => u * z) h
      simpa [mul_assoc] using h2
    have hzC : z ∈ Subgroup.centralizer ({x} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hzx
    have hpz : p ∈ Subgroup.zpowers z := by rwa [hPdef] at hp
    exact Subgroup.mem_centralizer_singleton_iff.mp ((Subgroup.zpowers_le.mpr hzC) hpz)
  rw [hkey] at hmem
  exact Subgroup.mem_bot.mp hmem

open LeanEval.GroupTheory.Defs Submission.Blueprint Work.ThmF in theorem fpf_oddPart {G : Type} [Group G] [Finite G] (hS : Situation G) (hC4 : ChIIFourProp) (H Q : Subgroup G) (t : G) (h : IsSplitRankOne H Q t) (hB3 : ∀ P : Subgroup G, P ≤ centD H t → (Nat.card P).Prime → HasFourGroup (Subgroup.centralizer (P : Set G))) (hnil : Group.IsNilpotent ↥Q) : ∀ d ∈ twoPoint H t, d ≠ 1 → ∀ x ∈ oddPart Q, d * x * d⁻¹ = x → x = 1 :=
  fpf_oddPart_of hS hC4 H Q t h hB3 hnil
    (kExistsProp_of h.stronglyEmbedded h.invol h.not_mem
      (hC4 G hS H h.stronglyEmbedded t h.invol h.not_mem).1)
    (fun X hSdata => oddPart_inf_centralizer_eq_bot (H := H) (Q := Q) (X := X) (t := t)
      h.le h.normal h.inf_eq hnil hSdata)

/-! ## Bridge to the `ThmG` vocabulary

`Work.ThmG.FpfOddPartProp` (`RankOneHyp` form, as consumed by
`Work.ThmG.rankOneStructure_of` / `Work.ThmG.rankOneStructure_of_seven`) follows from
`fpf_oddPart` once the nilpotency of `Q` is supplied: `RankOneHyp` provides `Situation`,
`IsSplitRankOne` and hypothesis (B3), and `ChIIFourProp` is an area `Prop` of the assembly.
The nilpotency input is available in area `ThmG` as `Work.ThmG.nilpotent_of_K_ne_one`
(Ch. V §1 Prop. 1 b), using `ThompsonFrobeniusProp` and `KNeOneProp`. -/

theorem fpfOddPartProp_of {G : Type} [Group G] [Finite G] (hC4 : ChIIFourProp)
    (hnil : ∀ (F : Type) [Group F] [Fintype F] (H Q : Subgroup F) (t : F),
      Work.ThmG.RankOneHyp F H Q t → Group.IsNilpotent ↥Q) :
    Work.ThmG.FpfOddPartProp :=
  fun F _ _ H Q t hhyp =>
    fpf_oddPart hhyp.1 hC4 H Q t hhyp.2.2.1 hhyp.2.2.2.2 (hnil F H Q t hhyp)


end Work.ThmF.ChV12
