import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.p3Normal_of_chIIFourP3Subnormal
import Submission.Work.NormalComplement.sec4_one_c
import Submission.Work.NormalComplement.pResidual_strategy
import Submission.Work.NormalComplement.appI_five_d_corrected
import Submission.Work.NormalComplement.card_sup_mul_card_inf
import Submission.Work.LocalPrelim.relIndex_sup_eq_relIndex_inf
import Submission.Work.NPC.Engine
import Submission.Work.Grun.pResidual
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.NormalComplement

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-- **`p`-part of a subgroup of a semidirect product `B = S ⋊ E` with `S` a 2-group.**

`T ≤ B = S ⊔ E` is a `p`-subgroup (`p` odd) containing a subgroup `P` of order `p`, and the
`p`-part of `E` is `p` (`¬ p ^ 2 ∣ |E|`).  Then `T = P`.

Indeed `T ⊓ S = ⊥` (`T` is a `p`-group, `S` a 2-group, `p ≠ 2`), so `S ⊔ T` has order `|T| · |S|`
and, being contained in `B`, this divides `|B| = |S| · |E|`; hence `|T|` divides `|E|`.  As `|T|` is
a power of `p` and `p ^ 2 ∤ |E|`, we get `|T| ∈ {1, p}`, and `|P| = p ≤ |T|` forces `T = P`. -/
theorem pgroup_eq_of_le_sup {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {B S E T P : Subgroup G} (hB : B = S ⊔ E) (hSE : S ⊓ E = ⊥) (hS2 : IsPGroup 2 S)
    (hSB : B ≤ Subgroup.normalizer (S : Set G)) (hTp : IsPGroup p T) (hTB : T ≤ B)
    (hPT : P ≤ T) (hPcard : Nat.card ↥P = p) (hEp : ¬ p ^ 2 ∣ Nat.card ↥E) : T = P := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hSB' : T ≤ Subgroup.normalizer (S : Set G) := hTB.trans hSB
  have hEB' : E ≤ Subgroup.normalizer (S : Set G) := le_sup_right.trans (hB ▸ hSB)
  -- `T ⊓ S = ⊥`: it is at once a `p`-group and a 2-group, and `p ≠ 2`.
  have hTS : T ⊓ S = ⊥ := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hTp.to_inf_left
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hS2.to_inf_right
    have hpow : p ^ a = 2 ^ b := by rw [← ha, ← hb]
    have ha0 : a = 0 := by
      by_contra hane
      have hdvd : p ∣ 2 ^ b := by
        rw [← hpow]; exact dvd_pow_self p hane
      have hp2' : p ∣ 2 := hp.dvd_of_dvd_pow hdvd
      rcases (Nat.dvd_prime Nat.prime_two).mp hp2' with h | h
      · exact hp.ne_one h
      · exact hp2 h
    rw [ha0, pow_zero] at ha
    exact Subgroup.card_eq_one.mp ha
  -- `|S ⊔ T| = |T| * |S|`
  have hcardST : Nat.card ↥(S ⊔ T) = Nat.card ↥T * Nat.card ↥S := by
    have h1 : Nat.card ↥(S ⊔ T) * Nat.card ↥(S ⊓ T) = Nat.card ↥S * Nat.card ↥T :=
      card_sup_mul_card_inf (H := S) (K := T) hSB'
    rw [inf_comm, hTS, Subgroup.card_bot, mul_one] at h1
    exact h1.trans (mul_comm _ _)
  -- `|B| = |S| * |E|`
  have hcardB : Nat.card ↥B = Nat.card ↥S * Nat.card ↥E := by
    have h1 : Nat.card ↥(S ⊔ E) * Nat.card ↥(S ⊓ E) = Nat.card ↥S * Nat.card ↥E :=
      card_sup_mul_card_inf (H := S) (K := E) hEB'
    rw [← hB, hSE, Subgroup.card_bot, mul_one] at h1
    exact h1
  -- `|T|` divides `|E|`
  have hTdvd : Nat.card ↥T ∣ Nat.card ↥E := by
    have h1 : Nat.card ↥(T ⊔ S) ∣ Nat.card ↥B :=
      Subgroup.card_dvd_of_le (sup_le hTB (le_sup_left.trans (le_of_eq hB.symm)))
    rw [sup_comm, hcardST, hcardB] at h1
    rw [mul_comm (Nat.card ↥T) (Nat.card ↥S)] at h1
    exact (Nat.mul_dvd_mul_iff_left Nat.card_pos).mp h1
  -- `|T| = p ^ k` with `k ≤ 1`
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hTp
  have hpk : k ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    have h2 : p ^ 2 ∣ Nat.card ↥T := hk ▸ pow_dvd_pow p hcon
    exact hEp (h2.trans hTdvd)
  have hpdvd : p ∣ Nat.card ↥T := by
    rw [← hPcard]; exact Subgroup.card_dvd_of_le hPT
  have hcardT : Nat.card ↥T = p := by
    have hk1 : 1 ≤ k := by
      by_contra hcon
      push_neg at hcon
      have hk0 : k = 0 := by omega
      rw [hk, hk0, pow_zero] at hpdvd
      exact hp.ne_one (Nat.dvd_one.mp hpdvd)
    rw [hk, show k = 1 by omega, pow_one]
  exact (Subgroup.eq_of_le_of_card_ge hPT (by rw [hcardT, hPcard])).symm

/-- **Peterfalvi I Ch. III §5 Lemma 1** (p. 184), the prerequisite for the §5 argument: if
`P ≤ X ≤ V = C_D(t)` and `N_H(P) ≤ N_H(X)` then `X = P`.

The proof follows the source.  In the case `X ⊓ A ≠ ⊥`, put `Y = X ⊓ A ⊴ X` (a nontrivial
`k ∈ J(D,t) ⊓ C_G(A) = N_K(Y)` exists because `|C_K(A)| = 2 ^ p - 1 ≠ 1`), so Ch. II §4 Prop. 3
(`hP3`) applies to the pair `(X, Y)`: it gives `N_G(X) = O^{2'}(C_G(X))·N_V(X)` and
`H ⊓ N_G(X) = S ⊔ (D ⊓ N_G(X))` with `S` a 2-group, `S ◁ H ⊓ N_G(X)` and `S ⊓ D = ⊥`.

Since `P ≤ X` and `N_H(P) ≤ N_H(X)` (the hypothesis `hN`), every `p`-subgroup of `N_H(P)` can be
estimated in the semidirect product `S ⋊ (D ⊓ N_G(X))`: as `|D|_p = p` (the source's §4 Lemma 1 (d),
`h.P_syl`), such a subgroup, if it contains `P`, equals `P` (`pgroup_eq_of_le_sup`).  Hence
`P` is a `p`-Sylow of `N_H(P)` and, by the normalizer criterion, of `H` and of `W`.

For the contradiction, `N_H(P) ≤ N_H(X) = S ⋊ N_D(X)` and `S ≤ F₀ ≤ C_G(X) ≤ C_G(P)`, while
`D ⊓ N_D(P) = (A ⊓ C_G(P)) ⊔ P ≤ C_G(P)` (§4 Lemma 1 (c), `sec4_one_c`), give
`N_H(P) ≤ C_H(P)`.  Burnside's normal `p`-complement theorem applied to `W` (whose Sylow `p` is
`P`) then produces a normal `Nn = O^p(W) < W` with `W = Nn·P`, and the strategy of §1 applied to
`E = W ⊓ D` gives `W₁ < W` normalised by `H` with `W₁ ⊔ D = H`, contradicting the minimality
of `W` — so `X ⊓ A ≠ ⊥` is impossible, and `X = X ⊓ A ⊔ P = P`. -/
theorem sec5_prereq_l1 (hFT : Submission.Blueprint.FeitThompsonProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) (X : Subgroup G) (hPX : P ≤ X)
    (hXV : X ≤ Submission.Blueprint.centD H t)
    (hN : H ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (X : Set G)) :
    X = P := by
  classical
  have hPleV : P ≤ Submission.Blueprint.centD H t := h.P_le.trans inf_le_right
  have hPleD : P ≤ Submission.Blueprint.twoPoint H t :=
    h.P_le.trans (inf_le_left.trans inf_le_right)
  have hXnA : X ≤ Subgroup.normalizer (A : Set G) := hXV.trans h.A_normal
  have hPnA : P ≤ Subgroup.normalizer (A : Set G) := hPleV.trans h.A_normal
  have hXsup : X ⊓ A ⊔ P = X := by
    refine le_antisymm (sup_le inf_le_left hPX) ?_
    intro x hx
    have hxV : x ∈ A ⊔ P := h.A_sup ▸ (hXV hx)
    have hxAP : x ∈ (↑A : Set G) * (↑P : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left A P hPnA]; exact hxV
    obtain ⟨a, ha, q, hq, haq⟩ := hxAP
    have haX : a ∈ X := by
      have h1 : a = x * q⁻¹ := by rw [← haq]; group
      rw [h1]; exact X.mul_mem hx (X.inv_mem (hPX hq))
    rw [← haq]
    exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨haX, ha⟩) hq
  have hXinf : X ⊓ A ⊓ P = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    have hx1 : x ∈ X ⊓ A := (Subgroup.mem_inf.mp hx).1
    have hx2 : x ∈ P := (Subgroup.mem_inf.mp hx).2
    have hxAP : x ∈ A ⊓ P :=
      Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx1).2, hx2⟩
    simpa [h.A_inf] using hxAP
  by_cases hXA : X ⊓ A = ⊥
  · rw [← hXsup, hXA, bot_sup_eq]
  · exfalso
    have hYleX : X ⊓ A ≤ X := inf_le_left
    have hXnormY : X ≤ Subgroup.normalizer ((X ⊓ A : Subgroup G) : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      intro x hx y hy
      rw [Subgroup.mem_inf] at hy ⊢
      exact ⟨X.mul_mem (X.mul_mem hx hy.1) (X.inv_mem hx),
        (Subgroup.mem_normalizer_iff.mp (hXnA hx) y).mp hy.2⟩
    have hsub : Submission.Blueprint.IsSubnormalIn (X ⊓ A) X :=
      Relation.ReflTransGen.single
        ⟨hYleX, (Subgroup.normal_subgroupOf_iff_le_normalizer hYleX).mpr hXnormY⟩
    -- a nontrivial `k ∈ C_K(A)` normalising `X ⊓ A`
    have hcardCK : (Design.CK H t A).ncard = 2 ^ p - 1 := h.A_CK
    have hp2 : 2 ≤ p := h.prime.two_le
    have hpow : 2 ^ p - 1 ≠ 1 := by
      have h1 : (2 : ℕ) ^ 2 ≤ 2 ^ p := pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2) hp2
      have h4 : 4 ≤ 2 ^ p := by simpa using h1
      omega
    have h1mem : (1 : G) ∈ Design.CK H t A := by
      refine ⟨⟨(Submission.Blueprint.twoPoint H t).one_mem, by simp⟩, ?_⟩
      exact (Subgroup.centralizer (A : Set G)).one_mem
    obtain ⟨k, hk, hk1⟩ : ∃ k ∈ Design.CK H t A, k ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      have hsingle : Design.CK H t A = {1} :=
        Set.eq_singleton_iff_unique_mem.mpr ⟨h1mem, hcon⟩
      rw [hsingle, Set.ncard_singleton] at hcardCK
      exact hpow hcardCK.symm
    have hkK : k ∈ Work.NormalComplement.Kset (Submission.Blueprint.twoPoint H t) t := hk.1
    have hkC : k ∈ Subgroup.centralizer (A : Set G) := hk.2
    have hkN : k ∈ Subgroup.normalizer ((X ⊓ A : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      apply le_antisymm
      · intro x hx
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
        rw [Subgroup.mem_inf] at hy ⊢
        have hcomm : y * k = k * y := (Subgroup.mem_centralizer_iff.mp hkC) y hy.2
        have hyx' : k * y * k⁻¹ = x := by
          rw [← hyx]
          exact (MulAut.conj_apply k y).symm
        have hxy : x = y := by rw [← hyx']; rw [← hcomm]; group
        rw [hxy]; exact hy
      · intro x hx
        refine Subgroup.mem_map.mpr ⟨x, hx, ?_⟩
        rw [Subgroup.mem_inf] at hx
        have hcomm : x * k = k * x := (Subgroup.mem_centralizer_iff.mp hkC) x hx.2
        have h1 : (↑(MulAut.conj k) : G →* G) x = k * x * k⁻¹ := MulAut.conj_apply k x
        rw [h1, ← hcomm]; group
    have hkIn : ∃ k' ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t,
        k' ≠ 1 ∧ k' ∈ Subgroup.normalizer ((X ⊓ A : Subgroup G) : Set G) :=
      ⟨k, hkK, hk1, hkN⟩
    have hP3 := hP3 G h.sit H h.se t h.invol h.notMem X (X ⊓ A) hXV hXA hsub hkIn
    obtain ⟨hNG, S, hS2, hSleFH, hSleH, hSN, hSD, hSsup⟩ := hP3
    -- ## `N_H(P) ≤ C_H(P)`
    have hPleC : P ≤ Subgroup.centralizer (P : Set G) := by
      haveI : Fact p.Prime := ⟨h.prime⟩
      haveI : IsCyclic ↥P := isCyclic_of_prime_card h.P_card
      haveI : IsMulCommutative ↥P := IsCyclic.isMulCommutative
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hc : (⟨y, hy⟩ : ↥P) * ⟨x, hx⟩ = (⟨x, hx⟩ : ↥P) * ⟨y, hy⟩ :=
        isMulCommutative_iff.mp (inferInstance : IsMulCommutative ↥P) ⟨y, hy⟩ ⟨x, hx⟩
      simpa using congrArg Subtype.val hc
    have hNH_le_C : H ⊓ Subgroup.normalizer (P : Set G) ≤
        Subgroup.centralizer (P : Set G) := by
      intro h0 hh0
      obtain ⟨hh0H, hh0NP⟩ := Subgroup.mem_inf.mp hh0
      have h0mem : h0 ∈ H ⊓ Subgroup.normalizer (X : Set G) :=
        Subgroup.mem_inf.mpr ⟨hh0H, hN hh0⟩
      rw [← hSsup] at h0mem
      have hBnormS : (Submission.Blueprint.twoPoint H t ⊓
          Subgroup.normalizer (X : Set G)) ≤ Subgroup.normalizer (S : Set G) :=
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans hSN
      have h0mem' : h0 ∈ (↑S : Set G) *
          (↑(Submission.Blueprint.twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left S _ hBnormS]
        exact h0mem
      obtain ⟨s, hs, d, hd, hsd⟩ := h0mem'
      have hsC : s ∈ Subgroup.centralizer (P : Set G) := by
        have hsF : s ∈ (oddResidual ↥(Subgroup.centralizer (X : Set G))).map
            (Subgroup.centralizer (X : Set G)).subtype :=
          (Subgroup.mem_inf.mp (hSleFH hs)).1
        exact (Subgroup.centralizer_le hPX) ((Subgroup.map_subtype_le _) hsF)
      have hdD : d ∈ Submission.Blueprint.twoPoint H t := (Subgroup.mem_inf.mp hd).1
      have hdNP : d ∈ Subgroup.normalizer (P : Set G) := by
        have hsNP : s ∈ Subgroup.normalizer (P : Set G) :=
          Subgroup.centralizer_le_normalizer _ hsC
        have h1 : d = s⁻¹ * h0 := by rw [← hsd]; group
        rw [h1]
        exact (Subgroup.normalizer (P : Set G)).mul_mem
          ((Subgroup.normalizer (P : Set G)).inv_mem hsNP) hh0NP
      have hdDP : d ∈ Submission.Blueprint.twoPoint H t ⊓
          Subgroup.normalizer (P : Set G) := Subgroup.mem_inf.mpr ⟨hdD, hdNP⟩
      have hdC : d ∈ Subgroup.centralizer (P : Set G) := by
        rw [(sec4_one_c hFT h.toSetup45A).1] at hdDP
        exact (sup_le inf_le_right hPleC) hdDP
      rw [← hsd]
      exact (Subgroup.centralizer (P : Set G)).mul_mem hsC hdC
    -- ## `P` is a `p`-Sylow of `H`, hence of `W`
    --
    -- `N_H(P) ≤ H ⊓ N_G(X) = S ⊔ (D ⊓ N_G(X))`, where `S` is a 2-group normal in `H ⊓ N_G(X)`
    -- with `S ⊓ D = ⊥` (Ch. II §4 Prop. 3) and `D ⊓ N_G(X) ≤ D` has `p`-part `p`.  Hence the
    -- `p`-part of `N_H(P)` is `p` (the source's "By §4 Lemma 1 (c), (d), `P` is a `p`-Sylow of
    -- `H`"), so `P` is a `p`-Sylow of `N_H(P)` and, by the normalizer criterion, of `H`.
    haveI : Fact p.Prime := ⟨h.prime⟩
    have hPp : IsPGroup p P :=
      IsPGroup.iff_card.mpr ⟨1, by rw [pow_one]; exact h.P_card⟩
    have hPleH : P ≤ H := hPleD.trans inf_le_left
    -- `p` is odd: `D` has odd order and `p ∣ |P| ∣ |D|`
    have hp2 : p ≠ 2 := by
      intro hpe
      have hdvdD : p ∣ Nat.card ↥(Submission.Blueprint.twoPoint H t) := by
        rw [← h.P_card]; exact Subgroup.card_dvd_of_le hPleD
      have h2dvd : 2 ∣ Nat.card ↥(Submission.Blueprint.twoPoint H t) := hpe ▸ hdvdD
      exact (Nat.not_even_iff_odd.mpr (h.se.2.2 t h.notMem)) (even_iff_two_dvd.mpr h2dvd)
    have hE_inf : S ⊓ (Submission.Blueprint.twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) =
        ⊥ := by
      rw [eq_bot_iff]
      intro s hs
      obtain ⟨hsS, hsE⟩ := Subgroup.mem_inf.mp hs
      have hsD : s ∈ Submission.Blueprint.twoPoint H t := (Subgroup.mem_inf.mp hsE).1
      have hmem : s ∈ S ⊓ Submission.Blueprint.twoPoint H t := Subgroup.mem_inf.mpr ⟨hsS, hsD⟩
      rwa [hSD, Subgroup.mem_bot] at hmem
    have hE_le_D : Submission.Blueprint.twoPoint H t ⊓ Subgroup.normalizer (X : Set G) ≤
        Submission.Blueprint.twoPoint H t := inf_le_left
    -- `p ^ 2` does not divide `|D|`, because `P` is a `p`-Sylow of `D`
    have hD_sq : ¬ p ^ 2 ∣ Nat.card ↥(Submission.Blueprint.twoPoint H t) := by
      intro hdvd
      have hcard : Nat.card ↥(P.subgroupOf (Submission.Blueprint.twoPoint H t)) *
          (P.subgroupOf (Submission.Blueprint.twoPoint H t)).index =
          Nat.card ↥(Submission.Blueprint.twoPoint H t) :=
        Subgroup.card_mul_index _
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPleD).toEquiv, h.P_card] at hcard
      rw [← hcard, pow_two] at hdvd
      exact h.P_syl.2.2 ((Nat.mul_dvd_mul_iff_left h.prime.pos).mp hdvd)
    have hE_sq : ¬ p ^ 2 ∣ Nat.card ↥(Submission.Blueprint.twoPoint H t ⊓
        Subgroup.normalizer (X : Set G)) :=
      fun hd => hD_sq (hd.trans (Subgroup.card_dvd_of_le hE_le_D))
    -- any `p`-subgroup of `N_H(P)` containing `P` equals `P`
    have hkey : ∀ T : Subgroup G, T ≤ H ⊓ Subgroup.normalizer (P : Set G) →
        IsPGroup p T → P ≤ T → T = P := by
      intro T hTR hTp hPT
      have hTB : T ≤ H ⊓ Subgroup.normalizer (X : Set G) := hTR.trans (le_inf inf_le_left hN)
      exact pgroup_eq_of_le_sup (B := H ⊓ Subgroup.normalizer (X : Set G)) h.prime hp2
        hSsup.symm hE_inf hS2 hSN hTp hTB hPT h.P_card hE_sq
    -- `P` is a `p`-Sylow of `N_H(P)`
    have hPN : P ≤ H ⊓ Subgroup.normalizer (P : Set G) :=
      le_inf hPleH Subgroup.le_normalizer
    have hSylN : ¬ p ∣ (P.subgroupOf (H ⊓ Subgroup.normalizer (P : Set G))).index := by
      intro hdvd
      obtain ⟨T, hTR, hTp, hPT⟩ :=
        Work.ThreePoints.exists_pSubgroup_lt_of_dvd_index h.prime hPp hPN hdvd
      exact hPT.ne (hkey T hTR hTp hPT.le).symm
    -- `P` is a `p`-Sylow of `H`: the normalizer criterion
    have hSylH : ¬ p ∣ (P.subgroupOf H).index := by
      intro hdvd
      obtain ⟨T, hTH, hTp, hPT⟩ :=
        Work.ThreePoints.exists_pSubgroup_lt_of_dvd_index h.prime hPp hPleH hdvd
      have hlt : P < T ⊓ Subgroup.normalizer (P : Set G) :=
        Work.Coprime.lt_inf_normalizer_of_lt hTp hPT
      have hsub : T ⊓ Subgroup.normalizer (P : Set G) ≤
          H ⊓ Subgroup.normalizer (P : Set G) :=
        le_inf (inf_le_left.trans hTH) inf_le_right
      exact hlt.ne (hkey _ hsub hTp.to_inf_left hlt.le).symm
    have hSylH' : IsSylowIn p P H := ⟨hPp, hPleH, hSylH⟩
    have hPleW : P ≤ W := h.P_le.trans (inf_le_left.trans inf_le_left)
    have hPsylW : IsSylowIn p P W := sylowIn_of_le_of_le hSylH' hPleW h.le
    -- `N_W(P) ≤ C_G(P)` in the ambient group
    have hPpW : IsPGroup p (P.subgroupOf W) :=
      hPsylW.1.comap_of_injective W.subtype W.subtype_injective
    have hNW_le_CG : (Subgroup.normalizer (P : Set G)).subgroupOf W ≤
        (Subgroup.centralizer (P : Set G)).subgroupOf W := by
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact hNH_le_C (Subgroup.mem_inf.mpr ⟨h.le x.2, hx⟩)
    -- the Burnside hypothesis inside `↥W`
    have hBurnHyp : Subgroup.normalizer
          ((hPpW.toSylow hPsylW.2.2 : Sylow p ↥W) : Set ↥W) ≤
        Subgroup.centralizer ((hPpW.toSylow hPsylW.2.2 : Sylow p ↥W) : Set ↥W) := by
      have hcoe : ((hPpW.toSylow hPsylW.2.2 : Sylow p ↥W) : Set ↥W) =
          (P.subgroupOf W : Set ↥W) :=
        congrArg (fun K : Subgroup ↥W => (K : Set ↥W))
          (IsPGroup.toSylow_coe hPpW hPsylW.2.2)
      rw [hcoe, ← Subgroup.subgroupOf_normalizer_eq (H := P) hPsylW.2.1]
      refine hNW_le_CG.trans ?_
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyP : (y : G) ∈ P := by simpa [Subgroup.mem_subgroupOf] using hy
      have hxy : (y : G) * (x : G) = (x : G) * (y : G) :=
        (Subgroup.mem_centralizer_iff.mp hx) (y : G) hyP
      exact Subtype.ext hxy
    have hburn : Work.NPC.HasNormalPComplement p ↥W :=
      Work.NPC.burnside_npc (hPpW.toSylow hPsylW.2.2) hBurnHyp
    obtain ⟨Nn, hNn⟩ := hburn
    haveI : Nn.Normal := hNn.normal
    have hNne : Nn ≠ ⊤ := by
      intro htop
      have hpW : p ∣ Nat.card ↥W := by
        have hd := Subgroup.card_dvd_of_le (H := P) (K := W) hPsylW.2.1
        rwa [h.P_card] at hd
      have hpd : p ∣ Nat.card Nn := by rw [htop, Subgroup.card_top]; exact hpW
      have hp1 : p ∣ 1 := by
        have hg : Nat.gcd (Nat.card Nn) p = 1 := hNn.coprime_card
        rw [← hg]; exact Nat.dvd_gcd hpd (dvd_refl p)
      exact h.prime.ne_one (Nat.dvd_one.mp hp1)
    -- `O^p(W) ≤ Nn`, hence `O^p(W) < W`
    have hprN : Work.NPC.Frobenius.pResidual p ↥W ≤ Nn := by
      rw [Work.NPC.Frobenius.pResidual, Subgroup.closure_le]
      rintro x hx
      have hdvd : orderOf ((QuotientGroup.mk' Nn) x) ∣ orderOf x := by
        apply orderOf_dvd_of_pow_eq_one
        rw [← map_pow, pow_orderOf_eq_one, map_one]
      obtain ⟨kk, hkk⟩ := (IsPGroup.iff_orderOf.mp hNn.isPGroup_quotient)
        ((QuotientGroup.mk' Nn) x)
      have hpk : p ^ kk ∣ orderOf x := hkk ▸ hdvd
      have hk0 : kk = 0 := by
        by_contra hk
        have hpkk : p ∣ p ^ kk := by
          simpa using (pow_dvd_pow p (Nat.one_le_iff_ne_zero.mpr hk) : p ^ 1 ∣ p ^ kk)
        exact hx (hpkk.trans hpk)
      have hone : (QuotientGroup.mk' Nn) x = 1 := by
        rw [← orderOf_eq_one_iff, hkk, hk0, pow_zero]
      rw [← QuotientGroup.ker_mk' Nn]
      exact MonoidHom.mem_ker.mpr hone
    have hpr_lt : Work.Grun.pResidual p W < W := by
      have hle : Work.Grun.pResidual p W ≤ Nn.map W.subtype := by
        rw [Work.Grun.pResidual_eq_map_pResidual p W]
        exact Subgroup.map_mono hprN
      have hlt : Nn.map W.subtype < W := by
        refine lt_of_le_of_ne (Subgroup.map_subtype_le _) ?_
        intro heq
        apply hNne
        rw [eq_top_iff]
        intro x _
        have hxW : (x : G) ∈ Nn.map W.subtype := by rw [heq]; exact x.2
        obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.mp hxW
        have hnx' : n = x := Subtype.ext hnx
        rw [← hnx']; exact hn
      exact lt_of_le_of_lt hle hlt
    have hpr_ne : ¬ W ≤ Work.Grun.pResidual p W := hpr_lt.2
    obtain ⟨y, hyW, hyK⟩ := Set.not_subset.mp hpr_ne
    have hEidx : ¬ p ∣ ((Design.Egrp H t W).subgroupOf W).index := by
      intro hd
      have hle : (P.subgroupOf W) ≤ (Design.Egrp H t W).subgroupOf W := by
        intro z hz
        rw [Subgroup.mem_subgroupOf] at hz ⊢
        exact (h.P_le hz).1
      exact hPsylW.2.2 (hd.trans (Subgroup.index_dvd_of_le hle))
    obtain ⟨W₁, hW₁lt, hW₁H, hHW₁, hW₁D⟩ :=
      pResidual_strategy (p := p) (E := Design.Egrp H t W) (W := W)
        (D := Submission.Blueprint.twoPoint H t) (H := H) (y := y)
        inf_le_left inf_le_right hEidx h.le h.normal h.sup hyW hyK
    have hcard := h.minW.2.2.2 W₁ hW₁H hHW₁ hW₁D
    have hcardlt : Nat.card ↥W₁ < Nat.card ↥W := by
      refine Nat.lt_of_le_of_ne
        (Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hW₁lt.1)) ?_
      intro heq
      have hWW₁ : W ≤ W₁ :=
        le_of_eq (Subgroup.eq_of_le_of_card_ge hW₁lt.1 (le_of_eq heq.symm)).symm
      exact hW₁lt.2 hWW₁
    omega

end Work.NormalComplement
