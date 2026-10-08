/-
# Ch. III §4 Prop. 2 (a): `E = K[A,P]P`, `E' = K[A,P]`, `E' ⊓ V = [A,P]`

This module proves `Work.NormalComplement.NC4.prop2a`, Peterfalvi I Ch. III §4 Proposition 2 (a)
(p.181), from the intermediate conclusions `Lemma1dConc` (Lemma 1 (d): `P` is a `p`-Sylow of `D`
and `E = E' ⋊ P`) and `Prop1Conc` (Prop. 1: `C_A(P)` is a Hall `π`-subgroup of `D`,
`⟨K⟩ ⊓ V ≤ [A,P]` and `⟨K⟩[A,P]P` is a normal complement of `C_A(P)` in `D`).

Notation: `D = twoPoint H t`, `E = Egrp H t W = W ⊓ D`, `E' = Ecomm H t W = ⁅E,E⁆`,
`V = centD H t = C_D(t)`, `C = C_A(P) = A ⊓ C_G(P)`, `K = Kset D t`, `Kg = ⟨K⟩ = Kgrp D t`,
`N = Kg[A,P]P`, `X = E ⊓ C`.

Route (the source's, with the missing details supplied):

* **Frattini.** `P` is a `p`-Sylow of `E` (Lemma 1 (d) and `P ≤ E`), so `D = E·N_D(P)`; Lemma 1 (c)
  (`sec4_one_c`) gives `N_D(P) = C·P`, and `P ≤ E` turns this into `D = E·C`. Hence
  `A = (E ⊓ A)·C` and, since `C` centralises `P`, `[A,P] = [E ⊓ A, P] ≤ [E,E] = E'`.
* **`X ≤ E'`.** `X ≤ E ⊓ C_D(P) = C_E(P) = C_{E'}(P)·P` (via `E = E'·P`), so `x ∈ X` is `y·p`
  with `y ∈ E'`, `p ∈ P`; `x^p = (y·p)^p ∈ E'·⟨p⟩^p = E'` (the auxiliary
  `pow_mul_mem_of_le_normalizer`), and `x` has order prime to `p` (all prime divisors of
  `|C_A(P)|` are in `π`, so `≠ p`), so `x ∈ ⟨x^p⟩ ≤ E'` by `mem_zpowers_pow_iff`.
* **`N ≤ E`.** `Kg ≤ E'` (Ch. III §2 Lemma 1 = `sec2_lemma1`), `[A,P] ≤ E'`, `P ≤ E`.
* **Counting.** `|E| = |N|·|X|` from `|D| = |E||C|/|E ⊓ C| = |N||C|`; since `N ⊴ D` and
  `N ⊓ X = ⊥` this gives `E = N ⊔ X`.
* **`E' ≤ N ⊔ [X,X]`.** `E = N ⊔ X` with `N ⊴ E`: every commutator of `E` is a product of
  `N`-elements and conjugates of commutators of `X` (the identities
  `⁅a*b,c⁆ = a⁅b,c⁆a⁻¹·⁅a,c⁆`, `⁅a,b*c⁆ = ⁅a,b⁆·b⁅a,c⁆b⁻¹`).
* **`X = 1`.** `X ≤ E' ≤ N ⊔ [X,X]` and `X ⊓ N = ⊥` give `X = [X,X]`; `X ≤ D` is solvable
  (`hFT`, `|D|` odd), and a solvable group equal to its commutator subgroup is trivial.
* **Conclusion.** `E = N`; `E' ⊇ Kg[A,P]` and `E' ≤ N = (Kg ⊔ [A,P]) ⊔ P` with `E' ⊓ P = ⊥` give
  `E' = Kg ⊔ [A,P]`; finally `E' ⊓ V = (Kg ⊓ V) ⊔ [A,P] = [A,P]` by `Prop1Conc`'s `Kg ⊓ V ≤ [A,P]`.
-/
import Mathlib
import Submission.Work.NormalComplement.NC4.Defs
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.sec4_one_c
import Submission.Work.NormalComplement.card_sup_mul_card_inf
import Submission.Work.NormalComplement.appI_five_d_corrected

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.NormalComplement.Design

namespace Work.NormalComplement.NC4

variable {G : Type*} [Group G] [Finite G]

/-- Auxiliary: if `Y ≤ N_G(A)`, `y ∈ A` and `p ∈ Y`, then `(y*p)^n` is of the form `s * p^n`
with `s ∈ A`. -/
lemma pow_mul_mem_of_le_normalizer {A Y : Subgroup G} (hAY : Y ≤ Subgroup.normalizer (A : Set G))
    {y p : G} (hy : y ∈ A) (hp : p ∈ Y) :
    ∀ n : ℕ, ∃ s ∈ A, (y * p) ^ n = s * p ^ n := by
  have hconj : ∀ m : ℕ, p ^ m * y * (p ^ m)⁻¹ ∈ A := by
    intro m
    induction m with
    | zero => simpa using hy
    | succ m ih =>
        have hstep : p ^ (m + 1) * y * (p ^ (m + 1))⁻¹ = p * (p ^ m * y * (p ^ m)⁻¹) * p⁻¹ := by
          group
        rw [hstep]
        exact (Subgroup.mem_normalizer_iff.mp (hAY hp) _).mp ih
  intro n
  induction n with
  | zero => exact ⟨1, A.one_mem, by simp⟩
  | succ n ih =>
      obtain ⟨s, hs, hsn⟩ := ih
      refine ⟨s * (p ^ n * y * (p ^ n)⁻¹), A.mul_mem hs (hconj n), ?_⟩
      rw [pow_succ, hsn, pow_succ]
      group

/-- A finite solvable group that equals its own commutator subgroup is trivial. -/
lemma eq_bot_of_isSolvable_commutator_eq_self (X : Subgroup G) (hS : Group.IsSolvable ↥X)
    (h : ⁅X, X⁆ = X) : X = ⊥ := by
  by_contra hne
  haveI : Group.IsSolvable ↥X := hS
  haveI : Nontrivial ↥X := (Subgroup.nontrivial_iff_ne_bot X).mpr hne
  have hlt := Group.IsSolvable.commutator_lt_of_ne_bot (G := ↥X) (H := ⊤) (by simp)
  have htop : (⁅(⊤ : Subgroup ↥X), ⊤⁆ : Subgroup ↥X) = ⊤ := by
    apply Subgroup.map_subtype_inj.mp
    simp only [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    exact h
  rw [htop] at hlt
  exact lt_irrefl _ hlt

theorem prop2a (hFT : Submission.Blueprint.FeitThompsonProp) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G}
    (h : Work.NormalComplement.Design.Setup45A G H t W p P A)
    (h1d : Work.NormalComplement.NC4.Lemma1dConc H t W p P A)
    (hP1 : Work.NormalComplement.NC4.Prop1Conc H t W p P A) :
    Work.NormalComplement.NC4.Prop2aConc H t W p P A := by
  have hp : p.Prime := h.prime
  -- ## abbreviations (local definitions, so that the statements below stay readable)
  let D : Subgroup G := twoPoint H t
  let E : Subgroup G := Egrp H t W
  let E' : Subgroup G := Ecomm H t W
  let V : Subgroup G := centD H t
  let C : Subgroup G := A ⊓ Subgroup.centralizer (P : Set G)
  let Kg : Subgroup G := Kgrp (twoPoint H t) t
  let N : Subgroup G := (Kg ⊔ ⁅A, P⁆) ⊔ P
  let X : Subgroup G := E ⊓ C
  -- ## elementary consequences
  have hD_odd : Odd (Nat.card ↥D) := h.se.2.2 t h.notMem
  have hD_solv : Group.IsSolvable ↥D := hFT ↥D hD_odd
  have hE_le_D : E ≤ D := inf_le_right
  have hV_le_D : V ≤ D := inf_le_left
  have hA_le_V : A ≤ V := h.A_le
  have hC_le_A : C ≤ A := inf_le_left
  have hC_le_cent : C ≤ Subgroup.centralizer (P : Set G) := inf_le_right
  have hC_le_V : C ≤ V := hC_le_A.trans hA_le_V
  have hE'_le_E : E' ≤ E :=
    (Subgroup.commutator_le_sup (Egrp H t W) (Egrp H t W)).trans (le_of_eq (sup_idem _))
  have hE_sup : E' ⊔ P = E := h1d.2.2
  have hE_inf_P : E' ⊓ P = ⊥ := h1d.2.1
  have hP_le_E : P ≤ E := hE_sup ▸ le_sup_right
  have hP_le_V : P ≤ V := le_trans h.P_le inf_le_right
  have hP_sylowD : IsSylowIn p P D := h1d.1
  have hP_sylowE : IsSylowIn p P E :=
    Work.NormalComplement.sylowIn_of_le_of_le hP_sylowD hP_le_E hE_le_D
  have hAP_le_V : ⁅A, P⁆ ≤ V := (Subgroup.commutator_le_sup A P).trans (le_of_eq h.A_sup)
  -- `E` is normalised by `D`
  have hE_norm : D ≤ Subgroup.normalizer (E : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro d hd x hx
    obtain ⟨hxW, hxD⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_normalizer_iff.mp (h.normal hd.1) x).mp hxW,
       (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (H := D) hd) x).mp hxD⟩
  -- the normal complement data from Proposition 1
  have hN_le_D : N ≤ D := hP1.2.2.2.1
  have hD_le_NG_N : D ≤ Subgroup.normalizer (N : Set G) := hP1.2.2.2.2.1
  have hN_inf_C : N ⊓ C = ⊥ := hP1.2.2.2.2.2.1
  have hN_sup_C : N ⊔ C = D := hP1.2.2.2.2.2.2
  have hKg_inf_V_le : Kg ⊓ V ≤ ⁅A, P⁆ := hP1.2.2.1
  have hX_le_E : X ≤ E := inf_le_left
  have hX_le_NG_N : X ≤ Subgroup.normalizer (N : Set G) :=
    le_trans (le_trans hX_le_E hE_le_D) hD_le_NG_N
  -- ## `E' = ⁅E,E⁆` is normalised by `E`
  have hE'_norm : E ≤ Subgroup.normalizer (E' : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro e he k hk
    have hconj : ∀ x ∈ Egrp H t W, e * x * e⁻¹ ∈ Egrp H t W := by
      intro x hx
      obtain ⟨hxW, hxD⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr
        ⟨(Subgroup.mem_normalizer_iff.mp (h.normal (hE_le_D he).1) x).mp hxW,
         (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (hE_le_D he)) x).mp hxD⟩
    have hle : (Egrp H t W).map (MulAut.conj e).toMonoidHom ≤ Egrp H t W := by
      rw [Subgroup.map_le_iff_le_comap]
      intro x hx
      simpa [MulAut.conj_apply] using hconj x hx
    have hmapE : (Egrp H t W).map (MulAut.conj e).toMonoidHom = Egrp H t W :=
      Subgroup.eq_of_le_of_card_ge hle
        (le_of_eq (Subgroup.card_map_of_injective (MulAut.conj e).injective).symm)
    have hmap : (⁅Egrp H t W, Egrp H t W⁆).map (MulAut.conj e).toMonoidHom
        = ⁅Egrp H t W, Egrp H t W⁆ := by
      rw [Subgroup.map_commutator, hmapE]
    have h1 : e * k * e⁻¹ ∈ (⁅Egrp H t W, Egrp H t W⁆).map (MulAut.conj e).toMonoidHom := by
      refine Subgroup.mem_map.mpr ⟨k, hk, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rwa [hmap] at h1
  have hP_norm_E' : P ≤ Subgroup.normalizer (E' : Set G) := hP_le_E.trans hE'_norm
  -- ## `Kg = ⟨K⟩` is normalised by `D`  (App. I (4))
  have htD : NormalizedBy t D := by
    show NormalizedBy t (twoPoint H t)
    exact Work.NormalComplement.twoPoint_normalizedBy
      (Work.NormalComplement.twoPoint_mul_self h.invol)
  have hcopD : Nat.Coprime (Nat.card ↥D) 2 := Nat.coprime_two_right.mpr hD_odd
  have hKapp : Kapp t D = Kset D t :=
    ((appI_one (d := 2) Nat.prime_two h.invol htD hcopD).2 rfl).1
  have hKg_eq : Kg = Subgroup.closure (Kapp t D) := by
    show Subgroup.closure (Kset D t) = Subgroup.closure (Kapp t D)
    rw [hKapp]
  have hKg_norm_D : D ≤ Subgroup.normalizer (Kg : Set G) := by
    have h4 := appI_four (X := D) (d := 2) Nat.prime_two h.invol htD hcopD
    intro d hd
    rw [hKg_eq, Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      exact h4.2.2.1 d hd k hk
    · intro hk
      have h1 := h4.2.2.1 d⁻¹ (D.inv_mem hd) (d * k * d⁻¹) hk
      rwa [show d⁻¹ * (d * k * d⁻¹) * (d⁻¹)⁻¹ = k from by group] at h1
  have hP_norm_AP : P ≤ Subgroup.normalizer ((⁅A, P⁆ : Subgroup G) : Set G) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator]
    have h1 : Subgroup.map (MulAut.conj q) A = A :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (h.A_normal (hP_le_V hq))
    have h2 : Subgroup.map (MulAut.conj q) P = P :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hq)
    rw [h1, h2]
  have hAP_le_norm_Kg : ⁅A, P⁆ ≤ Subgroup.normalizer (Kg : Set G) :=
    (Subgroup.commutator_le_sup A P).trans (le_trans (le_of_eq h.A_sup)
      (le_trans hV_le_D hKg_norm_D))
  have hP_norm_M : P ≤ Subgroup.normalizer ((Kg ⊔ ⁅A, P⁆ : Subgroup G) : Set G) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hKg_norm_D (le_trans hP_le_V hV_le_D hq)),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hP_norm_AP hq)]
  -- ## `C` is centralised by `P`
  have hC_comm : ∀ c ∈ C, ∀ q ∈ P, c * q = q * c :=
    fun c hc q hq => (Subgroup.mem_centralizer_iff.mp (hC_le_cent hc) q hq).symm
  have hP_norm_C : P ≤ Subgroup.normalizer (C : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro q hq c hc
    have h1 : q * c * q⁻¹ = c := by rw [← hC_comm c hc q hq]; group
    rw [h1]
    exact hc
  have hC_norm_E : C ≤ Subgroup.normalizer (E : Set G) := hC_le_V.trans (hV_le_D.trans hE_norm)
  -- ## Frattini: `D = E ⊔ C`
  have hD_eq_sup : D = E ⊔ C := by
    refine le_antisymm ?_ (sup_le hE_le_D (hC_le_V.trans hV_le_D))
    intro b hb
    obtain ⟨m, hm, n, hn, hmn⟩ := Work.NormalComplement.frattini_decomp hp hE_le_D
      (fun y hy m hm => (Subgroup.mem_normalizer_iff.mp (hE_norm hy) m).mp hm) hP_sylowE b hb
    have hn1 : n ∈ D ⊓ Subgroup.normalizer (P : Set G) := Subgroup.mem_inf.mpr ⟨hn.2, hn.1⟩
    have hNDP : D ⊓ Subgroup.normalizer (P : Set G) = C ⊔ P := (sec4_one_c hFT h).1
    have hn2 : n ∈ C ⊔ P := hNDP ▸ hn1
    obtain ⟨c, hc, q, hq, hcq⟩ := (Work.NormalComplement.mem_sup_mul hP_norm_C).mp hn2
    refine (Work.NormalComplement.mem_sup_mul hC_norm_E).mpr
      ⟨m * q, E.mul_mem hm (hP_le_E hq), c, hc, ?_⟩
    rw [hmn, hcq, show m * (c * q) = (m * q) * c by rw [hC_comm c hc q hq]; group]
  -- ## `A = (E ⊓ A) · C`
  have hA_decomp : ∀ a ∈ A, ∃ e ∈ E, ∃ c ∈ C, a = e * c := by
    intro a ha
    have haEC : a ∈ E ⊔ C := by
      rw [← hD_eq_sup]
      exact hA_le_V.trans hV_le_D ha
    exact (Work.NormalComplement.mem_sup_mul hC_norm_E).mp haEC
  -- ## `[A,P] ≤ E'`
  have hAP_le_E' : ⁅A, P⁆ ≤ E' := by
    rw [Subgroup.commutator_le]
    intro a ha q hq
    obtain ⟨e, he, c, hc, rfl⟩ := hA_decomp a ha
    have hcq : ⁅c, q⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact hC_comm c hc q hq
    rw [commutatorElement_mul_left_eq_conj_mul, hcq, mul_one]
    have hsimp : e * e⁻¹ * ⁅e, q⁆ = ⁅e, q⁆ := by group
    rw [hsimp]
    exact Subgroup.commutator_mem_commutator he (hP_le_E hq)
  -- ## `Kg ≤ E'`  (Ch. III §2 Lemma 1, here from App. I (5)(d))
  have hP_ne_bot : P ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥P = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [h.P_card] at h1
    exact hp.ne_one h1
  have hKset : Kset (twoPoint H t) t ⊆ (Ecomm H t W : Set G) := by
    have hCK : ∀ k ∈ Kapp t D, (∀ q ∈ P, q * k * q⁻¹ = k) → k = 1 := by
      intro k hk hfix
      haveI : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).mpr hP_ne_bot
      obtain ⟨q, hq⟩ := exists_ne (1 : ↥P)
      have hqP : (q : G) ∈ P := q.2
      have hqne : (q : G) ≠ 1 := fun hc => hq (Subtype.ext hc)
      exact h.P_fpf (q : G) hqP hqne k (by rw [← hKapp]; exact hk) (hfix (q : G) hqP)
    have h1 : Kapp t D ⊆ ((⁅Egrp H t W, Egrp H t W⁆ : Subgroup G) : Set G) :=
      (appI_five_d_corrected (X := D) (E := Egrp H t W) (P := P) (p := p)
        h.invol htD hD_odd hD_solv hE_le_D
        (fun x hx e he => (Subgroup.mem_normalizer_iff.mp (hE_norm hx) e).mp he)
        hP_sylowE (le_inf (hP_le_V.trans inf_le_right) (hP_le_E.trans hE_le_D)) hp hCK).1
    intro x hx
    exact h1 (by rw [hKapp]; exact hx)
  have hKg_le_E' : Kg ≤ E' := (Subgroup.closure_le (Ecomm H t W)).mpr hKset
  -- ## `p ∤ |C|`
  have hp_not_dvd_C : ¬ p ∣ Nat.card ↥C := by
    intro hd
    exact (hP1.1 p hp hd).2.2.1 rfl
  -- ## `X ≤ E'`
  have hX_le_E' : X ≤ E' := by
    intro x hx
    obtain ⟨hxE, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxsup : x ∈ E' ⊔ P := hE_sup ▸ hxE
    obtain ⟨y, hy, q, hq, hyq⟩ := (Work.NormalComplement.mem_sup_mul hP_norm_E').mp hxsup
    have hqE : q ∈ E := hP_le_E hq
    have hxp : x ^ p ∈ E' := by
      obtain ⟨s, hs, hs'⟩ := pow_mul_mem_of_le_normalizer (A := E') (Y := E) hE'_norm hy hqE p
      have hqp : q ^ p = 1 := by
        rw [← orderOf_dvd_iff_pow_eq_one]
        exact h.P_card ▸ Subgroup.orderOf_dvd_natCard P hq
      rw [hyq, hs', hqp, mul_one]
      exact hs
    have hxmem : x ∈ Subgroup.zpowers (x ^ p) := by
      rw [mem_zpowers_pow_iff]
      exact ((hp.coprime_iff_not_dvd).mpr (fun hd =>
        hp_not_dvd_C (hd.trans (Subgroup.orderOf_dvd_natCard C hxC)))).gcd_eq_one
    exact (Subgroup.zpowers_le.mpr hxp) hxmem
  -- ## `N ≤ E`
  have hN_le_E : N ≤ E :=
    sup_le (sup_le (hKg_le_E'.trans hE'_le_E) (hAP_le_E'.trans hE'_le_E)) hP_le_E
  -- ## cardinality: `|E| = |N| * |X|`
  have hcardD' : Nat.card ↥D * Nat.card ↥X = Nat.card ↥E * Nat.card ↥C := by
    have h1 := Work.NormalComplement.card_sup_mul_card_inf (H := E) (K := C) hC_norm_E
    rw [← hD_eq_sup] at h1
    exact h1
  have hcardNC : Nat.card ↥D = Nat.card ↥N * Nat.card ↥C := by
    have h1 := Work.NormalComplement.card_sup_mul_card_inf (H := N) (K := C)
      (le_trans hC_le_V (le_trans hV_le_D hD_le_NG_N))
    rw [hN_sup_C, hN_inf_C, Subgroup.card_bot, mul_one] at h1
    exact h1
  have hcardE : Nat.card ↥E = Nat.card ↥N * Nat.card ↥X := by
    have h1 : Nat.card ↥E * Nat.card ↥C = (Nat.card ↥N * Nat.card ↥X) * Nat.card ↥C := by
      rw [← hcardD', hcardNC]
      ring
    exact Nat.mul_right_cancel Nat.card_pos h1
  have hX_inf_N : X ⊓ N = ⊥ := by
    have h1 : X ⊓ N ≤ C ⊓ N := fun x hx => by
      obtain ⟨hxX, hxN⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨hxX.2, hxN⟩
    have h2 : C ⊓ N = ⊥ := by rw [inf_comm]; exact hN_inf_C
    exact le_bot_iff.mp (h1.trans (le_of_eq h2))
  have hN_sup_X_card : Nat.card ↥(N ⊔ X) = Nat.card ↥N * Nat.card ↥X := by
    have h1 := Work.NormalComplement.card_sup_mul_card_inf (H := N) (K := X) hX_le_NG_N
    rw [inf_comm N X, hX_inf_N, Subgroup.card_bot, mul_one] at h1
    exact h1
  have hN_sup_X_eq : N ⊔ X = E :=
    Subgroup.eq_of_le_of_card_ge (sup_le hN_le_E hX_le_E) (by rw [hN_sup_X_card, ← hcardE])
  -- ## `⁅N ⊔ X, N ⊔ X⁆ ≤ N ⊔ ⁅X,X⁆`
  have hcomm_key : ⁅N ⊔ X, N ⊔ X⁆ ≤ N ⊔ ⁅X, X⁆ := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨n₁, hn₁, x₁, hx₁, rfl⟩ := (Work.NormalComplement.mem_sup_mul hX_le_NG_N).mp ha
    obtain ⟨n₂, hn₂, x₂, hx₂, rfl⟩ := (Work.NormalComplement.mem_sup_mul hX_le_NG_N).mp hb
    have hNE : N ≤ N ⊔ ⁅X, X⁆ := le_sup_left
    have hXXE : ⁅X, X⁆ ≤ N ⊔ ⁅X, X⁆ := le_sup_right
    have hx₁E : x₁ ∈ E := hX_le_E hx₁
    have hx₂E : x₂ ∈ E := hX_le_E hx₂
    have hcore : ∀ u ∈ E, ∀ w ∈ N, ⁅u, w⁆ ∈ N := by
      intro u hu w hw
      rw [commutatorElement_def]
      exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp (hD_le_NG_N (hE_le_D hu)) w).mp hw)
        (N.inv_mem hw)
    have hm1 : n₁ ∈ N ⊔ ⁅X, X⁆ := hNE hn₁
    have hm2 : n₂ ∈ N ⊔ ⁅X, X⁆ := hNE hn₂
    have hm3 : n₁⁻¹ ∈ N ⊔ ⁅X, X⁆ := (N ⊔ ⁅X, X⁆).inv_mem hm1
    have hm4 : n₂⁻¹ ∈ N ⊔ ⁅X, X⁆ := (N ⊔ ⁅X, X⁆).inv_mem hm2
    have hm5 : ⁅x₁, n₂⁆ ∈ N ⊔ ⁅X, X⁆ := hNE (hcore x₁ hx₁E n₂ hn₂)
    have hm6 : ⁅x₁, x₂⁆ ∈ N ⊔ ⁅X, X⁆ := hXXE (Subgroup.commutator_mem_commutator hx₁ hx₂)
    have hm7 : ⁅n₁, n₂⁆ ∈ N ⊔ ⁅X, X⁆ := hNE (hcore n₁ (hN_le_E hn₁) n₂ hn₂)
    have hcore' : ∀ w ∈ N, ∀ u ∈ E, ⁅w, u⁆ ∈ N := by
      intro w hw u hu
      rw [← commutatorElement_inv]
      exact N.inv_mem (hcore u hu w hw)
    have hm8 : ⁅n₁, x₂⁆ ∈ N ⊔ ⁅X, X⁆ := hNE (hcore' n₁ hn₁ x₂ hx₂E)
    have hstep : ⁅n₁ * x₁, n₂ * x₂⁆
        = n₁ * (⁅x₁, n₂⁆ * n₂ * ⁅x₁, x₂⁆ * n₂⁻¹) * n₁⁻¹
            * (⁅n₁, n₂⁆ * n₂ * ⁅n₁, x₂⁆ * n₂⁻¹) := by
      rw [commutatorElement_mul_left_eq_conj_mul n₁ x₁ (n₂ * x₂),
        commutatorElement_mul_right_eq_mul_conj x₁ n₂ x₂,
        commutatorElement_mul_right_eq_mul_conj n₁ n₂ x₂]
    rw [hstep]
    have hY : ∀ {a b : G}, a ∈ N ⊔ ⁅X, X⁆ → b ∈ N ⊔ ⁅X, X⁆ → a * b ∈ N ⊔ ⁅X, X⁆ :=
      fun ha hb => (N ⊔ ⁅X, X⁆).mul_mem ha hb
    have hA : ⁅x₁, n₂⁆ * n₂ * ⁅x₁, x₂⁆ * n₂⁻¹ ∈ N ⊔ ⁅X, X⁆ :=
      hY (hY (hY hm5 hm2) hm6) hm4
    have hB : ⁅n₁, n₂⁆ * n₂ * ⁅n₁, x₂⁆ * n₂⁻¹ ∈ N ⊔ ⁅X, X⁆ :=
      hY (hY (hY hm7 hm2) hm8) hm4
    exact hY (hY (hY hm1 hA) hm3) hB
  have hEE_le : E' ≤ N ⊔ ⁅X, X⁆ := by
    have h1 : ⁅E, E⁆ = ⁅N ⊔ X, N ⊔ X⁆ := by rw [hN_sup_X_eq]
    rw [show E' = ⁅E, E⁆ from rfl, h1]
    exact hcomm_key
  -- ## `X = [X,X]`
  have hXX_le_X : ⁅X, X⁆ ≤ X :=
    (Subgroup.commutator_le_sup X X).trans (le_of_eq (sup_idem X))
  have hXX_le_NG_N : ⁅X, X⁆ ≤ Subgroup.normalizer (N : Set G) :=
    hXX_le_X.trans hX_le_E |>.trans (le_trans hE_le_D hD_le_NG_N)
  have hX_le_XX : X ≤ ⁅X, X⁆ := by
    intro x hx
    have h1 : x ∈ N ⊔ ⁅X, X⁆ := hEE_le (hX_le_E' hx)
    obtain ⟨n, hn, y, hy, hny⟩ := (Work.NormalComplement.mem_sup_mul hXX_le_NG_N).mp h1
    have hnX : n ∈ X := by
      have h1 : n * y ∈ X := by rw [← hny]; exact hx
      have h2 : (n * y) * y⁻¹ ∈ X := X.mul_mem h1 (X.inv_mem (hXX_le_X hy))
      have h3 : (n * y) * y⁻¹ = n := by group
      rwa [h3] at h2
    have hnbot : n = 1 := Subgroup.mem_bot.mp (by
      have hmem : n ∈ X ⊓ N := Subgroup.mem_inf.mpr ⟨hnX, hn⟩
      rwa [hX_inf_N] at hmem)
    rw [hnbot, one_mul] at hny
    rw [hny]
    exact hy
  have hX_eq_XX : X = ⁅X, X⁆ := le_antisymm hX_le_XX hXX_le_X
  -- ## `X = ⊥`
  have hX_solv : Group.IsSolvable ↥X :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (show X ≤ D from hX_le_E.trans hE_le_D))
      (Subgroup.inclusion_injective _)
  have hX_bot : X = ⊥ := eq_bot_of_isSolvable_commutator_eq_self X hX_solv hX_eq_XX.symm
  -- ## conclusion
  have hE_eq_N : E = N := by
    rw [← hN_sup_X_eq, hX_bot, sup_bot_eq]
  have hM_le : Kg ⊔ ⁅A, P⁆ ≤ E' := sup_le hKg_le_E' hAP_le_E'
  have hE'_le_M : E' ≤ Kg ⊔ ⁅A, P⁆ := by
    have h1 : E' ≤ (Kg ⊔ ⁅A, P⁆) ⊔ P := by
      have h2 : E' ≤ N ⊔ ⁅X, X⁆ := hEE_le
      rw [hX_bot] at h2
      simpa using h2
    intro e he
    have he1 : e ∈ (Kg ⊔ ⁅A, P⁆) ⊔ P := h1 he
    obtain ⟨m, hm, q, hq, hmq⟩ := (Work.NormalComplement.mem_sup_mul hP_norm_M).mp he1
    have hqE' : q ∈ E' := by
      have h3 : m⁻¹ * e ∈ E' := E'.mul_mem (E'.inv_mem (hM_le hm)) he
      rw [hmq, inv_mul_cancel_left] at h3
      exact h3
    have hq1 : q = 1 := Subgroup.mem_bot.mp (by
      have h4 : q ∈ E' ⊓ P := Subgroup.mem_inf.mpr ⟨hqE', hq⟩
      rwa [hE_inf_P] at h4)
    rw [hq1, mul_one] at hmq
    rw [hmq]
    exact hm
  have hE'_eq' : E' = Kg ⊔ ⁅A, P⁆ := le_antisymm hE'_le_M hM_le
  refine ⟨?_, ?_, ?_⟩
  · show E = N
    exact hE_eq_N
  · show E' = Kg ⊔ ⁅A, P⁆
    exact hE'_eq'
  · show E' ⊓ V = ⁅A, P⁆
    refine le_antisymm ?_ (le_inf hAP_le_E' hAP_le_V)
    intro x hx
    obtain ⟨hxE', hxV⟩ := Subgroup.mem_inf.mp hx
    rw [hE'_eq'] at hxE'
    obtain ⟨k, hk, a, ha, hka⟩ := (Work.NormalComplement.mem_sup_mul hAP_le_norm_Kg).mp hxE'
    have hkV : k ∈ V := by
      have h1 : x * a⁻¹ ∈ V := V.mul_mem hxV (V.inv_mem (hAP_le_V ha))
      have h2 : (k * a) * a⁻¹ = k := by group
      rwa [hka, h2] at h1
    have hk2 : k ∈ Kg ⊓ V := Subgroup.mem_inf.mpr ⟨hk, hkV⟩
    have hk3 : k ∈ ⁅A, P⁆ := hP1.2.2.1 hk2
    rw [hka]
    exact ⁅A, P⁆ |>.mul_mem hk3 ha

end Work.NormalComplement.NC4
