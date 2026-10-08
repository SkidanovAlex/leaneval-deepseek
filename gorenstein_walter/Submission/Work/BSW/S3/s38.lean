/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, §3 leaves)

# BSW §3, leaf 3.8: `IsBSWData G (2k − 1)`

Target: `Work.BSW.S3.s38 : Work.BSW.BSWS38Prop` (Bender 1974, (3.8)): under the case-(ii)
bundle `BSWCase2` the group carries Bender's conclusion (1)–(4) with `q = 2|K| − 1`.

Bender's argument (p. 235):

* choose `Q` of order `q = 2k−1` so that `N_G(Q) = QD` with `D` a subgroup of `F = C_G(x)` or of
  `K` — (3.6);
* by (3.7), `G`-conjugation inside `Q` is already `N_G(Q)`-conjugation, so `C_G(a) = Q` for
  `a ∈ Q♯`; hence `Q` is abelian and `C_G(Q) = Q`;
* `2|D| = q − 1`, i.e. `|D| = k − 1`, and `D = F^g` because `k − 1 ∤ k`;
* (4) holds because `C_G(X) = F` for every `1 ≠ X ≤ F` and `N_G(F) = F⟨t⟩` with `t` inverting
  `F`.

The counting that pins `|D|` is made explicit here: with `n = |G : N_G(Q)|`, `d = |D|`,
`q = 2k − 1` we have `n·d = 2k(k−1)` (orders), `q ∣ n − 1` (the free action of `Q` on the
conjugates of `Q`, a consequence of (3.7)), and `d ∣ k(k−1)` (the conjugacy clause of (3.6));
that forces `d = k − 1` and `n = 2k`.
-/
import Mathlib
import Submission.Work.BSW.S3.Defs
import Submission.Work.BSW.S3.s36
import Submission.Work.BSW.S3.s37
import Submission.Work.BSW.S3.s36aux
import Submission.Work.BSW.S3.bswCompletionPropFromLeaves
import Submission.Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot

namespace Work.BSW.S3

open Subgroup Work.GW2

variable {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G} {x : G} {p : ℕ}

/-! ## §3.8, the pure arithmetic core -/

private lemma s38_arith_B {k d n : ℕ} (hk : 4 < k) (hd : 0 < d) (hn : 0 < n)
    (h1 : n * d = 2 * k * (k - 1)) (h2 : 2 * k - 1 ∣ n - 1) (hdk : d ∣ k) : False := by
  have hk5 : 5 ≤ k := by omega
  have hk1 : 1 ≤ k := by omega
  have hnpos : 1 ≤ n := by omega
  obtain ⟨j, hj⟩ := h2
  have hne : n = (2 * k - 1) * j + 1 := by
    conv_lhs => rw [← Nat.sub_add_cancel hnpos]
    rw [hj]
  have hqcast : ((2 * k - 1 : ℕ) : ℤ) = 2 * (k : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * k)]; push_cast; ring
  have hnjZ : (n : ℤ) = (2 * (k : ℤ) - 1) * (j : ℤ) + 1 := by
    rw [hne]; push_cast; rw [hqcast]
  obtain ⟨b, hb⟩ := hdk
  have hb1 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · rw [h, mul_zero] at hb; omega
    · exact h
  have hbk : b ≤ k := by nlinarith [hb, hd, Nat.zero_le b]
  have hn_eq : n = 2 * b * (k - 1) := by
    have he : n * d = (2 * b * (k - 1)) * d := by rw [h1, hb]; ring
    exact Nat.eq_of_mul_eq_mul_right hd he
  have hcastk : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by rw [Nat.cast_sub hk1]; push_cast; ring
  have hnZ : (n : ℤ) = 2 * (b : ℤ) * ((k : ℤ) - 1) := by
    rw [hn_eq, Nat.cast_mul, Nat.cast_mul, hcastk]; push_cast; ring
  have hkey : (2 * (k : ℤ) - 1) * ((b : ℤ) - (j : ℤ)) = (b : ℤ) + 1 := by
    nlinarith [hnjZ, hnZ]
  have hqpos : (0 : ℤ) < 2 * (k : ℤ) - 1 := by omega
  have hbge : (1 : ℤ) ≤ (b : ℤ) := by exact_mod_cast hb1
  have hbkZ : (b : ℤ) ≤ (k : ℤ) := by exact_mod_cast hbk
  have hpos : 1 ≤ (b : ℤ) - (j : ℤ) := by
    by_contra h
    push Not at h
    nlinarith [hkey, hqpos, h, hbge]
  nlinarith [hkey, hqpos, hpos, hbkZ, hk5]

private lemma s38_arith_A {k d n : ℕ} (hk : 4 < k) (hd : 0 < d) (hn : 0 < n)
    (h1 : n * d = 2 * k * (k - 1)) (h2 : 2 * k - 1 ∣ n - 1) (hdk1 : d ∣ k - 1) :
    d = k - 1 ∧ n = 2 * k := by
  have hk5 : 5 ≤ k := by omega
  have hk1 : 1 ≤ k := by omega
  have hnpos : 1 ≤ n := by omega
  obtain ⟨j, hj⟩ := h2
  have hne : n = (2 * k - 1) * j + 1 := by
    conv_lhs => rw [← Nat.sub_add_cancel hnpos]
    rw [hj]
  have hqcast : ((2 * k - 1 : ℕ) : ℤ) = 2 * (k : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * k)]; push_cast; ring
  have hnjZ : (n : ℤ) = (2 * (k : ℤ) - 1) * (j : ℤ) + 1 := by
    rw [hne]; push_cast; rw [hqcast]
  obtain ⟨b, hb⟩ := hdk1
  have hb1 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · rw [h, mul_zero] at hb; omega
    · exact h
  have hbk : b ≤ k - 1 := by nlinarith [hb, hd, Nat.zero_le b]
  have hn_eq : n = 2 * k * b := by
    have he : n * d = (2 * k * b) * d := by rw [h1, hb]; ring
    exact Nat.eq_of_mul_eq_mul_right hd he
  have hnZ : (n : ℤ) = 2 * (k : ℤ) * (b : ℤ) := by
    rw [hn_eq]; push_cast; ring
  have hkey : (2 * (k : ℤ) - 1) * ((b : ℤ) - (j : ℤ)) = 1 - (b : ℤ) := by
    nlinarith [hnjZ, hnZ]
  have hqpos : (0 : ℤ) < 2 * (k : ℤ) - 1 := by omega
  have hbge : (1 : ℤ) ≤ (b : ℤ) := by exact_mod_cast hb1
  have hbkZ : (b : ℤ) ≤ (k : ℤ) - 1 := by exact_mod_cast hbk
  have hle1 : (b : ℤ) - (j : ℤ) ≤ 0 := by
    by_contra h
    push Not at h
    nlinarith [hkey, hqpos, h, hbge]
  have hle2 : 0 ≤ (b : ℤ) - (j : ℤ) := by
    by_contra h
    push Not at h
    nlinarith [hkey, hqpos, h, hbge, hbkZ, hk5]
  have hbj : (b : ℤ) - (j : ℤ) = 0 := by omega
  have hbz : (b : ℤ) = 1 := by nlinarith [hkey, hbj]
  have hbn : b = 1 := by omega
  subst hbn
  rw [mul_one] at hb
  exact ⟨hb.symm, by rw [hn_eq]; ring⟩

/-- **§3.8 arithmetic.**  See the file header. -/
theorem s38_arith {k d n : ℕ} (hk : 4 < k) (hd : 0 < d) (hn : 0 < n)
    (h1 : n * d = 2 * k * (k - 1))
    (h2 : 2 * k - 1 ∣ n - 1)
    (h3 : d ∣ k ∨ d ∣ k - 1) : d = k - 1 ∧ n = 2 * k := by
  rcases h3 with hdk | hdk1
  · exact (s38_arith_B hk hd hn h1 h2 hdk).elim
  · exact s38_arith_A hk hd hn h1 h2 hdk1

/-- The order identity of (3.8): `q(q² − 1) = 2·(2k−1)(k−1)(2k)` for `q = 2k − 1`. -/
theorem s38_order_arith (k : ℕ) (hk : 1 ≤ k) :
    (2 * k - 1) * ((2 * k - 1) * (2 * k - 1) - 1) =
      2 * ((2 * k - 1) * (k - 1) * (2 * k)) := by
  have e1 : 2 * k - 1 = 2 * (k - 1) + 1 := by omega
  have e2 : 2 * k = 2 * (k - 1) + 2 := by omega
  rw [e1, e2]
  have hs : (2 * (k - 1) + 1) * (2 * (k - 1) + 1) -
      1 = (2 * (k - 1)) * (2 * (k - 1) + 2) := by
    have h : (2 * (k - 1) + 1) * (2 * (k - 1) + 1) =
        (2 * (k - 1)) * (2 * (k - 1) + 2) + 1 := by ring
    omega
  rw [hs]
  ring

/-! ## Elementary consequences of (3.7) -/

/-- **Two distinct Sylow `p`-subgroups meet trivially**, given Bender's (3.7). -/
theorem inf_eq_bot_of_TI {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hTI : ∀ (Q : Sylow p G) (g : G),
      g ∉ Subgroup.normalizer ((Q : Subgroup G) : Set G) →
        (Q : Subgroup G) ⊓ conjSub g (Q : Subgroup G) = ⊥)
    {A B : Sylow p G} (hAB : A ≠ B) : (A : Subgroup G) ⊓ (B : Subgroup G) = ⊥ := by
  classical
  haveI : Fintype (Sylow p G) := Fintype.ofFinite _
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq G B A
  have hconj : conjSub a (B : Subgroup G) = (A : Subgroup G) := by
    rw [← ha]; rfl
  have haN : a ∉ Subgroup.normalizer ((B : Subgroup G) : Set G) := by
    intro hh
    refine hAB ?_
    rw [← ha]
    exact (Sylow.smul_eq_iff_mem_normalizer).mpr hh
  have h := hTI B a haN
  rw [hconj, inf_comm] at h
  exact h

/-- `conjSub a` sends `⟨u⟩` to `⟨a u a⁻¹⟩`. -/
theorem conjSub_zpowers (a u : G) :
    conjSub a (Subgroup.zpowers u) = Subgroup.zpowers (a * u * a⁻¹) := by
  have h : ((MulAut.conj a).toMonoidHom) u = a * u * a⁻¹ := MulAut.conj_apply a u
  rw [Work.GW2.conjSub, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
    MonoidHom.map_closure, Set.image_singleton, h]

/-- `conjSub a` commutes with `⊔`. -/
theorem conjSub_sup (a : G) (H J : Subgroup G) :
    conjSub a (H ⊔ J) = conjSub a H ⊔ conjSub a J := by
  rw [Work.GW2.conjSub, Subgroup.map_sup, Work.GW2.conjSub, Work.GW2.conjSub]

/-- **The free action of a Sylow `p`-subgroup on the other Sylow `p`-subgroups** (a consequence
of (3.7)): `|Q|` divides `|G : N_G(Q)| − 1`. -/
theorem index_dvd_of_TI {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hTI : ∀ (Q : Sylow p G) (g : G),
      g ∉ Subgroup.normalizer ((Q : Subgroup G) : Set G) →
        (Q : Subgroup G) ⊓ conjSub g (Q : Subgroup G) = ⊥)
    (Q : Sylow p G) :
    Nat.card ((Q : Subgroup G)) ∣ (Subgroup.normalizer ((Q : Subgroup G) : Set G)).index - 1 := by
  classical
  haveI : Fintype (Sylow p G) := Fintype.ofFinite _
  letI : MulAction ↥((Q : Subgroup G)) (Sylow p G) :=
    { smul := fun g R => (g : G) • R
      one_smul := fun R => by
        show ((1 : ↥((Q : Subgroup G))) : G) • R = R
        simp
      mul_smul := fun g h' R => by
        show (((g * h' : ↥((Q : Subgroup G)))) : G) • R = (g : G) • ((h' : G) • R)
        rw [Subgroup.coe_mul, mul_smul] }
  have hcard : Nat.card ↥((Q : Subgroup G)) ∣ Nat.card (Sylow p G) - 1 := by
    refine dvd_card_sub_one_of_fixedPointFree (A := ↥((Q : Subgroup G))) (α := Sylow p G) Q ?_ ?_
    · intro g
      show (g : G) • Q = Q
      rw [Sylow.smul_eq_iff_mem_normalizer]
      exact (Q : Subgroup G).le_normalizer g.2
    · intro g hg R hR
      by_contra hRQ
      have hR' : (g : G) • R = R := hR
      have hgR : (g : G) ∈ Subgroup.normalizer ((R : Subgroup G) : Set G) :=
        (Sylow.smul_eq_iff_mem_normalizer).mp hR'
      have hgm : (g : G) ∈ (R : Subgroup G) := by
        have hRle : (R : Subgroup G) ≤ Subgroup.normalizer ((R : Subgroup G) : Set G) :=
          Subgroup.le_normalizer
        have hN : ((R : Subgroup G).subgroupOf
            (Subgroup.normalizer ((R : Subgroup G) : Set G))).Normal :=
          (Subgroup.normal_subgroupOf_iff hRle).mpr fun p1 n hp1 hn =>
            (Subgroup.mem_normalizer_iff.mp hn p1).mp hp1
        have hidx : ¬ p ∣ ((R : Subgroup G).subgroupOf
            (Subgroup.normalizer ((R : Subgroup G) : Set G))).index := by
          have hh := Sylow.not_dvd_index (R.subtype hRle)
          rwa [Sylow.coe_subtype] at hh
        have hAp : IsPGroup p (Subgroup.zpowers (g : G)) := by
          refine (show IsPGroup p ((Q : Subgroup G)) from Q.isPGroup').to_le ?_
          exact Subgroup.zpowers_le.mpr g.2
        exact le_of_subgroupOf_normal_sylow hN hidx R.isPGroup' hRle
          (Subgroup.zpowers_le.mpr hgR) hAp (Subgroup.mem_zpowers (g : G))
      have hbot : (R : Subgroup G) ⊓ (Q : Subgroup G) = ⊥ :=
        inf_eq_bot_of_TI hTI hRQ
      have : (g : G) ∈ (⊥ : Subgroup G) := by
        rw [← hbot]
        exact ⟨hgm, g.2⟩
      exact hg (Subtype.ext (Subgroup.mem_bot.mp this))
  rw [Sylow.card_eq_index_normalizer Q] at hcard
  exact hcard

/-! ## `|Q| = 2k − 1` and parity -/

/-- In the case-(ii) bundle every Sylow `p`-subgroup has order `2|K| − 1`. -/
theorem s38_sylow_card (h : BSWCase2 G t s K x p) (Q : Sylow p G) :
    Nat.card ((Q : Subgroup G)) = 2 * Nat.card K - 1 := by
  haveI : Fact p.Prime := ⟨prime (h := h)⟩
  have hk4 := four_lt (h := h)
  obtain ⟨e, he⟩ := exists_pow (h := h)
  rw [Sylow.card_eq_multiplicity]
  have hG : Nat.card G = (2 * Nat.card K - 1) * (Nat.card K - 1) * (2 * Nat.card K) :=
    card_G (h := h)
  have hndvd1 : ¬ p ∣ Nat.card K - 1 := not_dvd_sub_one_K (h := h)
  have hndvd2 : ¬ p ∣ 2 * Nat.card K := not_dvd_two_mul_K (h := h)
  have hfac : (Nat.card G).factorization p = e := by
    have hnn : (Nat.card K - 1) * (2 * Nat.card K) ≠ 0 :=
      Nat.mul_ne_zero (by omega) (by omega)
    have hGq : Nat.card G = p ^ e * ((Nat.card K - 1) * (2 * Nat.card K)) := by
      rw [hG, ← he]; ring
    rw [hGq, Nat.factorization_mul (pow_ne_zero _ (prime (h := h)).ne_zero) hnn,
      Finsupp.add_apply, Nat.factorization_pow_self (prime (h := h)),
      Nat.factorization_eq_zero_of_not_dvd ((prime (h := h)).not_dvd_mul hndvd1 hndvd2),
      add_zero]
  rw [hfac, ← he]

/-- `p` is odd: it divides the odd number `2|K| − 1`. -/
theorem s38_p_odd (h : BSWCase2 G t s K x p) : Odd p := by
  obtain ⟨e, he⟩ := exists_pow (h := h)
  have hk1 : 1 ≤ Nat.card K := by have := four_lt (h := h); omega
  have he0 : e ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at he
    have := four_lt (h := h)
    omega
  have hdvd : p ∣ 2 * Nat.card K - 1 := he ▸ dvd_pow_self p he0
  have hodd : Odd (2 * Nat.card K - 1) := ⟨Nat.card K - 1, by omega⟩
  exact Odd.of_dvd' hodd hdvd

/-- **Bender (3.7), key step.**  If `X = A ⊓ B` is a maximal intersection of two distinct Sylow
`p`-subgroups, then `N_G(X)` has no normal Sylow `p`-subgroup.

Indeed, suppose `P ⊴ N_G(X)` is a Sylow `p`-subgroup.  Then `P` is the *unique* Sylow
`p`-subgroup of `N_G(X)`, so `X ≤ P` and every `p`-subgroup of `N_G(X)` lies in `P`.  Extend `P`
to a Sylow `C ⊇ P` of `G`; then `X ≤ C`, so `A ⊓ C = X` by maximality if `A ≠ C`, and hence
`N_A(X) = A ⊓ N_G(X) ≤ A ⊓ C = X`.  But `X` is a subgroup of the `p`-group `A`, and a finite
`p`-group satisfies the normalizer condition, so a self-normalizing subgroup of `A` is all of
`A`; thus `X = A ≤ B`, forcing `A = B`, a contradiction.  So `A = C`, and symmetrically
`B = C`, again giving `A = B`. -/
theorem normalizerNoNormalSylowB {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {A B : Sylow p G} (hAB : A ≠ B) {X : Subgroup G}
    (hX : X = (A : Subgroup G) ⊓ (B : Subgroup G))
    (hmax : ∀ C D : Sylow p G, C ≠ D →
      Nat.card ↥((C : Subgroup G) ⊓ (D : Subgroup G)) ≤ Nat.card ↥X) :
    ¬ ∃ P : Subgroup G, P ≤ Subgroup.normalizer (X : Set G) ∧ IsPGroup p P ∧
      (P.subgroupOf (Subgroup.normalizer (X : Set G))).Normal ∧
      ¬ p ∣ (P.subgroupOf (Subgroup.normalizer (X : Set G))).index := by
  rintro ⟨P, hPle, hPp, hPnorm, hidx⟩
  have hXleN : X ≤ Subgroup.normalizer (X : Set G) := Subgroup.le_normalizer
  obtain ⟨S, hPS⟩ := IsPGroup.exists_le_sylow hPp
  have key : ∀ (C D : Sylow p G), C ≠ D → X = (C : Subgroup G) ⊓ (D : Subgroup G) →
      C ≠ S → C = D := by
    intro C D _hCD hXCD hCS
    have hCle : X ≤ (C : Subgroup G) := by rw [hXCD]; exact inf_le_left
    have hXp : IsPGroup p X := C.isPGroup'.to_le hCle
    have hXP : X ≤ P := le_of_subgroupOf_normal_sylow hPnorm hidx hPp hPle hXleN hXp
    have hinf : X = (C : Subgroup G) ⊓ (S : Subgroup G) :=
      Subgroup.eq_of_le_of_card_ge (le_inf hCle (hXP.trans hPS)) (hmax C S hCS)
    have hCNleP : (C : Subgroup G) ⊓ Subgroup.normalizer (X : Set G) ≤ P :=
      le_of_subgroupOf_normal_sylow hPnorm hidx hPp hPle inf_le_right
        (C.isPGroup'.to_le inf_le_left)
    have hCNleX : (C : Subgroup G) ⊓ Subgroup.normalizer (X : Set G) ≤ X :=
      (le_inf inf_le_left (hCNleP.trans hPS)).trans (le_of_eq hinf.symm)
    have hCNeq : (C : Subgroup G) ⊓ Subgroup.normalizer (X : Set G) = X :=
      le_antisymm hCNleX (le_inf hCle hXleN)
    have hself : Subgroup.normalizer (X.subgroupOf (C : Subgroup G)) ≤
        X.subgroupOf (C : Subgroup G) := by
      intro v hv
      rw [Subgroup.mem_subgroupOf]
      have hvN : (v : G) ∈ Subgroup.normalizer (X : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        constructor
        · intro hx
          have h1 : (⟨x, hCle hx⟩ : ↥(C : Subgroup G)) ∈ X.subgroupOf (C : Subgroup G) := by
            rw [Subgroup.mem_subgroupOf]; exact hx
          have h2 : v * (⟨x, hCle hx⟩ : ↥(C : Subgroup G)) * v⁻¹ ∈
              X.subgroupOf (C : Subgroup G) :=
            (Subgroup.mem_normalizer_iff.mp hv (⟨x, hCle hx⟩ : ↥(C : Subgroup G))).mp h1
          rw [Subgroup.mem_subgroupOf] at h2
          simpa using h2
        · intro hx
          have hxC : x ∈ (C : Subgroup G) := by
            have h1 : (v : G) * x * (v : G)⁻¹ ∈ (C : Subgroup G) := hCle hx
            have h2 : (v : G)⁻¹ * ((v : G) * x * (v : G)⁻¹) * (v : G) ∈ (C : Subgroup G) :=
              C.mul_mem (C.mul_mem (C.inv_mem v.2) h1) v.2
            rwa [show (v : G)⁻¹ * ((v : G) * x * (v : G)⁻¹) * (v : G) = x from by group] at h2
          have h2 : v * (⟨x, hxC⟩ : ↥(C : Subgroup G)) * v⁻¹ ∈
              X.subgroupOf (C : Subgroup G) := by
            rw [Subgroup.mem_subgroupOf]; simpa using hx
          have h3 : (⟨x, hxC⟩ : ↥(C : Subgroup G)) ∈ X.subgroupOf (C : Subgroup G) :=
            (Subgroup.mem_normalizer_iff.mp hv (⟨x, hxC⟩ : ↥(C : Subgroup G))).mpr h2
          rwa [Subgroup.mem_subgroupOf] at h3
      have hmem : (v : G) ∈ (C : Subgroup G) ⊓ Subgroup.normalizer (X : Set G) :=
        ⟨v.2, hvN⟩
      rwa [hCNeq] at hmem
    haveI : Group.IsNilpotent ↥(C : Subgroup G) := IsPGroup.isNilpotent (C.isPGroup')
    have hnc : NormalizerCondition ↥(C : Subgroup G) :=
      Group.normalizerCondition_of_isNilpotent (G := ↥(C : Subgroup G))
    have htop : X.subgroupOf (C : Subgroup G) = ⊤ :=
      (normalizerCondition_iff_only_full_group_self_normalizing.mp hnc)
        (X.subgroupOf (C : Subgroup G))
        (le_antisymm hself Subgroup.le_normalizer)
    have hXC : X = (C : Subgroup G) := by
      refine le_antisymm hCle ?_
      intro a ha
      have h1 : (⟨a, ha⟩ : ↥(C : Subgroup G)) ∈ X.subgroupOf (C : Subgroup G) := by
        rw [htop]; trivial
      rwa [Subgroup.mem_subgroupOf] at h1
    have hCleD : (C : Subgroup G) ≤ (D : Subgroup G) := by
      have h1 : (C : Subgroup G) ⊓ (D : Subgroup G) = (C : Subgroup G) :=
        hXCD.symm.trans hXC
      exact h1 ▸ inf_le_right
    exact Sylow.ext (Subgroup.eq_of_le_of_card_ge hCleD (by
      rw [Sylow.card_eq_multiplicity D, Sylow.card_eq_multiplicity C]))
  have hAeq : A = S := by
    by_contra hAS
    exact hAB (key A B hAB hX hAS)
  have hBeq : B = S := by
    by_contra hBS
    exact hAB (key B A (Ne.symm hAB) (by rw [hX, inf_comm]) hBS).symm
  exact hAB (hAeq.trans hBeq.symm)

/-- **(3.7) for the bundle**: a Sylow `p`-subgroup of a case-(ii) group is TI. -/
theorem s38_TI (h : BSWCase2 G t s K x p) :
    ∀ (Q : Sylow p G) (g : G),
      g ∉ Subgroup.normalizer ((Q : Subgroup G) : Set G) →
        (Q : Subgroup G) ⊓ conjSub g (Q : Subgroup G) = ⊥ := by
  have hNo : ∀ (G' : Type) [Group G'] [Finite G'] (p' : ℕ) [Fact p'.Prime],
      ∀ (A B : Sylow p' G'), A ≠ B → ∀ X : Subgroup G',
        X = (A : Subgroup G') ⊓ (B : Subgroup G') →
        (∀ C D : Sylow p' G', C ≠ D →
          Nat.card ↥((C : Subgroup G') ⊓ (D : Subgroup G')) ≤ Nat.card ↥X) →
        ¬ ∃ P : Subgroup G', P ≤ Subgroup.normalizer (X : Set G') ∧ IsPGroup p' P ∧
          (P.subgroupOf (Subgroup.normalizer (X : Set G'))).Normal ∧
          ¬ p' ∣ (P.subgroupOf (Subgroup.normalizer (X : Set G'))).index :=
    fun G' _ _ p' _ A B hAB X hX hmax => normalizerNoNormalSylowB hAB hX hmax
  exact s37_of_no_normal_sylow s36 hNo G t s K x p h

/-! ## `N_G(Y) = N_G(F)` for nontrivial `Y ≤ F = C_G(x)` -/

/-- `N_G(F) = F⟨t⟩`, where `F = C_G(x)`. -/
theorem normalizer_centralizer_x_eq (h : BSWCase2 G t s K x p) :
    Subgroup.normalizer ((Subgroup.centralizer ({x} : Set G)) : Set G) =
      Subgroup.centralizer ({x} : Set G) ⊔ Subgroup.zpowers t := by
  have hle : Subgroup.zpowers t ≤
      Subgroup.normalizer ((Subgroup.centralizer ({x} : Set G)) : Set G) :=
    Subgroup.zpowers_le.mpr (t_mem_normalizer_centralizer_x h)
  have hinf : Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.zpowers t = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    rcases Work.BSW.mem_zpowers_t (hyps (h := h)) hy.2 with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hy.1) (t_notMem_centralizer_x h)
  have hcard : Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊔ Subgroup.zpowers t) =
      Nat.card ↥(Subgroup.normalizer ((Subgroup.centralizer ({x} : Set G)) : Set G)) := by
    rw [Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot hle hinf, Nat.card_zpowers,
      Work.BSW.orderOf_t (hyps (h := h)), cardinal_normalizer_centralizer_x (h := h),
      card_centralizer_x (h := h), Nat.mul_comm]
  exact (Subgroup.eq_of_le_of_card_ge (sup_le Subgroup.le_normalizer hle)
    (le_of_eq hcard.symm)).symm

/-- For `F = C_G(x)`: every nontrivial subgroup `Y ≤ F` has the same normalizer as `F`. -/
theorem normalizer_eq_centralizer_x_of_le (h : BSWCase2 G t s K x p) {Y : Subgroup G}
    (hY : Y ≠ ⊥) (hYle : Y ≤ Subgroup.centralizer ({x} : Set G)) :
    Subgroup.normalizer (Y : Set G) =
      Subgroup.normalizer ((Subgroup.centralizer ({x} : Set G)) : Set G) := by
  haveI : IsMulCommutative ↥(Subgroup.centralizer ({x} : Set G)) :=
    (inverts_centralizer_x h).2
  have hNF := normalizer_centralizer_x_eq h
  refine le_antisymm ?_ ?_
  · intro v hv
    haveI : Nontrivial Y := (Subgroup.nontrivial_iff_ne_bot Y).mpr hY
    obtain ⟨⟨a, haY⟩, ha1⟩ := exists_ne (1 : Y)
    have ha1' : a ≠ 1 := fun hh => ha1 (Subtype.ext hh)
    have hCa : Subgroup.centralizer ({a} : Set G) = Subgroup.centralizer ({x} : Set G) :=
      centralizer_eq_of_mem_centralizer_x h (hYle haY) ha1'
    have hva : v * a * v⁻¹ ∈ Subgroup.centralizer ({x} : Set G) :=
      hYle ((Subgroup.mem_normalizer_iff.mp hv a).mp haY)
    have hva1 : v * a * v⁻¹ ≠ 1 := by
      intro hh
      apply ha1'
      calc a = v⁻¹ * (v * a * v⁻¹) * v := by group
        _ = 1 := by rw [hh]; group
    have hCva : Subgroup.centralizer ({v * a * v⁻¹} : Set G) =
        Subgroup.centralizer ({x} : Set G) :=
      centralizer_eq_of_mem_centralizer_x h hva hva1
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
    show conjSub v (Subgroup.centralizer ({x} : Set G)) = Subgroup.centralizer ({x} : Set G)
    rw [← hCa, conjSub_centralizer, hCva, hCa]
  · rw [hNF]
    refine sup_le ?_ (Subgroup.zpowers_le.mpr ?_)
    · refine le_trans (Subgroup.le_centralizer (H := Subgroup.centralizer ({x} : Set G)))
        (le_trans (Subgroup.centralizer_le (s := (Y : Set G))
            (t := ((Subgroup.centralizer ({x} : Set G)) : Set G)) hYle)
          (Subgroup.centralizer_le_normalizer (Y : Set G)))
    · refine Subgroup.mem_normalizer_iff.mpr fun y => ?_
      constructor
      · intro hy
        have hti : t * y * t⁻¹ = y⁻¹ := (inverts_centralizer_x h).1 y (hYle hy)
        rw [hti]
        exact Y.inv_mem hy
      · intro hy
        have hwF : t * y * t⁻¹ ∈ Subgroup.centralizer ({x} : Set G) := hYle hy
        have hwinv : t * (t * y * t⁻¹) * t⁻¹ = (t * y * t⁻¹)⁻¹ :=
          (inverts_centralizer_x h).1 _ hwF
        have hyw : y = (t * y * t⁻¹)⁻¹ := by
          have h2 : t * (t * y * t⁻¹) * t⁻¹ = y := by
            rw [show t * (t * y * t⁻¹) * t⁻¹ = (t * t) * y * (t⁻¹ * t⁻¹) from by group,
              Work.BSW.t_mul_self (hyps (h := h))]
            have htinv : t⁻¹ * t⁻¹ = 1 := by
              rw [← mul_inv_rev, Work.BSW.t_mul_self (hyps (h := h)), inv_one]
            rw [htinv, mul_one, one_mul]
          exact h2.symm.trans hwinv
        rw [hyw]
        exact Y.inv_mem hy

/-- Conjugating `Y ≤ D` by `g` with `D^g = C_G(x)` transports the normalizer. -/
theorem normalizer_eq_of_le_of_conj (h : BSWCase2 G t s K x p) {Y D : Subgroup G} {g : G}
    (hY : Y ≠ ⊥) (hYle : Y ≤ D) (hconj : conjSub g D = Subgroup.centralizer ({x} : Set G)) :
    Subgroup.normalizer (Y : Set G) = Subgroup.normalizer (D : Set G) := by
  have hYne : conjSub g Y ≠ ⊥ := by
    intro hb
    apply hY
    have h1 : conjSub g⁻¹ (conjSub g Y) = Y := by
      rw [conjSub_conjSub, inv_mul_cancel, conjSub_one]
    rw [hb, Work.GW2.conjSub, Subgroup.map_bot] at h1
    exact h1.symm
  have hYF : conjSub g Y ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [← hconj]; exact conjSub_mono hYle g
  have hstep : Subgroup.normalizer ((conjSub g Y) : Set G) =
      Subgroup.normalizer ((conjSub g D) : Set G) := by
    rw [normalizer_eq_centralizer_x_of_le h hYne hYF, hconj]
  have h1 : conjSub g (Subgroup.normalizer (Y : Set G)) =
      conjSub g (Subgroup.normalizer (D : Set G)) := by
    rw [← normalizer_conjSub, ← normalizer_conjSub, hstep]
  have h2 := congrArg (conjSub g⁻¹) h1
  rwa [conjSub_conjSub, conjSub_conjSub, inv_mul_cancel, conjSub_one, conjSub_one] at h2

/-! ## The leaf -/

theorem s38 : Work.BSW.BSWS38Prop := by
  intro G _instGrp _instFin t s K x p h
  haveI : Fact p.Prime := ⟨prime (h := h)⟩
  have hGcard := card_G (h := h)
  have hk4 := four_lt (h := h)
  obtain ⟨e, he⟩ := exists_pow (h := h)
  obtain ⟨Q⟩ := Sylow.nonempty (p := p) (G := G)
  have hQcard : Nat.card ((Q : Subgroup G)) = 2 * Nat.card K - 1 := s38_sylow_card h Q
  have hQne : (Q : Subgroup G) ≠ ⊥ := by
    intro hb
    have h1 := hQcard
    rw [hb, Subgroup.card_bot] at h1
    omega
  have hQp : IsPGroup p ((Q : Subgroup G)) := Q.isPGroup'
  have hTI := s38_TI h
  -- (3.6) applied to `X = Q`
  obtain ⟨P, D, hPle, hDle, hPp, hidx, hPnorm, hsup, hinf, hconj⟩ :=
    s36 G t s K x p h (Q : Subgroup G) hQne hQp
  -- `P = Q`
  have hQleP : (Q : Subgroup G) ≤ P :=
    le_of_subgroupOf_normal_sylow hPnorm hidx hPp hPle Subgroup.le_normalizer hQp
  have hcardP : Nat.card ↥P ≤ Nat.card ((Q : Subgroup G)) := by
    obtain ⟨Q', hPQ'⟩ := IsPGroup.exists_le_sylow hPp
    calc Nat.card ↥P ≤ Nat.card ↥(Q' : Subgroup G) :=
          Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hPQ')
      _ = 2 * Nat.card K - 1 := s38_sylow_card h Q'
      _ = Nat.card ((Q : Subgroup G)) := hQcard.symm
  have hPeq : P = (Q : Subgroup G) := (Subgroup.eq_of_le_of_card_ge hQleP hcardP).symm
  have hPcard : Nat.card ↥P = 2 * Nat.card K - 1 := by rw [hPeq]; exact hQcard
  have hQDbot : (Q : Subgroup G) ⊓ D = ⊥ := by rw [← hPeq]; exact hinf
  have hNDle : D ≤ Subgroup.normalizer (P : Set G) := by rw [hPeq]; exact hDle
  have hNcard : Nat.card ↥(Subgroup.normalizer (((Q : Subgroup G)) : Set G)) =
      (2 * Nat.card K - 1) * Nat.card D := by
    have hh := Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot (H := P) (K := D) hNDle hinf
    rw [hsup] at hh
    rw [hh, hPcard]
  have hnpos : 0 < (Subgroup.normalizer (((Q : Subgroup G)) : Set G)).index := by
    rw [Subgroup.index_eq_card]; exact Nat.card_pos
  have hnd : (Subgroup.normalizer (((Q : Subgroup G)) : Set G)).index * Nat.card D =
      2 * Nat.card K * (Nat.card K - 1) := by
    have hkey : (2 * Nat.card K - 1) *
        ((Subgroup.normalizer (((Q : Subgroup G)) : Set G)).index * Nat.card D) =
        (2 * Nat.card K - 1) * (2 * Nat.card K * (Nat.card K - 1)) := by
      calc (2 * Nat.card K - 1) *
            ((Subgroup.normalizer (((Q : Subgroup G)) : Set G)).index * Nat.card D)
          = Nat.card ↥(Subgroup.normalizer (((Q : Subgroup G)) : Set G)) *
              (Subgroup.normalizer (((Q : Subgroup G)) : Set G)).index := by
            rw [hNcard]; ring
        _ = Nat.card G := Subgroup.card_mul_index _
        _ = (2 * Nat.card K - 1) * (2 * Nat.card K * (Nat.card K - 1)) := by
            rw [hGcard]; ring
    exact Nat.mul_left_cancel (by omega : 0 < 2 * Nat.card K - 1) hkey
  have hq : 2 * Nat.card K - 1 ∣
      (Subgroup.normalizer (((Q : Subgroup G)) : Set G)).index - 1 := by
    have hh := index_dvd_of_TI hTI Q
    rwa [hQcard] at hh
  obtain ⟨g₀, hg₀⟩ := hconj
  have hdvd : Nat.card D ∣ Nat.card K ∨ Nat.card D ∣ Nat.card K - 1 := by
    rcases hg₀ with hg | hg
    · right
      have h1 : Nat.card D ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set G)) := by
        have h2 := Subgroup.card_dvd_of_le hg
        rwa [card_conjSub g₀ D] at h2
      rwa [card_centralizer_x (h := h)] at h1
    · left
      have h2 := Subgroup.card_dvd_of_le hg
      rwa [card_conjSub g₀ D] at h2
  have hdpos : 0 < Nat.card D := Nat.card_pos
  obtain ⟨hDcard, _hn_eq⟩ := s38_arith (k := Nat.card K) (d := Nat.card D)
    (n := (Subgroup.normalizer (((Q : Subgroup G)) : Set G)).index) hk4 hdpos hnpos hnd hq hdvd
  have hFconj : ∃ g : G, conjSub g D = Subgroup.centralizer ({x} : Set G) := by
    rcases hg₀ with hg | hg
    · refine ⟨g₀, Subgroup.eq_of_le_of_card_ge hg ?_⟩
      rw [card_conjSub g₀ D, hDcard, card_centralizer_x (h := h)]
    · exfalso
      have h1 : Nat.card K - 1 ∣ Nat.card K := by
        have h2 := Subgroup.card_dvd_of_le hg
        rw [card_conjSub g₀ D, hDcard] at h2
        exact h2
      have h2 : Nat.card K - 1 ∣ 1 := by
        have h3 := Nat.dvd_sub h1 (dvd_refl (Nat.card K - 1))
        rwa [Nat.sub_sub_self (by omega : 1 ≤ Nat.card K)] at h3
      have h3 : Nat.card K - 1 ≤ 1 := Nat.le_of_dvd (by norm_num) h2
      omega
  obtain ⟨g, hgF⟩ := hFconj
  -- `Q` is abelian and `C_G(Q) = Q`
  have hCz : ∀ z ∈ ((Q : Subgroup G)), z ≠ 1 →
      Subgroup.centralizer ({z} : Set G) = (Q : Subgroup G) := by
    intro z hz hz1
    have hcz : Nat.card ↥(Subgroup.centralizer ({z} : Set G)) = 2 * Nat.card K - 1 :=
      card_centralizer_of_p_dvd (h := h) hz1
        (p_dvd_orderOf_of_mem_isPGroup (h := h) hQp hz hz1)
    have hpgrp : IsPGroup p ↥(Subgroup.centralizer ({z} : Set G)) :=
      IsPGroup.of_card (by rw [hcz]; exact he)
    obtain ⟨Q', hle⟩ := IsPGroup.exists_le_sylow hpgrp
    have hzQ' : z ∈ (Q' : Subgroup G) := by
      apply hle
      exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    have hQ'eq : Q' = Q := by
      by_contra hne'
      have hbot := inf_eq_bot_of_TI hTI hne'
      have hzbot : z ∈ (⊥ : Subgroup G) := by
        rw [← hbot]
        exact ⟨hzQ', hz⟩
      exact hz1 (Subgroup.mem_bot.mp hzbot)
    have hleQ : Subgroup.centralizer ({z} : Set G) ≤ (Q : Subgroup G) := hQ'eq ▸ hle
    exact Subgroup.eq_of_le_of_card_ge hleQ (by rw [hcz, hQcard])
  have hQab : IsMulCommutative ↥((Q : Subgroup G)) :=
    ⟨⟨fun (a b : ↥((Q : Subgroup G))) => Subtype.ext (by
      change (a : G) * (b : G) = (b : G) * (a : G)
      rcases eq_or_ne (a : G) 1 with ha | ha
      · rw [ha, one_mul, mul_one]
      · have hh := hCz (a : G) a.2 ha
        have hb : (b : G) ∈ Subgroup.centralizer ({(a : G)} : Set G) := by
          rw [hh]; exact b.2
        exact (Subgroup.mem_centralizer_singleton_iff.mp hb).symm)⟩⟩
  haveI : IsMulCommutative ↥((Q : Subgroup G)) := hQab
  have hCQ : Subgroup.centralizer (((Q : Subgroup G)) : Set G) = (Q : Subgroup G) := by
    refine le_antisymm ?_ (Subgroup.le_centralizer (H := ((Q : Subgroup G))))
    intro y hy
    haveI : Nontrivial ↥((Q : Subgroup G)) := (Subgroup.nontrivial_iff_ne_bot _).mpr hQne
    obtain ⟨⟨z, hz⟩, hz1⟩ := exists_ne (1 : ↥((Q : Subgroup G)))
    have hz1' : z ≠ 1 := fun hh => hz1 (Subtype.ext hh)
    have hyz : y ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp hy) z hz).symm
    rwa [hCz z hz hz1'] at hyz
  -- `D` is conjugate to `F`, so `N_G(D) = D⟨u⟩`
  have hD_eq : D = conjSub g⁻¹ (Subgroup.centralizer ({x} : Set G)) := by
    rw [← hgF, conjSub_conjSub, inv_mul_cancel, conjSub_one]
  have hDab : IsMulCommutative ↥D :=
    ⟨⟨fun (a b : ↥D) => Subtype.ext (by
      change (a : G) * (b : G) = (b : G) * (a : G)
      have h1 : (a : G) ∈ conjSub g⁻¹ (Subgroup.centralizer ({x} : Set G)) := by
        rw [← hD_eq]; exact a.2
      have h2 : (b : G) ∈ conjSub g⁻¹ (Subgroup.centralizer ({x} : Set G)) := by
        rw [← hD_eq]; exact b.2
      exact commute_of_mem_conjSub (inverts_centralizer_x h).2 h1 h2)⟩⟩
  have hu2 : orderOf (g⁻¹ * t * g) = 2 := by
    rw [show g⁻¹ * t * g = (MulAut.conj g⁻¹) t from by rw [MulAut.conj_apply]; group,
      MulEquiv.orderOf_eq, Work.BSW.orderOf_t (hyps (h := h))]
  have huInv : Inverts (g⁻¹ * t * g) D := by
    intro y hy
    rw [hD_eq] at hy
    have hfy : g * y * g⁻¹ ∈ Subgroup.centralizer ({x} : Set G) := by
      simpa using mem_conjSub_iff.mp hy
    have htinv := (inverts_centralizer_x h).1 (g * y * g⁻¹) hfy
    calc (g⁻¹ * t * g) * y * (g⁻¹ * t * g)⁻¹
        = g⁻¹ * (t * (g * y * g⁻¹) * t⁻¹) * g := by group
      _ = g⁻¹ * (g * y * g⁻¹)⁻¹ * g := by rw [htinv]
      _ = (g⁻¹ * (g * y * g⁻¹) * g)⁻¹ := by group
      _ = y⁻¹ := by rw [show g⁻¹ * (g * y * g⁻¹) * g = y from by group]
  have huD : g⁻¹ * t * g ∉ D := by
    intro hu
    rw [hD_eq] at hu
    have h1 : g * (g⁻¹ * t * g) * g⁻¹ ∈ Subgroup.centralizer ({x} : Set G) := by
      simpa using mem_conjSub_iff.mp hu
    rw [show g * (g⁻¹ * t * g) * g⁻¹ = t from by group] at h1
    exact t_notMem_centralizer_x h h1
  have hu2' : (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := by
    have hh := pow_orderOf_eq_one (g⁻¹ * t * g)
    rw [hu2, pow_two] at hh
    exact hh
  have huN : g⁻¹ * t * g ∈ Subgroup.normalizer (D : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have h := huInv y hy
      rw [h]
      exact D.inv_mem hy
    · intro hy
      have h := huInv ((g⁻¹ * t * g) * y * (g⁻¹ * t * g)⁻¹) hy
      have h2 : (g⁻¹ * t * g) * ((g⁻¹ * t * g) * y * (g⁻¹ * t * g)⁻¹) *
          (g⁻¹ * t * g)⁻¹ = y := by
        have h' : (g⁻¹ * t * g)⁻¹ * (g⁻¹ * t * g)⁻¹ = 1 := by
          rw [← mul_inv_rev, hu2', inv_one]
        calc (g⁻¹ * t * g) * ((g⁻¹ * t * g) * y * (g⁻¹ * t * g)⁻¹) * (g⁻¹ * t * g)⁻¹
            = ((g⁻¹ * t * g) * (g⁻¹ * t * g)) * y *
                ((g⁻¹ * t * g)⁻¹ * (g⁻¹ * t * g)⁻¹) := by group
          _ = y := by rw [hu2', h']; group
      rw [h2] at h
      rw [h]
      exact D.inv_mem hy
  have hleF : Subgroup.zpowers t ≤
      Subgroup.normalizer ((Subgroup.centralizer ({x} : Set G)) : Set G) :=
    Subgroup.zpowers_le.mpr (t_mem_normalizer_centralizer_x h)
  have hinfF : Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.zpowers t = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    rcases Work.BSW.mem_zpowers_t (hyps (h := h)) hy.2 with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hy.1) (t_notMem_centralizer_x h)
  have hND : Subgroup.normalizer (D : Set G) = D ⊔ Subgroup.zpowers (g⁻¹ * t * g) := by
    have h1 : conjSub g⁻¹ (Subgroup.centralizer ({x} : Set G) ⊔ Subgroup.zpowers t) =
        conjSub g⁻¹ (Subgroup.centralizer ({x} : Set G)) ⊔ Subgroup.zpowers (g⁻¹ * t * g) := by
      rw [conjSub_sup, conjSub_zpowers, inv_inv]
    rw [hD_eq, normalizer_conjSub, normalizer_centralizer_x_eq h, h1]
  have hinv : ∃ u : G, orderOf u = 2 ∧ u ∉ D ∧ Inverts u D ∧
      Subgroup.normalizer (D : Set G) = D ⊔ Subgroup.zpowers u :=
    ⟨g⁻¹ * t * g, hu2, huD, huInv, hND⟩
  -- the order identity `|G| = q(q²-1)/2`
  have hfinal : Nat.card G = (2 * Nat.card K - 1) *
      ((2 * Nat.card K - 1) * (2 * Nat.card K - 1) - 1) / 2 := by
    have hkey : (2 * Nat.card K - 1) *
        ((2 * Nat.card K - 1) * (2 * Nat.card K - 1) - 1) = 2 * Nat.card G := by
      rw [hGcard]
      exact (s38_order_arith (Nat.card K) (by omega)).trans (by ring)
    rw [hkey, Nat.mul_div_right _ (by norm_num : 0 < 2)]
  -- assemble
  refine ⟨⟨p, e, inferInstance, s38_p_odd h, he⟩, ?_, Q, ?_⟩
  · have := four_lt (h := h); omega
  · refine ⟨hQcard, hCQ, ?_, D, hDab, ?_, hQDbot, ?_, ?_, hinv, ?_⟩
    · intro g' hg'
      exact hTI Q g' hg'
    · rw [hDcard]
      have hq2 : 2 * Nat.card K - 1 - 1 = 2 * (Nat.card K - 1) := by
        have := four_lt (h := h); omega
      rw [hq2, Nat.mul_div_right _ (by norm_num : 0 < 2)]
    · rw [← hsup, hPeq]
    · intro X hX hXle
      exact normalizer_eq_of_le_of_conj h hX hXle hgF
    · exact hfinal

end Work.BSW.S3
