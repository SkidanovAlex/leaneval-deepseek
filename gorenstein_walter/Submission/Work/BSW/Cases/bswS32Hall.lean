/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW)

# Bender §3.1 (e),(f): `F = C_G(x)` is a Hall subgroup with normalizer disjointness

Bender, *The Brauer–Suzuki–Wall theorem*, Illinois J. Math. **18** (1974) 229–235, §3.1.

Let `G` be finite and `F ≤ G` a subgroup such that `C_G(a) = F` for every `a ∈ F`, `a ≠ 1`
(Bender's §3.1(i); in the application `F = C_G(x)` for `x ∉ H^G` inverted by `t`, where this is
`Work.BSW.S3.centralizer_eq_of_mem_centralizer`).  The file proves the two structural facts that
`BSWS31Prop` asks for:

* (`Work.BSW.S3.hall`, proved elsewhere in the workspace) `|F|` is coprime to its index, i.e.
  `F` is a Hall subgroup of `G`;
* `F ⊓ N_G(F)^g = ⊥` for `g ∉ N_G(F)` (Bender §3.1(iii), item (e) of `BSWS31Prop`).

The second statement is proved here from the "fixed-point congruence" for a prime order
automorphism: an element `z ∈ F ⊓ N_G(F^g)` acts by conjugation on the (abelian) group `F^g`
with all non-trivial orbits of size `orderOf z`, while `orderOf z` divides `|F^g|`; hence
`orderOf z ∣ 1`.
-/
import Mathlib
import Submission.Work.BSW.S3.Defs
import Submission.Work.BSW.S3.S31setup
import Submission.Work.BSW.S3.hall
import Submission.Work.BSW.Cases.S31core

set_option linter.style.haveILetI false

namespace Work.BSW.Cases

open Subgroup Work.GW2

section General

variable {G : Type} [Group G]

/-- The centralizer of the conjugate `(MulAut.conj g) a` is the conjugate of the centralizer
of `a`. -/
theorem centralizer_conjSub (g a : G) :
    Subgroup.centralizer ({(MulAut.conj g) a} : Set G)
      = conjSub g (Subgroup.centralizer ({a} : Set G)) := by
  ext x
  rw [conjSub, Subgroup.mem_map]
  constructor
  · intro hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    refine ⟨(MulAut.conj g)⁻¹ x, ?_, (MulAut.conj g).apply_symm_apply x⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hx'' : x * (g * a * g⁻¹) = (g * a * g⁻¹) * x := by
      simpa [MulAut.conj_apply] using hx
    rw [show (MulAut.conj g)⁻¹ x = g⁻¹ * x * g from by simp]
    calc g⁻¹ * x * g * a = g⁻¹ * (x * (g * a * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * a * g⁻¹) * x) * g := by rw [hx'']
      _ = a * (g⁻¹ * x * g) := by group
  · rintro ⟨w, hw, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hw ⊢
    change (MulAut.conj g) w * (MulAut.conj g) a = (MulAut.conj g) a * (MulAut.conj g) w
    rw [← map_mul, ← map_mul, hw]

/-- **Bender §3.1(i) implies TI.**  If every non-identity element of `F` is centralized exactly
by `F`, then distinct conjugates of `F` intersect trivially. -/
theorem inf_conjSub_eq_bot {F : Subgroup G}
    (h : ∀ a ∈ F, a ≠ 1 → Subgroup.centralizer ({a} : Set G) = F) :
    ∀ g : G, g ∉ Subgroup.normalizer (F : Set G) → F ⊓ conjSub g F = ⊥ := by
  intro g hg
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  by_contra hz1
  have hzF : z ∈ F := hz.1
  have hzA0 : z ∈ conjSub g F := hz.2
  have hzA : z ∈ Subgroup.map (MulAut.conj g).toMonoidHom F := hzA0
  rw [Subgroup.mem_map] at hzA
  obtain ⟨a, haF, haz⟩ := hzA
  have ha1 : a ≠ 1 := fun h1 => hz1 (by rw [← haz, h1, map_one])
  have hzC : Subgroup.centralizer ({z} : Set G) = F := h z hzF hz1
  have haC : Subgroup.centralizer ({a} : Set G) = F := h a haF ha1
  have hconj : Subgroup.centralizer ({z} : Set G)
      = conjSub g (Subgroup.centralizer ({a} : Set G)) := by
    rw [← haz]
    exact centralizer_conjSub g a
  rw [hzC, haC] at hconj
  exact hg (by rw [Subgroup.mem_normalizer_iff_map_conj_eq]; simpa [conjSub] using hconj.symm)

/-- The normalizer of a conjugate is the conjugate of the normalizer. -/
theorem normalizer_conjSub (g : G) (H : Subgroup G) :
    conjSub g (Subgroup.normalizer (H : Set G)) = Subgroup.normalizer (conjSub g H : Set G) := by
  simp only [conjSub]
  exact Subgroup.map_equiv_normalizer_eq H (MulAut.conj g)

end General

section Counting

variable {G : Type} [Group G] [Finite G]

/-- **Fixed-point congruence.**  If `x` has prime order `q`, normalizes `A` and acts
fixed-point-freely on `A` (`x * y * x⁻¹ = y` only for `y = 1`), then `q ∣ |A| - 1`.

Indeed `⟨x⟩ ≅ Z/q` acts on `A` by conjugation, so `|A|` is congruent to the number of fixed
points, which is `1`, modulo `q`. -/
theorem dvd_card_sub_one_of_fpf {A : Subgroup G} {x : G} {q : ℕ} (hq : q.Prime)
    (hx : orderOf x = q) (hxN : x ∈ Subgroup.normalizer (A : Set G))
    (hfpf : ∀ y ∈ A, x * y = y * x → y = 1) :
    q ∣ Nat.card ↥A - 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  let H : Subgroup G := Subgroup.zpowers x
  have hHle : H ≤ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.zpowers_le]
    exact hxN
  letI : MulAction ↥H ↥A :=
    { smul := fun h y => ⟨(h : G) * (y : G) * (h : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hHle h.2) (y : G)).mp y.2⟩
      one_smul := by
        intro y; apply Subtype.ext
        change (1 : G) * (y : G) * (1 : G)⁻¹ = (y : G)
        simp
      mul_smul := by
        intro a b y; apply Subtype.ext
        change (((a * b : ↥H)) : G) * (y : G) * (((a * b : ↥H)) : G)⁻¹
          = (a : G) * ((b : G) * (y : G) * (b : G)⁻¹) * (a : G)⁻¹
        rw [Subgroup.coe_mul]; group }
  have hHp : IsPGroup q ↥H := by
    refine IsPGroup.of_card (n := 1) ?_
    change Nat.card ↥(Subgroup.zpowers x) = q ^ 1
    rw [Nat.card_zpowers, hx, pow_one]
  have key := hHp.card_modEq_card_fixedPoints ↥A
  have hfix : Nat.card ↥(MulAction.fixedPoints ↥H ↥A) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun u v => ?_⟩, ⟨⟨⟨1, A.one_mem⟩, ?_⟩⟩⟩
    · have hmem : ∀ u : ↥(MulAction.fixedPoints ↥H ↥A), (u.1 : G) = 1 := by
        intro u
        have hu' : x * (u.1 : G) * x⁻¹ = (u.1 : G) :=
          congrArg Subtype.val
            ((MulAction.mem_fixedPoints.mp u.2) ⟨x, Subgroup.mem_zpowers x⟩)
        have hc : x * (u.1 : G) = (u.1 : G) * x := by
          have h2 := congrArg (fun w => w * x) hu'
          simpa [mul_assoc] using h2
        exact hfpf (u.1 : G) u.1.2 hc
      exact Subtype.ext (Subtype.ext (by rw [hmem u, hmem v]))
    · rw [MulAction.mem_fixedPoints]
      intro h
      apply Subtype.ext
      change (h : G) * (1 : G) * (h : G)⁻¹ = (1 : G)
      simp
  rw [hfix] at key
  exact (Nat.modEq_iff_dvd' Nat.card_pos).mp key.symm

/-- **Bender §3.1(iii) / item (e) of `BSWS31Prop`.**  If every non-identity element of `F` is
centralized exactly by `F`, then for `g ∉ N_G(F)` we have `F ⊓ N_G(F)^g = ⊥`.

Proof.  Suppose `1 ≠ z ∈ F ⊓ N_G(F^g)`.  Then `z` acts by conjugation on the conjugate `F^g`
(which is abelian, since `F` is), and every non-trivial orbit has size `orderOf z`: the
stabiliser of `y ∈ (F^g)^#` is `⟨z⟩ ⊓ C_G(y) = ⟨z⟩ ⊓ F^g ⊆ F ⊓ F^g = 1` by TI-ness.  Hence
`|F^g| ≡ 1 (mod orderOf z)`, while `orderOf z ∣ |F| = |F^g|` because `z ∈ F`.  So
`orderOf z ∣ 1`, a contradiction. -/
theorem tiNormalizer {F : Subgroup G}
    (h : ∀ a ∈ F, a ≠ 1 → Subgroup.centralizer ({a} : Set G) = F) :
    ∀ g : G, g ∉ Subgroup.normalizer (F : Set G) →
      F ⊓ conjSub g (Subgroup.normalizer (F : Set G)) = ⊥ := by
  intro g hg
  have hTI : F ⊓ conjSub g F = ⊥ := inf_conjSub_eq_bot h g hg
  rw [normalizer_conjSub]
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  by_contra hz1
  have hzF : z ∈ F := hz.1
  have hzN : z ∈ Subgroup.normalizer (conjSub g F : Set G) := hz.2
  have hzmemN : z ∈ conjSub g (Subgroup.normalizer (F : Set G)) := by
    rw [normalizer_conjSub]; exact hzN
  have hzpow : ∀ n : ℕ, z ^ n ∈ conjSub g (Subgroup.normalizer (F : Set G)) :=
    fun n => (conjSub g (Subgroup.normalizer (F : Set G))).pow_mem hzmemN n
  -- pick a prime `q` dividing `orderOf z` and set `β = z ^ (orderOf z / q)`, of order `q`
  have hzord1 : orderOf z ≠ 1 := fun h1 => hz1 (orderOf_eq_one_iff.mp h1)
  obtain ⟨q, hq, hqr⟩ := Nat.exists_prime_and_dvd hzord1
  haveI : Fact q.Prime := ⟨hq⟩
  have hβpow : (z ^ (orderOf z / q)) ^ q = 1 := by
    rw [← pow_mul, Nat.div_mul_cancel hqr, pow_orderOf_eq_one]
  have hβdvd : orderOf (z ^ (orderOf z / q)) ∣ q := orderOf_dvd_iff_pow_eq_one.mpr hβpow
  have hβne1 : z ^ (orderOf z / q) ≠ 1 := by
    intro h1
    have hdvd : orderOf z ∣ orderOf z / q := orderOf_dvd_iff_pow_eq_one.mpr h1
    have hpos : 0 < orderOf z / q := Nat.div_pos (Nat.le_of_dvd (orderOf_pos z) hqr) (Nat.Prime.pos hq)
    have hlt : orderOf z / q < orderOf z := Nat.div_lt_self (orderOf_pos z) (Nat.Prime.one_lt hq)
    exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.mpr hlt)
  have hβord : orderOf (z ^ (orderOf z / q)) = q := by
    rcases (Nat.dvd_prime hq).mp hβdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hβne1
    · exact h1
  -- `β` lies in `F` and hence is centralized exactly by `F`
  have hβF : z ^ (orderOf z / q) ∈ F := F.pow_mem hzF _
  have hβC : Subgroup.centralizer ({z ^ (orderOf z / q)} : Set G) = F := h _ hβF hβne1
  -- `β` normalizes the conjugate `F^g`
  have hβN : z ^ (orderOf z / q) ∈ Subgroup.normalizer (conjSub g F : Set G) := by
    rw [← normalizer_conjSub]
    exact hzpow _
  -- and acts fixed-point-freely on it
  have hfpf : ∀ y ∈ conjSub g F,
      z ^ (orderOf z / q) * y = y * z ^ (orderOf z / q) → y = 1 := by
    intro y hy hyc
    have hyC : y ∈ Subgroup.centralizer ({z ^ (orderOf z / q)} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hyc.symm
    rw [hβC] at hyC
    have hyinf : y ∈ F ⊓ conjSub g F := ⟨hyC, hy⟩
    rw [hTI] at hyinf
    exact Subgroup.mem_bot.mp hyinf
  have hdvd1 : q ∣ Nat.card ↥(conjSub g F) - 1 :=
    dvd_card_sub_one_of_fpf hq hβord hβN hfpf
  have hdvd2 : q ∣ Nat.card ↥(conjSub g F) := by
    have hFq : q ∣ Nat.card ↥F := by
      have h := orderOf_dvd_natCard (⟨z ^ (orderOf z / q), hβF⟩ : ↥F)
      have h2 : orderOf (⟨z ^ (orderOf z / q), hβF⟩ : ↥F) = q := by
        rw [← Subgroup.orderOf_coe (⟨z ^ (orderOf z / q), hβF⟩ : ↥F)]
        exact hβord
      rwa [h2] at h
    have hcard : Nat.card ↥(conjSub g F) = Nat.card ↥F := by
      simp only [conjSub]
      exact Subgroup.card_map_of_injective (K := F) (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective
    rwa [hcard]
  have hsub := Nat.dvd_sub hdvd2 hdvd1
  rw [Nat.sub_sub_self Nat.card_pos] at hsub
  exact Nat.Prime.not_dvd_one hq hsub

end Counting

theorem bswS32Hall {G : Type} [Group G] [Finite G] {t s x : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) (hx : x ∉ Work.BSW.HG t) (hinv : t⁻¹ * x * t = x⁻¹) :
    Nat.Coprime (Nat.card ↥(Subgroup.centralizer ({x} : Set G)))
        (Subgroup.centralizer ({x} : Set G)).index ∧
      (∀ g : G, g ∉ Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G) →
        Subgroup.centralizer ({x} : Set G) ⊓
          Work.GW2.conjSub g
            (Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G)) = ⊥) := by
  have hF : ∀ a ∈ Subgroup.centralizer ({x} : Set G), a ≠ 1 →
      Subgroup.centralizer ({a} : Set G) = Subgroup.centralizer ({x} : Set G) :=
    Work.BSW.S3.centralizer_eq_of_mem_centralizer h hx hinv
  exact ⟨Work.BSW.S3.hall _ hF, tiNormalizer hF⟩

end Work.BSW.Cases
