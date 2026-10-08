/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, §3 leaves)

# BSW §3: consequences of the case-(ii) bundle `BSWCase2`

Fundamental group-theoretic consequences of the case-(ii) bundle, shared by the leaves
(3.6) (`Work.BSW.S3.s36`), (3.7) (`Work.BSW.S3.s37`) and (3.8):

* `not_dvd_two_mul`, `not_dvd_sub_one`, `not_dvd_self` — `p ∤ 2k`, `p ∤ k-1`, `p ∤ k`
  where `k = Nat.card K` and `2k-1 = p^e`;
* `card_centralizer_t` — `|C_G(t)| = 2k`;
* `centralizer_card_of_p_dvd` (the heart of (3.5)) — *every* element `y ≠ 1` whose order is
  divisible by `p` has `orderOf y = p`, `|C_G(y)| = 2k-1`, and `y` is not conjugate to `y⁻¹`;
* `mem_HG_or_conj_centralizer` — an element `y ≠ 1` of order `≠ p` lies in `H^G` or is
  conjugate into `C_G(x)`;
* `normalizer_odd_order` — the normalizer of a nontrivial `p`-subgroup has odd order
  (Bender (3.6), first step).
-/
import Mathlib
import Submission.Work.BSW.S3.Defs
import Submission.Work.BSW.Basic
import Submission.Work.BSW.Api.card_sup_zpowers
import Submission.Work.BSW.Api.normalizer_K_eq

namespace Work.BSW.S3

open Subgroup Work.GW2

variable {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G} {x : G} {p : ℕ}

/-! ## Arithmetic around `2k - 1 = p ^ e` -/

/-- `p ∤ 2k` when `2k - 1` is a power of the prime `p` and `k > 1`. -/
theorem not_dvd_two_mul {k p e : ℕ} (hp : p.Prime) (he : 2 * k - 1 = p ^ e) (hk : 1 < k) :
    ¬ p ∣ 2 * k := by
  have he0 : e ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at he
    omega
  have hdvd : p ∣ 2 * k - 1 := he ▸ dvd_pow_self p he0
  intro h2k
  have hsub : p ∣ 2 * k - (2 * k - 1) := Nat.dvd_sub h2k hdvd
  have : 2 * k - (2 * k - 1) = 1 := by omega
  rw [this] at hsub
  exact hp.not_dvd_one hsub

/-- `p ∤ k - 1` when `2k - 1` is a power of the prime `p` and `k > 1`. -/
theorem not_dvd_sub_one {k p e : ℕ} (hp : p.Prime) (he : 2 * k - 1 = p ^ e) (hk : 1 < k) :
    ¬ p ∣ k - 1 := by
  have he0 : e ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at he
    omega
  have hdvd : p ∣ 2 * k - 1 := he ▸ dvd_pow_self p he0
  intro hkdvd
  have h2 : p ∣ 2 * (k - 1) := dvd_mul_of_dvd_right hkdvd 2
  have heq : 2 * (k - 1) = 2 * k - 2 := by omega
  rw [heq] at h2
  have hsub : p ∣ (2 * k - 1) - (2 * k - 2) := Nat.dvd_sub hdvd h2
  have : (2 * k - 1) - (2 * k - 2) = 1 := by omega
  rw [this] at hsub
  exact hp.not_dvd_one hsub

/-- `p ∤ k` when `2k - 1` is a power of the prime `p` and `k > 1`. -/
theorem not_dvd_self {k p e : ℕ} (hp : p.Prime) (he : 2 * k - 1 = p ^ e) (hk : 1 < k) :
    ¬ p ∣ k := fun h => not_dvd_two_mul hp he hk (dvd_mul_of_dvd_right h 2)

/-! ## Consequences of the bundle -/

section Bundle

/-- Projection helpers for the case-(ii) bundle. -/
theorem hyps {h : BSWCase2 G t s K x p} : BSWHyps2 G t s K := h.1
theorem four_lt {h : BSWCase2 G t s K x p} : 4 < Nat.card K := h.2.1
theorem card_G {h : BSWCase2 G t s K x p} : Nat.card G =
    (2 * Nat.card K - 1) * (Nat.card K - 1) * (2 * Nat.card K) := h.2.2.1
theorem not_mem_HG {h : BSWCase2 G t s K x p} : x ∉ Work.BSW.HG t := h.2.2.2.1
theorem t_inverts_x {h : BSWCase2 G t s K x p} : t⁻¹ * x * t = x⁻¹ := h.2.2.2.2.1
theorem card_centralizer_x {h : BSWCase2 G t s K x p} :
    Nat.card (Subgroup.centralizer ({x} : Set G)) = Nat.card K - 1 := h.2.2.2.2.2.1
theorem cardinal_normalizer_centralizer_x {h : BSWCase2 G t s K x p} :
    Nat.card (Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G)) =
      2 * (Nat.card K - 1) := h.2.2.2.2.2.2.1
theorem prime {h : BSWCase2 G t s K x p} : p.Prime := h.2.2.2.2.2.2.2.1
theorem exists_pow {h : BSWCase2 G t s K x p} : ∃ e : ℕ, 2 * Nat.card K - 1 = p ^ e :=
  h.2.2.2.2.2.2.2.2.1
theorem case2_cond {h : BSWCase2 G t s K x p} : ∀ y : G, y ≠ 1 → y ∉ Work.BSW.HG t →
    (∀ g : G, g * y * g⁻¹ ∉ Subgroup.centralizer ({x} : Set G)) →
    Nat.card (Subgroup.centralizer ({y} : Set G)) = 2 * Nat.card K - 1 ∧
      orderOf y = p ∧ ¬ IsConj y y⁻¹ := h.2.2.2.2.2.2.2.2.2

/-- `1 < Nat.card K`, hence the arithmetic lemmas apply. -/
theorem one_lt {h : BSWCase2 G t s K x p} : 1 < Nat.card K := by
  have := four_lt (h := h); omega

/-- `|C_G(t)| = 2|K|`. -/
theorem card_centralizer_t {h : BSWCase2 G t s K x p} :
    Nat.card (Subgroup.centralizer ({t} : Set G)) = 2 * Nat.card K := by
  rw [Work.BSW.centralizer_t_eq (hyps (h := h)), Work.BSW.Api.card_sup_zpowers (hyps (h := h))]

theorem not_dvd_two_mul_K {h : BSWCase2 G t s K x p} : ¬ p ∣ 2 * Nat.card K :=
  not_dvd_two_mul (prime (h := h)) (exists_pow (h := h)).choose_spec (one_lt (h := h))

theorem not_dvd_sub_one_K {h : BSWCase2 G t s K x p} : ¬ p ∣ Nat.card K - 1 :=
  not_dvd_sub_one (prime (h := h)) (exists_pow (h := h)).choose_spec (one_lt (h := h))

theorem not_dvd_K {h : BSWCase2 G t s K x p} : ¬ p ∣ Nat.card K :=
  not_dvd_self (prime (h := h)) (exists_pow (h := h)).choose_spec (one_lt (h := h))

/-- Conjugation does not change the order. -/
theorem orderOf_conj_eq (g y : G) : orderOf (g * y * g⁻¹) = orderOf y := by
  have h : SemiconjBy g y (g * y * g⁻¹) := by rw [SemiconjBy]; group
  exact (SemiconjBy.orderOf_eq g h).symm

/-- **The heart of (3.5).**  If `y ≠ 1` has order divisible by `p`, then `y` is a `p`-element
of order exactly `p`, its centralizer has order `2k-1`, and `y` is not conjugate to `y⁻¹`.

(Concretely: `y ∉ H^G` and no conjugate of `y` lies in `C_G(x)`, because both those groups have
orders (`2k` and `k-1`) coprime to `p`; then the bundle's `case2_cond` applies.) -/
theorem centralizer_card_of_p_dvd {h : BSWCase2 G t s K x p} {y : G} (hy : y ≠ 1)
    (hpy : p ∣ orderOf y) :
    Nat.card (Subgroup.centralizer ({y} : Set G)) = 2 * Nat.card K - 1 ∧
      orderOf y = p ∧ ¬ IsConj y y⁻¹ := by
  have hyH : y ∉ Work.BSW.HG t := by
    intro hyh
    obtain ⟨g, hg⟩ := hyh
    have h1 : orderOf (g * y * g⁻¹) = orderOf y := orderOf_conj_eq g y
    have h2 : orderOf (g * y * g⁻¹) ∣ Nat.card (Subgroup.centralizer ({t} : Set G)) :=
      Subgroup.orderOf_dvd_natCard _ hg
    rw [h1, card_centralizer_t (h := h)] at h2
    exact not_dvd_two_mul_K (h := h) (hpy.trans h2)
  have hyCx : ∀ g : G, g * y * g⁻¹ ∉ Subgroup.centralizer ({x} : Set G) := by
    intro g hg
    have h1 : orderOf (g * y * g⁻¹) = orderOf y := orderOf_conj_eq g y
    have h2 : orderOf (g * y * g⁻¹) ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) :=
      Subgroup.orderOf_dvd_natCard _ hg
    rw [h1, card_centralizer_x (h := h)] at h2
    exact not_dvd_sub_one_K (h := h) (hpy.trans h2)
  exact case2_cond (h := h) y hy hyH hyCx

/-- Every nonidentity `p`-element of `G` has order exactly `p`. -/
theorem orderOf_eq_p {h : BSWCase2 G t s K x p} {y : G} (hy : y ≠ 1) (hpy : p ∣ orderOf y) :
    orderOf y = p :=
  (centralizer_card_of_p_dvd (h := h) hy hpy).2.1

/-- For `y ≠ 1` a `p`-element, `|C_G(y)| = 2k-1` (in particular `C_G(y)` has odd order). -/
theorem card_centralizer_of_p_dvd {h : BSWCase2 G t s K x p} {y : G} (hy : y ≠ 1)
    (hpy : p ∣ orderOf y) :
    Nat.card (Subgroup.centralizer ({y} : Set G)) = 2 * Nat.card K - 1 :=
  (centralizer_card_of_p_dvd (h := h) hy hpy).1

/-- `y ≠ 1` a `p`-element is not conjugate to its inverse. -/
theorem not_isConj_inv {h : BSWCase2 G t s K x p} {y : G} (hy : y ≠ 1) (hpy : p ∣ orderOf y) :
    ¬ IsConj y y⁻¹ :=
  (centralizer_card_of_p_dvd (h := h) hy hpy).2.2

/-- A nonidentity element of a `p`-subgroup `X` has order divisible by `p`. -/
theorem p_dvd_orderOf_of_mem_isPGroup {h : BSWCase2 G t s K x p} {X : Subgroup G}
    (hX : IsPGroup p X) {y : G} (hyX : y ∈ X) (hy : y ≠ 1) : p ∣ orderOf y := by
  haveI : Fact p.Prime := ⟨prime (h := h)⟩
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf).mp hX ⟨y, hyX⟩
  have hcoe : orderOf y = p ^ j := (Subgroup.orderOf_coe (⟨y, hyX⟩ : ↥X)).trans hj
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hcoe
    exact hy (orderOf_eq_one_iff.mp hcoe)
  rw [hcoe]
  exact dvd_pow_self p hj0

theorem orderOf_eq_p_of_mem_isPGroup {h : BSWCase2 G t s K x p} {X : Subgroup G}
    (hX : IsPGroup p X) {y : G} (hyX : y ∈ X) (hy : y ≠ 1) : orderOf y = p :=
  orderOf_eq_p (h := h) hy (p_dvd_orderOf_of_mem_isPGroup (h := h) hX hyX hy)

theorem card_centralizer_of_mem_isPGroup {h : BSWCase2 G t s K x p} {X : Subgroup G}
    (hX : IsPGroup p X) {y : G} (hyX : y ∈ X) (hy : y ≠ 1) :
    Nat.card (Subgroup.centralizer ({y} : Set G)) = 2 * Nat.card K - 1 :=
  card_centralizer_of_p_dvd (h := h) hy (p_dvd_orderOf_of_mem_isPGroup (h := h) hX hyX hy)

theorem not_isConj_inv_of_mem_isPGroup {h : BSWCase2 G t s K x p} {X : Subgroup G}
    (hX : IsPGroup p X) {y : G} (hyX : y ∈ X) (hy : y ≠ 1) : ¬ IsConj y y⁻¹ :=
  not_isConj_inv (h := h) hy (p_dvd_orderOf_of_mem_isPGroup (h := h) hX hyX hy)

/-- **The dichotomy of (3.5).**  Every `y ≠ 1` is either of order `p`, or lies in `H^G`, or is
conjugate into `C_G(x)`. -/
theorem mem_HG_or_conj_centralizer {h : BSWCase2 G t s K x p} {y : G} (hy : y ≠ 1)
    (hyord : orderOf y ≠ p) :
    y ∈ Work.BSW.HG t ∨ ∃ g : G, g * y * g⁻¹ ∈ Subgroup.centralizer ({x} : Set G) := by
  by_contra hc
  push_neg at hc
  exact hyord (case2_cond (h := h) y hy hc.1 hc.2).2.1

/-- **Bender (3.6), first step.**  No involution normalizes a nontrivial `p`-subgroup `X`.

For `X ≠ 1` a `p`-subgroup and `u` of order `2` normalizing `X`, take a nonidentity `z` in the
centre of `X`.  If `u` centralizes `z`, then `u ∈ C_G(z)`, whose order is `2k-1`, odd — absurd
since `u` has order `2`.  So `u` does not centralize `z`; since `z` is central in `X`, the
element `z * (u * z * u⁻¹)` is fixed by `u`.  If it were `≠ 1`, `u` would centralize it and we
would be in the previous case; hence `z * (u * z * u⁻¹) = 1`, i.e. `u * z * u⁻¹ = z⁻¹` and `z`
is conjugate to its inverse, contradicting `not_isConj_inv_of_mem_isPGroup`. -/
theorem no_involution_normalizes (h : BSWCase2 G t s K x p) {X : Subgroup G} (hX : X ≠ ⊥)
    (hXp : IsPGroup p X) {u : G} (hu : orderOf u = 2) :
    u ∉ Subgroup.normalizer (X : Set G) := by
  intro huN
  haveI : Fact p.Prime := ⟨prime (h := h)⟩
  haveI : Nontrivial ↥X := by rw [Subgroup.nontrivial_iff_ne_bot]; exact hX
  haveI hZnt : Nontrivial ↥(Subgroup.center ↥X) := IsPGroup.center_nontrivial hXp
  obtain ⟨z, hz1⟩ := exists_ne (1 : ↥(Subgroup.center ↥X))
  have hzX : ((z : ↥X) : G) ∈ X := (z : ↥X).2
  have hz1G : ((z : ↥X) : G) ≠ 1 := fun h => hz1 (Subtype.ext (Subtype.ext h))
  have hmem : ∀ n : G, n ∈ X ↔ u * n * u⁻¹ ∈ X := huN
  -- first case: `u` centralizes some nonidentity element of `X`
  have key : ∀ w : G, w ∈ X → w ≠ 1 → u * w * u⁻¹ = w → False := by
    intro w hwX hw1 hcon
    have huw : u * w = w * u := by
      calc u * w = (u * w * u⁻¹) * u := by group
        _ = w * u := by rw [hcon]
    have hwcent : u ∈ Subgroup.centralizer ({w} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]; exact huw
    have hdvd : orderOf u ∣ Nat.card (Subgroup.centralizer ({w} : Set G)) :=
      Subgroup.orderOf_dvd_natCard _ hwcent
    rw [hu, card_centralizer_of_mem_isPGroup (h := h) hXp hwX hw1] at hdvd
    have h2a : 2 ∣ 2 * Nat.card K := dvd_mul_right 2 _
    have h2b : 2 ∣ 2 * Nat.card K - (2 * Nat.card K - 1) := Nat.dvd_sub h2a hdvd
    have h1 : 2 * Nat.card K - (2 * Nat.card K - 1) = 1 := by
      have := one_lt (h := h); omega
    rw [h1] at h2b
    omega
  -- the element `z * (u * z * u⁻¹)` is fixed by `u`
  have hzuX : u * ((z : ↥X) : G) * u⁻¹ ∈ X := (hmem _).mp hzX
  have hcomm : ((z : ↥X) : G) * (u * ((z : ↥X) : G) * u⁻¹) =
      (u * ((z : ↥X) : G) * u⁻¹) * ((z : ↥X) : G) := by
    have h := congrArg Subtype.val
      ((Subgroup.mem_center_iff.mp z.2 (⟨u * ((z : ↥X) : G) * u⁻¹, hzuX⟩ : ↥X)).symm)
    simpa using h
  have hfix : u * (((z : ↥X) : G) * (u * ((z : ↥X) : G) * u⁻¹)) * u⁻¹ =
      ((z : ↥X) : G) * (u * ((z : ↥X) : G) * u⁻¹) := by
    have hu2 : u * u = 1 := by
      have h := pow_orderOf_eq_one u
      rw [hu, pow_two] at h
      exact h
    have hu2inv : u⁻¹ * u⁻¹ = 1 := by rw [← mul_inv_rev, hu2, inv_one]
    have h2 : u * (u * ((z : ↥X) : G) * u⁻¹) * u⁻¹ = ((z : ↥X) : G) := by
      calc u * (u * ((z : ↥X) : G) * u⁻¹) * u⁻¹
          = (u * u) * ((z : ↥X) : G) * (u⁻¹ * u⁻¹) := by group
        _ = ((z : ↥X) : G) := by rw [hu2, hu2inv]; simp
    calc u * (((z : ↥X) : G) * (u * ((z : ↥X) : G) * u⁻¹)) * u⁻¹
        = (u * ((z : ↥X) : G) * u⁻¹) * (u * (u * ((z : ↥X) : G) * u⁻¹) * u⁻¹) := by
          group
      _ = (u * ((z : ↥X) : G) * u⁻¹) * ((z : ↥X) : G) := by rw [h2]
      _ = ((z : ↥X) : G) * (u * ((z : ↥X) : G) * u⁻¹) := hcomm.symm
  have hone : ((z : ↥X) : G) * (u * ((z : ↥X) : G) * u⁻¹) = 1 := by
    by_contra hne
    exact key _ (X.mul_mem hzX hzuX) hne hfix
  have hzinv : u * ((z : ↥X) : G) * u⁻¹ = ((z : ↥X) : G)⁻¹ := by
    rw [← mul_left_cancel_iff (a := ((z : ↥X) : G)), hone, mul_inv_cancel]
  exact not_isConj_inv_of_mem_isPGroup (h := h) hXp hzX hz1G (isConj_iff.mpr ⟨u, hzinv⟩)

/-- **Bender (3.6), first step, group form.**  The normalizer of a nontrivial `p`-subgroup has
odd order: an even-order group has an element of order `2` (Cauchy), which
`no_involution_normalizes` forbids. -/
theorem normalizer_odd_order (h : BSWCase2 G t s K x p) {X : Subgroup G} (hX : X ≠ ⊥)
    (hXp : IsPGroup p X) : Odd (Nat.card (Subgroup.normalizer (X : Set G))) := by
  by_contra hodd
  have heven : 2 ∣ Nat.card (Subgroup.normalizer (X : Set G)) := by
    rcases Nat.even_or_odd (Nat.card (Subgroup.normalizer (X : Set G))) with he | ho
    · exact he.two_dvd
    · exact absurd ho hodd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype (Subgroup.normalizer (X : Set G)) := Fintype.ofFinite _
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card (G := ↥(Subgroup.normalizer (X : Set G))) 2
    (by simpa using heven)
  have huG : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe, hu]
  exact no_involution_normalizes h hX hXp huG u.2

end Bundle

end Work.BSW.S3
