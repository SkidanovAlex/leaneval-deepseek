import Mathlib
import Submission.Work.BSW.Concl
import Submission.Work.BSW.Cases.sylow_two_structure
import Submission.Work.BSW.Cases.K2Count.no_involution_centralizes_odd
import Submission.Work.BSW.Cases.K4.card_normalizer_le_two_mul_card_centralizer
import Submission.Work.BSW.Cases.K4.inverts_of_fixedPointFree_involution

set_option linter.style.haveILetI false

namespace Work.BSW.Cases.K2Count

open Subgroup

/-- **The centralizer of an order-`3` subgroup has odd order** (Bender 1974, §1).

Suppose `2 ∣ |C_G(T)|`; Cauchy gives an involution `z ∈ C_G(T)`, and `|T| = 3` together with
Cauchy gives a nonidentity `y ∈ T` of order `3`, i.e. of odd order.  Since `z` centralizes `T` it
commutes with `y`, contradicting `Work.BSW.Cases.K2Count.no_involution_centralizes_odd`. -/
theorem odd_card_centralizer_of_card_three {G : Type} [Group G] [Finite G] {t s : G}
    {K : Subgroup G} (h : Work.GW2.BSWHyps2 G t s K) (hk : Nat.card ↥K = 2) (T : Subgroup G)
    (hT : Nat.card ↥T = 3) :
    Odd (Nat.card ↥(Subgroup.centralizer (T : Set G))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hodd
  rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hodd
  -- an involution `z` of `C_G(T)`
  obtain ⟨z, hz⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.centralizer (T : Set G))) 2 hodd
  -- a nonidentity element `y` of `T`, of order `3`
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥T) 3 (by rw [hT])
  have hzG : orderOf (z : G) = 2 := (Subgroup.orderOf_coe z).trans hz
  have hyG : orderOf (y : G) = 3 := (Subgroup.orderOf_coe y).trans hy
  have hyne : (y : G) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hyG
    exact absurd hyG (by norm_num)
  have hyodd : Odd (orderOf (y : G)) := by rw [hyG]; norm_num
  exact (Work.BSW.Cases.K2Count.no_involution_centralizes_odd h hk (y : G) hyne hyodd
    (z : G) hzG) ((Subgroup.mem_centralizer_iff.mp z.2) (y : G) y.2).symm

/-- **Pure group theory (no BSW hypotheses).**  If `T ≤ G` is a subgroup of order `3` whose
normalizer is strictly larger than its centralizer, then `|N_G(T)| = 2 · |C_G(T)|`.

`N_G(T)` acts on `T` by conjugation with kernel `C_G(T)`, and `|MulAut T| = Nat.totient 3 = 2`, so
`|N_G(T)| ≤ 2 · |C_G(T)|` (the already proved
`Work.BSW.Cases.K4.card_normalizer_le_two_mul_card_centralizer`).  Also `C_G(T) ≤ N_G(T)`, so
`|C_G(T)| ∣ |N_G(T)|`, and `C_G(T) ≠ N_G(T)` by hypothesis, so `|C_G(T)| < |N_G(T)|`; writing
`|N_G(T)| = k · |C_G(T)|` gives `2 ≤ k ≤ 2`. -/
theorem normalizer_card_eq_two_mul_centralizer {G : Type} [Group G] [Finite G] (T : Subgroup G)
    (hT : Nat.card ↥T = 3)
    (hne : Subgroup.normalizer (T : Set G) ≠ Subgroup.centralizer (T : Set G)) :
    Nat.card ↥(Subgroup.normalizer (T : Set G)) =
      2 * Nat.card ↥(Subgroup.centralizer (T : Set G)) := by
  have hCN : Subgroup.centralizer (T : Set G) ≤ Subgroup.normalizer (T : Set G) :=
    Subgroup.centralizer_le_normalizer (T : Set G)
  have hbound : Nat.card ↥(Subgroup.normalizer (T : Set G)) ≤
      2 * Nat.card ↥(Subgroup.centralizer (T : Set G)) :=
    Work.BSW.Cases.K4.card_normalizer_le_two_mul_card_centralizer T hT
  have hdvd : Nat.card ↥(Subgroup.centralizer (T : Set G)) ∣
      Nat.card ↥(Subgroup.normalizer (T : Set G)) := Subgroup.card_dvd_of_le hCN
  have hCpos : 0 < Nat.card ↥(Subgroup.centralizer (T : Set G)) := Nat.card_pos
  have hNpos : 0 < Nat.card ↥(Subgroup.normalizer (T : Set G)) := Nat.card_pos
  -- `|C| < |N|`
  have hlt : Nat.card ↥(Subgroup.centralizer (T : Set G)) <
      Nat.card ↥(Subgroup.normalizer (T : Set G)) := by
    rcases lt_or_eq_of_le (Nat.le_of_dvd hNpos hdvd) with hlt' | heq
    · exact hlt'
    · exact absurd (Subgroup.eq_of_le_of_card_ge hCN (le_of_eq heq.symm))
        (fun hc => hne hc.symm)
  obtain ⟨k, hk⟩ := hdvd
  rw [hk] at hlt
  have hkge : 2 ≤ k := by
    have h1 : Nat.card ↥(Subgroup.centralizer (T : Set G)) * 1 <
        Nat.card ↥(Subgroup.centralizer (T : Set G)) * k := by
      rw [mul_one]
      exact hlt
    have h2 : 1 < k := Nat.lt_of_mul_lt_mul_left h1
    omega
  have hkle : k ≤ 2 := by
    rw [hk] at hbound
    rw [mul_comm 2 (Nat.card ↥(Subgroup.centralizer (T : Set G)))] at hbound
    exact Nat.le_of_mul_le_mul_left hbound hCpos
  have hk2 : k = 2 := le_antisymm hkle hkge
  rw [hk, hk2]
  exact Nat.mul_comm _ _

/-- Elements of `N_G(T)` conjugate `C_G(T)` into itself: conjugation by `g ∈ N_G(T)` is a group
automorphism carrying `T` onto itself, hence `C_G(T)` onto itself. -/
theorem conj_mem_centralizer_of_mem_normalizer {G : Type} [Group G] (T : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (T : Set G)) {c : G}
    (hc : c ∈ Subgroup.centralizer (T : Set G)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (T : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro x hx
  have hgx : g⁻¹ * x * g ∈ T := by
    have h1 := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (T : Set G)).inv_mem hg) x).mp hx
    simpa using h1
  calc x * (g * c * g⁻¹) = g * ((g⁻¹ * x * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * x * g)) * g⁻¹ := by rw [hc (g⁻¹ * x * g) hgx]
    _ = (g * c * g⁻¹) * x := by group

/-- **Pure group theory (no BSW hypotheses).**  Let `C ≤ N` be subgroups of a finite group with
`C` of index `2` in `N` and `|C|` odd, and let `w ∈ N` be an involution inverting every element of
`C` (i.e. `w * c * w⁻¹ = c⁻¹` for `c ∈ C`).  Then

`#{u : G // orderOf u = 2 ∧ u ∈ N} = |C|`.

Indeed `w ∉ C` (else `2 = orderOf w ∣ |C|`, contradicting oddness), and no element of `C` is an
involution for the same reason.  Since `C` has index two in `N`, an element `u ∈ N` lies outside
`C` exactly when `u * w ∈ C` (`Subgroup.mul_mem_iff_of_index_two`); hence `c ↦ c * w` is a
bijection `↥C → {u : G // orderOf u = 2 ∧ u ∈ N}`: its values lie in `N`, are `≠ 1` (else
`w = c⁻¹ ∈ C`) and satisfy `(c * w) * (c * w) = 1` because `w * c = (w * c * w⁻¹) * w² = c⁻¹ * w`;
conversely `u ↦ u * w` is a left inverse. -/
theorem inv_count_of_index_two_inverting {G : Type} [Group G] [Finite G]
    (C N : Subgroup G) (hCN : C ≤ N) (hidx : (C.subgroupOf N).index = 2)
    (hodd : Odd (Nat.card ↥C)) (w : G) (hwN : w ∈ N) (hw2 : orderOf w = 2)
    (hinv : ∀ c ∈ C, w * c * w⁻¹ = c⁻¹) :
    Nat.card {u : G // orderOf u = 2 ∧ u ∈ N} = Nat.card ↥C := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hw2m : w * w = 1 := by
    have h1 : w ^ 2 = 1 := by rw [← hw2]; exact pow_orderOf_eq_one w
    rwa [pow_two] at h1
  have hnot2 : ¬ 2 ∣ Nat.card ↥C :=
    fun h2 => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  have hwC : w ∉ C := by
    intro hwC
    have hdvd : orderOf w ∣ Nat.card ↥C := by
      have h1 := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hwC)
      rwa [Nat.card_zpowers] at h1
    rw [hw2] at hdvd
    exact hnot2 hdvd
  have hmulmem : ∀ u : G, u ∈ N → u ∉ C → u * w ∈ C := by
    intro u huN huC
    have key : (⟨u, huN⟩ : ↥N) * (⟨w, hwN⟩ : ↥N) ∈ C.subgroupOf N ↔
        ((⟨u, huN⟩ : ↥N) ∈ C.subgroupOf N ↔ (⟨w, hwN⟩ : ↥N) ∈ C.subgroupOf N) :=
      Subgroup.mul_mem_iff_of_index_two (G := ↥N) hidx
    have key2 : u * w ∈ C ↔ (u ∈ C ↔ w ∈ C) := by
      simpa [Subgroup.mem_subgroupOf] using key
    exact key2.mpr (iff_of_false huC hwC)
  have hnotmem : ∀ u : G, orderOf u = 2 → u ∈ N → u ∉ C := by
    intro u hu2 _ huC
    have hdvd : orderOf u ∣ Nat.card ↥C := by
      have h1 := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr huC)
      rwa [Nat.card_zpowers] at h1
    rw [hu2] at hdvd
    exact hnot2 hdvd
  refine Nat.card_congr
    { toFun := fun u => ⟨(u : G) * w, hmulmem (u : G) u.2.2 (hnotmem (u : G) u.2.1 u.2.2)⟩
      invFun := fun c => ⟨(c : G) * w, ⟨?_, N.mul_mem (hCN c.2) hwN⟩⟩
      left_inv := fun u => Subtype.ext (by
        show ((u : G) * w) * w = (u : G)
        rw [mul_assoc, hw2m, mul_one])
      right_inv := fun c => Subtype.ext (by
        show ((c : G) * w) * w = (c : G)
        rw [mul_assoc, hw2m, mul_one]) }
  -- `orderOf (c * w) = 2`
  have hsq : ((c : G) * w) ^ 2 = 1 := by
    rw [pow_two]
    calc ((c : G) * w) * ((c : G) * w)
        = (c : G) * (w * (c : G) * w⁻¹) * (w * w) := by group
      _ = (c : G) * (c : G)⁻¹ * (w * w) := by rw [hinv (c : G) c.2]
      _ = 1 := by rw [mul_inv_cancel, hw2m, mul_one]
  have hne1 : (c : G) * w ≠ 1 := by
    intro h1
    apply hwC
    have h2 : w = (c : G)⁻¹ := by
      have hh : (c : G) * w = (c : G) * (c : G)⁻¹ := by rw [h1, mul_inv_cancel]
      exact mul_left_cancel hh
    rw [h2]
    exact C.inv_mem c.2
  exact orderOf_eq_prime hsq hne1

/-- **An involution of `N_G(T)` inverts `C_G(T)`** (Bender 1974, §1, p. 230): if `T` has order `3`
and `N_G(T) ≠ C_G(T)`, then `N_G(T) = C_G(T) ⟨w⟩` for an involution `w` which inverts `C_G(T)`;
consequently *every* element of `N_G(T) ∖ C_G(T)` is an involution and

`#{u : G // orderOf u = 2 ∧ u ∈ N_G(T)} = |C_G(T)|`.

Proof outline (all elementary):

* `N_G(T)/C_G(T)` embeds into `Aut(T)` (`Subgroup.normalizerMonoidHom`, or the action of `N_G(T)`
  on `T` by conjugation), and `|Aut(C₃)| = 2` because `T` is generated by an element of prime order
  `3` (an automorphism sends a generator to a generator, and `T` has exactly two generators);
  hence `|N_G(T) : C_G(T)| = 2` (it is not `1` by `hne`);
* `C_G(T)` has odd order: an involution centralizing `T` would commute with a nonidentity element
  of odd order, impossible by `Work.BSW.Cases.K2Count.no_involution_centralizes_odd` (which is
  proved and sorry-free — import it);
* hence `|N_G(T)| = 2 · |C_G(T)|` is even and Cauchy gives an involution `w ∈ N_G(T)`; as
  `C_G(T)` is odd, `w ∉ C_G(T)`, so `N_G(T) = C_G(T) ⊔ ⟨w⟩`;
* conjugation by `w` is an automorphism `σ` of `C_G(T)` with `σ² = id` (`w² = 1`) and no fixed
  point other than `1` (again by `no_involution_centralizes_odd` and the oddness of `C_G(T)`);
  then `σ(c) = c⁻¹` for all `c` — the map `c ↦ c * σ c⁻¹` is injective, hence bijective, and every
  element `c * σ c⁻¹` is inverted by `σ`;
* so `(w * c) * (w * c) = w * c * w * c = σ(c) * c = 1` for every `c ∈ C_G(T)`: all `|C_G(T)|`
  elements of the nontrivial coset are involutions, and `C_G(T)` has none.

No simplicity, no `3 ∤ n₂` and no (A)-type input is needed; the hypothesis `hne` is what rules out
the degenerate case `N_G(T) = C_G(T)`, in which there would be no involutions at all. -/
theorem k2_inv_count_of_ne {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) (hk : Nat.card ↥K = 2) (T : Subgroup G)
    (hT : Nat.card T = 3)
    (hne : Subgroup.normalizer (T : Set G) ≠ Subgroup.centralizer (T : Set G)) :
    Nat.card {u : G // orderOf u = 2 ∧ u ∈ Subgroup.normalizer (T : Set G)} =
      Nat.card ↥(Subgroup.centralizer (T : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCN : Subgroup.centralizer (T : Set G) ≤ Subgroup.normalizer (T : Set G) :=
    Subgroup.centralizer_le_normalizer (T : Set G)
  have hcardN : Nat.card ↥(Subgroup.normalizer (T : Set G)) =
      2 * Nat.card ↥(Subgroup.centralizer (T : Set G)) :=
    normalizer_card_eq_two_mul_centralizer T hT hne
  have hoddC : Odd (Nat.card ↥(Subgroup.centralizer (T : Set G))) :=
    odd_card_centralizer_of_card_three h hk T hT
  -- an involution `w ∈ N_G(T)`
  obtain ⟨w₀, hw₀⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(Subgroup.normalizer (T : Set G))) 2 (by rw [hcardN]; exact dvd_mul_right 2 _)
  let w : G := (w₀ : G)
  have hwN : w ∈ Subgroup.normalizer (T : Set G) := w₀.2
  have hw2 : orderOf w = 2 := (Subgroup.orderOf_coe w₀).trans hw₀
  have hw2m : w * w = 1 := by
    have h1 : w ^ 2 = 1 := by rw [← hw2]; exact pow_orderOf_eq_one w
    rwa [pow_two] at h1
  -- `w` normalizes `C_G(T)`
  have hnormw : w ∈ Subgroup.normalizer
      ((Subgroup.centralizer (T : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact conj_mem_centralizer_of_mem_normalizer T hwN hx
    · intro hx
      have h2 := conj_mem_centralizer_of_mem_normalizer T
        ((Subgroup.normalizer (T : Set G)).inv_mem hwN) hx
      have h3 : w⁻¹ * (w * x * w⁻¹) * (w⁻¹)⁻¹ = x := by group
      rwa [h3] at h2
  -- `w` acts fixed-point-freely on `C_G(T)`
  have hfix : ∀ a ∈ Subgroup.centralizer (T : Set G), w * a * w⁻¹ = a → a = 1 := by
    intro a ha hafix
    by_contra ha1
    have hdvd : orderOf a ∣ Nat.card ↥(Subgroup.centralizer (T : Set G)) := by
      have h1 := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr ha)
      rwa [Nat.card_zpowers] at h1
    have hodd : Odd (orderOf a) :=
      Nat.not_even_iff_odd.mp fun he =>
        (Nat.not_even_iff_odd.mpr hoddC) (even_iff_two_dvd.mpr (dvd_trans (even_iff_two_dvd.mp he) hdvd))
    have hcomm : w * a = a * w := by
      have h1 : (w * a * w⁻¹) * w = a * w := congrArg (fun z => z * w) hafix
      rw [show (w * a * w⁻¹) * w = w * a by group] at h1
      exact h1
    exact (Work.BSW.Cases.K2Count.no_involution_centralizes_odd h hk a ha1 hodd w hw2) hcomm
  have hinv : ∀ c ∈ Subgroup.centralizer (T : Set G), w * c * w⁻¹ = c⁻¹ :=
    (Work.BSW.Cases.K4.inverts_of_fixedPointFree_involution
      (Subgroup.centralizer (T : Set G)) w hw2m hnormw hfix).2
  -- `C_G(T)` has index two in `N_G(T)`
  have hidx : ((Subgroup.centralizer (T : Set G)).subgroupOf
      (Subgroup.normalizer (T : Set G))).index = 2 := by
    have h1 : (Subgroup.centralizer (T : Set G)).relIndex (Subgroup.normalizer (T : Set G)) *
        Nat.card ↥(Subgroup.centralizer (T : Set G)) =
        Nat.card ↥(Subgroup.normalizer (T : Set G)) := by
      have hh := Subgroup.relIndex_mul_card (Subgroup.centralizer (T : Set G))
        (Subgroup.normalizer (T : Set G))
      rwa [inf_of_le_left hCN] at hh
    have h2 : (Subgroup.centralizer (T : Set G)).relIndex (Subgroup.normalizer (T : Set G)) *
        Nat.card ↥(Subgroup.centralizer (T : Set G)) =
        2 * Nat.card ↥(Subgroup.centralizer (T : Set G)) := by
      rw [h1, hcardN]
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥(Subgroup.centralizer (T : Set G)))) h2
  exact inv_count_of_index_two_inverting (Subgroup.centralizer (T : Set G))
    (Subgroup.normalizer (T : Set G)) hCN hidx hoddC w hwN hw2 hinv

end Work.BSW.Cases.K2Count
