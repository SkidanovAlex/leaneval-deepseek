import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.StageB.StepB.mem_of_pow_card_eq_one_of_mem_sylow

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.StageB.StepB.mem_of_pow_card_eq_one`

In a finite group whose Sylow subgroups are all cyclic, an element `x` with `x ^ |N| = 1`
lies in every normal subgroup `N` (Peterfalvi, Bender–Suzuki, §2).

The proof is the per-prime argument: for a prime `p`, the `p`-part `y = x ^ (|x| / p ^ a)`
of `x` (where `p ^ a` is the `p`-part of the order of `x`) lies in some Sylow `p`-subgroup
`P`, which is cyclic; `P ⊓ N` is a Sylow `p`-subgroup of `N` of order `p ^ b` with `a ≤ b`,
so by the cyclic-group criterion `⟨y⟩ ≤ P ⊓ N ≤ N`.  Since the `p`-parts of `x` are
pairwise coprime powers of `x`, `|N ∩ ⟨x⟩|` is divisible by each `p ^ a`, hence equals
`|⟨x⟩|`, so `⟨x⟩ ≤ N` and `x ∈ N`.
-/

set_option linter.style.haveILetI false

namespace Work.PSU3.StageB.StepB

/-- If `A ≤ B` are subgroups of a group `G`, then `|A|` divides `|B|`. -/
theorem card_dvd_card_of_le {G : Type*} [Group G] {A B : Subgroup G} (h : A ≤ B) :
    Nat.card ↥A ∣ Nat.card ↥B := by
  have := Subgroup.card_subgroup_dvd_card (A.subgroupOf B)
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv] at this

/-- The `p`-part `x ^ (n / p ^ (n.factorization p))` of an element `x` of order `n` has order
`p ^ (n.factorization p)`. -/
theorem orderOf_pow_div_factorization {K : Type*} [Group K] [Finite K] {x : K} {p : ℕ}
    (hp : p.Prime) {n : ℕ} (hn : orderOf x = n) (hn0 : n ≠ 0) :
    orderOf (x ^ (n / p ^ n.factorization p)) = p ^ n.factorization p := by
  have hpa_dvd : p ^ n.factorization p ∣ n := Nat.ordProj_dvd n p
  have hdiv : (n / p ^ n.factorization p) ∣ n := Nat.div_dvd_of_dvd hpa_dvd
  rw [orderOf_pow, hn, Nat.gcd_eq_right hdiv]
  have hmul : p ^ n.factorization p * (n / p ^ n.factorization p) = n :=
    Nat.mul_div_cancel' hpa_dvd
  have hpos : 0 < n / p ^ n.factorization p :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpa_dvd) (pow_pos hp.pos _)
  exact (Nat.eq_div_of_mul_eq_right (Nat.pos_iff_ne_zero.mp hpos)
    (by rw [mul_comm]; exact hmul)).symm

/-- The `⊤` form of the main theorem: in a finite Z-group, `x ^ |N| = 1` forces `x ∈ N` for a
normal subgroup `N`. -/
theorem mem_of_pow_card_eq_one_of_isZGroup {K : Type*} [Group K] [Finite K] [IsZGroup K]
    (N : Subgroup K) [N.Normal] {x : K} (hxN : x ^ Nat.card ↥N = 1) : x ∈ N := by
  classical
  set H : Subgroup K := Subgroup.zpowers x with hH
  have hxH : x ∈ H := by rw [hH]; exact Subgroup.mem_zpowers x
  have hcardH : Nat.card ↥H = orderOf x := by rw [hH]; exact Nat.card_zpowers x
  have hn0 : orderOf x ≠ 0 := by
    rw [← hcardH]
    exact Nat.card_ne_zero.mpr ⟨⟨x, hxH⟩, inferInstance⟩
  have hxdvdN : orderOf x ∣ Nat.card ↥N := orderOf_dvd_iff_pow_eq_one.mpr hxN
  have key : ∀ p, p.Prime → p ^ (orderOf x).factorization p ∣ Nat.card ↥(N.subgroupOf H) := by
    intro p hp
    haveI : Fact p.Prime := ⟨hp⟩
    set y : K := x ^ (orderOf x / p ^ (orderOf x).factorization p) with hy
    have hyH : y ∈ H := by
      rw [hH, hy]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _
    have hyord : orderOf y = p ^ (orderOf x).factorization p := by
      rw [hy]
      exact orderOf_pow_div_factorization hp rfl hn0
    have hyN : y ∈ N := by
      have hIsP : IsPGroup p (Subgroup.zpowers y) :=
        IsPGroup.of_card (by rw [Nat.card_zpowers, hyord])
      obtain ⟨P, hyP⟩ := hIsP.exists_le_sylow
      refine mem_of_pow_card_eq_one_of_mem_sylow P (hyP (Subgroup.mem_zpowers y)) ?_
      rw [← orderOf_dvd_iff_pow_eq_one, hyord]
      exact dvd_trans (Nat.ordProj_dvd (orderOf x) p) hxdvdN
    have hyNh : (⟨y, hyH⟩ : ↥H) ∈ N.subgroupOf H := Subgroup.mem_subgroupOf.mpr hyN
    have hlea : Subgroup.zpowers (⟨y, hyH⟩ : ↥H) ≤ N.subgroupOf H :=
      Subgroup.zpowers_le.mpr hyNh
    have hdvd2 : Nat.card ↥(Subgroup.zpowers (⟨y, hyH⟩ : ↥H)) ∣
        Nat.card ↥(N.subgroupOf H) := card_dvd_card_of_le hlea
    have hcardz : Nat.card ↥(Subgroup.zpowers (⟨y, hyH⟩ : ↥H)) =
        p ^ (orderOf x).factorization p := by
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, hyord]
    rwa [hcardz] at hdvd2
  have hdvdH : Nat.card ↥H ∣ Nat.card ↥(N.subgroupOf H) := by
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p k hp hpk
    rw [hcardH] at hpk
    have hk_le : k ≤ (orderOf x).factorization p :=
      (hp.pow_dvd_iff_le_factorization hn0).mp hpk
    exact dvd_trans (Nat.pow_dvd_pow p hk_le) (key p hp)
  have hcard : Nat.card ↥(N.subgroupOf H) = Nat.card ↥H := by
    refine le_antisymm (Subgroup.card_le_card_group _) ?_
    exact Nat.le_of_dvd Nat.card_pos hdvdH
  have htop : N.subgroupOf H = ⊤ := Subgroup.eq_top_of_card_eq _ hcard
  have hHN : H ≤ N := by
    intro h hh
    have hmem : (⟨h, hh⟩ : ↥H) ∈ N.subgroupOf H := by
      rw [htop]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hmem
  exact hHN hxH

theorem mem_of_pow_card_eq_one {G : Type} [Group G] [Finite G] {D N : Subgroup G}
    (hND : N ≤ D) (hN : (N.subgroupOf D).Normal)
    (hcyc : ∀ (p : ℕ), p.Prime → ∀ (P : Sylow p ↥D), IsCyclic ↥P)
    {x : G} (hx : x ∈ D) (hxN : x ^ Nat.card ↥N = 1) : x ∈ N := by
  haveI : IsZGroup ↥D := ⟨hcyc⟩
  haveI : (N.subgroupOf D).Normal := hN
  have hcardND : Nat.card ↥(N.subgroupOf D) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hND).toEquiv
  have hpow : ((⟨x, hx⟩ : ↥D) ^ Nat.card ↥(N.subgroupOf D) : ↥D) = 1 := by
    rw [hcardND]
    apply Subtype.ext
    simpa using hxN
  exact Subgroup.mem_subgroupOf.mp (mem_of_pow_card_eq_one_of_isZGroup (N.subgroupOf D) hpow)

end Work.PSU3.StageB.StepB
