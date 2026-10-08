import Mathlib
import Submission.Work.ZassenhausSuzuki.QSZPrelim
import Submission.Work.ZassenhausSuzuki.SzSetting
import Submission.Work.ZassenhausSuzuki.SingerData
import Submission.Work.ZassenhausSuzuki.SingerExists
import Submission.Work.ZassenhausSuzuki.Q0sub_card_eq_center_card
import Submission.Work.ZassenhausSuzuki.centralizer_twoPoint_eq
import Submission.Work.ZassenhausSuzuki.strongly_real_conj_structure
import Submission.Work.ZassenhausSuzuki.SelfCent.Assemble
import Submission.Work.ZassenhausSuzuki.singer_conj_inf_eq_bot
import Submission.Work.ZassenhausSuzuki.card_Q_le_q
import Submission.Work.Models.Basic
import Submission.Work.ThmF.ChV12.Q0sub_elementary

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausSuzuki.QSZ_abelian_of_order_three` — Suzuki 1962, Theorem 1

**Statement.**  In a simple Zassenhaus split rank-one configuration `H = Q ⋊ D` with `Q` a
`2`-group, if `s ∈ Q` is an involution with `(s * t) ^ 3 = 1` (`s = σ = ρ` in the structure
identity of Peterfalvi II Ch. V §2), then `Q` is abelian.

This is the one hard input of `Work.ZassenhausSuzuki.Q_suzuki_sq`: it is Suzuki 1962,
Theorem 1 (§8) / Baumeister–Grüninger arXiv:1011.5836, Theorem 1, in the formalisation.

This file is the *complete* proof: the step `C_G(S.V) = S.V`, `|N_G(S.V)| = 2(q+1)` is supplied by
`Work.ZassenhausSuzuki.SelfCent.singerV_centralizer_normalizer`, which is assembled in
`Submission/Work/ZassenhausSuzuki/SelfCent/` from the self-centralising argument (extracted from
`Work.ZassenhausSuzuki.singerV_conj_inf_eq_bot`) and the class count of Suzuki §8 p. 118
(`SelfCent.Counts` plus `Work.ZassenhausSuzuki.numClasses_stronglyReal`).

## Route (Suzuki 1962, §8, pp. 117–119)

Assume `¬ IsAbelianSubgroup Q`.  Then `Q` is a Suzuki two-group (`QSZPrelim.isSuzukiTwoGroup_Q`),
and the construction of the Singer cycle (`SingerExists.exists_singer_cycle_data`) produces
`S : SingerCycle.Data G H t` inside `X = ⟨Q₀, K, t⟩ ≅ PSL(2,q)`.  The two deep inputs are
`Work.ZassenhausSuzuki.strongly_real_conj_structure` (Suzuki's element structure) and
`Work.ZassenhausSuzuki.centralizer_twoPoint_eq`; from them
`Work.ZassenhausSuzuki.singer_centralizer_eq` gives `C_G(S.V) = S.V` and
`|N_G(S.V)| = 2(q+1)`, and `Work.ZassenhausSuzuki.singer_conj_inf_eq_bot` makes the distinct
conjugates of `S.V` meet trivially.  `S.V` meets every conjugate of `Q` and of
`D = twoPoint H t` trivially (odd order vs. a `2`-group, resp. coprime orders), so the counting
endgame `Work.ZassenhausSuzuki.card_Q_le_q` gives `|Q| ≤ q = |Q0sub H|`; as `Q0sub H ≤ Q`,
`|Q| = q`, so `Q = Q0sub H` is elementary abelian — a contradiction.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open LeanEval.GroupTheory.Defs

namespace Work.ZassenhausSuzuki

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}

/-- Two subgroups whose orders are coprime meet trivially. -/
theorem inf_eq_bot_of_coprime_card {A B : Subgroup G}
    (h : Nat.Coprime (Nat.card ↥A) (Nat.card ↥B)) : A ⊓ B = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  have h1 : orderOf x ∣ Nat.card ↥A := Subgroup.orderOf_dvd_natCard A hx.1
  have h2 : orderOf x ∣ Nat.card ↥B := Subgroup.orderOf_dvd_natCard B hx.2
  have h3 : orderOf x ∣ 1 := by
    have := Nat.dvd_gcd h1 h2
    rwa [Nat.coprime_iff_gcd_eq_one.mp h] at this
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

/-- If `A` has odd order and `gcd |A| |B|` divides `2`, then `A ⊓ B = ⊥`. -/
theorem inf_eq_bot_of_odd_of_gcd_dvd_two {A B : Subgroup G}
    (hA : Odd (Nat.card ↥A)) (h : Nat.gcd (Nat.card ↥A) (Nat.card ↥B) ∣ 2) : A ⊓ B = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  have h1 : orderOf x ∣ Nat.card ↥A := Subgroup.orderOf_dvd_natCard A hx.1
  have h2 : orderOf x ∣ Nat.card ↥B := Subgroup.orderOf_dvd_natCard B hx.2
  have h3 : orderOf x ∣ 2 := (Nat.dvd_gcd h1 h2).trans h
  have ho : Odd (orderOf x) := Odd.of_dvd_nat hA h1
  rcases (Nat.dvd_prime Nat.prime_two).mp h3 with h4 | h4
  · exact orderOf_eq_one_iff.mp h4
  · rw [h4] at ho
    exact absurd ho (Nat.not_odd_iff_even.mpr even_two)

theorem QSZ_abelian_of_order_three {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G)
    (H Q : Subgroup G) (t : G) (h : Submission.Blueprint.IsSplitRankOne H Q t)
    (hZ : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {s : G} (hsQ : s ∈ Q) (hs2 : orderOf s = 2) (hst : (s * t) ^ 3 = 1) :
    Submission.Blueprint.IsAbelianSubgroup Q := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  by_contra hnab
  have hSuz : IsSuzukiTwoGroup ↥Q := isSuzukiTwoGroup_Q hs h hZ h2 hnab
  -- ## `t` is an involution
  have ht2 : t * t = 1 := by
    have h1 := pow_orderOf_eq_one t
    rw [h.invol] at h1
    simpa [pow_two] using h1
  -- ## `HasFourGroup G`: two distinct involutions of `Q` commute (they lie in `H`)
  have hfour : HasFourGroup G := by
    obtain ⟨x, y, hx2, hy2, hxy⟩ := hSuz.2.2.1
    refine ⟨(x : G), (y : G), ?_, ?_, ?_, ?_⟩
    · rw [Subgroup.orderOf_coe]; exact hx2
    · rw [Subgroup.orderOf_coe]; exact hy2
    · intro hxy'
      exact hxy (Subtype.ext hxy')
    · exact invH_commute h h2 (x : G)
        ⟨h.le x.2, by rw [Subgroup.orderOf_coe]; exact hx2⟩ (y : G)
        ⟨h.le y.2, by rw [Subgroup.orderOf_coe]; exact hy2⟩
  -- ## the hypothesis bundle `SzHyp`
  have hst_ne : s * t ≠ 1 := by
    intro h1
    have hst : s = t := by
      calc s = s * t * t := by rw [mul_assoc, ht2, mul_one]
        _ = 1 * t := by rw [h1]
        _ = t := one_mul t
    exact h.not_mem (hst ▸ h.le hsQ)
  have hst3 : orderOf (s * t) = 3 := orderOf_eq_prime hst hst_ne
  have hsz : SzHyp H Q t s :=
    { split := h, zass := hZ, two := h2, four := hfour,
      s_mem := hsQ, s_inv := hs2, ord3 := hst3 }
  -- ## `|D| + 1 = q`
  have hDq : Nat.card ↥(twoPoint H t) + 1 = Nat.card ↥(Work.ThmF.Q0sub H) := by
    have h1 := Q0sub_card_eq_center_card h hZ h2 hSuz
    have h2' := twoPoint_card_add_one_eq_center_card h hZ h2 hSuz
    omega
  -- ## the Singer cycle
  obtain ⟨S⟩ := exists_singer_cycle_data hsz hnab
  obtain ⟨hcent, hnormV⟩ := SelfCent.singerV_centralizer_normalizer hsz hnab S
    (fun x hx2 hsr => strongly_real_conj_structure hsz hnab S hx2 hsr)
    (fun k hk hk1 => centralizer_twoPoint_eq h hZ h2 hk hk1)
  have hTI : ∀ g : G, conj g S.V ≠ S.V → S.V ⊓ conj g S.V = ⊥ :=
    singer_conj_inf_eq_bot hsz S hcent
  have hOddV : Odd (Nat.card ↥S.V) := singer_odd_card_V hsz S
  -- ## the two disjointness facts
  obtain ⟨n, hn, hqcard, -⟩ := Work.ZassenhausSuzuki.Shadow.ChV12.X5isoPSL2_of hsz
  obtain ⟨a, hQa⟩ := (IsPGroup.iff_card (p := 2)).mp h2
  have hVQ : ∀ g : G, S.V ⊓ conj g Q = ⊥ := by
    intro g
    refine inf_eq_bot_of_coprime_card ?_
    have hQc : Nat.card ↥(conj g Q) = 2 ^ a := by
      rw [Work.Models.card_conj]; exact hQa
    rw [hQc]
    exact (Nat.coprime_two_right.mpr hOddV).pow_right a
  have hVD : ∀ g : G, S.V ⊓ conj g (twoPoint H t) = ⊥ := by
    intro g
    refine inf_eq_bot_of_odd_of_gcd_dvd_two hOddV ?_
    have hDc : Nat.card ↥(conj g (twoPoint H t)) = 2 ^ n - 1 := by
      rw [Work.Models.card_conj]; omega
    rw [S.card_V, hqcard, hDc]
    have h1 : Nat.gcd (2 ^ n + 1) (2 ^ n - 1) ∣ (2 ^ n + 1) := Nat.gcd_dvd_left _ _
    have h2' : Nat.gcd (2 ^ n + 1) (2 ^ n - 1) ∣ (2 ^ n - 1) := Nat.gcd_dvd_right _ _
    have h3 : Nat.gcd (2 ^ n + 1) (2 ^ n - 1) ∣ (2 ^ n + 1) - (2 ^ n - 1) :=
      Nat.dvd_sub h1 h2'
    have h4 : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by
      have := Nat.one_le_two_pow (n := n)
      omega
    rwa [h4] at h3
  -- ## the count
  have hle : Nat.card ↥Q ≤ Nat.card ↥(Work.ThmF.Q0sub H) :=
    card_Q_le_q h hZ h2 (SzHyp.Q_ne_bot hsz) S.V hDq S.card_V hnormV hTI hVQ hVD
  have hQ0sub_le_Q : Work.ThmF.Q0sub H ≤ Q := by
    rw [Work.ThmF.Q0sub, Subgroup.closure_le]
    intro x hx
    rw [Work.ThmF.mem_Q0_iff] at hx
    rcases hx with ⟨hxH, hx2⟩ | rfl
    · have : x ∈ involutions (Q : Set G) := by
        rw [← involutions_H_eq_involutions_Q h h2]
        exact ⟨hxH, hx2⟩
      exact this.1
    · exact Q.one_mem
  have hQeq : Q = Work.ThmF.Q0sub H :=
    (Subgroup.eq_of_le_of_card_ge hQ0sub_le_Q hle).symm
  -- ## contradiction: `Q = Q0sub H` is elementary abelian
  have hcomm := invH_commute h h2
  have habel : IsAbelianSubgroup Q := by
    rw [hQeq]
    exact (Work.ThmF.ChV12.Q0sub_elementary H hcomm).2.1
  exact hnab habel

end Work.ZassenhausSuzuki
