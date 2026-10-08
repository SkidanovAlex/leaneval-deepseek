import Mathlib
import Submission.Work.ZassenhausSuzuki.QSZ_abelian_of_order_three
import Submission.Work.ZassenhausSuzuki.QSZPrelim
import Submission.Work.ZassenhausSuzuki.SzSetting

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausSuzuki.QSZ_false_of_order_three_suz`

**Statement.**  A split rank-one Zassenhaus datum `H = Q ⋊ D` whose root group `Q` is a
*Suzuki two-group*, together with an involution `s ∈ Q` with `(s * t) ^ 3 = 1`, is impossible.

**Why it is true.**  `IsSuzukiTwoGroup ↥Q` supplies the non-abelianness of `Q` *and* is exactly
the hypothesis under which the counting argument of Suzuki 1962, §8 (formalised on disk as
`Work.ZassenhausSuzuki.QSZ_abelian_of_order_three`) runs.  That argument — the Singer cycle
`V ≤ X = ⟨Q₀, K, t⟩ ≅ PSL(2,q)`, `C_G(V) = V`, `|N_G(V)| = 2(q+1)`, the trivial intersection of
the conjugates of `V` with `Q` and with `D`, and the resulting count `|Q| ≤ q = |Q0sub H|` —
never uses the `IsSimpleGroup G` hypothesis of its statement: `Q` is abelian.  Since a Suzuki
two-group is by definition non-abelian, the datum cannot exist.

The formal content here is therefore a replay of the proof of
`QSZ_abelian_of_order_three` with

* the `IsSimpleGroup G` hypothesis dropped (it is unused there), and
* `IsSuzukiTwoGroup ↥Q` taken as a *hypothesis* rather than derived from `¬ IsAbelianSubgroup Q`
  (the derivation `Work.ZassenhausSuzuki.isSuzukiTwoGroup_Q` is not needed), while
* `¬ IsAbelianSubgroup Q` — which the Singer-cycle construction needs — is read off from the
  Suzuki structure of `Q`.

-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open LeanEval.GroupTheory.Defs

namespace Work.ZassenhausSuzuki

open Submission.Blueprint

theorem QSZ_false_of_order_three_suz {G : Type} [Group G] [Finite G]
    (H Q : Subgroup G) (t : G) (h : Submission.Blueprint.IsSplitRankOne H Q t)
    (hZ : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (hSuz : Submission.Blueprint.IsSuzukiTwoGroup ↥Q)
    {s : G} (hsQ : s ∈ Q) (hs2 : orderOf s = 2) (hst : (s * t) ^ 3 = 1) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  -- ## `Q` is not abelian, by the Suzuki structure of `Q`
  have hnab : ¬ IsAbelianSubgroup Q := by
    intro hab
    obtain ⟨x, y, hxy⟩ := hSuz.2.1
    exact hxy (Subtype.ext (by simpa using hab x x.2 y y.2))
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
