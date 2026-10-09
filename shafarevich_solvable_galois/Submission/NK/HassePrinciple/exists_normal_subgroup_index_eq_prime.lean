import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace NK.HassePrinciple

private theorem exists_normal_subgroup_index_eq_prime_aux :
    ∀ N : ℕ, ∀ {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime],
      Nat.card G = N → IsPGroup p G → Nontrivial G →
      ∃ N' : Subgroup G, N'.Normal ∧ N'.index = p := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro G _ _ p hpF hcard hG hnt
    by_cases hp : Nat.card G = p
    · exact ⟨⊥, Subgroup.normal_bot, by rw [Subgroup.index_bot, hp]⟩
    · obtain ⟨k, hk0, hk⟩ := hG.nontrivial_iff_card.mp hnt
      have hk1 : k ≠ 1 := by
        rintro rfl
        exact hp (by rw [hk, pow_one])
      -- the center is a nontrivial p-group, so it contains an element of order p
      haveI : Nontrivial ↥(Subgroup.center G) := hG.center_nontrivial
      have hpdvd : p ∣ Nat.card ↥(Subgroup.center G) := by
        obtain ⟨j, hj0, hj⟩ :=
          (hG.to_subgroup (Subgroup.center G)).nontrivial_iff_card.mp inferInstance
        rw [hj]
        exact dvd_pow_self p (ne_of_gt hj0)
      obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center G)) p hpdvd
      let H : Subgroup G := Subgroup.zpowers (z : G)
      have hHle : H ≤ Subgroup.center G := Subgroup.zpowers_le.mpr z.2
      have hHcard : Nat.card ↥H = p := by
        show Nat.card ↥(Subgroup.zpowers ((z : ↥(Subgroup.center G)) : G)) = p
        rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz]
      have hHnormal : H.Normal := by
        refine Subgroup.Normal.mk fun n hn g => ?_
        have hnZ : n ∈ Subgroup.center G := hHle hn
        have hcomm : g * n = n * g := (Subgroup.mem_center_iff.mp hnZ) g
        rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
        exact hn
      haveI : H.Normal := hHnormal
      -- the quotient by H has order p ^ (k - 1)
      have hquot : Nat.card (G ⧸ H) = p ^ (k - 1) := by
        have h1 : p * H.index = p ^ k := by
          have h' := Subgroup.card_mul_index H
          rw [hHcard, hk] at h'
          exact h'
        have hkp : k = (k - 1) + 1 := (Nat.succ_pred_eq_of_pos hk0).symm
        rw [hkp, pow_succ'] at h1
        have hcancel : H.index = p ^ (k - 1) := Nat.mul_left_cancel hpF.out.pos h1
        rw [← Subgroup.index_eq_card H, hcancel]
      haveI : Nontrivial (G ⧸ H) := by
        rw [← Finite.one_lt_card_iff_nontrivial, hquot]
        exact one_lt_pow₀ hpF.out.one_lt (by omega)
      have hlt : Nat.card (G ⧸ H) < N := by
        rw [← hcard, hquot, hk]
        exact Nat.pow_lt_pow_right hpF.out.one_lt (by omega)
      obtain ⟨Nbar, hNbar_normal, hNbar_index⟩ :=
        ih (Nat.card (G ⧸ H)) hlt (G := G ⧸ H) (p := p) rfl (hG.to_quotient H) inferInstance
      refine ⟨Subgroup.comap (QuotientGroup.mk' H) Nbar, hNbar_normal.comap _, ?_⟩
      rw [Subgroup.index_comap_of_surjective Nbar (QuotientGroup.mk'_surjective H)]
      exact hNbar_index

theorem exists_normal_subgroup_index_eq_prime {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hG : IsPGroup p G) (h : Nontrivial G) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = p :=
  exists_normal_subgroup_index_eq_prime_aux (Nat.card G) rfl hG h

end NK.HassePrinciple
