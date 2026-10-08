import Submission.Work.ZassenhausSuzuki.QSZPrelim
import Submission.Work.ZassenhausSuzuki.QSZPowFour
import Submission.Work.ZassenhausSuzuki.QSZ_abelian_of_order_three
import Submission.Work.Higman.card_eq_sq_or_cube

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausSuzuki.Q_suzuki_sq`

The second half of the target: in a simple Zassenhaus split rank-one configuration with a
non-abelian `2`-group `Q`, the order of `Q` is the square of the order of its centre.

The preliminary material (`IsSuzukiTwoGroup ↥Q`, Higman's dichotomy `|Q| = q|^2` or `q^3`, and
the number theory for the `q^3` case) lives in `QSZPrelim`; the remaining input — Suzuki 1962,
Theorem 1 (`σ = ρ` in the structure identity forces `Q` abelian) — is `QSZThm1`.
-/

namespace Work.ZassenhausSuzuki

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-! ## The target theorem -/

set_option maxHeartbeats 2000000 in
theorem Q_suzuki_sq {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G) (H Q : Subgroup G)
    (t : G) (h : Submission.Blueprint.IsSplitRankOne H Q t)
    (hZ : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q) :
    Submission.Blueprint.IsSuzukiTwoGroup ↥Q ∧
      Nat.card ↥Q = Nat.card ↥(Subgroup.center ↥Q) ^ 2 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hSuz : IsSuzukiTwoGroup ↥Q := isSuzukiTwoGroup_Q hs h hZ h2 hnab
  refine ⟨hSuz, ?_⟩
  obtain ⟨h2g⟩ := (Work.Higman.isSuzukiTwoGroup_iff_nonempty_isSuzuki2Grp (P := ↥Q)).mp hSuz
  rcases Work.Higman.card_eq_sq_or_cube h2g with hsq | hcu
  · exact hsq
  exfalso
  -- elementary facts about `t`
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rw [h.invol] at this
    simpa [pow_two] using this
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  -- the structure identity (`σ` the distinguished involution, `ρ` its partner)
  obtain ⟨⟨σ, ρ⟩, ⟨hσQ, hσord, hρQ, hσρrel⟩, huniq⟩ :=
    Work.ThmF.ChV12.structureIdentity (Work.ThmF.IsSplitRankOne.toData h)
  have hσQ : σ ∈ Q := hσQ
  have hσord : orderOf σ = 2 := hσord
  have hρQ : ρ ∈ Q := hρQ
  have hσρrel : t * σ * t⁻¹ = ρ * t * ρ⁻¹ := hσρrel
  -- Higman: exponent `4`, and `σ` is central
  have hρ4 : ρ ^ 4 = 1 := by
    have := suzuki_pow_four_eq_one hSuz (⟨ρ, hρQ⟩ : ↥Q)
    simpa using congrArg Subtype.val this
  have hσne : σ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hσord
    exact absurd hσord (by norm_num)
  have hσ2 : σ * σ = 1 := by
    have := pow_orderOf_eq_one σ
    rw [hσord] at this
    simpa [pow_two] using this
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ2
  have hσQord : orderOf (⟨σ, hσQ⟩ : ↥Q) = 2 := by
    rw [← Subgroup.orderOf_coe (⟨σ, hσQ⟩ : ↥Q)]; exact hσord
  have hσcent : (⟨σ, hσQ⟩ : ↥Q) ∈ Subgroup.center ↥Q := h2g.invol_mem_center hσQord
  have hσρcomm : σ * ρ = ρ * σ := by
    have := (Subgroup.mem_center_iff.mp hσcent) (⟨ρ, hρQ⟩ : ↥Q)
    exact (congrArg Subtype.val this).symm
  -- the structure identity in Suzuki's orientation (`t s t = r⁻¹ t r`)
  have hσρrel' : t * σ * t⁻¹ = (ρ⁻¹)⁻¹ * t * ρ⁻¹ := by rw [inv_inv]; exact hσρrel
  have hρinvQ : ρ⁻¹ ∈ Q := Q.inv_mem hρQ
  obtain ⟨k, hk⟩ := QSZ_rho_pow_eq_sigma hs H Q t h hZ h2 hσQ hσord hρinvQ hσρrel'
  have hk' : ρ ^ k = σ := by
    have h := congrArg Inv.inv hk
    rw [inv_pow, inv_inv, hσinv] at h
    exact h
  by_cases hρ2 : ρ ^ 2 = 1
  · -- ## Case `ρ² = 1`: then `σ = ρ`, `(σt)³ = 1`, and `Q` is abelian
    have hρord : orderOf ρ = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · exact hρ2
      · intro h1
        rw [h1, one_pow] at hk'
        exact hσne hk'.symm
    have hσeq : σ = ρ := by
      have hk2 : ρ ^ (k % 2) = σ := by
        have h1 : ρ ^ k = ρ ^ (k % 2) := pow_eq_pow_mod k hρ2
        rw [← h1]
        exact hk'
      have hlt : k % 2 < 2 := Nat.mod_lt _ (by norm_num)
      interval_cases h : k % 2
      · rw [pow_zero] at hk2
        exact absurd hk2.symm hσne
      · rw [pow_one] at hk2
        exact hk2.symm
    have hrel : t * σ * t = σ * t * σ := by
      have h1 := hσρrel
      rw [← hσeq, htinv, hσinv] at h1
      exact h1
    have hst3 : (σ * t) ^ 3 = 1 := by
      have h3 : (σ * t) ^ 3 = σ * (t * σ * t) * (σ * t) := by
        rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_two]
        group
      rw [h3]
      calc σ * (t * σ * t) * (σ * t) = σ * (σ * t * σ) * (σ * t) := by rw [hrel]
        _ = (σ * σ) * t * (σ * σ) * t := by group
        _ = t * t := by rw [hσ2]; group
        _ = 1 := ht2
    exact hnab (QSZ_abelian_of_order_three hs H Q t h hZ h2 hσQ hσord hst3)
  · -- ## Case `ρ² ≠ 1`: then `σ = ρ²` and `π = σt` has order `5`
    have hρord : orderOf ρ = 4 := by
      have hdvd : orderOf ρ ∣ 4 := orderOf_dvd_iff_pow_eq_one.mpr hρ4
      have hne1 : orderOf ρ ≠ 1 := fun h1 => by
        rw [orderOf_eq_one_iff.mp h1] at hρ2
        exact hρ2 (by simp)
      have hne2 : orderOf ρ ≠ 2 := fun h2' => hρ2 (by rw [← h2']; exact pow_orderOf_eq_one ρ)
      have hdvd' : orderOf ρ ∣ 2 ^ 2 := by simpa using hdvd
      obtain ⟨i, hi, heq⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).mp hdvd'
      have hi2 : i = 2 := by
        interval_cases i
        · rw [pow_zero] at heq; exact absurd heq hne1
        · rw [pow_one] at heq; exact absurd heq hne2
        · rfl
      rw [hi2, pow_two] at heq
      norm_num at heq
      exact heq
    have h6ρ : ρ ^ 6 = ρ ^ 2 := by
      rw [show (6 : ℕ) = 4 + 2 from rfl, pow_add, hρ4, one_mul]
    have hσeq : σ = ρ ^ 2 := by
      have hk4 : ρ ^ (k % 4) = σ := by
        have h1 : ρ ^ k = ρ ^ (k % 4) := pow_eq_pow_mod k hρ4
        rw [← h1]
        exact hk'
      have hlt : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
      interval_cases h : k % 4
      · rw [pow_zero] at hk4
        exact absurd hk4.symm hσne
      · rw [pow_one] at hk4
        exact absurd (by calc ρ ^ 2 = ρ * ρ := pow_two ρ
          _ = σ * σ := by rw [← hk4]
          _ = 1 := hσ2) hρ2
      · rw [pow_two] at hk4
        simpa [pow_two] using hk4.symm
      · have h1 : ρ ^ 3 = σ := hk4
        exact absurd (by calc ρ ^ 2 = ρ ^ 6 := h6ρ.symm
          _ = ρ ^ (3 + 3) := by rw [show (6 : ℕ) = 3 + 3 from rfl]
          _ = ρ ^ 3 * ρ ^ 3 := by rw [pow_add]
          _ = σ * σ := by rw [h1]
          _ = 1 := hσ2) hρ2
    -- relation (A): `(σt)² = ρ(σt)ρ⁻¹`
    have hA : (σ * t) ^ 2 = ρ * (σ * t) * ρ⁻¹ := by
      have h1 : σ * (t * σ * t⁻¹) = σ * (ρ * t * ρ⁻¹) := by rw [hσρrel]
      calc (σ * t) ^ 2 = σ * (t * σ * t⁻¹) := by rw [pow_two, htinv]; group
        _ = σ * (ρ * t * ρ⁻¹) := h1
        _ = ρ * (σ * t) * ρ⁻¹ := by
          rw [show ρ * (σ * t) * ρ⁻¹ = ρ * σ * t * ρ⁻¹ by group, ← hσρcomm]
          group
    -- `π⁻¹ = ρ²πρ²`
    have hπinv : (σ * t)⁻¹ = ρ ^ 2 * (σ * t) * ρ ^ 2 := by
      have h1 : (σ * t)⁻¹ = σ * (σ * t) * σ := by
        calc (σ * t)⁻¹ = t * σ := by rw [mul_inv_rev, htinv, hσinv]
          _ = (σ * σ) * (t * σ) := by rw [hσ2, one_mul]
          _ = σ * (σ * t) * σ := by group
      rw [h1, ← hσeq]
    -- `ρ²πρ² = π⁴`
    have hA2 : ρ ^ 2 * (σ * t) * ρ ^ 2 = (σ * t) ^ 4 := by
      have hsq4 : ρ ^ 2 * ρ ^ 2 = 1 := by rw [← pow_add]; norm_num; exact hρ4
      have hρinv : ρ⁻¹ ^ 2 = ρ ^ 2 := by
        rw [inv_pow]
        exact inv_eq_of_mul_eq_one_right hsq4
      have hB : ρ ^ 2 * (σ * t) * ρ⁻¹ ^ 2 = (σ * t) ^ 4 := by
        calc ρ ^ 2 * (σ * t) * ρ⁻¹ ^ 2
            = (ρ * ρ) * (σ * t) * (ρ⁻¹ * ρ⁻¹) := by rw [pow_two, pow_two]
          _ = ρ * (ρ * (σ * t) * ρ⁻¹) * ρ⁻¹ := by group
          _ = ρ * ((σ * t) ^ 2) * ρ⁻¹ := by rw [hA]
          _ = (ρ * (σ * t) * ρ⁻¹) * (ρ * (σ * t) * ρ⁻¹) := by rw [pow_two]; group
          _ = (σ * t) ^ 2 * (σ * t) ^ 2 := by rw [hA]
          _ = (σ * t) ^ 4 := by rw [← pow_add]
      calc ρ ^ 2 * (σ * t) * ρ ^ 2
          = ρ ^ 2 * (σ * t) * ρ⁻¹ ^ 2 := by rw [hρinv]
        _ = (σ * t) ^ 4 := hB
    have hπ5 : (σ * t) ^ 5 = 1 := by
      have hπ4 : (σ * t)⁻¹ = (σ * t) ^ 4 := by rw [hπinv, hA2]
      calc (σ * t) ^ 5 = (σ * t) * (σ * t) ^ 4 := by
            rw [show (5 : ℕ) = 1 + 4 from rfl, pow_add, pow_one]
        _ = (σ * t) * (σ * t)⁻¹ := by rw [← hπ4]
        _ = 1 := mul_inv_cancel _
    have hπne : σ * t ≠ 1 := by
      intro h1
      have htσ : t = σ := by
        calc t = σ⁻¹ * (σ * t) := by group
          _ = σ⁻¹ * 1 := by rw [h1]
          _ = σ := by rw [mul_one, hσinv]
      exact h.not_mem (by rw [htσ]; exact h.le hσQ)
    have hπord : orderOf (σ * t) = 5 := orderOf_eq_prime hπ5 hπne
    -- `q = |Z(Q)|` and `|G| = q³(q-1)(q³+1)`
    set q : ℕ := Nat.card ↥(Subgroup.center ↥Q) with hq
    have hDcard : Nat.card ↥(twoPoint H t) = q - 1 := by
      have h1 := twoPoint_card_add_one_eq_center_card h hZ h2 hSuz
      rw [← hq] at h1
      omega
    have hGcard : Nat.card G = q ^ 3 * (q - 1) * (q ^ 3 + 1) := by
      have h1 : Nat.card ↥H = Nat.card ↥Q * Nat.card ↥(twoPoint H t) :=
        Work.ThmF.card_H_eq_mul_of_data (Work.ThmF.IsSplitRankOne.toData h)
      have h2' : H.index = Nat.card ↥Q + 1 := Work.ThmG.rankOne_index h
      have h3 : Nat.card ↥H * H.index = Nat.card G := Subgroup.card_mul_index H
      rw [← h3, h1, hDcard, h2', hcu, hq]
    have hfive : 5 ∣ q ^ 3 * (q - 1) * (q ^ 3 + 1) := by
      rw [← hGcard, ← hπord]
      exact orderOf_dvd_natCard _
    -- `q = 2^m` with `m` even, hence `3 ∣ |D|`
    obtain ⟨m, hm⟩ := h2g.exists_card_omega1_eq_two_pow
    have hq2 : q = 2 ^ m := by rw [hq, center_eq_omega1_of_suzuki hSuz]; exact hm
    have hm2 : 2 ∣ m := two_dvd_of_five_dvd q m hq2 hfive
    have h3q : 3 ∣ q - 1 := three_dvd_of_two_dvd q m hq2 hm2
    have h3D : 3 ∣ Nat.card ↥(twoPoint H t) := by rw [hDcard]; exact h3q
    -- an order-`3` element of `D` is strongly real, hence conjugate to `ut`
    obtain ⟨α, hαord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(twoPoint H t)) 3 h3D
    have hα3 : ((α : G)) ^ 3 = 1 := by
      have h1 : orderOf (α : G) = 3 := by
        rw [Subgroup.orderOf_coe]; exact hαord
      rw [← h1]; exact pow_orderOf_eq_one (α : G)
    have hαD : (α : G) ∈ twoPoint H t := α.2
    have htαinv : t * (α : G) * t⁻¹ = (α : G)⁻¹ :=
      twoPoint_inverted h hZ (Work.ZassenhausPSL2.Feit.Q_ne_bot_of_split h) h2 (α : G) hαD
    have htα : t * (α : G) * t = (α : G)⁻¹ := by simpa [htinv] using htαinv
    have hαsr : ∃ a b : G, a * a = 1 ∧ b * b = 1 ∧ a * b = (α : G) := by
      refine ⟨t, t * (α : G), ht2, ?_, by rw [← mul_assoc, ht2, one_mul]⟩
      calc (t * (α : G)) * (t * (α : G)) = (t * (α : G) * t) * (α : G) := by group
        _ = (α : G)⁻¹ * (α : G) := by rw [htα]
        _ = 1 := inv_mul_cancel _
    have hαne : (α : G) * (α : G) ≠ 1 := by
      intro h1
      have h2' : ((α : G)) ^ 2 = 1 := by rw [pow_two]; exact h1
      have hdvd : 3 ∣ 2 := by
        have := orderOf_dvd_iff_pow_eq_one.mpr h2'
        rwa [Subgroup.orderOf_coe (α : ↥(twoPoint H t)), hαord] at this
      omega
    have hcommConj : ∀ g : G, ∀ u ∈ involutions (conj g H : Set G),
        ∀ v ∈ involutions (conj g H : Set G), u * v = v * u :=
      Work.ThmF.ChV12.involution_commute_conj (invH_commute h h2)
    obtain ⟨u, huQ0, hu1, g, hg⟩ := Work.ThmF.ChV12.exists_conj_eq_inv_mul_t
      h.stronglyEmbedded h.twoTransitive h.invol h.not_mem hcommConj hαne hαsr
    -- `(ut)³ = 1`
    have hut3 : (u * t) ^ 3 = 1 := by
      have hconj3 : (g * (α : G) * g⁻¹) ^ 3 = g * ((α : G) ^ 3) * g⁻¹ := by
        have := map_pow (MulAut.conj g).toMonoidHom (α : G) 3
        simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using this.symm
      calc (u * t) ^ 3 = (g * (α : G) * g⁻¹) ^ 3 := by rw [← hg]
        _ = g * ((α : G) ^ 3) * g⁻¹ := hconj3
        _ = 1 := by rw [hα3]; group
    -- `u` is an involution of `Q`
    have huInv : u ∈ involutions (H : Set G) := by
      rw [Work.ThmF.mem_Q0_iff] at huQ0
      rcases huQ0 with hh | hh
      · exact hh
      · exact absurd hh hu1
    have huQ : u ∈ Q := (involutions_H_eq_involutions_Q h h2 ▸ huInv).1
    have huord : orderOf u = 2 := huInv.2
    have hu2 : u * u = 1 := by
      have := pow_orderOf_eq_one u
      rw [huord] at this
      simpa [pow_two] using this
    have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
    -- `(ut)³ = 1` gives `tut = utu`, so `(u,u)` is the structure-identity pair,
    -- whence `σ = u = ρ`, contradicting `σ = ρ² ≠ ρ`
    have hrel : t * u * t = u * t * u := by
      have h2' : u * t * u * t * u * t = 1 := by
        rw [show u * t * u * t * u * t = (u * t) ^ 3 by
          rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_two, pow_one]; group]
        exact hut3
      have h3 : t * u * t * u * t = u := by
        calc t * u * t * u * t = u⁻¹ * (u * t * u * t * u * t) := by group
          _ = u⁻¹ * 1 := by rw [h2']
          _ = u := by rw [huinv, mul_one]
      have h4 : t * u * t * u = u * t := by
        calc t * u * t * u = t * u * t * u * (t * t) := by rw [ht2, mul_one]
          _ = (t * u * t * u * t) * t := by group
          _ = u * t := by rw [h3]
      calc t * u * t = (t * u * t * u) * u := by
            rw [mul_assoc (t * u * t) u u, hu2, mul_one]
        _ = (u * t) * u := by rw [h4]
    have huu : ((u, u) : G × G) = (σ, ρ) :=
      huniq (u, u) ⟨huQ, huord, huQ, by rw [htinv, huinv]; exact hrel⟩
    have hσρeq : σ = ρ := by
      have h1 : u = σ := congrArg Prod.fst huu
      have h2 : u = ρ := congrArg Prod.snd huu
      exact h1.symm.trans h2
    rw [hσeq] at hσρeq
    have hρ1 : ρ = 1 := by
      have := congrArg (fun z => z * ρ⁻¹) hσρeq
      simpa [pow_two, mul_assoc] using this
    exact hρ2 (by rw [hρ1]; simp)

end Work.ZassenhausSuzuki
