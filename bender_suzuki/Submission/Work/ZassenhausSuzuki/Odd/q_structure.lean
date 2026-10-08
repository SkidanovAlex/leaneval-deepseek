import Mathlib
import Submission.Work.ZassenhausSuzuki.Odd.OddDefs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausSuzuki.Odd.q_structure`

The numerical structure of the Suzuki rank-one configuration
(`H = Q ⋊ D`, `D = twoPoint H t`) needed by the "odd order" area: with
`q H = |Q₀sub H| = |Z(Q)|` one has

* `|Q| = q²` (`hord` of the hypothesis bundle, plus `Q₀sub H` computing `Z(Q)`);
* `|D| = q - 1` (`twoPoint_card_add_one_eq_center_card`);
* `q ≥ 4` and `q` is a power of `2` (Higman: `Ω₁(Q) = Z(Q)` is a `2`-group of order `≥ 4`);
* `3 ∤ q - 1` — the *Suzuki/Tits* parity: if `3 ∣ |D|` then an element of order `3` of `D`
  is strongly real, hence (`Work.ThmF.ChV12.exists_conj_eq_inv_mul_t`) conjugate to `u * t`
  with `u ∈ Q` an involution; then `(u * t)³ = 1`, and Suzuki's Theorem 1 in the form
  `Work.ZassenhausSuzuki.QSZ_abelian_of_order_three` forces `Q` abelian, contradicting
  `hnab`.  No hypothesis about `Fix θ` or a Tits endomorphism is needed: the contradiction
  is produced inside the configuration itself;
* `[G : H] = q² + 1` (`Work.ThmG.rankOne_index`).
-/

namespace Work.ZassenhausSuzuki.Odd

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

theorem q_structure (h : Work.ZassenhausSuzuki.Odd.SzOddHyp H Q t) :
    Nat.card ↥Q = Work.ZassenhausSuzuki.Odd.q H ^ 2 ∧
      Nat.card ↥(Submission.Blueprint.twoPoint H t) = Work.ZassenhausSuzuki.Odd.q H - 1 ∧
      4 ≤ Work.ZassenhausSuzuki.Odd.q H ∧
      (∃ l : ℕ, Work.ZassenhausSuzuki.Odd.q H = 2 ^ l) ∧
      ¬ 3 ∣ Work.ZassenhausSuzuki.Odd.q H - 1 ∧ H.index = Work.ZassenhausSuzuki.Odd.q H ^ 2 + 1 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  -- Higman's structure theory of the Suzuki two-group `↥Q`
  obtain ⟨h2g⟩ := (Work.Higman.isSuzukiTwoGroup_iff_nonempty_isSuzuki2Grp (P := ↥Q)).mp h.hSuz
  -- ## `q = |Z(Q)| = |Ω₁(Q)|`
  have hqcenter : q H = Nat.card ↥(Subgroup.center ↥Q) := by
    unfold q
    exact Q0sub_card_eq_center_card h.hsplit h.hzass h.h2 h.hSuz
  have hqomega : q H = Nat.card ↥(Work.Higman.omega1 ↥Q) := by
    rw [hqcenter, center_eq_omega1_of_suzuki h.hSuz]
  -- ## (1) `|Q| = q²`
  have hQcard : Nat.card ↥Q = q H ^ 2 := by
    rw [h.hord, ← hqcenter]
  -- ## (2) `|D| = q - 1`
  have hDcard : Nat.card ↥(Submission.Blueprint.twoPoint H t) = q H - 1 := by
    have h1 := twoPoint_card_add_one_eq_center_card h.hsplit h.hzass h.h2 h.hSuz
    rw [← hqcenter] at h1
    omega
  -- ## (3) `4 ≤ q`
  have hfour : 4 ≤ q H := by
    rw [hqomega]
    exact h2g.omega1_card_ge_four
  -- ## (4) `q` is a power of `2`
  have hpow : ∃ l : ℕ, q H = 2 ^ l := by
    obtain ⟨l, hl⟩ := h2g.exists_card_omega1_eq_two_pow
    exact ⟨l, by rw [hqomega]; exact hl⟩
  -- ## (5) `3 ∤ q - 1`
  have hnot3 : ¬ 3 ∣ q H - 1 := by
    intro h3
    -- an element of order `3` in `D = twoPoint H t`
    have h3D : 3 ∣ Nat.card ↥(Submission.Blueprint.twoPoint H t) := by
      rw [hDcard]; exact h3
    obtain ⟨α, hαord⟩ :=
      exists_prime_orderOf_dvd_card' (G := ↥(Submission.Blueprint.twoPoint H t)) 3 h3D
    -- `t` is an involution
    have ht2 : t * t = 1 := by
      have h1 := pow_orderOf_eq_one t
      rw [h.hsplit.invol] at h1
      simpa [pow_two] using h1
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    have hα3 : ((α : G)) ^ 3 = 1 := by
      have h1 : orderOf (α : G) = 3 := by
        rw [Subgroup.orderOf_coe]; exact hαord
      rw [← h1]; exact pow_orderOf_eq_one (α : G)
    have hαD : (α : G) ∈ Submission.Blueprint.twoPoint H t := α.2
    -- `t` inverts `D`, so `α` is strongly real
    have htαinv : t * (α : G) * t⁻¹ = (α : G)⁻¹ :=
      twoPoint_inverted h.hsplit h.hzass (Work.ZassenhausPSL2.Feit.Q_ne_bot_of_split h.hsplit)
        h.h2 (α : G) hαD
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
        have hh := orderOf_dvd_iff_pow_eq_one.mpr h2'
        rw [Subgroup.orderOf_coe (α : ↥(Submission.Blueprint.twoPoint H t)), hαord] at hh
        exact hh
      omega
    -- involutions in conjugates of `H` commute
    have hcommConj : ∀ g : G,
        ∀ u ∈ Submission.Blueprint.involutions (Submission.Blueprint.conj g H : Set G),
        ∀ v ∈ Submission.Blueprint.involutions (Submission.Blueprint.conj g H : Set G),
          u * v = v * u :=
      Work.ThmF.ChV12.involution_commute_conj (invH_commute h.hsplit h.h2)
    -- `α` is conjugate to `u * t` with `u` a non-identity element of `Q₀ H`
    obtain ⟨u, huQ0, hu1, g, hg⟩ :=
      Work.ThmF.ChV12.exists_conj_eq_inv_mul_t h.hsplit.stronglyEmbedded h.hsplit.twoTransitive
        h.hsplit.invol h.hsplit.not_mem hcommConj hαne hαsr
    -- hence `(u * t)³ = 1`
    have hut3 : (u * t) ^ 3 = 1 := by
      have hconj3 : (g * (α : G) * g⁻¹) ^ 3 = g * ((α : G) ^ 3) * g⁻¹ := by
        have h1 := map_pow (MulAut.conj g).toMonoidHom (α : G) 3
        simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h1.symm
      calc (u * t) ^ 3 = (g * (α : G) * g⁻¹) ^ 3 := by rw [← hg]
        _ = g * ((α : G) ^ 3) * g⁻¹ := hconj3
        _ = 1 := by rw [hα3]; group
    -- `u` is an involution of `Q`
    have huInv : u ∈ Submission.Blueprint.involutions (H : Set G) := by
      rw [Work.ThmF.mem_Q0_iff] at huQ0
      rcases huQ0 with hh | hh
      · exact hh
      · exact absurd hh hu1
    have huQ : u ∈ Q := (involutions_H_eq_involutions_Q h.hsplit h.h2 ▸ huInv).1
    have huord : orderOf u = 2 := huInv.2
    -- Suzuki's Theorem 1: `Q` would be abelian
    exact h.hnab (QSZ_abelian_of_order_three h.hG H Q t h.hsplit h.hzass h.h2 huQ huord hut3)
  -- ## (6) `[G : H] = q² + 1`
  have hindex : H.index = q H ^ 2 + 1 := by
    have h1 : H.index = Nat.card ↥Q + 1 := Work.ThmG.rankOne_index h.hsplit
    rw [h1, hQcard]
  exact ⟨hQcard, hDcard, hfour, hpow, hnot3, hindex⟩

end Work.ZassenhausSuzuki.Odd
