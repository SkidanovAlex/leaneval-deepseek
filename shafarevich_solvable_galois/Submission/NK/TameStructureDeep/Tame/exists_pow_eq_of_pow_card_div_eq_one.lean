import Mathlib.Algebra.Torsor.Defs
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.TameStructureDeep.Tame

/-- In a finite cyclic group `G`, every element `x` killed by the power `card G / ℓ`
is an `ℓ`-th power.  (The `ℓ`-th power map and the `card G / ℓ`-torsion subgroup
both have order `card G / ℓ`, and a cyclic group has a unique subgroup of each
divisor order.) -/
theorem exists_pow_eq_of_pow_card_div_eq_one {G : Type*} [Group G] [Fintype G] [IsCyclic G]
    {ℓ : ℕ} (hℓ : ℓ ∣ Fintype.card G) {x : G} (hx : x ^ (Fintype.card G / ℓ) = 1) :
    ∃ y : G, y ^ ℓ = x := by
  classical
  have hN_pos : 0 < Fintype.card G := Fintype.card_pos
  have hℓ_pos : 0 < ℓ := Nat.pos_of_dvd_of_pos hℓ hN_pos
  have hm_pos : 0 < Fintype.card G / ℓ :=
    Nat.div_pos (Nat.le_of_dvd hN_pos hℓ) hℓ_pos
  have hmul : ℓ * (Fintype.card G / ℓ) = Fintype.card G := Nat.mul_div_cancel' hℓ
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  -- write `x` as an integral power of the generator, reduced to `ZMod (card G)`
  obtain ⟨t, ht, -⟩ := IsCyclic.unique_zpow_zmod hg x
  have hpow : g ^ (t.val * (Fintype.card G / ℓ)) = 1 := by
    rw [ht] at hx
    rw [← pow_mul] at hx
    exact hx
  have hdvd : Fintype.card G ∣ t.val * (Fintype.card G / ℓ) := by
    have h := (orderOf_dvd_iff_pow_eq_one (x := g)).mpr hpow
    rwa [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card] at h
  have hdvd2 : ℓ ∣ t.val := by
    have h : ℓ * (Fintype.card G / ℓ) ∣ t.val * (Fintype.card G / ℓ) := by
      rwa [hmul]
    exact Nat.dvd_of_mul_dvd_mul_right hm_pos h
  obtain ⟨b, hb⟩ := hdvd2
  exact ⟨g ^ b, by rw [ht, hb, ← pow_mul, Nat.mul_comm b ℓ]⟩

end NK.TameStructureDeep.Tame
