import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.HallHigman.GLCore

/-- **Orbit transversal and count.** Let `t` be a permutation of a finite type `Q` with
`t ^ p = 1` for a prime `p`, whose unique fixed point is `z`. Then there is a set `R` of orbit
representatives (every element of `Q` is a `t`-iterate of some element of `R`) and
`p * #R = #Q + p - 1`. -/
lemma orbit_transversal_card {Q : Type*} [Fintype Q] (t : Equiv.Perm Q) {p : ℕ} (hp : p.Prime)
    (ht : t ^ p = 1) {z : Q} (hz : ∀ q, t q = q ↔ q = z) :
    ∃ R : Finset Q, (∀ q, ∃ k : ℕ, (t ^ k) q ∈ R) ∧ p * R.card = Fintype.card Q + p - 1 := by
  classical
  by_cases ht1 : t = 1
  · -- The degenerate case `t = 1`: every point is fixed, hence `Q = {z}`.
    refine ⟨{z}, ?_, ?_⟩
    · intro q
      refine ⟨0, ?_⟩
      rw [pow_zero]
      simp only [Finset.mem_singleton]
      exact (hz q).mp (by rw [ht1]; rfl)
    · rw [Finset.card_singleton]
      have hcard : Fintype.card Q = 1 :=
        Fintype.card_eq_one_iff.mpr ⟨z, fun y => (hz y).mp (by rw [ht1]; rfl)⟩
      rw [hcard]
      have hp1 : 1 ≤ p := hp.one_lt.le
      omega
  · -- The nontrivial case: `⟨t⟩` is a cyclic group of order `p` and acts on `Q`;
    -- Burnside's lemma computes the number of orbits.
    have hord_dvd : orderOf t ∣ p := orderOf_dvd_iff_pow_eq_one.mpr ht
    have hord : orderOf t = p := by
      rcases hp.eq_one_or_self_of_dvd (orderOf t) hord_dvd with h | h
      · exact absurd h (by intro hh; exact ht1 (orderOf_eq_one_iff.mp hh))
      · exact h
    have hcardH : Fintype.card (Subgroup.zpowers t) = p := by
      rw [Fintype.card_zpowers, hord]
    -- Every nonidentity element of `⟨t⟩` is a generator, so it has `z` as its only fixed point.
    have hfix : ∀ g : Subgroup.zpowers t, g ≠ 1 → MulAction.fixedBy Q g = {z} := by
      intro g hg
      have hzu : (g : Equiv.Perm Q) ∈ MulAction.stabilizer (Equiv.Perm Q) z := by
        rw [MulAction.mem_stabilizer_iff]
        have htmem0 : t ∈ MulAction.stabilizer (Equiv.Perm Q) z := by
          rw [MulAction.mem_stabilizer_iff]
          exact (hz z).mpr rfl
        exact (Subgroup.zpowers_le.mpr htmem0) g.2
      ext x
      rw [Set.mem_singleton_iff]
      constructor
      · intro hx
        rw [MulAction.mem_fixedBy] at hx
        have h1 : (g : Equiv.Perm Q) ∈ MulAction.stabilizer (Equiv.Perm Q) x := by
          rw [MulAction.mem_stabilizer_iff]
          rwa [Subgroup.smul_def] at hx
        have h2 : Subgroup.zpowers (g : Equiv.Perm Q) ≤ MulAction.stabilizer (Equiv.Perm Q) x :=
          Subgroup.zpowers_le.mpr h1
        have hgne1 : orderOf (g : Equiv.Perm Q) ≠ 1 := by
          rw [Subgroup.orderOf_coe]
          intro h; exact hg (orderOf_eq_one_iff.mp h)
        have hdvd : Fintype.card (Subgroup.zpowers (g : Equiv.Perm Q)) = p := by
          rw [Fintype.card_zpowers]
          have hd : orderOf (g : Equiv.Perm Q) ∣ p := by
            rw [Subgroup.orderOf_coe]
            have hsub := Subgroup.card_subgroup_dvd_card (Subgroup.zpowers g)
            rw [Nat.card_zpowers] at hsub
            rw [Nat.card_eq_fintype_card, hcardH] at hsub
            exact hsub
          rcases hp.eq_one_or_self_of_dvd _ hd with h' | h'
          · exact absurd h' hgne1
          · exact h'
        have hEq : Subgroup.zpowers (g : Equiv.Perm Q) = Subgroup.zpowers t := by
          refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr g.2) ?_
          rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hcardH, hdvd]
        have htmem : t ∈ Subgroup.zpowers (g : Equiv.Perm Q) := by
          rw [hEq]; exact Subgroup.mem_zpowers t
        have htx : t • x = x := MulAction.mem_stabilizer_iff.mp (h2 htmem)
        exact (hz x).mp htx
      · intro hx
        rw [hx, MulAction.mem_fixedBy, Subgroup.smul_def]
        exact hzu
    -- Burnside's lemma: sum of fixed-point counts `= #orbits * p`.
    have hf1 : Fintype.card ↥(MulAction.fixedBy Q (1 : Subgroup.zpowers t)) = Fintype.card Q := by
      simp
    have hsum : ∑ g : Subgroup.zpowers t, Fintype.card ↥(MulAction.fixedBy Q g)
        = Fintype.card Q + (p - 1) := by
      rw [← Finset.sum_erase_add (Finset.univ : Finset (Subgroup.zpowers t))
            (fun g => Fintype.card ↥(MulAction.fixedBy Q g))
            (Finset.mem_univ (1 : Subgroup.zpowers t)), hf1]
      have hconst : ∀ x ∈ (Finset.univ.erase (1 : Subgroup.zpowers t)),
          Fintype.card ↥(MulAction.fixedBy Q x) = 1 := by
        intro x hx
        simp [hfix x (Finset.mem_erase.mp hx).1]
      have herase :
          ∑ x ∈ (Finset.univ.erase (1 : Subgroup.zpowers t)),
              Fintype.card ↥(MulAction.fixedBy Q x) = p - 1 := by
        rw [Finset.sum_const_nat hconst, Finset.card_erase_of_mem (Finset.mem_univ _),
          Finset.card_univ, hcardH, Nat.mul_one]
      rw [herase, Nat.add_comm]
    have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
      (Subgroup.zpowers t) Q
    rw [hsum, hcardH] at hburn
    -- A transversal: one representative (`Quotient.out`) for each orbit.
    refine ⟨(Finset.univ : Finset
        (Quotient (MulAction.orbitRel (Subgroup.zpowers t) Q))).image Quotient.out, ?_, ?_⟩
    · intro q
      have hmem : Quotient.out (⟦q⟧ : Quotient
            (MulAction.orbitRel (Subgroup.zpowers t) Q)) ∈
          (Finset.univ : Finset
            (Quotient (MulAction.orbitRel (Subgroup.zpowers t) Q))).image Quotient.out :=
        Finset.mem_image.mpr ⟨⟦q⟧, Finset.mem_univ _, rfl⟩
      obtain ⟨g, hg⟩ : ∃ g : Subgroup.zpowers t,
          g • q = Quotient.out (⟦q⟧ : Quotient
            (MulAction.orbitRel (Subgroup.zpowers t) Q)) := by
        have he : (MulAction.orbitRel (Subgroup.zpowers t) Q)
            (Quotient.out (⟦q⟧ : Quotient
              (MulAction.orbitRel (Subgroup.zpowers t) Q))) q :=
          Quotient.exact (Quotient.out_eq (⟦q⟧ : Quotient
            (MulAction.orbitRel (Subgroup.zpowers t) Q)))
        exact MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp he)
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.2
      have hgq : (t ^ m) q = Quotient.out (⟦q⟧ : Quotient
          (MulAction.orbitRel (Subgroup.zpowers t) Q)) := by
        rw [hm]
        rw [Subgroup.smul_def] at hg
        simpa using hg
      have hpz : (t : Equiv.Perm Q) ^ (p : ℤ) = 1 := by rw [zpow_natCast, ht]
      obtain ⟨k, hk⟩ : ∃ k : ℕ, (t : Equiv.Perm Q) ^ m = t ^ k := by
        refine ⟨(m % (p : ℤ)).toNat, ?_⟩
        rw [zpow_eq_zpow_emod m hpz, ← zpow_natCast,
          Int.toNat_of_nonneg (Int.emod_nonneg m (by exact_mod_cast hp.ne_zero))]
      refine ⟨k, ?_⟩
      rw [← hk, hgq]
      exact hmem
    · have hRcard : ((Finset.univ : Finset
            (Quotient (MulAction.orbitRel (Subgroup.zpowers t) Q))).image Quotient.out).card
          = Fintype.card (Quotient (MulAction.orbitRel (Subgroup.zpowers t) Q)) := by
        rw [Finset.card_image_of_injective _ Quotient.out_injective, Finset.card_univ]
      rw [hRcard, mul_comm p]
      rw [← hburn]
      have hp1 : 1 ≤ p := hp.one_lt.le
      omega

end Work.HallHigman.GLCore
