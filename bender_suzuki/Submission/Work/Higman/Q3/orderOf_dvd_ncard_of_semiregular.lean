import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.Q3

/-- **Orbit count for a free permutation.**  If a permutation `α` of a finite type `Y` acts freely
— every power of `α` that fixes a point is the identity — then the order of `α` divides `|Y|`.

Indeed `Y` is the disjoint union of its `<α>`-orbits, and the orbit of any point `y` is in bijection
with `ZMod (period α y)`; freeness forces the period at each point to equal `orderOf α`.  Summing
the (equal) orbit sizes over the orbit quotient gives `|Y| = #orbits * orderOf α`. -/
theorem orderOf_dvd_card_of_free {Y : Type*} [Fintype Y] (α : Equiv.Perm Y)
    (hfree : ∀ k : ℕ, ∀ y : Y, (α ^ k) y = y → α ^ k = 1) :
    orderOf α ∣ Fintype.card Y := by
  classical
  -- The period of `α` at any point equals the order of `α`.
  have hper : ∀ y : Y, MulAction.period α y = orderOf α := by
    intro y
    refine Nat.dvd_antisymm (MulAction.period_dvd_orderOf α y) ?_
    rw [orderOf_dvd_iff_pow_eq_one]
    exact hfree (MulAction.period α y) y (MulAction.pow_period_smul α y)
  let G : Subgroup (Equiv.Perm Y) := Subgroup.zpowers α
  haveI : Fintype (MulAction.orbitRel.Quotient G Y) := Fintype.ofFinite _
  -- `Y` is the disjoint union of its orbits.
  have hcard : Fintype.card Y = ∑ ω : MulAction.orbitRel.Quotient G Y,
      Fintype.card (MulAction.orbit G ω.out) := by
    have e : Y ≃ (Σ ω : MulAction.orbitRel.Quotient G Y, MulAction.orbit G ω.out) :=
      MulAction.selfEquivSigmaOrbits G Y
    rw [Fintype.card_congr e, Fintype.card_sigma]
  -- Every orbit has cardinality `orderOf α`.
  have hterm : ∀ ω : MulAction.orbitRel.Quotient G Y,
      Fintype.card (MulAction.orbit G ω.out) = orderOf α := by
    intro ω
    have h1 := MulAction.minimalPeriod_eq_card (a := α) (b := ω.out)
    rw [← h1, ← MulAction.period_eq_minimalPeriod]
    exact hper ω.out
  rw [hcard, Finset.sum_congr rfl (fun ω _ => hterm ω), Finset.sum_const, Finset.card_univ,
    smul_eq_mul]
  exact dvd_mul_left _ _

/-- If `σ` is a permutation of a finite type `X` which is *semiregular* on a `σ`-invariant
subset `S` (no power of `σ` fixes a point of `S` unless that power is the identity), then the
order of `σ` divides `|S|`: every orbit of `⟨σ⟩` on `S` has size `orderOf σ`, and `S` is a
disjoint union of such orbits. -/
theorem orderOf_dvd_ncard_of_semiregular {X : Type*} [Finite X] (σ : Equiv.Perm X) (S : Set X)
    (hS : ∀ x ∈ S, σ x ∈ S)
    (hfree : ∀ k : ℕ, ∀ x ∈ S, (σ ^ k) x = x → σ ^ k = 1) :
    orderOf σ ∣ S.ncard := by
  classical
  haveI : Fintype X := Fintype.ofFinite X
  by_cases hSe : S.Nonempty
  · haveI : Fintype S := Fintype.ofFinite S
    -- `S` is invariant under `σ` in both directions (finiteness upgrades `σ '' S ⊆ S` to `=`).
    have hmap : σ '' S ⊆ S := by
      rintro _ ⟨y, hy, rfl⟩
      exact hS y hy
    have himg : σ '' S = S :=
      Set.eq_of_subset_of_ncard_le hmap (by rw [Set.ncard_image_of_injective _ σ.injective])
    have hinv : ∀ x : X, σ x ∈ S ↔ x ∈ S := by
      intro x
      refine ⟨fun hx => ?_, fun hx => hS x hx⟩
      have hx' : σ x ∈ σ '' S := himg.symm ▸ hx
      obtain ⟨y, hyS, hyx⟩ := hx'
      exact (σ.injective hyx) ▸ hyS
    -- Restrict `σ` to the invariant set `S`; this is a permutation `τ` of `S`.
    let τ : Equiv.Perm S := σ.subtypePerm hinv
    have htau_val : ∀ k (z : S), ((τ ^ k) z).val = (σ ^ k) z.val := by
      intro k z
      rw [Equiv.Perm.subtypePerm_pow]
      exact congrArg Subtype.val (Equiv.Perm.subtypePerm_apply (σ ^ k) _ z)
    -- `τ` and `σ` have the same order (both divisibilities, the reverse using `S ≠ ∅`).
    have horder : orderOf τ = orderOf σ := by
      refine Nat.dvd_antisymm ?_ ?_
      · rw [orderOf_dvd_iff_pow_eq_one]
        ext z
        rw [htau_val, pow_orderOf_eq_one]
        rfl
      · rw [orderOf_dvd_iff_pow_eq_one]
        obtain ⟨y0, hy0⟩ := hSe
        apply hfree (orderOf τ) y0 hy0
        have hyy : (τ ^ orderOf τ) ⟨y0, hy0⟩ = ⟨y0, hy0⟩ := by
          rw [pow_orderOf_eq_one]; rfl
        have h := htau_val (orderOf τ) ⟨y0, hy0⟩
        rw [hyy] at h
        exact h.symm
    -- `τ` is free, inheriting the semiregularity of `σ` on `S`.
    have hfreq : ∀ k : ℕ, ∀ y : S, (τ ^ k) y = y → τ ^ k = 1 := by
      intro k y hy
      have hy' : (σ ^ k) y.1 = y.1 := by
        have h := htau_val k y
        rw [hy] at h
        exact h.symm
      have h1 := hfree k y.1 y.2 hy'
      ext z
      rw [htau_val, h1]
      rfl
    have hncard : S.ncard = Fintype.card S := by
      rw [← Nat.card_coe_set_eq S, Nat.card_eq_fintype_card]
    have hcore := orderOf_dvd_card_of_free τ hfreq
    rw [← hncard] at hcore
    rwa [horder] at hcore
  · rw [Set.not_nonempty_iff_eq_empty.mp hSe, Set.ncard_empty]
    exact dvd_zero _

end Work.Higman.Q3
