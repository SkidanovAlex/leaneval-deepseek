import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GroupTheory

/-- A nontrivial minimal normal subgroup of a finite solvable group is elementary abelian: it is
abelian and its exponent is a prime `p`. -/
theorem isElementaryAbelian_of_minimal_normal (G : Type*) [Group G] [Finite G] [Group.IsSolvable G]
    (A : Subgroup G) [A.Normal] (hA : A ≠ ⊥)
    (hmin : ∀ B : Subgroup G, B.Normal → B ≤ A → B ≠ ⊥ → B = A) :
    ∃ p : ℕ, Nat.Prime p ∧ IsMulCommutative A ∧ ∀ x : A, x ^ p = 1 := by
  -- Step 1: `A` is abelian.  `⁅A, A⁆` is normal in `G`, so by minimality it is `⊥` or `A`;
  -- the latter is impossible because `G` is solvable, so `⁅A, A⁆ < A`.
  have hcomm : ⁅A, A⁆ = ⊥ := by
    by_contra hne
    have hlt : ⁅A, A⁆ < A := Group.IsSolvable.commutator_lt_of_ne_bot hA
    have hle : ⁅A, A⁆ ≤ A := Subgroup.commutator_le_left A A
    have hN : (⁅A, A⁆ : Subgroup G).Normal := inferInstance
    have heq : ⁅A, A⁆ = A := hmin ⁅A, A⁆ hN hle hne
    rw [heq] at hlt
    exact absurd hlt (lt_irrefl A)
  have hAabel : IsMulCommutative A := Subgroup.commutator_self_eq_bot_iff.mp hcomm
  -- Step 2: pick a prime `p` dividing the order of `A`; by Cauchy's theorem `A` has an element of
  -- order `p`.  The subgroup `A[p]` of `p`-torsion elements is characteristic in `A`, hence normal
  -- in `G`, hence equal to `A` by minimality, which forces the exponent of `A` to be `p`.
  have hnt : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr hA
  obtain ⟨p, hpp, hpdvd⟩ : ∃ p : ℕ, Nat.Prime p ∧ p ∣ Nat.card A := by
    have h2 := Finite.one_lt_card (α := A)
    exact Nat.exists_prime_and_dvd (by omega)
  haveI : Fact p.Prime := ⟨hpp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := A) p hpdvd
  refine ⟨p, hpp, hAabel, ?_⟩
  -- `Ap = A[p]` is the subgroup of `p`-torsion elements of the abelian group `A`.
  let Ap : Subgroup A :=
    { carrier := {a | a ^ p = 1}
      mul_mem' := by
        intro a b ha hb
        change (a * b) ^ p = 1
        rw [Commute.mul_pow (show Commute a b from (isMulCommutative_iff.mp hAabel a b)), ha, hb,
          mul_one]
      one_mem' := by
        change (1 : A) ^ p = 1
        simp
      inv_mem' := by
        intro a ha
        change a⁻¹ ^ p = 1
        rw [inv_pow, ha, inv_one] }
  -- `Ap` is characteristic in `A`: automorphisms commute with the `p`-th power map.
  have hApchar : Ap.Characteristic := by
    rw [Subgroup.characteristic_iff_map_eq]
    intro φ
    ext a
    constructor
    · intro ha
      rw [Subgroup.mem_map] at ha
      obtain ⟨b, hb, rfl⟩ := ha
      change (φ b) ^ p = 1
      rw [← map_pow, hb, map_one]
    · intro ha
      rw [Subgroup.mem_map]
      exact ⟨φ.symm a, by change (φ.symm a) ^ p = 1; rw [← map_pow, ha, map_one],
        φ.apply_symm_apply a⟩
  haveI : Ap.Characteristic := hApchar
  -- `Ap`, viewed inside `G`, is normal in `G`.
  let B : Subgroup G := Ap.map A.subtype
  have hBnorm : B.Normal := inferInstance
  have hBA : B ≤ A := Subgroup.map_subtype_le Ap
  have hxp : x ^ p = 1 := by rw [← orderOf_dvd_iff_pow_eq_one, hx]
  have hxAp : x ∈ Ap := hxp
  have hxB : (x : G) ∈ B := by
    change (x : G) ∈ Ap.map A.subtype
    rw [Subgroup.mem_map]
    exact ⟨x, hxAp, rfl⟩
  have hxne : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    exact hpp.ne_one hx.symm
  have hBne : B ≠ ⊥ := by
    intro hbot
    have h1 : (x : G) ∈ (⊥ : Subgroup G) := hbot ▸ hxB
    rw [Subgroup.mem_bot] at h1
    exact hxne (Subtype.ext (by simpa using h1))
  have hBeq : B = A := hmin B hBnorm hBA hBne
  -- Every element of `A` lies in `Ap`, hence has `p`-th power `1`.
  intro y
  have hyB : (y : G) ∈ B := hBeq.ge y.2
  change (y : G) ∈ Ap.map A.subtype at hyB
  exact (Subgroup.mem_map_iff_mem (Subgroup.subtype_injective A)).mp hyB

end Work.GroupTheory
