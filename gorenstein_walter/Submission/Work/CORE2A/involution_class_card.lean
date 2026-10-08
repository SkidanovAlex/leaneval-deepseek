import Mathlib

set_option linter.style.haveILetI false

namespace Work.CORE2A

/-- **Orbit–stabilizer count of a full conjugacy class of involutions.**

Let `K ≤ G` be a finite subgroup and `t ∈ K` an involution.  If all the involutions of `K`
are conjugate inside `K` (hypothesis `hclass`), then the number of involutions of `K` equals
the index in `K` of the centralizer of `t`,

`|{x ∈ K : x² = 1, x ≠ 1}| = [K : C_K(t)]`.

Indeed, conjugation by `K` makes the set of involutions of `K` a single orbit with stabilizer
`C_K(t)`, and the orbit–stabilizer theorem identifies the orbit size with the index of the
stabilizer. -/
theorem involution_class_card {G : Type} [Group G] [Finite G] (K : Subgroup G) (t : G)
    (htK : t ∈ K) (ht2 : orderOf t = 2)
    (hclass : ∀ x y : G, x ∈ K → y ∈ K → orderOf x = 2 → orderOf y = 2 →
      ∃ g ∈ K, g * x * g⁻¹ = y) :
    (Set.ncard {x : G | x ∈ K ∧ orderOf x = 2}) =
      (Subgroup.centralizer ({t} : Set G)).relIndex K := by
  classical
  -- Conjugation action of `K` on the ambient group `G`.
  let act : MulAction K G :=
    { smul := fun k x => k.1 * x * k.1⁻¹
      one_smul := by intro x; show (1 : K).1 * x * (1 : K).1⁻¹ = x; simp
      mul_smul := by
        intro a b x
        show (a * b).1 * x * (a * b).1⁻¹ = a.1 * (b.1 * x * b.1⁻¹) * a.1⁻¹
        simp [mul_assoc] }
  letI := act
  -- The `K`-orbit of `t` is exactly the set of involutions of `K`.
  have horb : MulAction.orbit K t = {x : G | x ∈ K ∧ orderOf x = 2} := by
    ext x
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨k, hk⟩
      subst hk
      refine ⟨?_, ?_⟩
      · change k.1 * t * k.1⁻¹ ∈ K
        exact K.mul_mem (K.mul_mem k.2 htK) (K.inv_mem k.2)
      · change orderOf (k.1 * t * k.1⁻¹) = 2
        have h : orderOf (k.1 * t * k.1⁻¹) = orderOf t := by
          rw [← MulAut.conj_apply k.1 t]
          exact MulEquiv.orderOf_eq (MulAut.conj k.1) t
        rw [h, ht2]
    · rintro ⟨hxK, hx2⟩
      obtain ⟨g, hgK, hg⟩ := hclass t x htK hxK ht2 hx2
      exact ⟨⟨g, hgK⟩, hg⟩
  -- The stabilizer of `t` is the centralizer of `t` intersected with `K`.
  have hstab : MulAction.stabilizer K t = (Subgroup.centralizer ({t} : Set G)).subgroupOf K := by
    ext k
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      change k.1 * t * k.1⁻¹ = t at h
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      have h1 := congrArg (· * k.1) h
      simp only [mul_assoc, inv_mul_cancel, mul_one] at h1
      exact h1.symm
    · intro h
      change k.1 * t * k.1⁻¹ = t
      have h' : t * k.1 = k.1 * t := h t (Set.mem_singleton t)
      rw [← h', mul_assoc, mul_inv_cancel, mul_one]
  -- Orbit–stabilizer: the orbit size is the index of the stabilizer.
  have hcard : Nat.card (MulAction.orbit K t) = (MulAction.stabilizer K t).index := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr (MulAction.orbitEquivQuotientStabilizer K t)
  calc Set.ncard {x : G | x ∈ K ∧ orderOf x = 2}
      = Nat.card {x : G | x ∈ K ∧ orderOf x = 2} := (Nat.card_coe_set_eq _).symm
    _ = Nat.card (MulAction.orbit K t) := Nat.card_congr (Set.equivOfEq horb.symm)
    _ = (MulAction.stabilizer K t).index := hcard
    _ = ((Subgroup.centralizer ({t} : Set G)).subgroupOf K).index := by rw [hstab]
    _ = (Subgroup.centralizer ({t} : Set G)).relIndex K := rfl

end Work.CORE2A
