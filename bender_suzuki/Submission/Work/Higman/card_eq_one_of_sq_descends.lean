import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman

/-- Auxiliary: from the homomorphism relation `hhom` for the squaring map modulo `D`,
the squaring map descends to a well defined map `G ⧸ Z(G) → Z(G) ⧸ D`, whose kernel is
trivial by `hker`.  Hence `[G : Z(G)] ≤ [Z(G) : D]`; combined with `|G| = |Z(G)|²`
this forces `D = ⊥`. -/
theorem card_eq_one_of_sq_descends {G : Type*} [Group G] [Finite G]
    (D : Subgroup G) (hDZ : D ≤ Subgroup.center G)
    (hb : ∀ x : G, x ^ 2 ∈ Subgroup.center G)
    (hKsq : ∀ z ∈ Subgroup.center G, z ^ 2 ∈ D)
    (hhom : ∀ x y : G, ((x*y)^2)⁻¹ * (x^2 * y^2) ∈ D)
    (hker : ∀ x : G, x ^ 2 ∈ D → x ∈ Subgroup.center G)
    (hcard : Nat.card G = Nat.card ↥(Subgroup.center G) ^ 2) :
    D = ⊥ := by
  let Z : Subgroup G := Subgroup.center G
  let DZ : Subgroup ↥Z := D.subgroupOf Z
  have hb' : ∀ x : G, x ^ 2 ∈ Z := hb
  have hKsq' : ∀ z ∈ Z, z ^ 2 ∈ D := hKsq
  have hker' : ∀ x : G, x ^ 2 ∈ D → x ∈ Z := hker
  -- The squaring map followed by reduction modulo `D`.
  let φ : G → Z ⧸ DZ := fun x => QuotientGroup.mk (⟨x^2, hb' x⟩ : Z)
  -- Its "kernel" is exactly `Z`.
  have key : ∀ a b : G, φ a = φ b ↔ a⁻¹ * b ∈ Z := by
    intro a b
    constructor
    · intro hab
      have hmem : (⟨a^2, hb' a⟩ : Z)⁻¹ * ⟨b^2, hb' b⟩ ∈ DZ := QuotientGroup.eq.mp hab
      have hmem2 : (a^2)⁻¹ * b^2 ∈ D := by
        rw [Subgroup.mem_subgroupOf] at hmem
        simpa using hmem
      have hw : (a⁻¹)^2 * b^2 ∈ D := by simpa [inv_pow] using hmem2
      have h1 := hhom a⁻¹ b
      have hirr : ((a⁻¹ * b)^2)⁻¹ ∈ D := by
        have := D.mul_mem h1 (D.inv_mem hw)
        simpa [mul_assoc] using this
      exact hker' (a⁻¹ * b) (by simpa using D.inv_mem hirr)
    · intro hab
      apply QuotientGroup.eq.mpr
      rw [Subgroup.mem_subgroupOf]
      have h2 : (a⁻¹ * b)^2 ∈ D := hKsq' _ hab
      have h1 := hhom a⁻¹ b
      have h3 : (a⁻¹)^2 * b^2 ∈ D := by
        have := D.mul_mem h2 h1
        simpa [mul_assoc] using this
      simpa [inv_pow] using h3
  have hφw : ∀ a b : G, (QuotientGroup.leftRel Z) a b → φ a = φ b :=
    fun a b hab => (key a b).mpr (QuotientGroup.leftRel_apply.mp hab)
  let f : G ⧸ Z → Z ⧸ DZ := Quotient.lift φ hφw
  have hf_apply : ∀ x : G, f ⟦x⟧ = φ x := fun x => rfl
  have hf_inj : Function.Injective f := by
    intro p q hpq
    obtain ⟨a, ha⟩ := Quotient.exists_rep p
    obtain ⟨b, hbq⟩ := Quotient.exists_rep q
    subst ha
    subst hbq
    rw [Quotient.eq]
    refine QuotientGroup.leftRel_apply.mpr ?_
    apply (key a b).mp
    rw [← hf_apply a, ← hf_apply b]
    exact hpq
  have hIndexLe : Z.index ≤ DZ.index := by
    rw [Subgroup.index_eq_card Z, Subgroup.index_eq_card DZ]
    exact @Nat.card_le_card_of_injective (G ⧸ Z) (Z ⧸ DZ)
      (Quotient.finite (QuotientGroup.leftRel DZ)) f hf_inj
  have hn : 0 < Nat.card ↥Z := Nat.card_pos
  have hZindex : Z.index = Nat.card ↥Z := by
    have h := Subgroup.index_mul_card Z
    have hc : Nat.card G = Nat.card ↥Z ^ 2 := hcard
    rw [hc, pow_two] at h
    exact Nat.mul_right_cancel hn h
  have hDZcard : Nat.card ↥DZ = Nat.card ↥D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDZ).toEquiv
  have hDZidx : DZ.index * Nat.card ↥D = Nat.card ↥Z := by
    rw [← hDZcard]
    exact Subgroup.index_mul_card DZ
  have hstep : Nat.card ↥Z * Nat.card ↥D ≤ Nat.card ↥Z := by
    calc Nat.card ↥Z * Nat.card ↥D
        = Z.index * Nat.card ↥D := by rw [hZindex]
      _ ≤ DZ.index * Nat.card ↥D := Nat.mul_le_mul_right _ hIndexLe
      _ = Nat.card ↥Z := hDZidx
  have hDle : Nat.card ↥D ≤ 1 := by
    have h2 : Nat.card ↥Z * Nat.card ↥D ≤ Nat.card ↥Z * 1 := by simpa using hstep
    exact Nat.le_of_mul_le_mul_left h2 hn
  have hD1 : Nat.card ↥D = 1 := by
    have hpos : 0 < Nat.card ↥D := Nat.card_pos
    omega
  exact Subgroup.card_eq_one.mp hD1

end Work.Higman
