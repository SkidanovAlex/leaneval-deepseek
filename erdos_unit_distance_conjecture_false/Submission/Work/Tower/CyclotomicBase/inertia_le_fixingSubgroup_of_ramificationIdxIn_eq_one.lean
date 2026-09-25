import Mathlib

open NumberField

namespace Work.Tower.CyclotomicBase

/-! ## Auxiliary coercion lemmas

We need to compare the action of `Gal(K/ℚ)` on `𝓞 K` with the action of `Gal(↥E/ℚ)` on `𝓞 ↥E`
through the canonical ring homomorphism `𝓞 ↥E → 𝓞 K`. -/

private lemma coe_algebraMap_coe {K : Type} [Field K] [NumberField K]
    (E : IntermediateField ℚ K) (y : 𝓞 ↥E) :
    algebraMap (𝓞 K) K (algebraMap (𝓞 ↥E) (𝓞 K) y) = algebraMap ↥E K (y : ↥E) := by
  rw [← IsScalarTower.algebraMap_apply (𝓞 ↥E) (𝓞 K) K,
    IsScalarTower.algebraMap_apply (𝓞 ↥E) (↥E) K]

private lemma algebraMap_smul_K {K : Type} [Field K] [NumberField K]
    (σ : Gal(K/ℚ)) (y : 𝓞 K) :
    algebraMap (𝓞 K) K (σ • y) = σ (algebraMap (𝓞 K) K y) := by
  rw [algebraMap.smul']; rfl

private lemma algebraMap_smul_E {K : Type} [Field K] [NumberField K]
    (E : IntermediateField ℚ K) (τ : Gal(↥E/ℚ)) (x : 𝓞 ↥E) :
    algebraMap (𝓞 ↥E) (↥E) (τ • x) = τ (algebraMap (𝓞 ↥E) (↥E) x) := by
  rw [algebraMap.smul']; rfl

private lemma restrictNormalHom_algebraMap {K : Type} [Field K] [NumberField K]
    (E : IntermediateField ℚ K) [Normal ℚ ↥E] (σ : Gal(K/ℚ)) (z : ↥E) :
    algebraMap ↥E K ((AlgEquiv.restrictNormalHom ↥E σ) z) = σ (algebraMap ↥E K z) := by
  change (↑(((AlgEquiv.restrictNormalHom ↥E) σ) z) : K) = σ ↑z
  rw [AlgEquiv.restrictNormalHom_apply]

/-- The canonical map `𝓞 ↥E → 𝓞 K` is equivariant for the action of `Gal(K/ℚ)` on `𝓞 K`
and the action of `Gal(↥E/ℚ)` on `𝓞 ↥E` via restriction of automorphisms. -/
private lemma map_smul_ringOfIntegers {K : Type} [Field K] [NumberField K]
    (E : IntermediateField ℚ K) [Normal ℚ ↥E] (σ : Gal(K/ℚ)) (x : 𝓞 ↥E) :
    algebraMap (𝓞 ↥E) (𝓞 K) ((AlgEquiv.restrictNormalHom ↥E σ) • x)
      = σ • algebraMap (𝓞 ↥E) (𝓞 K) x := by
  apply NumberField.RingOfIntegers.coe_injective
  simp only [coe_algebraMap_coe, algebraMap_smul_K, restrictNormalHom_algebraMap]

theorem inertia_le_fixingSubgroup_of_ramificationIdxIn_eq_one {K : Type} [Field K] [NumberField K]
    [IsGalois ℚ K] (E : IntermediateField ℚ K) [IsGalois ℚ ↥E] (q : ℕ) [Fact (Nat.Prime q)]
    (P : Ideal (NumberField.RingOfIntegers K)) [P.IsPrime]
    (Q : Ideal (NumberField.RingOfIntegers ↥E)) [Q.IsPrime]
    [Q.LiesOver (Ideal.span {(q : ℤ)})] [P.LiesOver Q]
    (h : (Ideal.span {(q : ℤ)}).ramificationIdxIn (NumberField.RingOfIntegers ↥E) = 1) :
    Ideal.inertia Gal(K/ℚ) P ≤ E.fixingSubgroup := by
  -- The inertia subgroup of `Q` in `Gal(↥E/ℚ)` is trivial, since its cardinality equals the
  -- ramification index `e(Q / q) = 1`.
  have hbot : Ideal.inertia Gal(↥E/ℚ) Q = ⊥ := by
    rw [← Subgroup.card_eq_one,
      Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(↥E/ℚ)) (Ideal.span {(q : ℤ)}) Q, h]
  intro σ hσ
  rw [Ideal.mem_inertia] at hσ
  rw [IntermediateField.mem_fixingSubgroup_iff]
  -- The restriction of an inertia element to `E` again lies in an inertia subgroup.
  have hmem : AlgEquiv.restrictNormalHom ↥E σ ∈ Ideal.inertia Gal(↥E/ℚ) Q := by
    rw [Ideal.mem_inertia]
    intro y
    rw [Ideal.over_def P Q, Ideal.mem_under, map_sub, map_smul_ringOfIntegers]
    exact hσ (algebraMap (𝓞 ↥E) (𝓞 K) y)
  have hτ : AlgEquiv.restrictNormalHom ↥E σ = 1 := by
    have hmem' := hmem
    rw [hbot] at hmem'
    simpa using hmem'
  intro x hx
  have h2 := AlgEquiv.restrictNormalHom_apply E σ (⟨x, hx⟩ : ↥E)
  rw [hτ] at h2
  exact h2.symm

end Work.Tower.CyclotomicBase
