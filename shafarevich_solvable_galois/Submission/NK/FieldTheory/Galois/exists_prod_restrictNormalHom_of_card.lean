import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.FieldTheory.Galois.Basic
import Submission.NK.Mine.galoisGroup_sup_prod
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace NK.FieldTheory.Galois

variable {F F' : Type*} [Field F] [Field F'] [Algebra F F']
    (A B : IntermediateField F F')

/-- Two `F`-algebra automorphisms of the compositum `A ⊔ B` which agree on `A` and on `B`
agree everywhere: `A ⊔ B` is generated, over `F`, by `A ∪ B`. -/
private lemma eq_of_eqOn_sup_of_sup {σ τ : ↥(A ⊔ B) ≃ₐ[F] ↥(A ⊔ B)}
    (hA : ∀ x : ↥A, σ ⟨x.1, (le_sup_left : A ≤ A ⊔ B) x.2⟩ = τ ⟨x.1, (le_sup_left : A ≤ A ⊔ B) x.2⟩)
    (hB : ∀ y : ↥B, σ ⟨y.1, (le_sup_right : B ≤ A ⊔ B) y.2⟩ = τ ⟨y.1, (le_sup_right : B ≤ A ⊔ B) y.2⟩) :
    σ = τ := by
  have hρ : σ⁻¹ * τ = 1 := by
    -- it suffices that `σ⁻¹ * τ` fixes `A` and `B` pointwise
    have key : ∀ ρ : ↥(A ⊔ B) ≃ₐ[F] ↥(A ⊔ B),
        (∀ x : ↥A, ρ ⟨x.1, (le_sup_left : A ≤ A ⊔ B) x.2⟩ = ⟨x.1, (le_sup_left : A ≤ A ⊔ B) x.2⟩) →
        (∀ y : ↥B, ρ ⟨y.1, (le_sup_right : B ≤ A ⊔ B) y.2⟩ = ⟨y.1, (le_sup_right : B ≤ A ⊔ B) y.2⟩) →
        ρ = 1 := by
      intro ρ h₁ h₂
      -- `A` and `B`, viewed inside the compositum `A ⊔ B`
      let A' : IntermediateField F ↥(A ⊔ B) :=
        IntermediateField.comap (IntermediateField.val (A ⊔ B)) A
      let B' : IntermediateField F ↥(A ⊔ B) :=
        IntermediateField.comap (IntermediateField.val (A ⊔ B)) B
      have hmemA' : ∀ x : ↥(A ⊔ B), x ∈ A' ↔ (x : F') ∈ A := fun x =>
        Subalgebra.mem_comap A.toSubalgebra (IntermediateField.val (A ⊔ B)) x
      have hmemB' : ∀ x : ↥(A ⊔ B), x ∈ B' ↔ (x : F') ∈ B := fun x =>
        Subalgebra.mem_comap B.toSubalgebra (IntermediateField.val (A ⊔ B)) x
      -- the images of `A'` and `B'` in `F'` are `A` and `B`
      have hmapA : IntermediateField.map (IntermediateField.val (A ⊔ B)) A' = A := by
        apply le_antisymm
        · intro y hy
          rw [IntermediateField.mem_map] at hy
          obtain ⟨x, hx, rfl⟩ := hy
          exact (hmemA' x).mp hx
        · intro y hy
          rw [IntermediateField.mem_map]
          exact ⟨⟨y, (le_sup_left : A ≤ A ⊔ B) hy⟩, (hmemA' _).mpr hy, rfl⟩
      have hmapB : IntermediateField.map (IntermediateField.val (A ⊔ B)) B' = B := by
        apply le_antisymm
        · intro y hy
          rw [IntermediateField.mem_map] at hy
          obtain ⟨x, hx, rfl⟩ := hy
          exact (hmemB' x).mp hx
        · intro y hy
          rw [IntermediateField.mem_map]
          exact ⟨⟨y, (le_sup_right : B ≤ A ⊔ B) hy⟩, (hmemB' _).mpr hy, rfl⟩
      have hmapTop : IntermediateField.map (IntermediateField.val (A ⊔ B))
          (⊤ : IntermediateField F ↥(A ⊔ B)) = A ⊔ B := by
        apply le_antisymm
        · intro y hy
          rw [IntermediateField.mem_map] at hy
          obtain ⟨x, -, rfl⟩ := hy
          exact x.2
        · intro y hy
          rw [IntermediateField.mem_map]
          exact ⟨⟨y, hy⟩, trivial, rfl⟩
      -- hence `A' ⊔ B' = ⊤`, since `A ⊔ B` is the whole of the ambient field
      have hsup : A' ⊔ B' = ⊤ := by
        apply IntermediateField.map_injective (IntermediateField.val (A ⊔ B))
        rw [IntermediateField.map_sup, hmapA, hmapB, hmapTop]
      have hmemA : ρ ∈ A'.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro x hx
        have hxA : (x : F') ∈ A := (hmemA' x).mp hx
        rw [show x = (⟨x.1, (le_sup_left : A ≤ A ⊔ B) hxA⟩ : ↥(A ⊔ B)) from Subtype.ext rfl]
        exact h₁ ⟨x.1, hxA⟩
      have hmemB : ρ ∈ B'.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro x hx
        have hxB : (x : F') ∈ B := (hmemB' x).mp hx
        rw [show x = (⟨x.1, (le_sup_right : B ≤ A ⊔ B) hxB⟩ : ↥(A ⊔ B)) from Subtype.ext rfl]
        exact h₂ ⟨x.1, hxB⟩
      have h1 : ρ ∈ (A' ⊔ B').fixingSubgroup := by
        rw [IntermediateField.fixingSubgroup_sup]
        exact ⟨hmemA, hmemB⟩
      rw [hsup, IntermediateField.fixingSubgroup_top] at h1
      simpa using h1
    exact key _ (fun x => by
      calc (σ⁻¹ * τ) ⟨x.1, (le_sup_left : A ≤ A ⊔ B) x.2⟩
          = σ⁻¹ (τ ⟨x.1, (le_sup_left : A ≤ A ⊔ B) x.2⟩) := by simp
        _ = σ⁻¹ (σ ⟨x.1, (le_sup_left : A ≤ A ⊔ B) x.2⟩) := by rw [hA x]
        _ = ⟨x.1, (le_sup_left : A ≤ A ⊔ B) x.2⟩ := by simp) (fun y => by
      calc (σ⁻¹ * τ) ⟨y.1, (le_sup_right : B ≤ A ⊔ B) y.2⟩
          = σ⁻¹ (τ ⟨y.1, (le_sup_right : B ≤ A ⊔ B) y.2⟩) := by simp
        _ = σ⁻¹ (σ ⟨y.1, (le_sup_right : B ≤ A ⊔ B) y.2⟩) := by rw [hB y]
        _ = ⟨y.1, (le_sup_right : B ≤ A ⊔ B) y.2⟩ := by simp)
  exact inv_mul_eq_one.mp hρ

/-- **Compositum of two Galois extensions with independent Galois groups.**

If `A` and `B` are finite normal extensions of `F` inside `F'`, and the order of the Galois group
of the compositum `A ⊔ B` is the product of the orders of the Galois groups of `A` and `B`, then
restriction of automorphisms induces an isomorphism
`Gal(A ⊔ B/F) ≃* Gal(A/F) × Gal(B/F)`.

Indeed the restriction map is always injective (`A ⊔ B` is generated by `A` and `B`), and the
hypothesis on the cardinalities forces it to be surjective.  The two compatibility conditions
express that the components of the isomorphism are the actual restrictions. -/
theorem exists_prod_restrictNormalHom_of_card {F F' : Type*} [Field F] [Field F'] [Algebra F F']
    (A B : IntermediateField F F') [FiniteDimensional F ↥A] [Normal F ↥A]
    [FiniteDimensional F ↥B] [Normal F ↥B]
    [FiniteDimensional F ↥(A ⊔ B)] [Normal F ↥(A ⊔ B)]
    (hcard : Nat.card (↥(A ⊔ B) ≃ₐ[F] ↥(A ⊔ B)) =
        Nat.card ((↥A ≃ₐ[F] ↥A) × (↥B ≃ₐ[F] ↥B))) :
    ∃ φ : (↥(A ⊔ B) ≃ₐ[F] ↥(A ⊔ B)) ≃* ((↥A ≃ₐ[F] ↥A) × (↥B ≃ₐ[F] ↥B)),
      (∀ (σ : ↥(A ⊔ B) ≃ₐ[F] ↥(A ⊔ B)) (x : ↥A),
        (((φ σ).1 x : ↥A) : F') = ((σ ⟨x.1, (le_sup_left : A ≤ A ⊔ B) x.2⟩ : ↥(A ⊔ B)) : F')) ∧
      (∀ (σ : ↥(A ⊔ B) ≃ₐ[F] ↥(A ⊔ B)) (y : ↥B),
        (((φ σ).2 y : ↥B) : F') = ((σ ⟨y.1, (le_sup_right : B ≤ A ⊔ B) y.2⟩ : ↥(A ⊔ B)) : F')) := by
  -- view `A` and `B` as `F`-subalgebras of the compositum, so that `restrictNormalHom` applies
  letI : Algebra ↥A ↥(A ⊔ B) := (IntermediateField.inclusion le_sup_left).toRingHom.toAlgebra
  haveI : IsScalarTower F ↥A ↥(A ⊔ B) := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra ↥B ↥(A ⊔ B) := (IntermediateField.inclusion le_sup_right).toRingHom.toAlgebra
  haveI : IsScalarTower F ↥B ↥(A ⊔ B) := IsScalarTower.of_algebraMap_eq' rfl
  let ρ₁ : (↥(A ⊔ B) ≃ₐ[F] ↥(A ⊔ B)) →* (↥A ≃ₐ[F] ↥A) := AlgEquiv.restrictNormalHom ↥A
  let ρ₂ : (↥(A ⊔ B) ≃ₐ[F] ↥(A ⊔ B)) →* (↥B ≃ₐ[F] ↥B) := AlgEquiv.restrictNormalHom ↥B
  let φ₀ : (↥(A ⊔ B) ≃ₐ[F] ↥(A ⊔ B)) →* ((↥A ≃ₐ[F] ↥A) × (↥B ≃ₐ[F] ↥B)) := ρ₁.prod ρ₂
  -- the two components are the restrictions, as maps into `F'`
  have hcoe₁ : ∀ (σ : ↥(A ⊔ B) ≃ₐ[F] ↥(A ⊔ B)) (x : ↥A),
      (((ρ₁ σ) x : ↥A) : F') = ((σ ⟨x.1, (le_sup_left : A ≤ A ⊔ B) x.2⟩ : ↥(A ⊔ B)) : F') := by
    intro σ x
    exact congrArg (fun z : ↥(A ⊔ B) => (z : F'))
      (AlgEquiv.restrictNormal_commutes (F := F) (E := ↥A) (K₁ := ↥(A ⊔ B)) (K₂ := ↥(A ⊔ B)) σ x)
  have hcoe₂ : ∀ (σ : ↥(A ⊔ B) ≃ₐ[F] ↥(A ⊔ B)) (y : ↥B),
      (((ρ₂ σ) y : ↥B) : F') = ((σ ⟨y.1, (le_sup_right : B ≤ A ⊔ B) y.2⟩ : ↥(A ⊔ B)) : F') := by
    intro σ y
    exact congrArg (fun z : ↥(A ⊔ B) => (z : F'))
      (AlgEquiv.restrictNormal_commutes (F := F) (E := ↥B) (K₁ := ↥(A ⊔ B)) (K₂ := ↥(A ⊔ B)) σ y)
  have hinj : Function.Injective φ₀ := by
    intro σ τ h
    have h₁ : ρ₁ σ = ρ₁ τ := by simpa [φ₀] using congrArg Prod.fst h
    have h₂ : ρ₂ σ = ρ₂ τ := by simpa [φ₀] using congrArg Prod.snd h
    apply eq_of_eqOn_sup_of_sup A B
    · intro x
      have hx : (σ.restrictNormal ↥A) x = (τ.restrictNormal ↥A) x :=
        congrArg (fun f : ↥A ≃ₐ[F] ↥A => f x) h₁
      show σ (algebraMap ↥A ↥(A ⊔ B) x) = τ (algebraMap ↥A ↥(A ⊔ B) x)
      rw [← AlgEquiv.restrictNormal_commutes (F := F) (E := ↥A) (K₁ := ↥(A ⊔ B))
            (K₂ := ↥(A ⊔ B)) σ x,
        ← AlgEquiv.restrictNormal_commutes (F := F) (E := ↥A) (K₁ := ↥(A ⊔ B))
            (K₂ := ↥(A ⊔ B)) τ x, hx]
    · intro y
      have hy : (σ.restrictNormal ↥B) y = (τ.restrictNormal ↥B) y :=
        congrArg (fun f : ↥B ≃ₐ[F] ↥B => f y) h₂
      show σ (algebraMap ↥B ↥(A ⊔ B) y) = τ (algebraMap ↥B ↥(A ⊔ B) y)
      rw [← AlgEquiv.restrictNormal_commutes (F := F) (E := ↥B) (K₁ := ↥(A ⊔ B))
            (K₂ := ↥(A ⊔ B)) σ y,
        ← AlgEquiv.restrictNormal_commutes (F := F) (E := ↥B) (K₁ := ↥(A ⊔ B))
            (K₂ := ↥(A ⊔ B)) τ y, hy]
  haveI : Fintype (↥(A ⊔ B) ≃ₐ[F] ↥(A ⊔ B)) := Fintype.ofFinite _
  haveI : Fintype ((↥A ≃ₐ[F] ↥A) × (↥B ≃ₐ[F] ↥B)) := Fintype.ofFinite _
  have hcard' : Fintype.card (↥(A ⊔ B) ≃ₐ[F] ↥(A ⊔ B)) =
      Fintype.card ((↥A ≃ₐ[F] ↥A) × (↥B ≃ₐ[F] ↥B)) := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
    exact hcard
  have hbij : Function.Bijective φ₀ :=
    (Fintype.bijective_iff_injective_and_card φ₀).mpr ⟨hinj, hcard'⟩
  refine ⟨MulEquiv.ofBijective φ₀ hbij, ?_, ?_⟩
  · intro σ x
    rw [MulEquiv.ofBijective_apply]
    simpa [φ₀] using hcoe₁ σ x
  · intro σ y
    rw [MulEquiv.ofBijective_apply]
    simpa [φ₀] using hcoe₂ σ y

end NK.FieldTheory.Galois
