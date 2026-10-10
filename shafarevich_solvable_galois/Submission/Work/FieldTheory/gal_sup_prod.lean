import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.FieldTheory

/-- Conjugation of `F`-algebra automorphisms along an `F`-algebra equivalence:
an equivalence `e : L ≃ₐ[F] A` induces an isomorphism of groups
`Aut_F(A) ≃* Aut_F(L)`, `σ ↦ e⁻¹ σ e`. -/
noncomputable def algEquivAutMulEquiv {F L A : Type*} [Field F] [Field L] [Field A]
    [Algebra F L] [Algebra F A] (e : L ≃ₐ[F] A) : (A ≃ₐ[F] A) ≃* (L ≃ₐ[F] L) where
  toFun σ := e.trans (σ.trans e.symm)
  invFun σ := e.symm.trans (σ.trans e)
  left_inv σ := by ext x; simp [AlgEquiv.trans_apply]
  right_inv σ := by ext x; simp [AlgEquiv.trans_apply]
  map_mul' σ τ := by ext x; simp [AlgEquiv.trans_apply]

/-- The Galois group of a compositum of linearly disjoint finite Galois subextensions is the
product of the Galois groups.  (Equivalently: the restriction map
`Gal(L ⊔ M / F) → Gal(L/F) × Gal(M/F)` is an isomorphism.)

Suggested proof: the restriction map
`φ := (AlgEquiv.restrictNormalHom (L.restrict le_sup_left)).prod
        (AlgEquiv.restrictNormalHom (M.restrict le_sup_right))`
(after transporting along `IntermediateField.restrictAlgEquiv` to land in `L ≃ₐ[F] L` and
`M ≃ₐ[F] M`) is injective (an automorphism of `L ⊔ M` fixing `L` and `M` is the identity), and
`Nat.card Gal(L⊔M/F) = finrank F (L ⊔ M) = finrank F L * finrank F M`
(`IsGalois.card_aut_eq_finrank`, `IntermediateField.LinearDisjoint.finrank_sup`,
`IntermediateField.LinearDisjoint.of_inf_eq_bot`) equals
`Nat.card (Gal(L/F) × Gal(M/F))`, so `MulEquiv.ofBijective` finishes. -/
theorem gal_sup_prod (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω]
    (L M : IntermediateField F Ω) [FiniteDimensional F L] [IsGalois F L]
    [FiniteDimensional F M] [IsGalois F M] (h : L ⊓ M = ⊥) :
    Nonempty ((↥(L ⊔ M) ≃ₐ[F] ↥(L ⊔ M)) ≃* ((L ≃ₐ[F] L) × (M ≃ₐ[F] M))) := by
  haveI : IsGalois F ↥(L ⊔ M) := ⟨⟩
  haveI : FiniteDimensional F ↥(L ⊔ M) := inferInstance
  -- `L` and `M` are linearly disjoint, so the degree of the compositum is the product.
  have hld : L.LinearDisjoint ↥M := IntermediateField.LinearDisjoint.of_inf_eq_bot h
  have hfin : Module.finrank F ↥(L ⊔ M) = Module.finrank F ↥L * Module.finrank F ↥M :=
    hld.finrank_sup
  -- the two factors, viewed as intermediate fields of the compositum
  let A : IntermediateField F ↥(L ⊔ M) := L.restrict le_sup_left
  let B : IntermediateField F ↥(L ⊔ M) := M.restrict le_sup_right
  haveI : IsGalois F ↥A := IsGalois.of_algEquiv (IntermediateField.restrictAlgEquiv le_sup_left)
  haveI : IsGalois F ↥B := IsGalois.of_algEquiv (IntermediateField.restrictAlgEquiv le_sup_right)
  have hAB : A ⊔ B = ⊤ := by
    rw [← IntermediateField.lift_inj, IntermediateField.lift_top, IntermediateField.lift_sup,
      IntermediateField.lift_restrict le_sup_left, IntermediateField.lift_restrict le_sup_right]
  -- the two restriction maps
  have eA : ↥L ≃ₐ[F] ↥A := IntermediateField.restrictAlgEquiv le_sup_left
  have eB : ↥M ≃ₐ[F] ↥B := IntermediateField.restrictAlgEquiv le_sup_right
  let φL : Gal(↥(L ⊔ M)/F) →* Gal(↥L/F) :=
    (algEquivAutMulEquiv eA).toMonoidHom.comp (AlgEquiv.restrictNormalHom A)
  let φM : Gal(↥(L ⊔ M)/F) →* Gal(↥M/F) :=
    (algEquivAutMulEquiv eB).toMonoidHom.comp (AlgEquiv.restrictNormalHom B)
  let φ : Gal(↥(L ⊔ M)/F) →* (Gal(↥L/F) × Gal(↥M/F)) := φL.prod φM
  -- injectivity: an automorphism of the compositum fixing `L` and `M` is the identity
  have hker : ∀ σ : Gal(↥(L ⊔ M)/F), φ σ = 1 → σ = 1 := by
    intro σ hσ
    have hσ' : (φL σ, φM σ) = (1, 1) := by simpa [φ, MonoidHom.prod_apply] using hσ
    have hσA : φL σ = 1 := ((Prod.mk.injEq _ _ _ _).mp hσ').1
    have hσB : φM σ = 1 := ((Prod.mk.injEq _ _ _ _).mp hσ').2
    have h2A : AlgEquiv.restrictNormalHom A σ = 1 := by
      have h1 : (algEquivAutMulEquiv eA) (AlgEquiv.restrictNormalHom A σ) = 1 := by
        simpa [φL, MonoidHom.comp_apply] using hσA
      apply (algEquivAutMulEquiv eA).injective
      rw [h1, map_one]
    have h2B : AlgEquiv.restrictNormalHom B σ = 1 := by
      have h1 : (algEquivAutMulEquiv eB) (AlgEquiv.restrictNormalHom B σ) = 1 := by
        simpa [φM, MonoidHom.comp_apply] using hσB
      apply (algEquivAutMulEquiv eB).injective
      rw [h1, map_one]
    have hAmem : σ ∈ A.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have h3 := AlgEquiv.restrictNormalHom_apply A σ ⟨x, hx⟩
      rw [h2A] at h3
      simpa using h3.symm
    have hBmem : σ ∈ B.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have h3 := AlgEquiv.restrictNormalHom_apply B σ ⟨x, hx⟩
      rw [h2B] at h3
      simpa using h3.symm
    rw [← Subgroup.mem_bot, ← IntermediateField.fixingSubgroup_top, ← hAB,
      IntermediateField.fixingSubgroup_sup]
    exact ⟨hAmem, hBmem⟩
  have hinj : Function.Injective φ := (injective_iff_map_eq_one φ).mpr hker
  -- the codomain is finite (both factors are finite Galois groups)
  haveI : Finite (Gal(↥L/F) × Gal(↥M/F)) := by
    apply Nat.finite_of_card_ne_zero
    rw [Nat.card_prod, IsGalois.card_aut_eq_finrank F ↥L, IsGalois.card_aut_eq_finrank F ↥M]
    exact Nat.mul_ne_zero (Module.finrank_pos.ne') (Module.finrank_pos.ne')
  -- and the two groups have the same order
  have hcardeq : Nat.card (Gal(↥L/F) × Gal(↥M/F)) = Nat.card Gal(↥(L ⊔ M)/F) := by
    rw [Nat.card_prod, IsGalois.card_aut_eq_finrank F ↥L, IsGalois.card_aut_eq_finrank F ↥M,
      ← hfin, IsGalois.card_aut_eq_finrank F ↥(L ⊔ M)]
  have hbij : Function.Bijective φ := hinj.bijective_of_nat_card_le hcardeq.le
  exact ⟨MulEquiv.ofBijective φ hbij⟩

end Work.FieldTheory
