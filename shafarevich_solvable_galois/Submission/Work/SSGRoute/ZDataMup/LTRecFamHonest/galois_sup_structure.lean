import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.SupStructure
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The compositum of two commutative-exponent-`p` Galois subextensions

Obligation (P2) of `NOTES_LTRecFam_session5.md` §3, in its composable general form: if `L₁` and `L₂`
are finite Galois subextensions of a field `Ω` over a base field `F`, and both Galois groups
`Gal(L₁/F)`, `Gal(L₂/F)` are commutative of exponent `p`, then the same holds for the compositum
`L₁ ⊔ L₂` (which is assumed finite dimensional over `F`).

All of the hypotheses about `k`, `NumberField`, `IsAlgClosure`, `IsSepClosure` and the
`DistribMulAction` of `Gal(K/k)` on `ZMod p` in the requested statement are irrelevant to the
mathematics; the statement is proved here in the general form `galois_sup_general` and then
specialised.

## Proof

* `IsGalois F ↥(L₁ ⊔ L₂)` is an instance (from `IntermediateField.normal_sup` for the normality and
  the corresponding separability instance).
* For the commutativity and the exponent we embed the Galois group of the compositum into the
  product of the two Galois groups: the restriction maps
  `Gal(L₁ ⊔ L₂/F) →* Gal(L/F)` for `L = L₁, L₂` (legitimate because `L₁`, `L₂` are normal over
  `F`) are injective on the pair.  This is exactly the statement that an automorphism of the
  compositum that fixes both `L₁` and `L₂` is the identity, which is the Galois correspondence
  identity `fixingSubgroup (A ⊔ B) = fixingSubgroup A ⊓ fixingSubgroup B` together with
  `A ⊔ B = ⊤` for the two transported subfields `A = L₁.restrict _`, `B = L₂.restrict _`.
* Then `φ (a * b) = φ a * φ b = φ b * φ a = φ (b * a)` because both coordinates live in commutative
  groups, and `φ (a ^ p) = (φ a) ^ p = 1 = φ 1`.
-/

namespace Work.SSGRoute.ZDataMup.LTRecFamHonest

open IntermediateField

noncomputable section

/-- Conjugation of `F`-algebra automorphisms along an `F`-algebra equivalence: an equivalence
`e : L ≃ₐ[F] A` induces the isomorphism of groups `Aut_F(A) ≃* Aut_F(L)`, `σ ↦ e ∘ σ ∘ e⁻¹`. -/
noncomputable def supConjAutMulEquiv {F L A : Type*} [Field F] [Field L] [Field A]
    [Algebra F L] [Algebra F A] (e : L ≃ₐ[F] A) : (A ≃ₐ[F] A) ≃* (L ≃ₐ[F] L) where
  toFun σ := e.trans (σ.trans e.symm)
  invFun σ := e.symm.trans (σ.trans e)
  left_inv σ := by ext x; simp [AlgEquiv.trans_apply]
  right_inv σ := by ext x; simp [AlgEquiv.trans_apply]
  map_mul' σ τ := by ext x; simp [AlgEquiv.trans_apply]

/-- **The compositum of two finite Galois extensions with commutative Galois groups of exponent `p`
again has a commutative Galois group of exponent `p`.** -/
theorem galois_sup_general {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {p : ℕ}
    (L₁ L₂ : IntermediateField F Ω) [FiniteDimensional F L₁] [IsGalois F L₁]
    [FiniteDimensional F L₂] [IsGalois F L₂] [FiniteDimensional F ↥(L₁ ⊔ L₂)]
    (hcomm₁ : ∀ a b : ↥L₁ ≃ₐ[F] ↥L₁, a * b = b * a)
    (hcomm₂ : ∀ a b : ↥L₂ ≃ₐ[F] ↥L₂, a * b = b * a)
    (hexp₁ : ∀ a : ↥L₁ ≃ₐ[F] ↥L₁, a ^ p = 1)
    (hexp₂ : ∀ a : ↥L₂ ≃ₐ[F] ↥L₂, a ^ p = 1) :
    IsGalois F ↥(L₁ ⊔ L₂) ∧
    (∀ a b : ↥(L₁ ⊔ L₂) ≃ₐ[F] ↥(L₁ ⊔ L₂), a * b = b * a) ∧
    (∀ a : ↥(L₁ ⊔ L₂) ≃ₐ[F] ↥(L₁ ⊔ L₂), a ^ p = 1) := by
  haveI : IsGalois F ↥(L₁ ⊔ L₂) := ⟨⟩
  -- the two factors, viewed as intermediate fields of the compositum
  let A : IntermediateField F ↥(L₁ ⊔ L₂) := L₁.restrict (le_sup_left : L₁ ≤ L₁ ⊔ L₂)
  let B : IntermediateField F ↥(L₁ ⊔ L₂) := L₂.restrict (le_sup_right : L₂ ≤ L₁ ⊔ L₂)
  haveI hA : IsGalois F ↥A :=
    IsGalois.of_algEquiv (IntermediateField.restrictAlgEquiv (le_sup_left : L₁ ≤ L₁ ⊔ L₂))
  haveI hB : IsGalois F ↥B :=
    IsGalois.of_algEquiv (IntermediateField.restrictAlgEquiv (le_sup_right : L₂ ≤ L₁ ⊔ L₂))
  have eA : ↥L₁ ≃ₐ[F] ↥A := IntermediateField.restrictAlgEquiv (le_sup_left : L₁ ≤ L₁ ⊔ L₂)
  have eB : ↥L₂ ≃ₐ[F] ↥B := IntermediateField.restrictAlgEquiv (le_sup_right : L₂ ≤ L₁ ⊔ L₂)
  let cA : (↥A ≃ₐ[F] ↥A) ≃* (↥L₁ ≃ₐ[F] ↥L₁) := supConjAutMulEquiv eA
  let cB : (↥B ≃ₐ[F] ↥B) ≃* (↥L₂ ≃ₐ[F] ↥L₂) := supConjAutMulEquiv eB
  let φL : (↥(L₁ ⊔ L₂) ≃ₐ[F] ↥(L₁ ⊔ L₂)) →* (↥L₁ ≃ₐ[F] ↥L₁) :=
    cA.toMonoidHom.comp (AlgEquiv.restrictNormalHom ↥A)
  let φM : (↥(L₁ ⊔ L₂) ≃ₐ[F] ↥(L₁ ⊔ L₂)) →* (↥L₂ ≃ₐ[F] ↥L₂) :=
    cB.toMonoidHom.comp (AlgEquiv.restrictNormalHom ↥B)
  let φ : (↥(L₁ ⊔ L₂) ≃ₐ[F] ↥(L₁ ⊔ L₂)) →*
      ((↥L₁ ≃ₐ[F] ↥L₁) × (↥L₂ ≃ₐ[F] ↥L₂)) := φL.prod φM
  -- the pair of restrictions is injective: an automorphism of the compositum which fixes both
  -- `L₁` and `L₂` is the identity
  have hker : ∀ σ : ↥(L₁ ⊔ L₂) ≃ₐ[F] ↥(L₁ ⊔ L₂), φ σ = 1 → σ = 1 := by
    intro σ hσ
    have hσ' : (φL σ, φM σ) = (1, 1) := by simpa [φ, MonoidHom.prod_apply] using hσ
    have hσA : φL σ = 1 := (Prod.mk.injEq _ _ _ _).mp hσ' |>.1
    have hσB : φM σ = 1 := (Prod.mk.injEq _ _ _ _).mp hσ' |>.2
    have h2A : AlgEquiv.restrictNormalHom ↥A σ = 1 := by
      have h1 : cA (AlgEquiv.restrictNormalHom ↥A σ) = 1 := by
        simpa [φL, MonoidHom.comp_apply] using hσA
      apply cA.injective
      rw [h1, map_one]
    have h2B : AlgEquiv.restrictNormalHom ↥B σ = 1 := by
      have h1 : cB (AlgEquiv.restrictNormalHom ↥B σ) = 1 := by
        simpa [φM, MonoidHom.comp_apply] using hσB
      apply cB.injective
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
    have hAB : A ⊔ B = ⊤ := by
      rw [← IntermediateField.lift_inj, IntermediateField.lift_top, IntermediateField.lift_sup,
        IntermediateField.lift_restrict, IntermediateField.lift_restrict]
    rw [← Subgroup.mem_bot, ← IntermediateField.fixingSubgroup_top, ← hAB,
      IntermediateField.fixingSubgroup_sup]
    exact ⟨hAmem, hBmem⟩
  have hinj : Function.Injective φ := (injective_iff_map_eq_one φ).mpr hker
  refine ⟨this, ?_, ?_⟩
  · intro a b
    have h1 : φL (a * b) = φL (b * a) := by rw [map_mul, map_mul, hcomm₁ (φL a) (φL b)]
    have h2 : φM (a * b) = φM (b * a) := by rw [map_mul, map_mul, hcomm₂ (φM a) (φM b)]
    exact hinj (by rw [show φ (a * b) = (φL (a * b), φM (a * b)) from rfl,
      show φ (b * a) = (φL (b * a), φM (b * a)) from rfl, h1, h2])
  · intro a
    have h1 : φL (a ^ p) = 1 := by rw [map_pow, hexp₁ (φL a)]
    have h2 : φM (a ^ p) = 1 := by rw [map_pow, hexp₂ (φM a)]
    exact hker (a ^ p) (by
      rw [show φ (a ^ p) = (φL (a ^ p), φM (a ^ p)) from rfl, h1, h2]; rfl)

theorem galois_sup_structure (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (L₁ : IntermediateField ↥K Ω) (L₂ : IntermediateField ↥K Ω)
    [FiniteDimensional ↥K L₁] [IsGalois ↥K L₁]
    [FiniteDimensional ↥K L₂] [IsGalois ↥K L₂] [FiniteDimensional ↥K ↥(L₁ ⊔ L₂)]
    (hcomm₁ : ∀ a b : ↥L₁ ≃ₐ[↥K] ↥L₁, a * b = b * a)
    (hcomm₂ : ∀ a b : ↥L₂ ≃ₐ[↥K] ↥L₂, a * b = b * a)
    (hexp₁ : ∀ a : ↥L₁ ≃ₐ[↥K] ↥L₁, a ^ p = 1)
    (hexp₂ : ∀ a : ↥L₂ ≃ₐ[↥K] ↥L₂, a ^ p = 1) :
    IsGalois ↥K ↥(L₁ ⊔ L₂) ∧
    (∀ a b : ↥(L₁ ⊔ L₂) ≃ₐ[↥K] ↥(L₁ ⊔ L₂), a * b = b * a) ∧
    (∀ a : ↥(L₁ ⊔ L₂) ≃ₐ[↥K] ↥(L₁ ⊔ L₂), a ^ p = 1) :=
  galois_sup_general L₁ L₂ hcomm₁ hcomm₂ hexp₁ hexp₂

end

end Work.SSGRoute.ZDataMup.LTRecFamHonest
