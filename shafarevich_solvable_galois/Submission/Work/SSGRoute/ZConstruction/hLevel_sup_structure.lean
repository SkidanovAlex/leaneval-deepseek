import Mathlib
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.SupStructure
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZConstruction

open Classical

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

open Work.SSGRoute.ZDataMup.LTRecFamHonest

/-!
## The structure of the compositum of two finite Galois subextensions

Let `Ω` be an algebraic closure of `↥K` (with `K/k` a finite Galois number field extension), and let
`L₁ L₂ ⊆ Ω` be finite Galois over `↥K` whose Galois groups are commutative of exponent `p` (such
as two Kummer levels `hLevel β₁`, `hLevel β₂`).

Then the compositum `L₁ ⊔ L₂` is again finite Galois over `↥K` with a commutative Galois group of
exponent `p`.  This is the general (composable) form of the statement needed for the target; the
group-theoretic content is that restriction to `L₁` and to `L₂` combines to an *injective*
monoid homomorphism

  `Gal(L₁ ⊔ L₂ / ↥K) ↪ Gal(L₁/↥K) × Gal(L₂/↥K)`,

built from `AlgEquiv.restrictNormalHom` and the equality
`(L₁ ⊔ L₂).fixingSubgroup = L₁.fixingSubgroup ⊓ L₂.fixingSubgroup`
(`IntermediateField.fixingSubgroup_sup`).
-/

/-- **The compositum of two finite Galois subextensions with abelian exponent-`p` Galois groups
has abelian exponent-`p` Galois group.**

Concretely: `Gal(L₁ ⊔ L₂/↥K)` embeds into `Gal(L₁/↥K) × Gal(L₂/↥K)` via restriction, and the
latter is commutative of exponent `p`. -/
theorem galois_sup_structure {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (L₁ L₂ : IntermediateField ↥K Ω)
    [FiniteDimensional ↥K ↥L₁] [IsGalois ↥K ↥L₁]
    [FiniteDimensional ↥K ↥L₂] [IsGalois ↥K ↥L₂]
    (hcomm₁ : ∀ a b : ↥L₁ ≃ₐ[↥K] ↥L₁, a * b = b * a)
    (hcomm₂ : ∀ a b : ↥L₂ ≃ₐ[↥K] ↥L₂, a * b = b * a)
    (hexp₁ : ∀ a : ↥L₁ ≃ₐ[↥K] ↥L₁, a ^ p = 1)
    (hexp₂ : ∀ a : ↥L₂ ≃ₐ[↥K] ↥L₂, a ^ p = 1) :
    IsGalois ↥K ↥(L₁ ⊔ L₂) ∧
    (∀ a b : ↥(L₁ ⊔ L₂) ≃ₐ[↥K] ↥(L₁ ⊔ L₂), a * b = b * a) ∧
    (∀ a : ↥(L₁ ⊔ L₂) ≃ₐ[↥K] ↥(L₁ ⊔ L₂), a ^ p = 1) := by
  -- `Ω` is Galois over `↥K`, hence separable.
  haveI hgalΩ : IsGalois ↥K Ω := h_galois_base
  -- The compositum is separable (`Algebra.isSeparable_tower_bot_of_isSeparable`) and normal
  -- (instance `IntermediateField.normal_sup`).
  have hgal : IsGalois ↥K ↥(L₁ ⊔ L₂) :=
    { to_isSeparable := Algebra.isSeparable_tower_bot_of_isSeparable ↥K ↥(L₁ ⊔ L₂) Ω
      to_normal := inferInstance }
  haveI := hgal
  -- Restriction to the two factors, as a monoid homomorphism on `Gal(Ω/↥K)`.
  let Φ : (Ω ≃ₐ[↥K] Ω) →* (↥L₁ ≃ₐ[↥K] ↥L₁) × (↥L₂ ≃ₐ[↥K] ↥L₂) :=
    (AlgEquiv.restrictNormalHom ↥L₁).prod (AlgEquiv.restrictNormalHom ↥L₂)
  have hkerΦ : Φ.ker = (L₁ ⊔ L₂).fixingSubgroup := by
    rw [MonoidHom.ker_prod, IntermediateField.restrictNormalHom_ker L₁,
      IntermediateField.restrictNormalHom_ker L₂, IntermediateField.fixingSubgroup_sup]
  -- Restriction to the compositum.
  let q : (Ω ≃ₐ[↥K] Ω) →* (↥(L₁ ⊔ L₂) ≃ₐ[↥K] ↥(L₁ ⊔ L₂)) :=
    AlgEquiv.restrictNormalHom ↥(L₁ ⊔ L₂)
  have hqsurj : Function.Surjective q :=
    AlgEquiv.restrictNormalHom_surjective (F := ↥K) (K₁ := ↥(L₁ ⊔ L₂)) Ω
  have hkerq : q.ker = (L₁ ⊔ L₂).fixingSubgroup :=
    IntermediateField.restrictNormalHom_ker (L₁ ⊔ L₂)
  have hker_eq : q.ker = Φ.ker := by rw [hkerq, hkerΦ]
  -- `Gal(L₁ ⊔ L₂/↥K) ≃ Gal(Ω/↥K)/ker q = Gal(Ω/↥K)/ker Φ`.
  let e : (↥(L₁ ⊔ L₂) ≃ₐ[↥K] ↥(L₁ ⊔ L₂)) ≃* (Ω ≃ₐ[↥K] Ω) ⧸ q.ker :=
    (QuotientGroup.quotientKerEquivOfSurjective q hqsurj).symm
  -- The restriction map on the compositum, with values in the product of the two Galois groups.
  let Ψ : (↥(L₁ ⊔ L₂) ≃ₐ[↥K] ↥(L₁ ⊔ L₂)) →*
      (↥L₁ ≃ₐ[↥K] ↥L₁) × (↥L₂ ≃ₐ[↥K] ↥L₂) :=
    (QuotientGroup.kerLift Φ).comp
      ((QuotientGroup.quotientMulEquivOfEq hker_eq).toMonoidHom.comp e.toMonoidHom)
  have hΨinj : Function.Injective Ψ :=
    (QuotientGroup.kerLift_injective Φ).comp
      ((QuotientGroup.quotientMulEquivOfEq hker_eq).injective.comp e.injective)
  refine ⟨hgal, ?_, ?_⟩
  · intro a b
    apply hΨinj
    rw [map_mul, map_mul]
    exact Prod.ext (hcomm₁ (Ψ a).1 (Ψ b).1) (hcomm₂ (Ψ a).2 (Ψ b).2)
  · intro a
    apply hΨinj
    rw [map_pow, map_one]
    exact Prod.ext (hexp₁ (Ψ a).1) (hexp₂ (Ψ a).2)

theorem hLevel_sup_structure (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω] (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (β₁ β₂ : (↥K)ˣ) :
    FiniteDimensional ↥K ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (K := K) (Ω := Ω) (p := p) β₁ ⊔
      Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (K := K) (Ω := Ω) (p := p) β₂) ∧
    IsGalois ↥K ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (K := K) (Ω := Ω) (p := p) β₁ ⊔
      Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (K := K) (Ω := Ω) (p := p) β₂) ∧
    (∀ σ : ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (K := K) (Ω := Ω) (p := p) β₁ ⊔
        Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (K := K) (Ω := Ω) (p := p) β₂) ≃ₐ[↥K]
        ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (K := K) (Ω := Ω) (p := p) β₁ ⊔
          Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (K := K) (Ω := Ω) (p := p) β₂), σ ^ p = 1) ∧
    (∀ a b : ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (K := K) (Ω := Ω) (p := p) β₁ ⊔
        Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (K := K) (Ω := Ω) (p := p) β₂) ≃ₐ[↥K]
        ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (K := K) (Ω := Ω) (p := p) β₁ ⊔
          Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (K := K) (Ω := Ω) (p := p) β₂), a * b = b * a) := by
  haveI hgal₁ : IsGalois ↥K ↥(hLevel (K := K) (Ω := Ω) (p := p) β₁) :=
    hLevel_isGalois (K := K) (Ω := Ω) (p := p) ζ hζ β₁
  haveI hgal₂ : IsGalois ↥K ↥(hLevel (K := K) (Ω := Ω) (p := p) β₂) :=
    hLevel_isGalois (K := K) (Ω := Ω) (p := p) ζ hζ β₂
  haveI hfd₁ : FiniteDimensional ↥K ↥(hLevel (K := K) (Ω := Ω) (p := p) β₁) :=
    hLevel_finiteDimensional (K := K) (Ω := Ω) (p := p) ζ hζ β₁
  haveI hfd₂ : FiniteDimensional ↥K ↥(hLevel (K := K) (Ω := Ω) (p := p) β₂) :=
    hLevel_finiteDimensional (K := K) (Ω := Ω) (p := p) ζ hζ β₂
  have hsup := galois_sup_structure (p := p) (K := K) (Ω := Ω)
    (L₁ := hLevel (K := K) (Ω := Ω) (p := p) β₁)
    (L₂ := hLevel (K := K) (Ω := Ω) (p := p) β₂)
    (hLevel_isMulCommutative (K := K) (Ω := Ω) (p := p) ζ hζ β₁)
    (hLevel_isMulCommutative (K := K) (Ω := Ω) (p := p) ζ hζ β₂)
    (hLevel_aut_pow_eq_one (K := K) (Ω := Ω) (p := p) ζ hζ β₁)
    (hLevel_aut_pow_eq_one (K := K) (Ω := Ω) (p := p) ζ hζ β₂)
  exact ⟨hLevel_sup_finiteDimensional (K := K) (Ω := Ω) (p := p) ζ hζ β₁ β₂,
    hsup.1, hsup.2.2, hsup.2.1⟩

end

end Work.SSGRoute.ZConstruction
