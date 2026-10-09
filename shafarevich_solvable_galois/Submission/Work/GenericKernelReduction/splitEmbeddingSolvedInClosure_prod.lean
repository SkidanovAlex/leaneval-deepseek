import Mathlib
import Submission.Work.GenericKernelReduction.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Products of split embedding problems with coprime kernel orders

This file proves that the closure-form split embedding property
`Work.GenericKernelReduction.SplitEmbeddingSolvedInClosure` is closed under products of kernels
whose orders are coprime.

The mathematical content: if `L/ℚ` is a finite Galois extension and `M_A`, `M_B ⊆ ℚ̄` are finite
Galois extensions of `ℚ` realising the split embedding problems attached to the actions `φA`, `φB`
of `G = Gal(L/ℚ)` on the coprime groups `A`, `B`, then the compositum `M = M_A·M_B` realises the
split embedding problem attached to `φA × φB` on `A × B`, provided `M_A · M_B` is the *fibre
product* `Gal(M_A/ℚ) ×_{Gal(L/ℚ)} Gal(M_B/ℚ)`; the latter holds because the degrees of `M_A/L`
and `M_B/L` are `|A|` and `|B|` and hence coprime.

## Implementation notes

The Galois structures `Algebra ↥L ↥M` used below are the canonical inclusions; the abstract
`Algebra ↥L ↥M` structure carried by a witness of `SplitEmbeddingSolvedInClosure` is an arbitrary
`ℚ`-algebra structure whose algebra map is an automorphism ("twist") of `L`.  The twist is
extracted by `exists_twist` and accounted for explicitly in the isomorphism constructed below.
-/

namespace Work.GenericKernelReduction

set_option maxHeartbeats 4000000

open scoped Classical

/-! ## Extracting the twist of an abstract `Algebra ↥L ↥M` structure -/

/-- **The twist of an abstract algebra structure.**

Let `L ≤ MA` be intermediate fields of `Ω/F` with `L/F` Galois, and let `Algebra ↥L ↥MA` be *any*
`F`-algebra structure on `↥MA` (compatible with the `F`-algebra structure, `IsScalarTower`).  Then
the algebra map `↥L → ↥MA`, viewed as an `F`-embedding into `Ω`, has image exactly `L`, and hence
induces an element `α : ↥L ≃ₐ[F] ↥L` of `Gal(L/F)`, characterised by
`(α x : Ω) = (algebraMap ↥L ↥MA x : Ω)`.

(Up to the identification `↥MA` with the subfield `MA ⊆ Ω`, such an algebra structure is precisely
given by a twist `α ∈ Gal(L/F)`: the algebra map is `x ↦ α x`.) -/
theorem exists_twist {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
    (L MA : IntermediateField F Ω) (hgal : IsGalois F L)
    (hAlg : Algebra ↥L ↥MA) (hST : IsScalarTower F ↥L ↥MA) :
    ∃ α : ↥L ≃ₐ[F] ↥L, ∀ x : ↥L, (α x : Ω) = (algebraMap ↥L ↥MA x : Ω) := by
  letI := hAlg
  haveI := hST
  haveI := hgal
  let ψ : ↥L →ₐ[F] Ω := (IntermediateField.val MA).comp (IsScalarTower.toAlgHom F ↥L ↥MA)
  have hψ : ψ.fieldRange = L := AlgHom.fieldRange_of_normal ψ
  have hmem : ∀ x : ↥L, ψ x ∈ L.toSubalgebra := fun x => by
    have h1 : ψ x ∈ ψ.fieldRange := AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩
    rw [hψ] at h1
    exact h1
  have hsurj : Function.Surjective (ψ.codRestrict L.toSubalgebra hmem) := by
    intro y
    have hy : (y : Ω) ∈ ψ.fieldRange := by rw [hψ]; exact y.2
    obtain ⟨x, hx⟩ := AlgHom.mem_fieldRange.mp hy
    exact ⟨x, Subtype.ext hx⟩
  exact ⟨AlgEquiv.ofBijective (ψ.codRestrict L.toSubalgebra hmem)
    ⟨RingHom.injective _, hsurj⟩, fun x => rfl⟩

/-! ## Restriction of automorphisms to a subfield -/

section Restrict

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]

/-- Restriction of `Gal(M/F)` to a subfield `K ≤ M`, as a homomorphism `Gal(M/F) →* Gal(K/F)`,
using the inclusion `↥K → ↥M` as the algebra structure on `↥M` over `↥K`. -/
noncomputable def restrictHom (M K : IntermediateField F Ω) (hKM : K ≤ M) (hN : Normal F ↥K) :
    (M ≃ₐ[F] M) →* (K ≃ₐ[F] K) := by
  letI : Algebra ↥K ↥M := (IntermediateField.inclusion hKM).toRingHom.toAlgebra
  haveI : IsScalarTower F ↥K ↥M := IsScalarTower.of_algHom (IntermediateField.inclusion hKM)
  haveI := hN
  exact AlgEquiv.restrictNormalHom ↥K

/-- The defining property of `restrictHom`: it is given by restricting an automorphism to `K`. -/
theorem restrictHom_apply (M K : IntermediateField F Ω) (hKM : K ≤ M) (hN : Normal F ↥K)
    (σ : M ≃ₐ[F] M) (x : ↥K) :
    ((restrictHom M K hKM hN σ x : ↥K) : Ω) = (σ ⟨(x : Ω), hKM x.2⟩ : Ω) := by
  letI : Algebra ↥K ↥M := (IntermediateField.inclusion hKM).toRingHom.toAlgebra
  haveI : IsScalarTower F ↥K ↥M := IsScalarTower.of_algHom (IntermediateField.inclusion hKM)
  haveI := hN
  have key : ∀ y : ↥K, (algebraMap ↥K ↥M y : ↥M) = ⟨(y : Ω), hKM y.2⟩ := fun y => by
    have h := RingHom.algebraMap_toAlgebra ((IntermediateField.inclusion hKM).toRingHom)
    rw [h]
    rfl
  have h1 : (restrictHom M K hKM hN) σ = σ.restrictNormal ↥K := rfl
  rw [h1]
  have h2 := AlgEquiv.restrictNormal_commutes σ ↥K x
  rw [key, key] at h2
  exact congrArg (fun z : ↥M => (z : Ω)) h2

/-- `restrictHom` is surjective when the ambient extension is Galois. -/
theorem restrictHom_surjective {M K : IntermediateField F Ω} (hKM : K ≤ M)
    (hN : Normal F ↥K) (hNM : Normal F ↥M) :
    Function.Surjective (restrictHom M K hKM hN) := by
  letI : Algebra ↥K ↥M := (IntermediateField.inclusion hKM).toRingHom.toAlgebra
  haveI : IsScalarTower F ↥K ↥M := IsScalarTower.of_algHom (IntermediateField.inclusion hKM)
  haveI := hN
  haveI := hNM
  exact AlgEquiv.restrictNormalHom_surjective (E := ↥M) (K₁ := ↥K)

end Restrict

/-! ## Counting lemmas -/

/-- Lagrange in the form used below: the order of a finite group is the product of the order of
the kernel of a homomorphism and the order of its range. -/
theorem card_eq_ker_mul_card_range {X Z : Type*} [Group X] [Group Z] [Finite X]
    (f : X →* Z) : Nat.card X = Nat.card f.ker * Nat.card f.range := by
  have h := Subgroup.card_mul_index (f.ker : Subgroup X)
  rw [Subgroup.index_ker] at h
  exact h.symm


/-! ## The product theorem -/

/-- **The split embedding property is closed under products of coprime kernels.** -/
theorem splitEmbeddingSolvedInClosure_prod {L : IntermediateField ℚ (AlgebraicClosure ℚ)}
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {A B : Type} [Group A] [Finite A] [Group B] [Finite B]
    (hcop : Nat.Coprime (Nat.card A) (Nat.card B))
    (φA : (L ≃ₐ[ℚ] L) →* MulAut A) (φB : (L ≃ₐ[ℚ] L) →* MulAut B)
    (hA : Work.GenericKernelReduction.SplitEmbeddingSolvedInClosure L A φA)
    (hB : Work.GenericKernelReduction.SplitEmbeddingSolvedInClosure L B φB) :
    Work.GenericKernelReduction.SplitEmbeddingSolvedInClosure L (A × B)
      (Work.GenericKernelReduction.prodAction φA φB) := by
  classical
  obtain ⟨MA, hLMA, hFdMA, hGalMA, hAlgMA, hSTMA, hFdLMA, hGalLMA, eA, heA⟩ := hA
  obtain ⟨MB, hLMB, hFdMB, hGalMB, hAlgMB, hSTMB, hFdLMB, hGalLMB, eB, heB⟩ := hB
  -- the twists of the two abstract algebra structures
  obtain ⟨α, hα⟩ : ∃ α : (L ≃ₐ[ℚ] L), ∀ x : ↥L,
      (α x : AlgebraicClosure ℚ) = (algebraMap ↥L ↥MA x : AlgebraicClosure ℚ) :=
    exists_twist L MA ‹IsGalois ℚ L› hAlgMA hSTMA
  obtain ⟨β, hβ⟩ : ∃ β : (L ≃ₐ[ℚ] L), ∀ x : ↥L,
      (β x : AlgebraicClosure ℚ) = (algebraMap ↥L ↥MB x : AlgebraicClosure ℚ) :=
    exists_twist L MB ‹IsGalois ℚ L› hAlgMB hSTMB
  -- the compositum
  let M : IntermediateField ℚ (AlgebraicClosure ℚ) := MA ⊔ MB
  have hleA : MA ≤ M := le_sup_left
  have hleB : MB ≤ M := le_sup_right
  have hLM : L ≤ M := hLMA.trans hleA
  haveI : FiniteDimensional ℚ MA := hFdMA
  haveI : IsGalois ℚ MA := hGalMA
  haveI : FiniteDimensional ℚ MB := hFdMB
  haveI : IsGalois ℚ MB := hGalMB
  haveI : FiniteDimensional ℚ M := inferInstance
  haveI hgalM : IsGalois ℚ M :=
    @FiniteGaloisIntermediateField.instIsGaloisSubtypeMemIntermediateFieldMax ℚ (AlgebraicClosure ℚ)
      _ _ _ MA MB hGalMA hGalMB
  -- restrictions to `MA`, `MB` and `L`
  let ρA : (M ≃ₐ[ℚ] M) →* (MA ≃ₐ[ℚ] MA) := restrictHom M MA hleA hGalMA.to_normal
  let ρB : (M ≃ₐ[ℚ] M) →* (MB ≃ₐ[ℚ] MB) := restrictHom M MB hleB hGalMB.to_normal
  let ρL : (M ≃ₐ[ℚ] M) →* (L ≃ₐ[ℚ] L) := restrictHom M L hLM (inferInstance : Normal ℚ ↥L)
  let rA : (M ≃ₐ[ℚ] M) →* (A ⋊[φA] (L ≃ₐ[ℚ] L)) := eA.symm.toMonoidHom.comp ρA
  let rB : (M ≃ₐ[ℚ] M) →* (B ⋊[φB] (L ≃ₐ[ℚ] L)) := eB.symm.toMonoidHom.comp ρB
  have hrA : ∀ σ : (M ≃ₐ[ℚ] M), eA (rA σ) = ρA σ := fun σ => by
    rw [show (rA σ) = eA.symm (ρA σ) from rfl, MulEquiv.apply_symm_apply]
  have hrB : ∀ σ : (M ≃ₐ[ℚ] M), eB (rB σ) = ρB σ := fun σ => by
    rw [show (rB σ) = eB.symm (ρB σ) from rfl, MulEquiv.apply_symm_apply]
  have hρA_apply : ∀ (σ : (M ≃ₐ[ℚ] M)) (x : ↥MA),
      ((ρA σ x : ↥MA) : AlgebraicClosure ℚ)
        = (σ ⟨(x : AlgebraicClosure ℚ), hleA x.2⟩ : AlgebraicClosure ℚ) :=
    fun σ x => restrictHom_apply M MA hleA hGalMA.to_normal σ x
  have hρB_apply : ∀ (σ : (M ≃ₐ[ℚ] M)) (x : ↥MB),
      ((ρB σ x : ↥MB) : AlgebraicClosure ℚ)
        = (σ ⟨(x : AlgebraicClosure ℚ), hleB x.2⟩ : AlgebraicClosure ℚ) :=
    fun σ x => restrictHom_apply M MB hleB hGalMB.to_normal σ x
  have hρL_apply : ∀ (σ : (M ≃ₐ[ℚ] M)) (x : ↥L),
      ((ρL σ x : ↥L) : AlgebraicClosure ℚ)
        = (σ ⟨(x : AlgebraicClosure ℚ), hLM x.2⟩ : AlgebraicClosure ℚ) :=
    fun σ x => restrictHom_apply M L hLM (inferInstance : Normal ℚ ↥L) σ x
  -- The key relations: the `G`-component of `rA`/`rB` is the restriction to `L`, conjugated by
  -- the twists.
  have hrelA : ∀ σ : (M ≃ₐ[ℚ] M), α * SemidirectProduct.rightHom (rA σ) = ρL σ * α := by
    intro σ
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    have hL : ((α * SemidirectProduct.rightHom (rA σ)) x : AlgebraicClosure ℚ)
        = (σ ⟨(α x : AlgebraicClosure ℚ), hLM (α x).2⟩ : AlgebraicClosure ℚ) := by
      rw [show ((α * SemidirectProduct.rightHom (rA σ)) x)
        = (α (SemidirectProduct.rightHom (rA σ) x) : ↥L) from rfl]
      rw [hα (SemidirectProduct.rightHom (rA σ) x)]
      rw [← heA (rA σ) x, hrA σ]
      rw [hρA_apply σ (algebraMap ↥L ↥MA x)]
      exact congrArg (fun z : ↥M => (σ z : AlgebraicClosure ℚ)) (Subtype.ext (hα x).symm)
    have hR : ((ρL σ * α) x : AlgebraicClosure ℚ)
        = (σ ⟨(α x : AlgebraicClosure ℚ), hLM (α x).2⟩ : AlgebraicClosure ℚ) := by
      rw [show ((ρL σ * α) x) = (ρL σ (α x) : ↥L) from rfl]
      rw [hρL_apply σ (α x)]
    rw [hL, hR]
  have hrelB : ∀ σ : (M ≃ₐ[ℚ] M), β * SemidirectProduct.rightHom (rB σ) = ρL σ * β := by
    intro σ
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    have hL : ((β * SemidirectProduct.rightHom (rB σ)) x : AlgebraicClosure ℚ)
        = (σ ⟨(β x : AlgebraicClosure ℚ), hLM (β x).2⟩ : AlgebraicClosure ℚ) := by
      rw [show ((β * SemidirectProduct.rightHom (rB σ)) x)
        = (β (SemidirectProduct.rightHom (rB σ) x) : ↥L) from rfl]
      rw [hβ (SemidirectProduct.rightHom (rB σ) x)]
      rw [← heB (rB σ) x, hrB σ]
      rw [hρB_apply σ (algebraMap ↥L ↥MB x)]
      exact congrArg (fun z : ↥M => (σ z : AlgebraicClosure ℚ)) (Subtype.ext (hβ x).symm)
    have hR : ((ρL σ * β) x : AlgebraicClosure ℚ)
        = (σ ⟨(β x : AlgebraicClosure ℚ), hLM (β x).2⟩ : AlgebraicClosure ℚ) := by
      rw [show ((ρL σ * β) x) = (ρL σ (β x) : ↥L) from rfl]
      rw [hρL_apply σ (β x)]
    rw [hL, hR]
  -- injectivity of `(rA, rB)`
  have hker : ∀ σ : (M ≃ₐ[ℚ] M), rA σ = 1 → rB σ = 1 → σ = 1 := by
    intro σ hA1 hB1
    have hρA : ρA σ = 1 := by rw [← hrA σ, hA1, map_one]
    have hρB : ρB σ = 1 := by rw [← hrB σ, hB1, map_one]
    have hfixA : σ ∈ (MA.restrict hleA).fixingSubgroup := by
      refine (IntermediateField.mem_fixingSubgroup_iff _ σ).mpr ?_
      intro y hy
      have hy' : y.1 ∈ MA := (IntermediateField.mem_restrict hleA y).mp hy
      have h1 : ρA σ ⟨y.1, hy'⟩ = ⟨y.1, hy'⟩ := by rw [hρA]; rfl
      have h2 := hρA_apply σ ⟨y.1, hy'⟩
      rw [h1] at h2
      refine Subtype.ext ?_
      exact h2.symm
    have hfixB : σ ∈ (MB.restrict hleB).fixingSubgroup := by
      refine (IntermediateField.mem_fixingSubgroup_iff _ σ).mpr ?_
      intro y hy
      have hy' : y.1 ∈ MB := (IntermediateField.mem_restrict hleB y).mp hy
      have h1 : ρB σ ⟨y.1, hy'⟩ = ⟨y.1, hy'⟩ := by rw [hρB]; rfl
      have h2 := hρB_apply σ ⟨y.1, hy'⟩
      rw [h1] at h2
      refine Subtype.ext ?_
      exact h2.symm
    have htop : MA.restrict hleA ⊔ MB.restrict hleB = ⊤ := by
      rw [← IntermediateField.lift_inj, IntermediateField.lift_top, IntermediateField.lift_sup,
        IntermediateField.lift_restrict hleA, IntermediateField.lift_restrict hleB]
    have key : (MA.restrict hleA).fixingSubgroup ⊓ (MB.restrict hleB).fixingSubgroup
        = ⊥ := by
      rw [← IntermediateField.fixingSubgroup_sup, htop, IntermediateField.fixingSubgroup_top]
    have hmem : σ ∈ (MA.restrict hleA).fixingSubgroup ⊓ (MB.restrict hleB).fixingSubgroup :=
      ⟨hfixA, hfixB⟩
    rw [key] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hinj : Function.Injective (fun σ : (M ≃ₐ[ℚ] M) => (rA σ, rB σ)) := by
    intro σ τ h
    rw [Prod.mk.injEq] at h
    have h1 : σ * τ⁻¹ = 1 :=
      hker (σ * τ⁻¹) (by rw [map_mul, map_inv, h.1, mul_inv_cancel])
        (by rw [map_mul, map_inv, h.2, mul_inv_cancel])
    have h2 : (σ * τ⁻¹) * τ = 1 * τ := by rw [h1]
    rwa [mul_assoc, inv_mul_cancel, mul_one, one_mul] at h2
  -- surjectivity of `rA`, `rB`
  have hsurjA : Function.Surjective rA :=
    (eA.symm.surjective).comp (restrictHom_surjective hleA hGalMA.to_normal hgalM.to_normal)
  have hsurjB : Function.Surjective rB :=
    (eB.symm.surjective).comp (restrictHom_surjective hleB hGalMB.to_normal hgalM.to_normal)
  -- finiteness and cardinality of `Gal(M/ℚ)`
  haveI : Finite (L ≃ₐ[ℚ] L) := Nat.finite_of_card_ne_zero (by
    rw [IsGalois.card_aut_eq_finrank ℚ ↥L]
    exact (Module.finrank_pos (R := ℚ) (M := ↥L)).ne')
  haveI : Finite (M ≃ₐ[ℚ] M) := Nat.finite_of_card_ne_zero (by
    rw [IsGalois.card_aut_eq_finrank ℚ ↥M]
    exact (Module.finrank_pos (R := ℚ) (M := ↥M)).ne')
  haveI : Finite (A ⋊[φA] (L ≃ₐ[ℚ] L)) :=
    Finite.of_injective _ SemidirectProduct.equivProd.injective
  haveI : Finite (B ⋊[φB] (L ≃ₐ[ℚ] L)) :=
    Finite.of_injective _ SemidirectProduct.equivProd.injective
  haveI : Finite ((A × B) ⋊[prodAction φA φB] (L ≃ₐ[ℚ] L)) :=
    Finite.of_injective _ SemidirectProduct.equivProd.injective
  have hcardA : Nat.card (A ⋊[φA] (L ≃ₐ[ℚ] L)) = Nat.card A * Nat.card (L ≃ₐ[ℚ] L) := by
    rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
  have hcardB : Nat.card (B ⋊[φB] (L ≃ₐ[ℚ] L)) = Nat.card B * Nat.card (L ≃ₐ[ℚ] L) := by
    rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
  have hdvdA : Nat.card A * Nat.card (L ≃ₐ[ℚ] L) ∣ Nat.card (M ≃ₐ[ℚ] M) := by
    rw [← hcardA]
    exact Subgroup.card_dvd_of_surjective (f := rA) hsurjA
  have hdvdB : Nat.card B * Nat.card (L ≃ₐ[ℚ] L) ∣ Nat.card (M ≃ₐ[ℚ] M) := by
    rw [← hcardB]
    exact Subgroup.card_dvd_of_surjective (f := rB) hsurjB
  have hlcm : Nat.card A * Nat.card B * Nat.card (L ≃ₐ[ℚ] L) ∣ Nat.card (M ≃ₐ[ℚ] M) := by
    rw [← Nat.Coprime.lcm_eq_mul hcop,
      ← Nat.lcm_mul_right (Nat.card A) (Nat.card (L ≃ₐ[ℚ] L)) (Nat.card B)]
    exact Nat.lcm_dvd hdvdA hdvdB
  have hcard3 : Nat.card ((L ≃ₐ[ℚ] L) × A × B)
      = Nat.card A * Nat.card B * Nat.card (L ≃ₐ[ℚ] L) := by
    rw [Nat.card_prod, Nat.card_prod]
    ring
  have hle : Nat.card (M ≃ₐ[ℚ] M) ≤ Nat.card A * Nat.card B * Nat.card (L ≃ₐ[ℚ] L) := by
    have hκ : Function.Injective (fun σ : (M ≃ₐ[ℚ] M) =>
        (ρL σ, (rA σ).left, (rB σ).left)) := by
      intro σ τ h
      have h1 : ρL σ = ρL τ := congrArg Prod.fst h
      have h2 : (rA σ).left = (rA τ).left := congrArg (fun x => x.2.1) h
      have h3 : (rB σ).left = (rB τ).left := congrArg (fun x => x.2.2) h
      have h4 : SemidirectProduct.rightHom (rA σ) = SemidirectProduct.rightHom (rA τ) := by
        have h5 := hrelA σ
        have h6 := hrelA τ
        rw [← h1] at h6
        exact mul_left_cancel (h5.trans h6.symm)
      have h7 : SemidirectProduct.rightHom (rB σ) = SemidirectProduct.rightHom (rB τ) := by
        have h5 := hrelB σ
        have h6 := hrelB τ
        rw [← h1] at h6
        exact mul_left_cancel (h5.trans h6.symm)
      exact hinj (Prod.ext (SemidirectProduct.ext h2 h4) (SemidirectProduct.ext h3 h7))
    have := Nat.card_le_card_of_injective _ hκ
    rwa [hcard3] at this
  have hcardP : Nat.card (M ≃ₐ[ℚ] M) = Nat.card A * Nat.card B * Nat.card (L ≃ₐ[ℚ] L) :=
    le_antisymm hle (Nat.le_of_dvd Nat.card_pos hlcm)
  -- the explicit group homomorphism `Gal(M/ℚ) →* (A × B) ⋊ Gal(L/ℚ)`
  have hleftA : ∀ σ τ : (M ≃ₐ[ℚ] M),
      (rA (σ * τ)).left = (rA σ).left * φA ((rA σ).right) ((rA τ).left) := fun σ τ => by
    rw [map_mul, SemidirectProduct.mul_left]
  have hleftB : ∀ σ τ : (M ≃ₐ[ℚ] M),
      (rB (σ * τ)).left = (rB σ).left * φB ((rB σ).right) ((rB τ).left) := fun σ τ => by
    rw [map_mul, SemidirectProduct.mul_left]
  have hAc : ∀ σ τ : (M ≃ₐ[ℚ] M),
      (φA α) ((rA (σ * τ)).left)
        = (φA α) ((rA σ).left) * (φA (ρL σ)) ((φA α) ((rA τ).left)) := fun σ τ => by
    rw [hleftA σ τ, map_mul (φA α)]
    congr 1
    rw [← MulAut.mul_apply, ← map_mul,
      show α * (rA σ).right = α * SemidirectProduct.rightHom (rA σ) from rfl, hrelA σ,
      map_mul, MulAut.mul_apply]
  have hBc : ∀ σ τ : (M ≃ₐ[ℚ] M),
      (φB β) ((rB (σ * τ)).left)
        = (φB β) ((rB σ).left) * (φB (ρL σ)) ((φB β) ((rB τ).left)) := fun σ τ => by
    rw [hleftB σ τ, map_mul (φB β)]
    congr 1
    rw [← MulAut.mul_apply, ← map_mul,
      show β * (rB σ).right = β * SemidirectProduct.rightHom (rB σ) from rfl, hrelB σ,
      map_mul, MulAut.mul_apply]
  let ē : (M ≃ₐ[ℚ] M) →* ((A × B) ⋊[prodAction φA φB] (L ≃ₐ[ℚ] L)) :=
    { toFun := fun σ => ⟨(φA α ((rA σ).left), φB β ((rB σ).left)), ρL σ⟩
      map_one' := by
        refine SemidirectProduct.ext ?_ ?_
        · refine Prod.ext ?_ ?_
          · show (φA α) ((rA 1).left) = 1
            rw [map_one (rA), SemidirectProduct.one_left, map_one]
          · show (φB β) ((rB 1).left) = 1
            rw [map_one (rB), SemidirectProduct.one_left, map_one]
        · show ρL 1 = 1
          rw [map_one]
      map_mul' := fun σ τ => by
        refine SemidirectProduct.ext ?_ ?_
        · exact Prod.ext (hAc σ τ) (hBc σ τ)
        · exact map_mul ρL σ τ }
  have hēinj : Function.Injective ē := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    have h1 : ρL σ = 1 :=
      congrArg (fun x : (A × B) ⋊[prodAction φA φB] (L ≃ₐ[ℚ] L) => x.right) hσ
    have h2 : (rA σ).left = 1 := by
      refine (φA α).injective ?_
      have h := congrArg (fun x : (A × B) ⋊[prodAction φA φB] (L ≃ₐ[ℚ] L) => x.left.1) hσ
      change (φA α) ((rA σ).left) = 1 at h
      rw [map_one]
      exact h
    have h3 : (rB σ).left = 1 := by
      refine (φB β).injective ?_
      have h := congrArg (fun x : (A × B) ⋊[prodAction φA φB] (L ≃ₐ[ℚ] L) => x.left.2) hσ
      change (φB β) ((rB σ).left) = 1 at h
      rw [map_one]
      exact h
    have h4 : SemidirectProduct.rightHom (rA σ) = 1 := by
      have h := hrelA σ
      rw [h1, one_mul] at h
      have h2 : α * SemidirectProduct.rightHom (rA σ) = α * 1 := by rw [h, mul_one]
      exact mul_left_cancel h2
    have h5 : SemidirectProduct.rightHom (rB σ) = 1 := by
      have h := hrelB σ
      rw [h1, one_mul] at h
      have h2 : β * SemidirectProduct.rightHom (rB σ) = β * 1 := by rw [h, mul_one]
      exact mul_left_cancel h2
    exact hker σ (SemidirectProduct.ext h2 h4) (SemidirectProduct.ext h3 h5)
  have hcard2 : Nat.card ((A × B) ⋊[prodAction φA φB] (L ≃ₐ[ℚ] L))
      = Nat.card A * Nat.card B * Nat.card (L ≃ₐ[ℚ] L) := by
    rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod, Nat.card_prod]
  have hēbij : Function.Bijective ē :=
    hēinj.bijective_of_nat_card_le (by rw [hcard2, hcardP])
  let ēe : (M ≃ₐ[ℚ] M) ≃* ((A × B) ⋊[prodAction φA φB] (L ≃ₐ[ℚ] L)) :=
    MulEquiv.ofBijective ē hēbij
  -- the solution
  letI hAlgM : Algebra ↥L ↥M := (IntermediateField.inclusion hLM).toRingHom.toAlgebra
  haveI hSTMr : IsScalarTower ℚ ↥L ↥M := IsScalarTower.of_algHom (IntermediateField.inclusion hLM)
  haveI hFdLM : FiniteDimensional ↥L ↥M := Module.Finite.of_restrictScalars_finite ℚ ↥L ↥M
  haveI hGalLM : IsGalois ↥L ↥M := IsGalois.tower_top_of_isGalois ℚ ↥L ↥M
  refine ⟨M, hLM, inferInstance, inferInstance, hAlgM, hSTMr, hFdLM, hGalLM, ēe.symm, ?_⟩
  intro g x
  have h2 : ē (ēe.symm g) = g := ēe.apply_symm_apply g
  have h3 : ρL (ēe.symm g) = SemidirectProduct.rightHom g :=
    congrArg (fun x : (A × B) ⋊[prodAction φA φB] (L ≃ₐ[ℚ] L) => x.right) h2
  refine Subtype.ext ?_
  rw [show (ēe.symm g) (algebraMap ↥L ↥M x)
      = (ēe.symm g) ⟨(x : AlgebraicClosure ℚ), hLM x.2⟩ from rfl]
  rw [← hρL_apply (ēe.symm g) x, h3]
  rfl

end Work.GenericKernelReduction
