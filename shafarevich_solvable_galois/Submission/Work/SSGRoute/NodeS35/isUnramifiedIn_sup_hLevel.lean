import Mathlib
import Submission.Work.SSGRoute.H9.swIsUnramifiedIn_hLevel_of_kills_inertia
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.NodeS35

/-- **Inertia of a place over `oddPrime A` fixes the Kummer level of `b`** (single-unit form).

If the Kummer cochain of `b` vanishes on the inertia subgroup of `A` over `k`, then every inertia
element of any place `B` of `Ω` lying over the prime `oddPrime A` of `↥K` fixes the level
`K(b^{1/p})`.  This is exactly the hypothesis of
`Work.SSGRoute.ZDataMup.isUnramifiedIn_of_inertia_subset_fixingSubgroup` for a single level. -/
theorem inertia_subset_fixingSubgroup_hLevel {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (b : (↥K)ˣ)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hkill : ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ = 0) :
    ∀ (B : ValuationSubring Ω), SSGRoute.IsFinPlace ↥K B →
      B.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K
          (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA) →
      ∀ σ : Ω ≃ₐ[↥K] Ω, SSGRoute.IsInertia ↥K B σ →
        σ ∈ (Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p)
          b).fixingSubgroup := by
  classical
  -- The Kummer level of `b` is a finite Galois extension of `↥K` (its Galois group has order
  -- dividing `p`); this is what makes its fixing subgroup normal inside `Gal(Ω/↥K)`.
  haveI hfd : FiniteDimensional ↥K
      ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) b) :=
    Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_finiteDimensional (K := K) (Ω := Ω) (p := p)
      (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) b
  haveI hgal : IsGalois ↥K
      ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) b) :=
    Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_isGalois (K := K) (Ω := Ω) (p := p)
      (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) b
  intro B _hB hBc σ hσ
  -- Inertia at the base place `A` itself fixes the Kummer level of `b`.
  have hfixA : ∀ τ : Ω ≃ₐ[↥K] Ω, SSGRoute.IsInertia ↥K A τ →
      τ ∈ (Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p)
        b).fixingSubgroup := by
    intro τ hτ
    have hτK : τ.restrictScalars k ∈ K.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact τ.commutes ⟨x, hx⟩
    have hI : SSGRoute.IsInertia k A (τ.restrictScalars k) :=
      (Work.SSGRoute.ZDataMup.LocalUnramified.isInertia_restrictScalars_iff K A τ).mpr hτ
    have h0 := hkill (τ.restrictScalars k) hτK hI
    rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK)
      (hζ := hζ) (β := b) hτK] at h0
    have heq : (IntermediateField.fixingSubgroupEquiv K) ⟨τ.restrictScalars k, hτK⟩ = τ := by
      ext x
      rfl
    rw [heq] at h0
    exact (Work.SSGRoute.ZDataMup.OddForm.odd_kummerCharZMod_eq_zero_iff_mem_fixingSubgroup
      (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K)
      (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) b τ).mp h0
  -- Every place `B` over the prime `oddPrime A` is conjugate to `A`; transport inertia through
  -- the conjugation, using normality of the fixing subgroup.
  obtain ⟨g, hg⟩ := Commons.RingTheory.Valuation.exists_smul_eq_of_comap_eq (F := ↥K) (E := Ω) A B
    ((Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K) (A := A) hA).trans hBc.symm)
  have hI : SSGRoute.IsInertia ↥K A (g⁻¹ * σ * g) := by
    have hconj := Work.SSGRoute.isInertia_conj (k := ↥K) (Ω := Ω) A g (g⁻¹ * σ * g)
    rw [hg, show g * (g⁻¹ * σ * g) * g⁻¹ = σ from by group] at hconj
    exact hconj.mp hσ
  have hmem : g⁻¹ * σ * g ∈
      (Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p)
        b).fixingSubgroup :=
    hfixA _ hI
  have hconj : g * (g⁻¹ * σ * g) * g⁻¹ ∈
      (Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p)
        b).fixingSubgroup :=
    ((inferInstance :
        ((Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p)
          b).fixingSubgroup).Normal)).conj_mem
      (g⁻¹ * σ * g) hmem g
  rwa [show g * (g⁻¹ * σ * g) * g⁻¹ = σ from by group] at hconj

theorem isUnramifiedIn_sup_hLevel {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] [NumberField ↥K] [IsSepClosure ↥K Ω]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (b₁ b₂ : (↥K)ˣ)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hkill₁ : ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b₁ σ = 0)
    (hkill₂ : ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b₂ σ = 0)
    [FiniteDimensional ↥K ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) b₁
      ⊔ Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) b₂)]
    [IsGalois ↥K ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) b₁
      ⊔ Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) b₂)]
    [NumberField ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) b₁
      ⊔ Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) b₂)] :
    NK.HeckeL.IsUnramifiedIn (K := ↥K)
      (L := ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) b₁
        ⊔ Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) b₂))
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA) := by
  classical
  -- Both Kummer levels are unramified at the prime below `A`; their compositum is then unramified
  -- as well, since the inertia of a place over the prime fixes the compositum exactly when it
  -- fixes both factors.
  refine Work.SSGRoute.ZDataMup.isUnramifiedIn_of_inertia_subset_fixingSubgroup (K := ↥K) (Ω := Ω)
    (Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) b₁ ⊔
      Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) b₂)
    (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA) ?_
  intro B hB hBc σ hσ
  rw [IntermediateField.fixingSubgroup_sup]
  exact ⟨inertia_subset_fixingSubgroup_hLevel (K := K) (p := p) (k := k) (Ω := Ω)
      ζ hζ hζK b₁ A hA hkill₁ B hB hBc σ hσ,
    inertia_subset_fixingSubgroup_hLevel (K := K) (p := p) (k := k) (Ω := Ω)
      ζ hζ hζK b₂ A hA hkill₂ B hB hBc σ hσ⟩

end Work.SSGRoute.NodeS35
