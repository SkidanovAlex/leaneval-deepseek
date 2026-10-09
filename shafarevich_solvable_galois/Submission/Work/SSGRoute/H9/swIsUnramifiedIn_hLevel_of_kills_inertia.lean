import Mathlib
import Submission.Work.SSGRoute.H9.swPairingValueFrob
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.H9

theorem swIsUnramifiedIn_hLevel_of_kills_inertia {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (b : (↥K)ˣ)
    [FiniteDimensional ↥K ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) b)]
    [IsGalois ↥K ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) b)]
    [NumberField ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) b)]
    (A : ValuationSubring Ω) (hA : _root_.SSGRoute.IsFinPlace k A)
    (hkill : ∀ σ ∈ K.fixingSubgroup, _root_.SSGRoute.IsInertia k A σ →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ = 0) :
    NK.HeckeL.IsUnramifiedIn (K := ↥K)
      (L := ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) b))
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA) := by
  classical
  -- The Kummer level of `b` at `A`.
  have hfixA : ∀ σ : Ω ≃ₐ[↥K] Ω, _root_.SSGRoute.IsInertia ↥K A σ →
      σ ∈ (Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) b).fixingSubgroup := by
    intro σ hσ
    -- `σ` restricts to an element of `G_k` fixing `K`, inertia at `A` over `k`
    have hσK : σ.restrictScalars k ∈ K.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact σ.commutes ⟨x, hx⟩
    have hI : _root_.SSGRoute.IsInertia k A (σ.restrictScalars k) :=
      (Work.SSGRoute.ZDataMup.LocalUnramified.isInertia_restrictScalars_iff K A σ).mpr hσ
    -- the hypothesis kills the Kummer cochain there
    have h0 := hkill (σ.restrictScalars k) hσK hI
    rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK)
      (hζ := hζ) (β := b) hσK] at h0
    have heq : (IntermediateField.fixingSubgroupEquiv K) ⟨σ.restrictScalars k, hσK⟩ = σ := by
      ext x
      rfl
    rw [heq] at h0
    -- faithfulness of the Kummer character on its Kummer level
    exact (Work.SSGRoute.ZDataMup.OddForm.odd_kummerCharZMod_eq_zero_iff_mem_fixingSubgroup
      (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K)
      (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) b σ).mp h0
  -- Every inertia element of `A` fixes `hLevel b`, hence the prime below `A` is unramified:
  -- first extend the statement to every place over the prime `oddPrime A hA` (two places over
  -- one prime are conjugate, and the fixing subgroup of a Galois level is normal).
  refine Work.SSGRoute.ZDataMup.isUnramifiedIn_of_inertia_subset_fixingSubgroup (K := ↥K) (Ω := Ω)
    (Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) b)
    (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA) ?_
  intro B _hB hBc σ hσ
  obtain ⟨g, hg⟩ := Commons.RingTheory.Valuation.exists_smul_eq_of_comap_eq (F := ↥K) (E := Ω) A B
    ((Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K) (A := A) hA).trans hBc.symm)
  have hI : _root_.SSGRoute.IsInertia ↥K A (g⁻¹ * σ * g) := by
    have hconj := Work.SSGRoute.isInertia_conj (k := ↥K) (Ω := Ω) A g (g⁻¹ * σ * g)
    rw [hg, show g * (g⁻¹ * σ * g) * g⁻¹ = σ from by group] at hconj
    exact hconj.mp hσ
  have hmem : g⁻¹ * σ * g ∈
      (Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) b).fixingSubgroup :=
    hfixA _ hI
  have hconj : g * (g⁻¹ * σ * g) * g⁻¹ ∈
      (Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) b).fixingSubgroup :=
    ((inferInstance :
        ((Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) b).fixingSubgroup).Normal)).conj_mem
      (g⁻¹ * σ * g) hmem g
  rwa [show g * (g⁻¹ * σ * g) * g⁻¹ = σ from by group] at hconj

end Work.SSGRoute.H9
