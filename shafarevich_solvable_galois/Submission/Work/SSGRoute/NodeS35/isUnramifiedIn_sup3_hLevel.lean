import Mathlib
import Submission.Work.SSGRoute.H9.swIsUnramifiedIn_hLevel_of_kills_inertia
import Submission.Work.SSGRoute.NodeS35.isUnramifiedIn_sup_hLevel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.NodeS35

theorem isUnramifiedIn_sup3_hLevel {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] [NumberField ↥K] [IsSepClosure ↥K Ω]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (b₁ b₂ b₃ : (↥K)ˣ)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hkill₁ : ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b₁ σ = 0)
    (hkill₂ : ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b₂ σ = 0)
    (hkill₃ : ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b₃ σ = 0)
    [FiniteDimensional ↥K ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) b₁
      ⊔ Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) b₂
      ⊔ Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) b₃)]
    [IsGalois ↥K ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) b₁
      ⊔ Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) b₂
      ⊔ Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) b₃)]
    [NumberField ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) b₁
      ⊔ Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) b₂
      ⊔ Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) b₃)] :
    NK.HeckeL.IsUnramifiedIn (K := ↥K)
      (L := ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) b₁
        ⊔ Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) b₂
        ⊔ Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) b₃))
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA) := by
  classical
  -- The compositum of the three Kummer levels is unramified at the prime below `A`: it suffices
  -- to show that the inertia of any place over that prime fixes each of the three factors.
  refine Work.SSGRoute.ZDataMup.isUnramifiedIn_of_inertia_subset_fixingSubgroup (K := ↥K) (Ω := Ω)
    (Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) b₁ ⊔
      Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) b₂ ⊔
      Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := p) b₃)
    (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA) ?_
  intro B hB hBc σ hσ
  rw [IntermediateField.fixingSubgroup_sup, IntermediateField.fixingSubgroup_sup]
  exact ⟨⟨inertia_subset_fixingSubgroup_hLevel (K := K) (p := p) (k := k) (Ω := Ω)
        ζ hζ hζK b₁ A hA hkill₁ B hB hBc σ hσ,
      inertia_subset_fixingSubgroup_hLevel (K := K) (p := p) (k := k) (Ω := Ω)
        ζ hζ hζK b₂ A hA hkill₂ B hB hBc σ hσ⟩,
    inertia_subset_fixingSubgroup_hLevel (K := K) (p := p) (k := k) (Ω := Ω)
        ζ hζ hζK b₃ A hA hkill₃ B hB hBc σ hσ⟩

end Work.SSGRoute.NodeS35
