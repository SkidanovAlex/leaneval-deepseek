import Mathlib
import Submission.NK.HassePrinciple.ideleInclusion_smul_of_restrict
import Submission.NK.GlobalCFT.Inclusion.globalCFT_invariants_ideleClassGroup
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_exists
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_injective

namespace NK.CFTLib

theorem inclusion_smul_of_tower {K M L : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Field L] [NumberField L] [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L] [FiniteDimensional K M] [FiniteDimensional M L] [FiniteDimensional K L] [IsGalois K M] [IsGalois M L] : ∃ ψ : NK.GlobalCFT.IdeleClassGroup M →* NK.GlobalCFT.IdeleClassGroup L, Function.Injective ψ ∧ (∀ q : NK.GlobalCFT.IdeleClassGroup L, (∀ σ : Gal(L/M), σ • q = q) ↔ q ∈ ψ.range) ∧ (∀ (σ : Gal(L/K)) (q : NK.GlobalCFT.IdeleClassGroup M), ψ (AlgEquiv.restrictNormalHom M σ • q) = σ • ψ q) := by
  classical
  have hN : Normal K M := IsGalois.to_normal
  have hchoice : ∀ w : NK.GlobalCFT.Place L, ∃ v : NK.GlobalCFT.Place M,
      NK.GlobalCFT.Place.LiesOver w v :=
    fun w => NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := M) (L := L) w
  choose u hu using hchoice
  obtain ⟨φ, hφ⟩ :=
    NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_exists (K := M) (L := L) u hu
  obtain ⟨ψ, hψ⟩ :=
    NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_exists (K := M) (L := L)
      u hu φ hφ
  refine ⟨ψ, ?_, ?_, ?_⟩
  · exact NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_injective u hu φ hφ ψ hψ
  · intro q
    exact NK.GlobalCFT.Inclusion.globalCFT_invariants_ideleClassGroup u hu φ hφ ψ hψ q
  · intro σ q
    obtain ⟨x, rfl⟩ := NK.GlobalCFT.IdeleClassGroup.mk_surjective M q
    rw [NK.GlobalCFT.IdeleClassGroup.smul_mk, hψ ((AlgEquiv.restrictNormalHom M σ) • x),
      hψ x, NK.GlobalCFT.IdeleClassGroup.smul_mk,
      NK.HassePrinciple.ideleInclusion_smul_of_restrict u hu φ hφ σ x]

end NK.CFTLib
