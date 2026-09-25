import Mathlib
import Submission.NK.NUV2.Wall
import Submission.NK.NUV2.RouteB.exists_hausPiGen

namespace NK.NUV2.Transfer

attribute [local instance] NK.Reconstruct.NumFieldIn.finite NK.Reconstruct.NumFieldIn.numberField

theorem levelInfinity_mono {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (K M : NK.Reconstruct.NumFieldIn ℚ Ω) [IsSepClosure ↥K.L Ω] [IsSepClosure ↥M.L Ω]
    (h : K.L ≤ M.L) (ℓ : ℕ) [Fact ℓ.Prime] :
    NK.Reconstruct.levelInfinityOf K ℓ ≤ NK.Reconstruct.levelInfinityOf M ℓ := by
  intro x hx
  change x ∈ NK.Reconstruct.levelInfinity (K := K.L) ℓ at hx
  change x ∈ NK.Reconstruct.levelInfinity (K := M.L) ℓ
  rw [NK.Reconstruct.mem_levelInfinity_iff] at hx
  rw [NK.Reconstruct.mem_levelInfinity_iff]
  intro g hg
  obtain ⟨Φ, hΦ⟩ := NK.NUV2.RouteB.exists_hausPiGen Ω K M h ℓ
  have hzero : NK.Reconstruct.hausMk (K := ↥M.L) (K' := Ω) (ℓ := ℓ)
      (Additive.ofMul (NK.Reconstruct.galToGamma (K := ↥M.L) (K' := Ω) ℓ g)) = 0 := by
    rw [NK.Reconstruct.hausMk_eq_zero_iff,
      NK.Reconstruct.mem_invisibleSubmodule_iff_gammaHausMk]
    exact hg
  have hΦg : Φ (NK.Reconstruct.hausMk (K := ↥M.L) (K' := Ω) (ℓ := ℓ)
        (Additive.ofMul (NK.Reconstruct.galToGamma (K := ↥M.L) (K' := Ω) ℓ g)))
      = NK.Reconstruct.hausMk (K := ↥K.L) (K' := Ω) (ℓ := ℓ)
          (Additive.ofMul (NK.Reconstruct.generalBaseChange K M h ℓ
            (NK.Reconstruct.galToGamma (K := ↥M.L) (K' := Ω) ℓ g))) := by
    simpa using hΦ (Additive.ofMul (NK.Reconstruct.galToGamma (K := ↥M.L) (K' := Ω) ℓ g))
  have hzeroK : NK.Reconstruct.hausMk (K := ↥K.L) (K' := Ω) (ℓ := ℓ)
      (Additive.ofMul (NK.Reconstruct.galToGamma (K := ↥K.L) (K' := Ω) ℓ
        (NK.Reconstruct.galRestrict h g))) = 0 := by
    rw [← NK.Reconstruct.generalBaseChange_galToGamma K M h ℓ g, ← hΦg, hzero, map_zero]
  have hgK : NK.Reconstruct.gammaHausMk (K := ↥K.L) (K' := Ω) (ℓ := ℓ)
      (NK.Reconstruct.galToGamma (K := ↥K.L) (K' := Ω) ℓ
        (NK.Reconstruct.galRestrict h g)) = 1 := by
    have hmem : Additive.ofMul (NK.Reconstruct.galToGamma (K := ↥K.L) (K' := Ω) ℓ
        (NK.Reconstruct.galRestrict h g))
        ∈ NK.Reconstruct.invisibleSubmodule (K := ↥K.L) (K' := Ω) (ℓ := ℓ) := by
      rw [← NK.Reconstruct.hausMk_eq_zero_iff]
      exact hzeroK
    have h' := (NK.Reconstruct.mem_invisibleSubmodule_iff_gammaHausMk
      (K := ↥K.L) (K' := Ω) (ℓ := ℓ) (Additive.ofMul (NK.Reconstruct.galToGamma
        (K := ↥K.L) (K' := Ω) ℓ (NK.Reconstruct.galRestrict h g)))).mp hmem
    simpa using h'
  have hfix := hx (NK.Reconstruct.galRestrict h g) hgK
  rwa [NK.Reconstruct.galRestrict_apply] at hfix

end NK.NUV2.Transfer
