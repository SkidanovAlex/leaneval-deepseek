import Mathlib
import Submission.Work.SSGRoute.GrunwaldEscapeCore.diagonal_at_level
import Submission.Work.SSGRoute.ZDataMup.LocalUnramified.kummerCharZMod_eq_zero_iff_apply_sqrt
import Submission.Work.SSGRoute.ZConstruction.localKummerDictionary
import Submission.Work.SSGRoute.ZDataTwo.kummerCochar_conjElem
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The diagonal of the local Kummer pairing, in the form consumed by the antisymmetry

This is `kummerIdx_localArtinFactor_eq_zero` (`diagonal_at_level.lean`) transported to the *global*
Kummer character `Work.SSGRoute.kummerCharZMod`: with `τ : Ω ≃ₐ[↥K] Ω` a lift of the local Artin
image `θ^E_𝔭 c = artE (onePlace 𝔭 (localImageAt 𝔭 c))`,

  `kummerCharZMod c τ = 0`.

The passage uses `kummerCharZMod_eq_zero_iff_apply_sqrt` (the Kummer character vanishes exactly when
the automorphism fixes the chosen `p`-th root) and the elementary fact that, the canonical root
`kummerSqrtZMod p c` and `γ` differing by a `p`-th root of unity, `τ` — which fixes `γ` (by the
internal diagonal) and fixes `ζ` (it is `↥K`-linear) — fixes it too.

This is exactly the hypothesis `hdiag` of `kummerCharZMod_antisymm`
(`kummerChar_antisymm.lean`), so the antisymmetry of the local Kummer pairing follows from the
Artin family of `localArtinFamily.lean` and the diagonal above.
-/

open scoped NumberField
open NumberField IsDedekindDomain
open NK.GlobalCFT

namespace Work.SSGRoute.GrunwaldEscapeCore

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  [IsAlgClosed Ω]

/-- **The diagonal of the local Kummer pairing at a big level, in global form.** -/
theorem kummerCharZMod_localArtinFactor_eq_zero
    (p : ℕ) [Fact p.Prime]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (E : IntermediateField ↥K Ω) [FiniteDimensional ↥K E] [IsGalois ↥K E]
    (F : IntermediateField ↥K ↥E) [FiniteDimensional ↥K F] [Normal ↥K F] [NumberField ↥F]
    (artE : Idele ↥K →* (↥E ≃ₐ[↥K] ↥E)) (artF : Idele ↥K →* (↥F ≃ₐ[↥K] ↥F))
    (hcompat : ∀ x : Idele ↥K,
      AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := ↥E) F (artE x) = artF x)
    (hkerF : ∀ y : Idele ↥F, artF (Idele.normIdeleHom ↥K ↥F y) = 1)
    (𝔭 : NK.Chebotarev.PrimeIdeal ↥K)
    (c : (↥K)ˣ) (γ : (↥E)ˣ) (hγ : γ ^ p = Units.map (algebraMap ↥K ↥E) c)
    (hγF : (γ : ↥E) ∈ F)
    (hc : NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) c ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥F)
        (NK.GlobalCFT.Place.ofFinite 𝔭))
    (τ : Ω ≃ₐ[↥K] Ω)
    (hτ : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E τ =
      artE (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) c))) :
    Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c τ = 0 := by
  classical
  -- the internal diagonal: `θ^E_𝔭 c` fixes `γ`
  have hdiag := kummerIdx_localArtinFactor_eq_zero p ζ hζ F artE artF hcompat hkerF 𝔭 c γ hγ hγF hc
  have hfixE : (artE (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
      (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) c)))
      (γ : ↥E) = (γ : ↥E) :=
    (Work.SSGRoute.kummerIdx_eq_zero_iff_apply_eq p hζ c γ hγ _).mp hdiag
  -- hence `τ` fixes `γ`
  have hfixγ : τ ((γ : ↥E) : Ω) = ((γ : ↥E) : Ω) := by
    have h1 : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E τ (γ : ↥E) = (γ : ↥E) := by
      rw [hτ]
      exact hfixE
    have h2 := congrArg (fun x : ↥E => (x : Ω)) h1
    rwa [AlgEquiv.restrictNormalHom_apply] at h2
  -- `τ` is `↥K`-linear, hence fixes `ζ`
  have hfixζ : τ (algebraMap ↥K Ω ζ) = algebraMap ↥K Ω ζ := AlgEquiv.commutes τ ζ
  have hζΩ : IsPrimitiveRoot (algebraMap ↥K Ω ζ) p :=
    hζ.map_of_injective (algebraMap ↥K Ω).injective
  -- the canonical root and `γ` differ by a `p`-th root of unity
  have hγpow : (((γ : ↥E) : Ω)) ^ p = algebraMap ↥K Ω (c : ↥K) := by
    have h := congrArg (fun u : (↥E)ˣ => ((u : ↥E) : Ω)) hγ
    simp only [Units.val_pow_eq_pow_val, Units.coe_map] at h
    rw [IsScalarTower.algebraMap_apply ↥K ↥E Ω]
    exact h
  have hrootpow : (Work.SSGRoute.kummerSqrtZMod (Ω := Ω) p c / ((γ : ↥E) : Ω)) ^ p = 1 := by
    rw [div_pow, Work.SSGRoute.kummerSqrtZMod_pow, hγpow, div_self]
    exact (map_ne_zero (algebraMap ↥K Ω)).mpr c.ne_zero
  obtain ⟨j, -, hj⟩ := IsPrimitiveRoot.eq_pow_of_pow_eq_one hζΩ hrootpow
  have hγΩ0 : ((γ : ↥E) : Ω) ≠ 0 := by
    intro h
    refine Units.ne_zero γ (Subtype.coe_injective ?_)
    show ((γ : ↥E) : Ω) = ((0 : ↥E) : Ω)
    simpa using h
  have hroot : Work.SSGRoute.kummerSqrtZMod (Ω := Ω) p c =
      ((γ : ↥E) : Ω) * (algebraMap ↥K Ω ζ) ^ j := by
    have h0 : Work.SSGRoute.kummerSqrtZMod (Ω := Ω) p c =
        (Work.SSGRoute.kummerSqrtZMod (Ω := Ω) p c / ((γ : ↥E) : Ω)) * ((γ : ↥E) : Ω) :=
      (div_mul_cancel₀ _ hγΩ0).symm
    rw [h0, hj, mul_comm]
  rw [Work.SSGRoute.ZDataMup.LocalUnramified.kummerCharZMod_eq_zero_iff_apply_sqrt p hζ c τ,
    hroot, map_mul, map_pow, hfixζ, hfixγ]

end Work.SSGRoute.GrunwaldEscapeCore
