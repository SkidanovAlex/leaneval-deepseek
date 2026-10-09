import Mathlib
import Submission.Work.SSGRoute.myv2.DiagCorr
import Submission.Work.SSGRoute.ZConstruction.kummerCharZModAdd
import Submission.Work.SSGRoute.ZConstruction.exists_abelianArtin_localFactors
import Submission.Work.SSGRoute.ZDataMup.ArtinUniqueness.artinMap_restrictNormalHom_eq_abelian
import Submission.Work.SSGRoute.myv2.sup_isMulCommutative
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The diagonal of the local Kummer pairing at a level `E`, with the correction

`Work.SSGRoute.N2v2.kummerCharZMod_pairing_antisymm` (corrected antisymmetry) needs, for a fixed
place `𝔭` and a level `E` (finite abelian over `↥K`), a single element `σ₀` with

  `χ_c τ = χ_c σ₀`  for every `c` with `KummerField c ≤ E` and every lift `τ` of the local factor
  `θ_𝔭(c)`.

For odd `p` one can take `σ₀ = 1` (`kummerCharZMod_localArtinFactor_eq_zero`); for `p = 2` the
correction is `σ₀` = a lift of `θ_𝔭(ζ)⁻¹ = θ_𝔭(-1)⁻¹`, because the norm of the Kummer root is `-c`.
Here `σ₀` is always taken to be a lift of `θ_𝔭(ζ ^ (p (p-1)/2))⁻¹`, uniformly in `p`, and the
statement is reduced to the *twisted diagonal* `kummerCharZMod_eq_zero_of_localNorm_correction`
applied at the small field `F = ↥K⟮c^{1/p}⟯ ⊆ E`.

The `hdata` hypothesis is exactly what `kummerSubfield_data_correction` supplies (the small field,
the `p`-th root, and the corrected local-norm membership).
-/

open scoped NumberField
open NumberField IsDedekindDomain
open NK.GlobalCFT

namespace Work.SSGRoute.N2v2

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  [IsAlgClosed Ω]

/-- `onePlace` is multiplicative. -/
theorem onePlace_mul_local {K : Type} [Field K] [NumberField K] (w : Place K)
    (u v : (Place.localField K w)ˣ) :
    NK.HassePrinciple.onePlace w (u * v) =
      NK.HassePrinciple.onePlace w u * NK.HassePrinciple.onePlace w v := by
  rw [← NK.CFTLib.IdeleHasse.onePlaceHom_apply (K := K) w (u * v),
    ← NK.CFTLib.IdeleHasse.onePlaceHom_apply (K := K) w u,
    ← NK.CFTLib.IdeleHasse.onePlaceHom_apply (K := K) w v, map_mul]

/-- `localImageAt` is multiplicative. -/
theorem localImageAt_mul_local {K : Type} [Field K] [NumberField K] (v : Place K) (u v' : Kˣ) :
    NK.CFTLib.IdeleHasse.localImageAt v (u * v') =
      NK.CFTLib.IdeleHasse.localImageAt v u * NK.CFTLib.IdeleHasse.localImageAt v v' := by
  simp only [NK.CFTLib.IdeleHasse.localImageAt, map_mul]

/-- **The diagonal of the local Kummer pairing at a level `E`, with the correction.** -/
theorem hdiag_E
    (p : ℕ) [Fact p.Prime]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (E : IntermediateField ↥K Ω) [FiniteDimensional ↥K E] [IsGalois ↥K E]
    [IsMulCommutative (↥E ≃ₐ[↥K] ↥E)]
    (artE : Idele ↥K →* (↥E ≃ₐ[↥K] ↥E))
    (𝔭 : NK.Chebotarev.PrimeIdeal ↥K)
    (hdata : ∀ c : (↥K)ˣ, NK.LocalAnabelian.kummerField (K' := Ω) p c ≤ E →
      ∃ (F : IntermediateField ↥K ↥E) (_ : FiniteDimensional ↥K F) (_ : Normal ↥K F)
        (_ : NumberField ↥F)
        (artF : Idele ↥K →* (↥F ≃ₐ[↥K] ↥F)) (γ : (↥E)ˣ),
        (∀ x : Idele ↥K,
          AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := ↥E) F (artE x) = artF x) ∧
        (∀ y : Idele ↥F, artF (Idele.normIdeleHom ↥K ↥F y) = 1) ∧
        γ ^ p = Units.map (algebraMap ↥K ↥E) c ∧ (γ : ↥E) ∈ F ∧
        NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭)
          (Units.mk0 (ζ ^ (p * (p - 1) / 2))
            (pow_ne_zero _ (hζ.ne_zero (Fact.out : p.Prime).ne_zero)) * c) ∈
          NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥F)
            (NK.GlobalCFT.Place.ofFinite 𝔭)) :
    ∃ σ₀ : Ω ≃ₐ[↥K] Ω,
      ∀ c : (↥K)ˣ, NK.LocalAnabelian.kummerField (K' := Ω) p c ≤ E →
      ∀ τ : Ω ≃ₐ[↥K] Ω,
        AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E τ =
          artE (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
            (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) c)) →
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c τ =
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c σ₀ := by
  classical
  haveI hAlgClK : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  haveI hsep : IsSepClosure ↥K Ω := IsSepClosure.of_isAlgClosure_of_perfectField ↥K Ω
  -- the correction element of `↥Kˣ`
  have hcorr0 : ζ ^ (p * (p - 1) / 2) ≠ 0 :=
    pow_ne_zero _ (hζ.ne_zero (Fact.out : p.Prime).ne_zero)
  -- `σ₀` : a lift of the inverse of the local factor of the correction element
  obtain ⟨σ₀, hσ₀⟩ := AlgEquiv.restrictNormalHom_surjective (F := ↥K) (K₁ := E) (E := Ω)
    (artE (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
      (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭)
        (Units.mk0 (ζ ^ (p * (p - 1) / 2)) hcorr0))))⁻¹
  refine ⟨σ₀, fun c hcE τ hτ => ?_⟩
  obtain ⟨F, hFfd, hFn, hFnf, artF, γ, hcompat, hkerF, hγ, hγF, hcloc⟩ := hdata c hcE
  -- `τ * σ₀⁻¹` is a lift of the local factor of the corrected element
  have hτσ : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E (τ * σ₀⁻¹) =
      artE (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭)
          (Units.mk0 (ζ ^ (p * (p - 1) / 2)) hcorr0 * c))) := by
    rw [map_mul, map_inv, hτ, hσ₀, inv_inv]
    rw [show NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
          (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭)
            (Units.mk0 (ζ ^ (p * (p - 1) / 2)) hcorr0 * c)) =
        (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
            (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) c)) *
          (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
            (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭)
              (Units.mk0 (ζ ^ (p * (p - 1) / 2)) hcorr0))) from by
      rw [mul_comm (Units.mk0 (ζ ^ (p * (p - 1) / 2)) hcorr0) c, localImageAt_mul_local,
        onePlace_mul_local]]
    rw [map_mul]
  have h0 : Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c (τ * σ₀⁻¹) = 0 :=
    kummerCharZMod_eq_zero_of_localNorm_correction p K ζ hζ E F artE artF hcompat hkerF 𝔭 c γ
      hγ hγF hcloc (τ * σ₀⁻¹) hτσ
  have h1 : Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c (τ * σ₀⁻¹) +
      Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c σ₀ =
      Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c τ := by
    rw [← Work.SSGRoute.ZConstruction.kummerCharZMod_apply_mul (ζ := ζ) (hζ := hζ) c (τ * σ₀⁻¹) σ₀]
    congr 1
    group
  rw [← h1, h0, zero_add]

end Work.SSGRoute.N2v2
