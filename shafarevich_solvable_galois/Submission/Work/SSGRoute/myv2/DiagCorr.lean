import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.Kummer.exists_algEquiv_apply_eq_mul_of_pow_eq
import Submission.Work.Kummer.norm_eq_primRoot_pow_mul_of_kummer_generator
import Submission.Work.SSGRoute.GrunwaldEscapeCore.mem_localNormSubgroup_algebra_norm
import Submission.Work.SSGRoute.ZDataMup.LocalUnramified.kummerCharZMod_eq_zero_iff_apply_sqrt
import Submission.Work.SSGRoute.ZDataMup.ideleArtin_ideleOfPrime_of_unramified
import Submission.Work.SSGRoute.ZDataMup.ideleArtin_restrictNormalHom
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The twisted diagonal of the local Kummer pairing (all primes `p`)

This is `Work.SSGRoute.GrunwaldEscapeCore.kummerCharZMod_localArtinFactor_eq_zero` with the local
norm hypothesis imposed on `ζ ^ (p (p-1)/2) * c` rather than on `c`.  For odd `p` the correction is
`1` and the two statements coincide; for `p = 2` the correction is `-1`, which is exactly what the
norm of the Kummer root is (`Work.SSGRoute.N2v2.mem_localNormSubgroup_of_kummerRoot_correction`).

The conclusion keeps the *unchanged* Kummer character `χ_c` (evaluated at a lift of the local Artin
image of the corrected element), which is what the corrected antisymmetry
(`Work.SSGRoute.N2v2.kummerCharZMod_pairing_antisymm`) consumes.
-/

open scoped NumberField
open NumberField IsDedekindDomain
open NK.GlobalCFT

namespace Work.SSGRoute.N2v2

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  [IsAlgClosed Ω]

/-- **The twisted diagonal of the local Kummer pairing.**  With compatible Artin maps `artE`, `artF`
of `F ≤ E` (`artF` kills the idèlic norms), `c ∈ ↥Kˣ`, `γ` a `p`-th root of `c` lying in `F`, and
`ζ ^ (p (p-1)/2) * c` a local norm at `𝔭` for `F/↥K`: the Kummer character of `c` vanishes on any
lift `τ` of `artE (onePlace 𝔭 (localImageAt 𝔭 (ζ ^ (p (p-1)/2) * c)))`. -/
theorem kummerCharZMod_eq_zero_of_localNorm_correction
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
    (hc : NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭)
        (Units.mk0 (ζ ^ (p * (p - 1) / 2))
          (pow_ne_zero _ (hζ.ne_zero (Fact.out : p.Prime).ne_zero)) * c) ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥F)
        (NK.GlobalCFT.Place.ofFinite 𝔭))
    (τ : Ω ≃ₐ[↥K] Ω)
    (hτ : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E τ =
      artE (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭)
          (Units.mk0 (ζ ^ (p * (p - 1) / 2))
            (pow_ne_zero _ (hζ.ne_zero (Fact.out : p.Prime).ne_zero)) * c)))) :
    Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c τ = 0 := by
  classical
  -- the Artin factor of the corrected element fixes `F`
  have hone : NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
      (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭)
        (Units.mk0 (ζ ^ (p * (p - 1) / 2))
          (pow_ne_zero _ (hζ.ne_zero (Fact.out : p.Prime).ne_zero)) * c)) ∈
      Idele.normImage ↥K ↥F :=
    (NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff (K := ↥K) (L := ↥F)
      (NK.GlobalCFT.Place.ofFinite 𝔭) _).mpr hc
  obtain ⟨y, hy⟩ := Idele.mem_normImage.mp hone
  have hy' : NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
      (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭)
        (Units.mk0 (ζ ^ (p * (p - 1) / 2))
          (pow_ne_zero _ (hζ.ne_zero (Fact.out : p.Prime).ne_zero)) * c)) =
      Idele.normIdeleHom ↥K ↥F y :=
    Idele.ext (fun v => by rw [Idele.normIdeleHom_apply]; exact hy v)
  have hres : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := ↥E) F
      (artE (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭)
          (Units.mk0 (ζ ^ (p * (p - 1) / 2))
            (pow_ne_zero _ (hζ.ne_zero (Fact.out : p.Prime).ne_zero)) * c)))) = 1 := by
    rw [hcompat, hy', hkerF y]
  -- hence `τ` fixes the root `γ`
  have hfixγ : τ ((γ : ↥E) : Ω) = ((γ : ↥E) : Ω) := by
    have h1 : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := ↥E) F
        (artE (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
          (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭)
            (Units.mk0 (ζ ^ (p * (p - 1) / 2))
              (pow_ne_zero _ (hζ.ne_zero (Fact.out : p.Prime).ne_zero)) * c))))
        ⟨(γ : ↥E), hγF⟩ = ⟨(γ : ↥E), hγF⟩ := by
      rw [hres]
      rfl
    have h2 : (artE (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
          (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭)
            (Units.mk0 (ζ ^ (p * (p - 1) / 2))
              (pow_ne_zero _ (hζ.ne_zero (Fact.out : p.Prime).ne_zero)) * c)))) (γ : ↥E) =
        (γ : ↥E) := by
      have h2' := congrArg (fun (x : ↥F) => (x : ↥E)) h1
      rwa [AlgEquiv.restrictNormalHom_apply] at h2'
    have h4 : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E τ (γ : ↥E) = (γ : ↥E) := by
      rw [hτ]
      exact h2
    have h5 := congrArg (fun (x : ↥E) => (x : Ω)) h4
    rwa [AlgEquiv.restrictNormalHom_apply] at h5
  -- `τ` is `↥K`-linear, hence fixes `ζ`
  have hfixζ : τ (algebraMap ↥K Ω ζ) = algebraMap ↥K Ω ζ := AlgEquiv.commutes τ ζ
  have hζΩ : IsPrimitiveRoot (algebraMap ↥K Ω ζ) p :=
    hζ.map_of_injective (algebraMap ↥K Ω).injective
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

end Work.SSGRoute.N2v2
