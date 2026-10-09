import Mathlib
import Submission.NK.CFTLib.HR.localNormSubgroup_ofInfinite_eq_top
import Submission.NK.CFTLib.IdeleHasse.onePlace_localNorm
import Submission.Work.SSGRoute.step4_y_escape_v2.RayClass
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The archimedean local factor of a norm-killing homomorphism, when `K` has no real place

Let `M / K` be a finite Galois extension of number fields, `K` an intermediate field of an
algebraic closure `Ω` of `k`, and assume that **every** infinite place `w` of `K` is complex
(`hnoReal`).  For a group homomorphism `Φ : 𝕀_K →* Gal(M/K)` which kills all norm idèles
`N_{M/K}(𝕀_M)`, the archimedean local factor at `w` is trivial:

`Φ (onePlace w (localImageAt w γ)) = 1` for every `γ ∈ Kˣ`.

The mathematics is short.  A complex infinite place of `K` remains complex in any finite
extension, so every place `W` of `M` above `w` is complex, the local field at `W` is `ℂ` and the
archimedean local norm `ℂˣ → ℂˣ` is surjective.  Hence the local norm subgroup of `K_wˣ` is all of
`K_wˣ` (Mathlib's `NumberField.InfinitePlace.LiesOver.isComplex_of_isComplex_under` together with
`NK.NUV2.ArtinBridge.localNormInfinite_range_eq_top_of_complex_complex`, packaged as
`NK.CFTLib.HR.localNormSubgroup_ofInfinite_eq_top_of_isTotallyComplex`).  The one-place dictionary
`NK.CFTLib.IdeleHasse.onePlace_ofInfinite_mem_normImage_iff` then says exactly that the one-place
idèle `onePlace w a` is a norm idèle, and `Φ` kills it.
-/

namespace Work.SSGRoute

/-- **The archimedean local factor of a norm-killing homomorphism is trivial when `K` has no real
place.** -/
theorem hLocalFactor_infinite_noReal {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (hnoReal : ∀ w : NumberField.InfinitePlace ↥K, w.IsComplex)
    (M : IntermediateField ↥K Ω) [FiniteDimensional ↥K M] [IsGalois ↥K M]
    (Φ : NK.GlobalCFT.Idele ↥K →* (↥M ≃ₐ[↥K] ↥M))
    (hΦ : ∀ x ∈ NK.GlobalCFT.Idele.normImage ↥K ↥M, Φ x = 1)
    (w : NumberField.InfinitePlace ↥K) (γ : (↥K)ˣ) :
    Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofInfinite w)
      (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofInfinite w) γ)) = 1 := by
  -- `K` is totally complex, hence at every infinite place its local norm subgroup is everything.
  have htop : NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥M)
        (NK.GlobalCFT.Place.ofInfinite w) = ⊤ :=
    NK.CFTLib.HR.localNormSubgroup_ofInfinite_eq_top_of_isTotallyComplex
      (M := ↥K) (E := ↥M) (⟨hnoReal⟩ : NumberField.IsTotallyComplex ↥K) w
  have hmem : NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofInfinite w) γ
      ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥M)
          (NK.GlobalCFT.Place.ofInfinite w) := by
    rw [htop]
    exact Subgroup.mem_top _
  -- The one-place dictionary turns this into membership of the norm idèles, killed by `Φ`.
  exact hΦ _ ((NK.CFTLib.IdeleHasse.onePlace_ofInfinite_mem_normImage_iff
      (K := ↥K) (L := ↥M) w _).mpr hmem)

end Work.SSGRoute
