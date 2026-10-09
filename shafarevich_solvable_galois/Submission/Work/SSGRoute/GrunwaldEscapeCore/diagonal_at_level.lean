import Mathlib
import Submission.NK.CFTLib.IdeleHasse.onePlace_localNorm
import Submission.Work.SSGRoute.grunwald_kummer_idx
import Submission.Work.SSGRoute.GrunwaldEscapeCore.localArtinFamily
import Submission.Work.SSGRoute.GrunwaldEscapeCore.norm_kummerRoot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The diagonal of the local Kummer pairing, at a big level

`NOTE_orthogonality_route.md` §6.3/§7.  With `artE`, `artF` the compatible Artin maps of
`localArtinFamily.lean` for the pair `F ≤ E` (`F = κ(γ)`, `γ ^ p = c`), the **diagonal**

  `kummerIdx c γ hγ (θ^E_𝔭 c) = 0`,      `θ^E_𝔭 x := artE (onePlace 𝔭 (localImageAt 𝔭 x))`,

follows from the *small-level* input `c ∈ localNormSubgroup (ofFinite 𝔭)` (which
`mem_localNormSubgroup_of_kummerRoot` supplies: `c` is the norm of its own `p`-th root) as follows:

* `onePlace 𝔭 (localImageAt 𝔭 c) ∈ N_{F/κ} 𝕀_F` by the one-place dictionary
  (`onePlace_mem_normImage_iff`);
* hence `artF` kills it (the kernel clause of the Artin map), so by compatibility `θ^E_𝔭 c` fixes `F`;
* `γ ∈ F`, so `θ^E_𝔭 c` fixes `γ`, i.e. the Kummer index vanishes
  (`Work.SSGRoute.kummerIdx_eq_zero_of_apply_eq`).

This is exactly the hypothesis `hdiag` of `kummerCharZMod_antisymm`, so together the two files give
the antisymmetry of the local Kummer pairing at the level `E`.
-/

open scoped NumberField
open NumberField IsDedekindDomain
open NK.GlobalCFT

namespace Work.SSGRoute.GrunwaldEscapeCore

variable {κ E : Type} [Field κ] [NumberField κ] [Field E] [NumberField E] [Algebra κ E]
  [FiniteDimensional κ E] [IsGalois κ E]

/-- **The diagonal at a big level.**  For `p` prime, `ζ ∈ κ` a primitive `p`-th root of unity,
`F ≤ E` a subfield with compatible Artin maps `artE`, `artF` (compatible = the restriction of
`artE` is `artF`; `artF` kills the idèlic norms), `c ∈ κˣ`, `γ ∈ Eˣ` a `p`-th root of `c` lying in
`F`, and `c` a local norm at `𝔭` for the extension `F/κ`: the Kummer index of `θ^E_𝔭 c` at
`(c, γ)` vanishes. -/
theorem kummerIdx_localArtinFactor_eq_zero
    (p : ℕ) [Fact p.Prime] (ζ : κ) (hζ : IsPrimitiveRoot ζ p)
    (F : IntermediateField κ E) [FiniteDimensional κ F] [Normal κ F] [NumberField ↥F]
    (artE : Idele κ →* Gal(E/κ)) (artF : Idele κ →* Gal(↥F/κ))
    (hcompat : ∀ x : Idele κ, AlgEquiv.restrictNormalHom (F := κ) (K₁ := E) F (artE x) = artF x)
    (hkerF : ∀ y : Idele ↥F, artF (Idele.normIdeleHom κ ↥F y) = 1)
    (𝔭 : HeightOneSpectrum (𝓞 κ))
    (c : κˣ) (γ : Eˣ) (hγ : γ ^ p = Units.map (algebraMap κ E) c)
    (hγF : (γ : E) ∈ F)
    (hc : NK.CFTLib.IdeleHasse.localImageAt (K := κ) (NK.GlobalCFT.Place.ofFinite 𝔭) c ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := κ) (L := ↥F)
        (NK.GlobalCFT.Place.ofFinite 𝔭)) :
    Work.SSGRoute.kummerIdx p hζ c γ hγ
      (artE (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
        (NK.CFTLib.IdeleHasse.localImageAt (K := κ) (NK.GlobalCFT.Place.ofFinite 𝔭) c))) = 0 := by
  classical
  have hone : NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
      (NK.CFTLib.IdeleHasse.localImageAt (K := κ) (NK.GlobalCFT.Place.ofFinite 𝔭) c) ∈
      Idele.normImage κ ↥F :=
    (NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff (K := κ) (L := ↥F)
      (NK.GlobalCFT.Place.ofFinite 𝔭) _).mpr hc
  obtain ⟨y, hy⟩ := Idele.mem_normImage.mp hone
  have hy' : NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
      (NK.CFTLib.IdeleHasse.localImageAt (K := κ) (NK.GlobalCFT.Place.ofFinite 𝔭) c) =
      Idele.normIdeleHom κ ↥F y :=
    Idele.ext (fun v => by rw [Idele.normIdeleHom_apply]; exact hy v)
  have hres : AlgEquiv.restrictNormalHom (F := κ) (K₁ := E) F
      (artE (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
        (NK.CFTLib.IdeleHasse.localImageAt (K := κ) (NK.GlobalCFT.Place.ofFinite 𝔭) c))) = 1 := by
    rw [hcompat, hy', hkerF y]
  have hfix : (artE (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
      (NK.CFTLib.IdeleHasse.localImageAt (K := κ) (NK.GlobalCFT.Place.ofFinite 𝔭) c)))
      (γ : E) = (γ : E) := by
    have h1 : AlgEquiv.restrictNormalHom (F := κ) (K₁ := E) F
        (artE (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
          (NK.CFTLib.IdeleHasse.localImageAt (K := κ) (NK.GlobalCFT.Place.ofFinite 𝔭) c)))
        ⟨(γ : E), hγF⟩ = ⟨(γ : E), hγF⟩ := by
      rw [hres]
      rfl
    have h2 := congrArg (fun (x : ↥F) => (x : E)) h1
    rwa [AlgEquiv.restrictNormalHom_apply] at h2
  exact Work.SSGRoute.kummerIdx_eq_zero_of_apply_eq p hζ c γ hγ _ hfix

end Work.SSGRoute.GrunwaldEscapeCore
