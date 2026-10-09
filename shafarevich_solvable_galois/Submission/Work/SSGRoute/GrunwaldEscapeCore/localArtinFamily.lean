import Mathlib
import Submission.NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust
import Submission.NK.CFTLib.ArtinReciprocityIdealProved
import Submission.Work.SSGRoute.ZDataMup.ideleArtin_ideleOfPrime_of_unramified
import Submission.Work.SSGRoute.ZDataMup.ideleArtin_restrictNormalHom
import Submission.NK.NUV2.ARL.abelianWeakToStrong
import Submission.Work.SSGRoute.GrunwaldEscapeCore.norm_kummerRoot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local Artin family, from a single idèlic datum

`NOTE_orthogonality_route.md` §6.3.  Fix a finite abelian extension `E/κ` of number fields.  For a
subfield `F ≤ E` (again abelian over `κ`) we produce idèlic Artin maps `artE`, `artF` **from one and
the same congruence datum** `(m, U, hadj)`:

* both kill the principal idèles and the idèlic norms (the kernel clause of
  `Work.SSGRoute.ZDataMup.exists_ideleArtinMap_with_kernel`),
* both are Frobenius-normalised at every prime unramified in the respective extension
  (`Work.SSGRoute.ZDataMup.ideleArtin_ideleOfPrime_of_unramified`, the conductor drop),
* **and they are compatible**: `restrictNormalHom F (artE x) = artF x`
  (`Work.SSGRoute.ZDataMup.ideleArtin_restrictNormalHom`).

The compatibility is the piece that turns the *small-level* diagonal
(`mem_localNormSubgroup_of_kummerRoot`: `x ∈ localNormSubgroup (ofFinite 𝔭)` for `F = κ(x^{1/p})`)
into the *diagonal at the big level* `E`, i.e. into the hypothesis `hdiag` of
`kummerCharZMod_antisymm` (`kummerChar_antisymm.lean`) — see
`GrunwaldEscapeCore/diagonal_at_level.lean`.
-/

open scoped NumberField
open NumberField IsDedekindDomain
open NK.GlobalCFT

namespace Work.SSGRoute.GrunwaldEscapeCore

variable {κ E : Type} [Field κ] [NumberField κ] [Field E] [NumberField E] [Algebra κ E]
  [FiniteDimensional κ E] [IsGalois κ E]

/-- **The two-level Artin family from a single idèlic datum.** -/
theorem exists_artinFamily_two_levels
    (hcomm : ∀ a b : Gal(E/κ), a * b = b * a)
    (F : IntermediateField κ E) [FiniteDimensional κ F] [Normal κ F] [NumberField ↥F]
    (hcommF : ∀ a b : Gal(↥F/κ), a * b = b * a) :
    ∃ (artE : Idele κ →* Gal(E/κ)) (artF : Idele κ →* Gal(↥F/κ)),
      (∀ y : Idele E, artE (Idele.normIdeleHom κ E y) = 1) ∧
      (∀ x : κˣ, artE (Idele.principalIdele κ x) = 1) ∧
      (∀ y : Idele ↥F, artF (Idele.normIdeleHom κ ↥F y) = 1) ∧
      (∀ x : κˣ, artF (Idele.principalIdele κ x) = 1) ∧
      (∀ 𝔮 : NK.Chebotarev.PrimeIdeal κ, NK.HeckeL.IsUnramifiedIn (K := κ) (L := E) 𝔮 →
        artE (NK.HeckeL.ideleOfPrime κ 𝔮) = NK.Chebotarev.frobAtPrime (K := κ) (L := E) 𝔮) ∧
      (∀ 𝔮 : NK.Chebotarev.PrimeIdeal κ, NK.HeckeL.IsUnramifiedIn (K := κ) (L := ↥F) 𝔮 →
        artF (NK.HeckeL.ideleOfPrime κ 𝔮) = NK.Chebotarev.frobAtPrime (K := κ) (L := ↥F) 𝔮) ∧
      (∀ x : Idele κ, AlgEquiv.restrictNormalHom (F := κ) (K₁ := E) F (artE x) = artF x) := by
  classical
  obtain ⟨m, hm, hramE, hprincE⟩ := NK.CFTLib.artinReciprocityIdeal_proved κ E hcomm
  obtain ⟨U, hU, hadj⟩ := NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust κ m hm
  obtain ⟨artE, hagreeE, hkerE, hprinE, _hgoodE, _hsurjE⟩ :=
    Work.SSGRoute.ZDataMup.exists_ideleArtinMap_with_kernel (K := κ) (L := E) hcomm m hm hramE hprincE U hU hadj
  have hramF : ∀ p : HeightOneSpectrum (𝓞 κ), (m : 𝓞 κ) ∉ p.asIdeal →
      Ideal.ramificationIdxIn p.asIdeal (𝓞 ↥F) = 1 := fun p hp =>
    NK.NUV2.ARL.ramificationIdxIn_eq_one_of_intermediateField (K := κ) (L := E) F p (hramE p hp)
  have hprincF : NK.CFTLib.artinKillsPrincipal κ ↥F m :=
    NK.NUV2.ARL.artinKillsPrincipal_of_intermediateField (K := κ) (L := E) F hramE hprincE
  obtain ⟨artF, hagreeF, hkerF, hprinF, _hgoodF, _hsurjF⟩ :=
    Work.SSGRoute.ZDataMup.exists_ideleArtinMap_with_kernel (K := κ) (L := ↥F) hcommF m hm hramF hprincF U hU
      hadj
  refine ⟨artE, artF, ?_, hprinE, ?_, hprinF, ?_, ?_, ?_⟩
  · intro y
    rw [← MonoidHom.mem_ker, hkerE]
    exact Subgroup.mem_sup_left
      (Idele.mem_normImage.mpr ⟨y, fun v => by rw [Idele.normIdeleHom_apply]⟩)
  · intro y
    rw [← MonoidHom.mem_ker, hkerF]
    exact Subgroup.mem_sup_left
      (Idele.mem_normImage.mpr ⟨y, fun v => by rw [Idele.normIdeleHom_apply]⟩)
  · intro 𝔮 hunr
    rw [hagreeE]
    exact Work.SSGRoute.ZDataMup.ideleArtin_ideleOfPrime_of_unramified (K := κ) (L := E) hcomm m hm hramE hprincE
      U hU hadj hunr
  · intro 𝔮 hunr
    rw [hagreeF]
    exact Work.SSGRoute.ZDataMup.ideleArtin_ideleOfPrime_of_unramified (K := κ) (L := ↥F) hcommF m hm hramF
      hprincF U hU hadj hunr
  · intro x
    rw [hagreeE, hagreeF]
    exact Work.SSGRoute.ZDataMup.ideleArtin_restrictNormalHom (K := κ) (L := E) hcomm m hm hramE U hU hadj F
      hcommF x

end Work.SSGRoute.GrunwaldEscapeCore
