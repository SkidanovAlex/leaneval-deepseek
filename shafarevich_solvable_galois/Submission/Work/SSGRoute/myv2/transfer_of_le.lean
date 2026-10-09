import Mathlib
import Submission.Work.SSGRoute.ZDataMup.ArtinUniqueness.artinMap_restrictNormalHom_eq_abelian
import Submission.Work.SSGRoute.ZConstruction.hLocalFactor_restrictNormalHom_eq
import Submission.Work.SSGRoute.EscapeCoreLib.isGalois_comap
import Submission.Work.SSGRoute.N2v2.isUnramifiedIn_of_algEquiv
import Submission.Work.SSGRoute.Sha2Lib.ideleClassEquiv_refl
import Submission.Work.SSGRoute.ZDataMup.normImage_topIntermediateField
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.myv2

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- **The idèlic norm image is invariant under a `↥K`-algebra isomorphism of the extension.**

Local copy of `Work.SSGRoute.N2v2.normImage_eq_of_algEquiv` with the finiteness hypotheses made
explicit (the lane imported here cannot import the `N2v2` aggregator: it clashes with the
`OddGate` re-export of `mupH1locLcHoms`). -/
theorem normImage_eq_of_algEquiv' {K L₁ L₂ : Type*} [Field K] [NumberField K] [Field L₁]
    [NumberField L₁] [Field L₂] [NumberField L₂] [Algebra K L₁] [Algebra K L₂]
    [FiniteDimensional K L₁] [FiniteDimensional K L₂] (e : L₁ ≃ₐ[K] L₂) :
    NK.GlobalCFT.Idele.normImage K L₂ = NK.GlobalCFT.Idele.normImage K L₁ := by
  have h := Work.SSGRoute.ZDataMup.normImage_map_ideleEquiv (K := K) (L := L₁) (K' := K)
    (L' := L₂) (RingEquiv.refl K) e.toRingEquiv (fun x => by simpa using e.commutes x)
  have hid : (NK.GlobalCFT.Idele.normImage K L₁).map
      (NK.GlobalCFTdeep.Transport.ideleEquiv (RingEquiv.refl K)).toMonoidHom =
      NK.GlobalCFT.Idele.normImage K L₁ := by
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      change (NK.GlobalCFTdeep.Transport.ideleEquiv (RingEquiv.refl K)) y ∈
        NK.GlobalCFT.Idele.normImage K L₁
      rwa [Work.SSGRoute.Sha2Lib.ssgr_ideleEquiv_refl_apply y]
    · intro x hx
      refine Subgroup.mem_map.mpr ⟨x, hx, ?_⟩
      exact Work.SSGRoute.Sha2Lib.ssgr_ideleEquiv_refl_apply x
  rw [← h, hid]

set_option maxHeartbeats 1000000 in
/-- **Level compatibility of the idèlic Artin map, in elementwise form.**  For `M ≤ E` two finite
abelian levels over `↥K` and Artin maps `art : 𝕀_↥K →* Gal(M/↥K)`, `Φ : 𝕀_↥K →* Gal(E/↥K)`, both
pinned by the kernel clause (`N𝕀 ⊔ Kˣ`) and the Frobenius normalisation at every unramified prime,
the restriction to `M` of `Φ x` is `art x`: the two agree on the copy of `M` inside `E`.

Route: `Work.SSGRoute.ZDataMup.ArtinUniqueness.artinMap_restrictNormalHom_eq_abelian` applied with
`L := M.comap (IsScalarTower.toAlgHom ↥K ↥E Ω)` (the copy of `↥M` inside `↥E`, with
`EscapeCoreLib.comapAlgEquiv K E M hME : ↥M ≃ₐ[↥K] ↥L`), the Artin map `art` being transported along
that `AlgEquiv`.  (The pointwise form is the memberwise reading of the resulting identity of monoid
homomorphisms; `EscapeCoreLib.isGalois_comap_of_le_over` and `FiniteDimensional.of_injective` give the
instances on the copy of `M` inside `E`.) -/
theorem transfer_of_le (p : ℕ) [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M E : IntermediateField ↥K Ω) [FiniteDimensional ↥K M] [IsGalois ↥K M] [NumberField ↥M]
    [FiniteDimensional ↥K E] [IsGalois ↥K E] [IsMulCommutative (↥E ≃ₐ[↥K] ↥E)]
    [NumberField ↥E] (hME : M ≤ E)
    (art : NK.GlobalCFT.Idele ↥K →* (↥M ≃ₐ[↥K] ↥M))
    (hker : art.ker = NK.GlobalCFT.Idele.normImage ↥K ↥M ⊔
      NK.GlobalCFT.Idele.principalSubgroup ↥K)
    (hfrob : ∀ Q : NK.Chebotarev.PrimeIdeal ↥K, NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥M) Q →
      art (NK.HeckeL.ideleOfPrime ↥K Q) = NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥M) Q)
    (Φ : NK.GlobalCFT.Idele ↥K →* (↥E ≃ₐ[↥K] ↥E))
    (hΦker : Φ.ker = NK.GlobalCFT.Idele.normImage ↥K ↥E ⊔
      NK.GlobalCFT.Idele.principalSubgroup ↥K)
    (hΦfrob : ∀ Q : NK.Chebotarev.PrimeIdeal ↥K, NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥E) Q →
      Φ (NK.HeckeL.ideleOfPrime ↥K Q) = NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥E) Q) :
    ∀ (x : NK.GlobalCFT.Idele ↥K) (y : ↥M),
      (((art x) y : ↥M) : Ω) = (((Φ x) ⟨(y : Ω), hME y.2⟩ : ↥E) : Ω) := by
  classical
  -- ## Number-field structures, and the copy `L` of `M` inside `E`
  haveI hNK : NumberField ↥K :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField K
  let L : IntermediateField ↥K ↥E := M.comap (IsScalarTower.toAlgHom ↥K ↥E Ω)
  let e : ↥M ≃ₐ[↥K] ↥L := Work.SSGRoute.EscapeCoreLib.comapAlgEquiv K E M hME
  haveI hGalL : IsGalois ↥K L :=
    Work.SSGRoute.EscapeCoreLib.isGalois_comap_of_le_over K E M hME
  haveI hFinL : FiniteDimensional ↥K L :=
    FiniteDimensional.of_injective e.symm.toLinearEquiv.toLinearMap e.symm.injective
  haveI hNumL : NumberField ↥L :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField L
  haveI hNormL : Normal ↥K L := IsGalois.to_normal
  haveI hNormE : Normal ↥K ↥E := IsGalois.to_normal
  -- ## Commutativity of the Galois groups involved
  have hcommE : ∀ a b : (↥E ≃ₐ[↥K] ↥E), a * b = b * a :=
    fun a b => IsMulCommutative.is_comm.comm a b
  have hcommL : ∀ a b : (↥L ≃ₐ[↥K] ↥L), a * b = b * a := by
    intro a b
    obtain ⟨a', rfl⟩ :=
      AlgEquiv.restrictNormalHom_surjective (F := ↥K) (E := ↥E) (K₁ := ↥L) a
    obtain ⟨b', rfl⟩ :=
      AlgEquiv.restrictNormalHom_surjective (F := ↥K) (E := ↥E) (K₁ := ↥L) b
    rw [← map_mul, ← map_mul, hcommE a' b']
  have hcommM : ∀ a b : (↥M ≃ₐ[↥K] ↥M), a * b = b * a := by
    intro a b
    exact NK.NUV2.ARL.SC.conjHom_injective e (by
      rw [map_mul, map_mul]
      exact hcommL _ _)
  -- ## The Artin map of `M/↥K`, transported to the copy of `M` inside `E`
  let Ψ : NK.GlobalCFT.Idele ↥K →* (↥L ≃ₐ[↥K] ↥L) := (NK.NUV2.ARL.SC.conjHom e).comp art
  have hΨker : Ψ.ker = NK.GlobalCFT.Idele.normImage ↥K ↥L ⊔
      NK.GlobalCFT.Idele.principalSubgroup ↥K := by
    have h1 : Ψ.ker = art.ker :=
      MonoidHom.ker_comp_of_injective art (NK.NUV2.ARL.SC.conjHom e)
        (NK.NUV2.ARL.SC.conjHom_injective e)
    rw [h1, hker, normImage_eq_of_algEquiv' e]
  have hΨfrob : ∀ Q : NK.Chebotarev.PrimeIdeal ↥K,
      NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥L) Q →
      Ψ (NK.HeckeL.ideleOfPrime ↥K Q) = NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥L) Q := by
    intro Q hunrL
    have hunrM : NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥M) Q :=
      (Work.SSGRoute.N2v2.isUnramifiedIn_of_algEquiv (K := ↥K) e Q).mpr hunrL
    have hfrobL : NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥L) Q
        = (NK.NUV2.ARL.SC.conjHom e)
            (NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥M) Q) :=
      NK.NUV2.ARL.SC.frobAtPrime_conjHom (K := ↥K) e hcommM Q hunrM
    show (NK.NUV2.ARL.SC.conjHom e) (art (NK.HeckeL.ideleOfPrime ↥K Q))
        = NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥L) Q
    rw [hfrobL, ← hfrob Q hunrM]
  -- ## Level compatibility of the abelian Artin maps of `↥E/↥K` and of the copy of `M`
  have hcomp : (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := ↥E) ↥L).comp Φ = Ψ :=
    Work.SSGRoute.ZDataMup.ArtinUniqueness.artinMap_restrictNormalHom_eq_abelian
      (K := ↥K) (M := ↥E) hcommE L Φ hΦker hΦfrob Ψ hΨker hΨfrob
  -- ## Memberwise reading
  intro x y
  let f : ↥L ≃ₐ[↥K] ↥L := AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := ↥E) ↥L (Φ x)
  have hx : f = Ψ x := (MonoidHom.ext_iff.mp hcomp) x
  have key : (f (e y) : Ω) = (Ψ x (e y) : Ω) :=
    congrArg (fun g : ↥L ≃ₐ[↥K] ↥L => (g (e y) : Ω)) hx
  have hL : (f (e y) : Ω) = (((Φ x) ⟨(y : Ω), hME y.2⟩ : ↥E) : Ω) := by
    have h1 : ((f (e y) : ↥L) : ↥E) = ((Φ x) ⟨(y : Ω), hME y.2⟩ : ↥E) := by
      rw [show f (e y) = AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := ↥E) ↥L (Φ x) (e y)
        from rfl]
      rw [AlgEquiv.restrictNormalHom_apply]
      rfl
    exact congrArg (fun z : ↥E => (z : Ω)) h1
  have hR : (Ψ x (e y) : Ω) = (((art x) y : ↥M) : Ω) := by
    show (((NK.NUV2.ARL.SC.conjHom e) (art x)) (e y) : Ω) = (((art x) y : ↥M) : Ω)
    rw [NK.NUV2.ARL.SC.conjHom_apply, AlgEquiv.symm_apply_apply]
    exact Work.SSGRoute.EscapeCoreLib.comapAlgEquiv_coe K E M hME ((art x) y)
  calc (((art x) y : ↥M) : Ω)
      = (Ψ x (e y) : Ω) := hR.symm
    _ = (f (e y) : Ω) := key.symm
    _ = (((Φ x) ⟨(y : Ω), hME y.2⟩ : ↥E) : Ω) := hL

end Work.SSGRoute.myv2
