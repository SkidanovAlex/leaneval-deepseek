import Mathlib
import Submission.Work.SSGRoute.ZDataMup.localFaithful_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Local faithfulness of the abelian Artin map at one place

Milne, *CFT*, V.5.3(a): for a finite abelian extension `L / K` of number fields, a one-place idèle
`onePlace v a` lying in `N_{L/K} 𝕀_L · Kˣ` already lies in `N_{L/K} 𝕀_L`.

The proof reduces to the abelian "one place omitted" form of Hilbert reciprocity
(`lfab_hilbertReciprocity_abelian`), which in turn follows from the cyclic case
(`NK.CFTLib.hilbertReciprocity_onePlace_aux`) together with the *local intersection identity*: the
local norm subgroup at a place is the intersection of the local norm subgroups of the finite cyclic
intermediate extensions (established in `Work.SSGRoute.ZDataMup.localFaithful_aux`).
-/

set_option maxHeartbeats 8000000

namespace Work.SSGRoute.ZDataMup

open NK.GlobalCFT
open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

/-- **The one-place step at a finite place from the cyclic case.** -/
theorem lfab_localImage_mem_localNormSubgroup_ofFinite
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a) (x : Kˣ)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hM : ∀ M : IntermediateField K L, IsCyclic (↥M ≃ₐ[K] ↥M) →
      NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite Q) x ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := M)
          (NK.GlobalCFT.Place.ofFinite Q)) :
    NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite Q) x ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite Q) := by
  classical
  rw [localNormSubgroup_iInf_cyclic_ofFinite (K := K) (L := L) hcomm Q, Subgroup.mem_iInf]
  exact fun M => hM M.1 M.2

/-- **The one-place step from the cyclic case.**  If the local image of `x` at `v₀` is a local norm
for the extension by every cyclic intermediate field, then it is a local norm for `L`. -/
theorem lfab_localImage_mem_localNormSubgroup_of_cyclic
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a) (x : Kˣ) (v₀ : NK.GlobalCFT.Place K)
    (hM : ∀ M : IntermediateField K L, IsCyclic (↥M ≃ₐ[K] ↥M) →
      NK.CFTLib.IdeleHasse.localImageAt v₀ x ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := M) v₀) :
    NK.CFTLib.IdeleHasse.localImageAt v₀ x ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v₀ := by
  rcases v₀ with w | Q
  · exact lfab_localImage_mem_localNormSubgroup_ofInfinite (K := K) (L := L) hcomm x w hM
  · exact lfab_localImage_mem_localNormSubgroup_ofFinite (K := K) (L := L) hcomm x Q hM

/-- **Hilbert reciprocity for abelian extensions, "one place omitted" form** (Milne, *CFT*,
VII.8.1(a)): a global element `x ∈ Kˣ` which is a local norm at every place different from `v₀` is
a local norm at `v₀`. -/
theorem lfab_hilbertReciprocity_abelian
    {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a) (x : Kˣ) (v₀ : NK.GlobalCFT.Place K)
    (h : ∀ v : NK.GlobalCFT.Place K, v ≠ v₀ →
      NK.CFTLib.IdeleHasse.localImageAt v x ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v) :
    NK.CFTLib.IdeleHasse.localImageAt v₀ x ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v₀ := by
  classical
  refine lfab_localImage_mem_localNormSubgroup_of_cyclic (K := K) (L := L) hcomm x v₀ ?_
  intro M hcyc
  haveI : IsCyclic (M ≃ₐ[K] M) := hcyc
  haveI : IsGalois K ↥M := isGalois_intermediateField_of_comm hcomm M
  refine NK.CFTLib.hilbertReciprocity_onePlace_aux (K := K) (L := ↥M) x v₀ ?_
  intro v hv
  have hmem : NK.CFTLib.localImageHom (K := K) v x ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v := h v hv
  have h1 : NK.HassePrinciple.onePlace v (NK.CFTLib.localImageHom (K := K) v x)
      ∈ NK.GlobalCFT.Idele.normImage K L :=
    (NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff (K := K) (L := L) v _).mpr hmem
  have h2 : NK.HassePrinciple.onePlace v (NK.CFTLib.localImageHom (K := K) v x)
      ∈ NK.GlobalCFT.Idele.normImage K ↥M :=
    NK.NUV2.ARL.normImage_le_of_tower (K := K) (L := ↥M) (M := L) h1
  exact (NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff (K := K) (L := ↥M) v _).mp h2

/-- **Local faithfulness of the abelian Artin map at one place** (Milne, *CFT*, V.5.3(a)):
a one-place idèle in `N_{L/K}𝕀_L · Kˣ` already lies in `N_{L/K}𝕀_L`. -/
theorem localFaithful_abelian {K : Type} [Field K] [NumberField K] {L : Type} [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    {v : NK.GlobalCFT.Place K} {a : (NK.GlobalCFT.Place.localField K v)ˣ}
    (h : NK.HassePrinciple.onePlace v a ∈
      NK.GlobalCFT.Idele.normImage K L ⊔ NK.GlobalCFT.Idele.principalSubgroup K) :
    NK.HassePrinciple.onePlace v a ∈ NK.GlobalCFT.Idele.normImage K L :=
  onePlace_mem_normImage_of_hilbertReciprocity_abelian (K := K) (L := L)
    (fun {x} {v₀} hx => lfab_hilbertReciprocity_abelian (K := K) (L := L) hcomm x v₀ hx) h

end Work.SSGRoute.ZDataMup
