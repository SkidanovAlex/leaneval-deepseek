import Mathlib
import Submission.Work.SSGRoute.ZDataMup.NKArtinUmbrella
import Submission.NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm_of_finiteDimensional
import Submission.NK.CFTLib.hilbertReciprocityCyclicAux
import Submission.NK.CFTLib.hilbertReciprocity_cyclic
import Submission.NK.NUV2.ARL.isOpenNorm
import Submission.Work.SSGRoute.ZDataMup.abelian_local_norm_step
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataMup

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K]
variable {L : Type} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The local image of `x : Kˣ` is the component of the principal idèle. -/
theorem localImageAt_eq_principalIdele (v : NK.GlobalCFT.Place K) (x : Kˣ) :
    NK.CFTLib.IdeleHasse.localImageAt v x = (NK.GlobalCFT.Idele.principalIdele K x) v := rfl

/-- Every intermediate field of an abelian Galois extension is Galois over the base. -/
theorem isGalois_intermediateField_of_comm (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (M : IntermediateField K L) : IsGalois K ↥M := by
  haveI : IsMulCommutative (L ≃ₐ[K] L) := IsMulCommutative.of_comm hcomm
  haveI : IsAbelianGalois K L := {}
  exact (inferInstance : IsGalois K ↥M)

/-- The one-place idèle of a component of an idèle norm is an idèle norm. -/
theorem onePlace_apply_mem_normImage_gen {n : NK.GlobalCFT.Idele K}
    (hn : n ∈ NK.GlobalCFT.Idele.normImage K L) (v : NK.GlobalCFT.Place K) :
    NK.HassePrinciple.onePlace v (n v) ∈ NK.GlobalCFT.Idele.normImage K L := by
  rw [NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm_of_finiteDimensional]
  intro w
  by_cases hw : w = v
  · subst hw
    obtain ⟨y, hy⟩ :=
      (NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm_of_finiteDimensional
        (K := K) (L := L) n).mp hn w
    exact ⟨y, by rw [NK.HassePrinciple.onePlace_apply_self]; exact hy⟩
  · exact ⟨1, by rw [NK.HassePrinciple.onePlace_apply_ne hw,
      NK.GlobalCFT.Idele.normIdeleFun_one_apply]⟩

/-- Monotonicity of the idèlic norm subgroup along the tower `K ⊆ M ⊆ L`. -/
theorem normImage_mono_intermediate (M : IntermediateField K L) :
    NK.GlobalCFT.Idele.normImage K L ≤ NK.GlobalCFT.Idele.normImage K ↥M :=
  NK.NUV2.ARL.normImage_le_of_tower (K := K) (L := ↥M) (M := L)

/-- **Hilbert reciprocity for abelian extensions, "one place omitted" form**: a global element of
`Kˣ` which is a local norm at every place different from `v₀` is a local norm at `v₀`. -/
theorem hilbertReciprocity_abelian (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    {x : Kˣ} {v₀ : NK.GlobalCFT.Place K}
    (h : ∀ v : NK.GlobalCFT.Place K, v ≠ v₀ →
      NK.CFTLib.IdeleHasse.localImageAt v x ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v) :
    NK.CFTLib.IdeleHasse.localImageAt v₀ x ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v₀ := by
  refine abelian_local_norm_step (K := K) (L := L) hcomm (fun M hc => ?_)
  haveI : IsGalois K ↥M := isGalois_intermediateField_of_comm (K := K) (L := L) hcomm M
  have hM : ∀ v : NK.GlobalCFT.Place K, v ≠ v₀ →
      NK.CFTLib.IdeleHasse.localImageAt v x ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := ↥M) v := by
    intro v hv
    have h1 : NK.HassePrinciple.onePlace v (NK.CFTLib.IdeleHasse.localImageAt v x) ∈
        NK.GlobalCFT.Idele.normImage K L :=
      (NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff (K := K) (L := L) v
        (NK.CFTLib.IdeleHasse.localImageAt v x)).mpr (h v hv)
    have h2 : NK.HassePrinciple.onePlace v (NK.CFTLib.IdeleHasse.localImageAt v x) ∈
        NK.GlobalCFT.Idele.normImage K ↥M :=
      normImage_mono_intermediate (K := K) (L := L) M h1
    exact (NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff (K := K) (L := ↥M) v
      (NK.CFTLib.IdeleHasse.localImageAt v x)).mp h2
  haveI : IsCyclic (↥M ≃ₐ[K] ↥M) := hc
  exact NK.CFTLib.hilbertReciprocity_onePlace_aux (K := K) (L := ↥M) x v₀ hM

/-- **The reduction of the target to the "one place omitted" form of Hilbert reciprocity.** -/
theorem onePlace_mem_normImage_of_hilbertReciprocity_abelian
    (hQ : ∀ {x : Kˣ} {v₀ : NK.GlobalCFT.Place K},
      (∀ v : NK.GlobalCFT.Place K, v ≠ v₀ →
        NK.CFTLib.IdeleHasse.localImageAt v x ∈
          NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v) →
      NK.CFTLib.IdeleHasse.localImageAt v₀ x ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v₀)
    {v : NK.GlobalCFT.Place K} {a : (NK.GlobalCFT.Place.localField K v)ˣ}
    (h : NK.HassePrinciple.onePlace v a ∈
      NK.GlobalCFT.Idele.normImage K L ⊔ NK.GlobalCFT.Idele.principalSubgroup K) :
    NK.HassePrinciple.onePlace v a ∈ NK.GlobalCFT.Idele.normImage K L := by
  obtain ⟨n, hn, p, hp, hnp⟩ := Subgroup.mem_sup.mp h
  obtain ⟨x, rfl⟩ := NK.GlobalCFT.Idele.mem_principalSubgroup.mp hp
  -- every component of `n` is a local norm
  have hnm : ∀ w : NK.GlobalCFT.Place K,
      n w ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) w := by
    intro w
    obtain ⟨y, hy⟩ :=
      (NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm_of_finiteDimensional
        (K := K) (L := L) n).mp hn w
    rw [hy]
    exact NK.CFTLib.IdeleHasse.normIdeleFun_mem_localNormSubgroup (K := K) (L := L) y w
  -- away from `v` the component of the principal idèle is the inverse of a component of `n`
  have hcomp : ∀ w : NK.GlobalCFT.Place K, w ≠ v →
      (NK.GlobalCFT.Idele.principalIdele K x) w = (n w)⁻¹ := by
    intro w hw
    have h1 := congrArg (fun z : NK.GlobalCFT.Idele K => z w) hnp
    rw [NK.GlobalCFT.Idele.mul_apply, NK.GlobalCFT.Idele.principalIdele_apply,
      NK.HassePrinciple.onePlace_apply_ne hw] at h1
    exact eq_inv_of_mul_eq_one_left (by simpa [mul_comm] using h1)
  have hstep : ∀ w : NK.GlobalCFT.Place K, w ≠ v →
      NK.CFTLib.IdeleHasse.localImageAt w x ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) w := by
    intro w hw
    rw [localImageAt_eq_principalIdele, hcomp w hw]
    exact Subgroup.inv_mem _ (hnm w)
  have h0 : NK.CFTLib.IdeleHasse.localImageAt v x ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v := hQ hstep
  have hprin : NK.GlobalCFT.Idele.principalIdele K x ∈ NK.GlobalCFT.Idele.normImage K L := by
    rw [NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm_of_finiteDimensional]
    intro w
    by_cases hw : w = v
    · subst hw
      have hm : (NK.GlobalCFT.Idele.principalIdele K x) w ∈
          NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) w := by
        rw [← localImageAt_eq_principalIdele]
        exact h0
      exact NK.CFTLib.exists_normIdeleFun_eq_of_mem_localNormSubgroup (K := K) (L := L) hm
    · have hm : (NK.GlobalCFT.Idele.principalIdele K x) w ∈
          NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) w := by
        rw [hcomp w hw]
        exact Subgroup.inv_mem _ (hnm w)
      exact NK.CFTLib.exists_normIdeleFun_eq_of_mem_localNormSubgroup (K := K) (L := L) hm
  rw [← hnp]
  exact Subgroup.mul_mem _ hn hprin

theorem onePlace_mem_normImage_of_mem_sup_abelian {K : Type} [Field K] [NumberField K]
    {L : Type} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    {v : NK.GlobalCFT.Place K} {a : (NK.GlobalCFT.Place.localField K v)ˣ}
    (h : NK.HassePrinciple.onePlace v a ∈
      NK.GlobalCFT.Idele.normImage K L ⊔ NK.GlobalCFT.Idele.principalSubgroup K) :
    NK.HassePrinciple.onePlace v a ∈ NK.GlobalCFT.Idele.normImage K L :=
  onePlace_mem_normImage_of_hilbertReciprocity_abelian (K := K) (L := L)
    (fun {x} {v₀} hx => hilbertReciprocity_abelian (K := K) (L := L) hcomm hx) h

end Work.SSGRoute.ZDataMup
