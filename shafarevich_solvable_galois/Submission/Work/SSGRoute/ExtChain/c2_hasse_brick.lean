import Mathlib
import Submission.Work.SSGRoute.ExtChain.C2Deps
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.SSGRoute.ExtChain

open scoped NumberField RestrictedProduct NumberField.LiesOver
open NumberField IsDedekindDomain

noncomputable section

/-- Hasse's norm principle at an involution of a finite Galois extension of number fields `K/k`, in involution form. Let `τ : K ≃ₐ[k] K` satisfy `τ ^ 2 = 1` and `τ ≠ 1` (so `K / K^τ` is quadratic). If an idèle `y` of `K` satisfies `y * (τ • y) = principalIdele K w₀` for a unit `w₀ : Kˣ`, then `w₀ = w * (τ • w)` for some unit `w : Kˣ`. The hypothesis forces `τ • w₀ = w₀` (apply `τ` and use injectivity of the principal idèle map, `NK.HassePrinciple.principalIdele_injective`), so `w₀` is an element of the fixed field `K^τ`; the conclusion is Hasse's norm principle for the quadratic extension `K / K^τ`, for which one identifies `y * (τ • y)` with the norm of the idèle `y` from `K` to `K^τ` (`NK.GlobalCFT.Idele.normIdeleHom` and the product formula `NK.GlobalCFT.Inclusion.globalCFT_prod_smul_eq_inclusion_normIdeleHom`), and then invokes the unconditional cyclic Hasse norm result `NK.HassePrinciple.HasseNormTheorem.hasse_norm` (on disk as `NK.GlobalCFTdeep.hasseNormTheorem`, or the licensed input `NK.GlobalCFTdeep.cyclicHasseInput`). -/
theorem c2_hasse_brick {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (τ : K ≃ₐ[k] K) (hτ : τ ^ 2 = 1) (hnt : τ ≠ 1)
    (y : NK.GlobalCFT.Idele K) (w₀ : Kˣ)
    (hy : y * (τ • y) = NK.GlobalCFT.Idele.principalIdele K w₀) :
    ∃ w : Kˣ, w₀ = w * (τ • w) := by
  classical
  -- ## The fixed field of `τ` and the involution viewed over it
  set F : IntermediateField k K := IntermediateField.fixedField (Subgroup.zpowers τ) with hF
  have hfix : F.fixingSubgroup = Subgroup.zpowers τ := by
    rw [hF]; exact IntermediateField.fixingSubgroup_fixedField _
  set τF : K ≃ₐ[F] K :=
    F.fixingSubgroupEquiv ⟨τ, by rw [hfix]; exact Subgroup.mem_zpowers τ⟩ with hτF
  -- ## `Gal(K/F)` has exactly two elements, `1` and `τF`
  have hcard : Fintype.card (K ≃ₐ[F] K) = 2 := by
    rw [← Nat.card_eq_fintype_card]
    rw [← Nat.card_congr F.fixingSubgroupEquiv.toEquiv]
    rw [hfix, Nat.card_zpowers]
    exact orderOf_eq_prime hτ hnt
  have hne : (1 : K ≃ₐ[F] K) ≠ τF := by
    intro h
    apply hnt
    have h2 : F.fixingSubgroupEquiv.symm (1 : K ≃ₐ[F] K) = F.fixingSubgroupEquiv.symm τF := by
      rw [h]
    rw [map_one, hτF, MulEquiv.symm_apply_apply] at h2
    exact (Subtype.ext_iff.mp h2).symm
  have huniv : (Finset.univ : Finset (K ≃ₐ[F] K)) = {1, τF} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x _
      exact Finset.mem_univ x
    · rw [Finset.card_pair hne, Finset.card_univ, hcard]
  -- ## The actions of `τF` and of `τ` on idèles agree
  have hsmul : (τF • y : NK.GlobalCFT.Idele K) = τ • y := by
    apply NK.GlobalCFT.Idele.ext
    intro w
    rw [NK.GlobalCFT.Idele.smul_apply, NK.GlobalCFT.Idele.smul_apply]
    rfl
  -- ## `τ` fixes `w₀`
  have hτw₀ : τ • w₀ = w₀ := by
    have h1 := congrArg (fun z : NK.GlobalCFT.Idele K => τ • z) hy
    rw [NK.GlobalCFT.Galois.globalCFT_smul_idele_mul,
      NK.GlobalCFT.Galois.globalCFT_smul_principalIdele] at h1
    have hττ : τ * τ = 1 := by rw [← pow_two]; exact hτ
    have hyyy : (τ • (τ • y) : NK.GlobalCFT.Idele K) = y := by
      rw [← NK.GlobalCFT.Galois.globalCFT_mul_smul_idele τ τ y, hττ,
        NK.GlobalCFT.Galois.globalCFT_one_smul_idele]
    rw [hyyy, mul_comm] at h1
    exact (NK.HassePrinciple.principalIdele_injective K (hy.symm.trans h1)).symm
  -- ## `w₀` as a unit of the fixed field
  have hτw₀K : τ (w₀ : K) = (w₀ : K) := by
    have h := congrArg (fun u : Kˣ => (u : K)) hτw₀
    simpa using h
  have hmemF : ((w₀ : K)) ∈ F := by
    rw [hF, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have hstab : τ ∈ MulAction.stabilizer (K ≃ₐ[k] K) (w₀ : K) := by
      rw [MulAction.mem_stabilizer_iff]
      exact hτw₀K
    exact MulAction.mem_stabilizer_iff.mp (Subgroup.zpowers_le.mpr hstab hσ)
  have hmemFinv : (((w₀⁻¹ : Kˣ) : K)) ∈ F := by
    have h : ((w₀ : K))⁻¹ ∈ F := inv_mem hmemF
    simpa using h
  let u : (↥F)ˣ :=
    Units.mk ⟨(w₀ : K), hmemF⟩ ⟨((w₀⁻¹ : Kˣ) : K), hmemFinv⟩
      (by ext; simp) (by ext; simp)
  have hu : Units.map (algebraMap ↥F K).toMonoidHom u = w₀ := by
    ext; rfl
  -- ## The idèle inclusion `𝕀_F → 𝕀_K`
  have hlu : ∀ w : NK.GlobalCFT.Place K, ∃ v : NK.GlobalCFT.Place ↥F,
      NK.GlobalCFT.Place.LiesOver w v :=
    fun w => NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder w
  let ul : NK.GlobalCFT.Place K → NK.GlobalCFT.Place ↥F :=
    fun w => Classical.choose (hlu w)
  have hul : ∀ w : NK.GlobalCFT.Place K, NK.GlobalCFT.Place.LiesOver w (ul w) :=
    fun w => Classical.choose_spec (hlu w)
  obtain ⟨φ, hφ⟩ := NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_exists ul hul
  have hinj : Function.Injective φ := by
    intro x z hxz
    apply NK.GlobalCFT.Idele.ext
    intro v
    obtain ⟨w, hw⟩ :=
      NK.GlobalCFT.Inclusion.globalCFT_exists_placeOver (K := ↥F) (L := K) v
    have hw' : ul w = v :=
      NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique (hul w) hw
    have hcomp : NK.GlobalCFT.Place.localAlgebraMapUnits w (ul w) (hul w) (x (ul w)) =
        NK.GlobalCFT.Place.localAlgebraMapUnits w (ul w) (hul w) (z (ul w)) := by
      have h := congrArg (fun z : NK.GlobalCFT.Idele K => z w) hxz
      rw [hφ, hφ] at h
      exact h
    have h2 := NK.GlobalCFT.Inclusion.globalCFT_localAlgebraMapUnits_injective (hul w) hcomp
    rwa [hw'] at h2
  have hprincipal : φ (NK.GlobalCFT.Idele.principalIdele ↥F u) =
      NK.GlobalCFT.Idele.principalIdele K w₀ := by
    rw [NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_principalIdele ul hul φ hφ u, hu]
  -- ## The product formula: the norm of `y` is `y * (τ • y)`
  have hprod : (∏ σ : K ≃ₐ[F] K, σ • y) = y * (τ • y) := by
    rw [show (Finset.univ : Finset (K ≃ₐ[F] K)) = {1, τF} from huniv]
    rw [Finset.prod_pair hne, NK.GlobalCFT.Galois.globalCFT_one_smul_idele, hsmul]
  have hnorm_eq : NK.GlobalCFT.Idele.normIdeleHom ↥F K y =
      NK.GlobalCFT.Idele.principalIdele ↥F u := by
    apply hinj
    rw [← NK.GlobalCFT.Inclusion.globalCFT_prod_smul_eq_inclusion_normIdeleHom ul hul φ hφ y,
      hprod, hy, hprincipal]
  -- ## Hasse's norm theorem for the quadratic extension `K / K^τ`
  haveI : IsCyclic (K ≃ₐ[↥F] K) := by
    haveI : IsCyclic (↥F.fixingSubgroup) := by rw [hfix]; infer_instance
    exact (F.fixingSubgroupEquiv.isCyclic).mp ‹IsCyclic ↥F.fixingSubgroup›
  have hmem : NK.GlobalCFT.Idele.principalIdele ↥F u ∈
      NK.GlobalCFT.Idele.normImage ↥F K := by
    rw [NK.GlobalCFT.Idele.mem_normImage]
    refine ⟨y, fun v => ?_⟩
    rw [← NK.GlobalCFT.Idele.normIdeleHom_apply (K := ↥F) (L := K) (x := y) (v := v)]
    exact (congrArg (fun z : NK.GlobalCFT.Idele ↥F => z v) hnorm_eq).symm
  obtain ⟨b, hb⟩ := NK.GlobalCFTdeep.cyclicHasseInput.hasse_norm.hasse_norm
    (K := ↥F) (L := K) inferInstance u hmem
  -- the unit `u` is the norm of `b`
  have hnorm : Units.map (Algebra.norm ↥F) b = u := by
    apply NK.HassePrinciple.principalIdele_injective ↥F
    rw [← NK.GlobalCFT.Idele.normIdeleHom_principalIdele (K := ↥F) (L := K) b]
    exact NK.GlobalCFT.Idele.ext (fun v => (congrFun hb v).symm)
  -- ## Conclusion
  refine ⟨b, ?_⟩
  have hlast : Units.map (algebraMap ↥F K).toMonoidHom (Units.map (Algebra.norm ↥F) b) = w₀ := by
    rw [hnorm, hu]
  rw [← hlast, ← NK.GlobalCFTdeep.prod_smul_eq_map_algebraMap_norm (K := ↥F) (L := K) b]
  rw [show (Finset.univ : Finset (K ≃ₐ[F] K)) = {1, τF} from huniv]
  rw [Finset.prod_pair hne, one_smul]
  congr 1

end

end Work.SSGRoute.ExtChain
