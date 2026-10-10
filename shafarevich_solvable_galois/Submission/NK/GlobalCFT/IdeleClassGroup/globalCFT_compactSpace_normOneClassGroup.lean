import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFT.IdeleClassGroup.globalCFT_exists_finset_isBoundedIntegral
import Submission.NK.GlobalCFT.IdeleClassGroup.globalCFT_exists_unit_archimedean
import Submission.NK.GlobalCFT.IdeleClassGroup.globalCFT_isCompact_normOneBounded
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The norm-one idèle class group is compact

For a number field `K` the norm-one idèle class group `C¹_K = 𝕀¹_K ⧸ Kˣ` is compact.  This is the
finiteness theorem for the idèle class group: it uses the finiteness of the class group (via
`globalCFT_exists_finset_isBoundedIntegral`: every idèle can be multiplied by a principal idèle
into the bounded-integral idèles at a fixed finite set of places) and Dirichlet's unit theorem
(via `globalCFT_exists_unit_archimedean`: the archimedean components can then be adjusted by a unit
into a fixed annulus).  The resulting set `normOneBounded K S C` of locally bounded idèles of
content one is compact, and every class of `C¹_K` has a representative in it.

## Main result

* `NK.GlobalCFT.IdeleClassGroup.globalCFT_compactSpace_normOneClassGroup`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT.IdeleClassGroup

variable {K : Type*} [Field K] [NumberField K]

/-- **Every norm-one idèle has a locally bounded translate by a principal idèle.**  Combining the
finite-place reduction (finiteness of the class group) with the archimedean adjustment
(Dirichlet's unit theorem). -/
theorem globalCFT_exists_finset_isLocallyBounded :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (C : ℝ), 1 ≤ C ∧
      ∀ x ∈ Idele.normOne K, ∃ k : Kˣ,
        IsLocallyBounded K S C (Idele.principalIdele K k * x) := by
  obtain ⟨S, C₀, hC₀, hfin⟩ := globalCFT_exists_finset_isBoundedIntegral (K := K)
  obtain ⟨C₁, hC₁, harch⟩ := globalCFT_exists_unit_archimedean (K := K) S hC₀
  have hpos : (0 : ℝ) < C₀ := by linarith
  refine ⟨S, max C₀ C₁, le_max_of_le_left hC₀, fun x hx => ?_⟩
  obtain ⟨k₁, hk₁⟩ := hfin x
  have hy_mem : Idele.principalIdele K k₁ * x ∈ Idele.normOne K := by
    rw [Idele.mem_normOne, abs_mul_principalIdele, Idele.mem_normOne.mp hx]
  obtain ⟨k₂, hk₂unit, hk₂arch⟩ := harch (Idele.principalIdele K k₁ * x) hy_mem hk₁
  refine ⟨k₂ * k₁, ?_⟩
  have hmul : Idele.principalIdele K (k₂ * k₁) * x =
      Idele.principalIdele K k₂ * (Idele.principalIdele K k₁ * x) := by
    rw [map_mul, mul_assoc]
  rw [hmul]
  exact ⟨isBoundedIntegral_mono hpos (le_max_left _ _)
      (isBoundedIntegral_mul_of_norm_eq_one hk₂unit hk₁),
    fun w => ⟨le_trans (inv_anti₀ (by linarith) (le_max_right _ _)) (hk₂arch w).1,
      le_trans (hk₂arch w).2 (le_max_right _ _)⟩⟩

theorem globalCFT_compactSpace_normOneClassGroup {K : Type*} [Field K] [NumberField K] :
    CompactSpace (NK.GlobalCFT.IdeleClassGroup.normOneClassGroup K) := by
  obtain ⟨S, C, hC, hcover⟩ := globalCFT_exists_finset_isLocallyBounded (K := K)
  have hcompact : IsCompact (normOneBounded K S C) :=
    globalCFT_isCompact_normOneBounded S hC
  set T : Set (Idele.normOne K) :=
    ((↑) : Idele.normOne K → Idele K) ⁻¹' normOneBounded K S C with hT
  have hTcompact : IsCompact T := by
    have h1 : ((↑) : Idele.normOne K → Idele K) '' T = normOneBounded K S C := by
      rw [hT]
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hz
        exact ⟨⟨z, (mem_normOneBounded.mp hz).2⟩, hz, rfl⟩
    exact (Topology.IsEmbedding.subtypeVal.isCompact_iff).mpr (h1.symm ▸ hcompact)
  have hsurj : Function.Surjective
      (fun x : T => (QuotientGroup.mk x :
        Idele.normOne K ⧸ (Idele.principalSubgroup K).subgroupOf (Idele.normOne K))) := by
    rintro ⟨y⟩
    obtain ⟨k, hk⟩ := hcover y y.2
    have hzn : Idele.principalIdele K k * (y : Idele K) ∈ Idele.normOne K := by
      rw [Idele.mem_normOne, abs_mul_principalIdele, Idele.mem_normOne.mp y.2]
    have hmem : Idele.principalIdele K k * (y : Idele K) ∈ normOneBounded K S C :=
      mem_normOneBounded.mpr ⟨hk, hzn⟩
    refine ⟨⟨⟨Idele.principalIdele K k * (y : Idele K), hzn⟩, hmem⟩, ?_⟩
    change QuotientGroup.mk (⟨Idele.principalIdele K k * (y : Idele K), hzn⟩ : Idele.normOne K)
      = QuotientGroup.mk y
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hcoe : ((↑((⟨Idele.principalIdele K k * (y : Idele K), hzn⟩ : Idele.normOne K)⁻¹ * y) :
        Idele K)) = (Idele.principalIdele K k)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      simp [mul_comm]
    rw [hcoe]
    exact Idele.mem_principalSubgroup.mpr ⟨k⁻¹, map_inv (Idele.principalIdele K) k⟩

  have hcont : Continuous (fun x : T => (QuotientGroup.mk x :
      Idele.normOne K ⧸ (Idele.principalSubgroup K).subgroupOf (Idele.normOne K))) :=
    continuous_quotient_mk'.comp continuous_subtype_val
  have hTu : IsCompact (Set.univ : Set T) :=
    isCompact_univ_iff.mpr (isCompact_iff_compactSpace.mp hTcompact)
  have himg : (fun x : T => (QuotientGroup.mk x :
      Idele.normOne K ⧸ (Idele.principalSubgroup K).subgroupOf (Idele.normOne K))) '' Set.univ
      = Set.univ :=
    Set.eq_univ_of_forall fun z => by
      obtain ⟨a, ha⟩ := hsurj z
      exact ⟨a, Set.mem_univ a, ha⟩
  have : IsCompact (Set.univ : Set (Idele.normOne K ⧸
      (Idele.principalSubgroup K).subgroupOf (Idele.normOne K))) :=
    himg ▸ hTu.image hcont
  exact isCompact_univ_iff.mp this

end NK.GlobalCFT.IdeleClassGroup
