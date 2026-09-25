import Mathlib
import Submission.NK.HassePrinciple.Placement
import Submission.Commons.RingTheory.Valuation.exists_mem_stabilizer_restrictNormalHom_eq_of_isGalois
import Submission.Commons.FieldTheory.Galois.comap_smul_eq_restrictNormalHom_smul
import Submission.Commons.RingTheory.Valuation.ValuationSubring.eq_top_of_comap_algebraMap_eq_top

namespace NK.HassePrinciple

universe u

open scoped Pointwise

/-- The image of the decomposition group of a place `A` of `K'` under the restriction map to a
finite Galois level `L` is the decomposition group of the restricted place: every `τ : Gal(L/K)`
stabilising `A ∩ L` lifts to a `σ : Gal(K'/K)` stabilising `A`, and conversely the restriction of a
stabiliser of `A` stabilises `A ∩ L`. -/
theorem map_levelRestrict_stabSubgroup {K K' : Type u} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (A : ValuationSubring K')
    (L : FiniteGaloisIntermediateField K K') :
    (NK.BrauerHasse.stabSubgroup A).map (NK.HassePrinciple.levelRestrict L) =
      NK.HassePrinciple.valuationStab (A.comap (algebraMap ↥L K')) := by
  apply le_antisymm
  · -- An element of `D_A` restricts to an element stabilising `A ∩ L`.
    intro τ hτ
    rw [Subgroup.mem_map] at hτ
    obtain ⟨σ, hσ, rfl⟩ := hτ
    rw [MulAction.mem_stabilizer_iff] at hσ ⊢
    have hmain := Commons.FieldTheory.Galois.comap_smul_eq_restrictNormalHom_smul A σ
      (L : IntermediateField K K')
    rw [hσ] at hmain
    exact hmain.symm
  · -- Every element stabilising `A ∩ L` lifts to an element of `D_A`.
    intro τ hτ
    rw [MulAction.mem_stabilizer_iff] at hτ
    by_cases hC : A.comap (algebraMap K K') = ⊤
    · -- If `A` is everything (`A = ⊤`, as `K'/K` is algebraic) both groups are everything.
      have hAtop : A = ⊤ :=
        Commons.RingTheory.Valuation.ValuationSubring.eq_top_of_comap_algebraMap_eq_top A
          (inferInstance) hC
      rw [hAtop]
      rw [Subgroup.mem_map]
      obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := K)
        (K₁ := ↥(L : IntermediateField K K')) (E := K') τ
      refine ⟨σ, ?_, hσ⟩
      rw [MulAction.mem_stabilizer_iff]
      ext x
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      simp
    · obtain ⟨σ, hσA, hσres⟩ :=
        Commons.RingTheory.Valuation.exists_mem_stabilizer_restrictNormalHom_eq_of_isGalois
          (F := K) (E := K') A hC (L : IntermediateField K K') τ hτ
      rw [Subgroup.mem_map]
      exact ⟨σ, hσA, hσres⟩

end NK.HassePrinciple
