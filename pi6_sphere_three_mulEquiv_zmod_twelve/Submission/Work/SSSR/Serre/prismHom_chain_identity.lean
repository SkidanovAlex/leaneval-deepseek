import Mathlib
import Submission.Work.SSSR.Serre.simpHomChain
import Submission.Work.SSSR.Serre.prismSumIdentity
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

open Work.Serre
variable {R : Type} [CommRing R] [Nontrivial R]

set_option maxHeartbeats 1000000

open CategoryTheory Limits AlgebraicTopology Simplicial
open scoped Simplicial
namespace Work.SSSR.Serre

noncomputable section

variable {X : Type} [TopologicalSpace X] {A : Set X} {N : ℕ}

theorem prismHom_chain_identity (H : SimpHom X A N) (m : ℕ) (hm : m + 1 ≤ N) :
    CategoryTheory.CategoryStruct.comp (prismHom R H (m + 1))
        ((singChainC R X).d (m + 2) (m + 1))
      + CategoryTheory.CategoryStruct.comp ((singChainC R X).d (m + 1) m)
          (prismHom R H m)
      = CategoryTheory.CategoryStruct.id ((singChainC R X).X (m + 1))
        - topChainMap R H (m + 1) := by
  apply (singX X).chainComplex_hom_ext
  intro σ
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  · simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_add, LinearMap.add_apply,
      ModuleCat.hom_sub, LinearMap.sub_apply, ModuleCat.hom_id, LinearMap.id_apply]
    rw [prismHom_gen H (m + 1) σ, topChainMap_gen H (m + 1) σ, singChain_d_gen (X := X) m σ]
    simp only [prismVal, topVal, map_sum, map_zsmul]
    have hs1 : (∑ k : Fin (m + 2), ((-1 : ℤ) ^ ((k : ℕ) + 1)) •
          (ModuleCat.Hom.hom ((singChainC R X).d (m + 2) (m + 1)))
            ((ModuleCat.Hom.hom ((singX X).ιChainComplex (R := ModuleCat.of R R)
              (hSimplex H (m + 1) k σ))) (1 : R)))
        = ∑ k : Fin (m + 2), ((-1 : ℤ) ^ ((k : ℕ) + 1)) •
            ∑ i : Fin (m + 3), ((-1 : ℤ) ^ (i : ℕ)) •
              (ModuleCat.Hom.hom ((singX X).ιChainComplex (R := ModuleCat.of R R)
                ((singX X).δ i (hSimplex H (m + 1) k σ)))) (1 : R) := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [singChain_d_gen (X := X) (m + 1) (hSimplex H (m + 1) k σ)]
    have hs2 : (∑ k : Fin (m + 2), ((-1 : ℤ) ^ (k : ℕ)) •
          (ModuleCat.Hom.hom (prismHom R H m)
            ((ModuleCat.Hom.hom ((singX X).ιChainComplex (R := ModuleCat.of R R)
              ((singX X).δ k σ))) (1 : R))))
        = ∑ k : Fin (m + 2), ((-1 : ℤ) ^ (k : ℕ)) •
            ∑ j : Fin (m + 1), ((-1 : ℤ) ^ ((j : ℕ) + 1)) •
              (ModuleCat.Hom.hom ((singX X).ιChainComplex (R := ModuleCat.of R R)
                (hSimplex H m j ((singX X).δ k σ)))) (1 : R) := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [prismHom_gen H m ((singX X).δ k σ)]
      simp only [prismVal, map_sum, map_zsmul]
    rw [hs1, hs2]
    apply Work.SSSR.Cohomology.Crux33.eq_of_coords_eq
    simp only [map_add, map_sub, map_zsmul, map_sum]
    have hA : (∑ x : Fin (m + 2), ∑ y : Fin (m + 3),
          ((-1 : ℤ) ^ ((x : ℕ) + 1 + (y : ℕ))) •
            (Work.SSSR.Cohomology.Crux33.coords (singX X) (m + 1))
              ((ModuleCat.Hom.hom ((singX X).ιChainComplex (R := ModuleCat.of R R)
                ((singX X).δ y (hSimplex H (m + 1) x σ)))) (1 : R)))
        = ∑ x : Fin (m + 2), ∑ y : Fin (m + 3),
          ((-1 : ℤ) ^ ((x : ℕ) + 1 + (y : ℕ))) •
            Finsupp.single ((singX X).δ y (hSimplex H (m + 1) x σ)) (1 : R) := by
      refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
      rw [Work.SSSR.Cohomology.Crux33.coords_ι]
    have hB : (∑ x : Fin (m + 2), ∑ y : Fin (m + 1),
          ((-1 : ℤ) ^ ((x : ℕ) + ((y : ℕ) + 1))) •
            (Work.SSSR.Cohomology.Crux33.coords (singX X) (m + 1))
              ((ModuleCat.Hom.hom ((singX X).ιChainComplex (R := ModuleCat.of R R)
                (hSimplex H m y ((singX X).δ x σ)))) (1 : R)))
        = ∑ x : Fin (m + 2), ∑ y : Fin (m + 1),
          ((-1 : ℤ) ^ ((x : ℕ) + ((y : ℕ) + 1))) •
            Finsupp.single (hSimplex H m y ((singX X).δ x σ)) (1 : R) := by
      refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
      rw [Work.SSSR.Cohomology.Crux33.coords_ι]
    have hR : (Work.SSSR.Cohomology.Crux33.coords (singX X) (m + 1))
          ((ModuleCat.Hom.hom ((singX X).ιChainComplex (R := ModuleCat.of R R) σ)) (1 : R)) -
        (Work.SSSR.Cohomology.Crux33.coords (singX X) (m + 1))
          ((ModuleCat.Hom.hom ((singX X).ιChainComplex (R := ModuleCat.of R R)
            (gSimplex H (m + 1) σ))) (1 : R))
        = Finsupp.single σ (1 : R) - Finsupp.single (gSimplex H (m + 1) σ) (1 : R) := by
      rw [Work.SSSR.Cohomology.Crux33.coords_ι, Work.SSSR.Cohomology.Crux33.coords_ι]
    simp_rw [Finset.smul_sum, smul_smul, ← pow_add]
    rw [hA, hB, hR]
    exact prismSumIdentity H m hm σ

end

end Work.SSSR.Serre
