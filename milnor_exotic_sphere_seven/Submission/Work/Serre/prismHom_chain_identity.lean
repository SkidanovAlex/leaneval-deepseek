import Mathlib
import Submission.Work.Serre.simpHomChain
import Submission.Work.Serre.prismSumIdentity

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1000000

open CategoryTheory Limits AlgebraicTopology Simplicial
open scoped Simplicial

namespace Work.Serre

noncomputable section

variable {X : Type} [TopologicalSpace X] {A : Set X} {N : ℕ}

@[simp]
lemma coords_single {n : ℕ} (x : singX X _⦋n⦌) :
    (Work.Cohomology.Crux33.coords (singX X) n)
        ((ModuleCat.Hom.hom ((singX X).ιChainComplex (R := ModuleCat.of ℤ ℤ) x)) (1 : ℤ))
      = Finsupp.single x (1 : ℤ) :=
  Work.Cohomology.Crux33.coords_ι (singX X) n x

theorem prismHom_chain_identity (H : SimpHom X A N) (m : ℕ) (hm : m + 1 ≤ N) :
    CategoryTheory.CategoryStruct.comp (prismHom H (m + 1))
        ((singChainC X).d (m + 2) (m + 1))
      + CategoryTheory.CategoryStruct.comp ((singChainC X).d (m + 1) m)
          (prismHom H m)
      = CategoryTheory.CategoryStruct.id ((singChainC X).X (m + 1))
        - topChainMap H (m + 1) := by
  apply (singX X).chainComplex_hom_ext
  intro σ
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  · simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_add, LinearMap.add_apply,
      ModuleCat.hom_sub, LinearMap.sub_apply, ModuleCat.hom_id, LinearMap.id_apply]
    rw [prismHom_gen H (m + 1) σ, topChainMap_gen H (m + 1) σ, singChain_d_gen (X := X) m σ]
    simp only [prismVal, topVal, map_sum, map_zsmul]
    have hs1 : (∑ k : Fin (m + 2), ((-1 : ℤ) ^ ((k : ℕ) + 1)) •
          (ModuleCat.Hom.hom ((singChainC X).d (m + 2) (m + 1)))
            ((ModuleCat.Hom.hom ((singX X).ιChainComplex (R := ModuleCat.of ℤ ℤ)
              (hSimplex H (m + 1) k σ))) (1 : ℤ)))
        = ∑ k : Fin (m + 2), ((-1 : ℤ) ^ ((k : ℕ) + 1)) •
            ∑ i : Fin (m + 3), ((-1 : ℤ) ^ (i : ℕ)) •
              (ModuleCat.Hom.hom ((singX X).ιChainComplex (R := ModuleCat.of ℤ ℤ)
                ((singX X).δ i (hSimplex H (m + 1) k σ)))) (1 : ℤ) := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [singChain_d_gen (X := X) (m + 1) (hSimplex H (m + 1) k σ)]
    have hs2 : (∑ k : Fin (m + 2), ((-1 : ℤ) ^ (k : ℕ)) •
          (ModuleCat.Hom.hom (prismHom H m)
            ((ModuleCat.Hom.hom ((singX X).ιChainComplex (R := ModuleCat.of ℤ ℤ)
              ((singX X).δ k σ))) (1 : ℤ))))
        = ∑ k : Fin (m + 2), ((-1 : ℤ) ^ (k : ℕ)) •
            ∑ j : Fin (m + 1), ((-1 : ℤ) ^ ((j : ℕ) + 1)) •
              (ModuleCat.Hom.hom ((singX X).ιChainComplex (R := ModuleCat.of ℤ ℤ)
                (hSimplex H m j ((singX X).δ k σ)))) (1 : ℤ) := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [prismHom_gen H m ((singX X).δ k σ)]
      simp only [prismVal, map_sum, map_zsmul]
    rw [hs1, hs2]
    apply Work.Cohomology.Crux33.eq_of_coords_eq
    simp only [map_add, map_sub, map_zsmul, map_sum]
    have hA : (∑ x : Fin (m + 2), ∑ y : Fin (m + 3),
          ((-1 : ℤ) ^ ((x : ℕ) + 1 + (y : ℕ))) •
            (Work.Cohomology.Crux33.coords (singX X) (m + 1))
              ((ModuleCat.Hom.hom ((singX X).ιChainComplex (R := ModuleCat.of ℤ ℤ)
                ((singX X).δ y (hSimplex H (m + 1) x σ)))) (1 : ℤ)))
        = ∑ x : Fin (m + 2), ∑ y : Fin (m + 3),
          ((-1 : ℤ) ^ ((x : ℕ) + 1 + (y : ℕ))) •
            Finsupp.single ((singX X).δ y (hSimplex H (m + 1) x σ)) (1 : ℤ) := by
      refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
      rw [Work.Cohomology.Crux33.coords_ι]
    have hB : (∑ x : Fin (m + 2), ∑ y : Fin (m + 1),
          ((-1 : ℤ) ^ ((x : ℕ) + ((y : ℕ) + 1))) •
            (Work.Cohomology.Crux33.coords (singX X) (m + 1))
              ((ModuleCat.Hom.hom ((singX X).ιChainComplex (R := ModuleCat.of ℤ ℤ)
                (hSimplex H m y ((singX X).δ x σ)))) (1 : ℤ)))
        = ∑ x : Fin (m + 2), ∑ y : Fin (m + 1),
          ((-1 : ℤ) ^ ((x : ℕ) + ((y : ℕ) + 1))) •
            Finsupp.single (hSimplex H m y ((singX X).δ x σ)) (1 : ℤ) := by
      refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
      rw [Work.Cohomology.Crux33.coords_ι]
    have hR : (Work.Cohomology.Crux33.coords (singX X) (m + 1))
          ((ModuleCat.Hom.hom ((singX X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ)) (1 : ℤ)) -
        (Work.Cohomology.Crux33.coords (singX X) (m + 1))
          ((ModuleCat.Hom.hom ((singX X).ιChainComplex (R := ModuleCat.of ℤ ℤ)
            (gSimplex H (m + 1) σ))) (1 : ℤ))
        = Finsupp.single σ (1 : ℤ) - Finsupp.single (gSimplex H (m + 1) σ) (1 : ℤ) := by
      rw [Work.Cohomology.Crux33.coords_ι, Work.Cohomology.Crux33.coords_ι]
    simp_rw [Finset.smul_sum, smul_smul, ← pow_add]
    rw [hA, hB, hR]
    exact prismSumIdentity H m hm σ

end

end Work.Serre
