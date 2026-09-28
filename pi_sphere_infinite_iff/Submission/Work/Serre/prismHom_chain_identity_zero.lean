import Mathlib
import Submission.Work.Serre.simpHomChain

/-!
# The chain identity in degree `0`

`Work.Serre.prismHom_chain_identity_zero`: in degree `0`, the chain homotopy attached to a family
`SimpHom.G` satisfies `∂T = 𝟙 - τ`, i.e. every `0`-chain is homologous to its "top" image.
-/

open CategoryTheory Limits AlgebraicTopology Simplicial
open scoped Simplicial

namespace Work.Serre

noncomputable section

variable {X : Type} [TopologicalSpace X] {A : Set X} {N : ℕ}

theorem prismHom_chain_identity_zero (H : SimpHom X A N) :
    CategoryTheory.CategoryStruct.comp (prismHom H 0) ((singChainC X).d 1 0)
      = CategoryTheory.CategoryStruct.id ((singChainC X).X 0) - topChainMap H 0 := by
  apply (singX X).chainComplex_hom_ext
  intro σ
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  have h1 : (prismHom H 0).hom (((singX X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom (1 : ℤ))
      = ∑ k : Fin 1, ((-1 : ℤ) ^ ((k : ℕ) + 1)) •
          ((singX X).ιChainComplex (R := ModuleCat.of ℤ ℤ) (hSimplex H 0 k σ)).hom (1 : ℤ) :=
    prismHom_gen H 0 σ
  have h2 : (topChainMap H 0).hom
      (((singX X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom (1 : ℤ))
      = ((singX X).ιChainComplex (R := ModuleCat.of ℤ ℤ) (gSimplex H 0 σ)).hom (1 : ℤ) :=
    topChainMap_gen H 0 σ
  have h3 : ((singChainC X).d 1 0).hom
      (((singX X).ιChainComplex (R := ModuleCat.of ℤ ℤ) (hSimplex H 0 0 σ)).hom (1 : ℤ))
      = ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) •
          (((singX X).ιChainComplex (R := ModuleCat.of ℤ ℤ)
            ((singX X).δ i (hSimplex H 0 0 σ))).hom (1 : ℤ)) :=
    singChain_d_gen (X := X) 0 (hSimplex H 0 0 σ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sub, LinearMap.sub_apply,
    ModuleCat.hom_id, LinearMap.id_apply, h1, h2, h3, map_sum, map_zsmul, Fin.sum_univ_one,
    Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul]
  have hlast := δ_hSimplex_last H 0 (by omega) σ
  rw [show (Fin.last (0 + 1) : Fin 2) = 1 from rfl, show (Fin.last 0 : Fin 1) = 0 from rfl] at hlast
  rw [hlast]
  have hzero := δ_hSimplex_zero H 0 (by omega) σ
  rw [hzero]
  simp only [neg_one_zsmul, zsmul_eq_mul, mul_one] at *
  abel

end

end Work.Serre
