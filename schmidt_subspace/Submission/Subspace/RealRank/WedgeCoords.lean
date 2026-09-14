import Mathlib
import Submission.Subspace.RealRank.Containment
import Submission.Subspace.RealRank.Annihilator
import Submission.Commons.LinearAlgebra.Plucker.eq_span_of_minors_proportional

/-!
# The coordinate identification `ℚ^{Idx} ≅ ⋀^r ℚ^N`

`Idx N r = {S : Finset (Fin N) // S.card = r}` indexes both the compound matrix and (through the
standard basis of the exterior power) the space `⋀^r ℚ^N`.  Concretely, the standard basis of
`⋀^r ℚ^N` is `wedgeBasis N r`, and

`wedgeEquiv (fun T => (compound r V) T S) = ⋀_{i ∈ S} v_i`,

i.e. the `S`-th column of the compound matrix of `V` is exactly the coordinate vector of the
wedge `⋀_{i ∈ S} v_i` (the `v_i` being the columns of `V`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators exteriorPower
open ExteriorAlgebra

namespace Submission.Subspace.RealRank

variable {N r : ℕ}

/-- The standard basis of `⋀^r ℚ^N`, indexed by `Idx N r`. -/
noncomputable def wedgeBasis (N r : ℕ) :
    Module.Basis (Idx N r) ℚ (⋀[ℚ]^r (Fin N → ℚ)) :=
  Module.Basis.exteriorPower r (Pi.basisFun ℚ (Fin N))

lemma wedgeBasis_apply (S : Idx N r) :
    wedgeBasis N r S = exteriorPower.ιMulti_family ℚ r (Pi.basisFun ℚ (Fin N)) S :=
  exteriorPower.basis_apply ℚ r (Pi.basisFun ℚ (Fin N)) S

/-- The coordinate identification `ℚ^{Idx} ≅ ⋀^r ℚ^N`. -/
noncomputable def wedgeEquiv (N r : ℕ) :
    (Idx N r → ℚ) ≃ₗ[ℚ] (⋀[ℚ]^r (Fin N → ℚ)) :=
  (wedgeBasis N r).equivFun.symm

lemma wedgeEquiv_apply (x : Idx N r → ℚ) :
    wedgeEquiv N r x = ∑ S : Idx N r, x S • wedgeBasis N r S :=
  Module.Basis.equivFun_symm_apply _ x

/-- **The columns of the compound matrix are the coordinate vectors of the wedges.** -/
theorem wedgeEquiv_compound_col (V : Matrix (Fin N) (Fin N) ℚ) (S : Idx N r) :
    wedgeEquiv N r (fun T : Idx N r => (Commons.LinearAlgebra.Matrix.compound r V) T S)
      = exteriorPower.ιMulti_family ℚ r (fun j : Fin N => fun k : Fin N => V k j) S := by
  classical
  have hrepr : ∀ T : Idx N r,
      ((wedgeBasis N r).repr (exteriorPower.ιMulti_family ℚ r
        (fun j : Fin N => fun k : Fin N => V k j) S)) T
      = (Commons.LinearAlgebra.Matrix.compound r V) T S := by
    intro T
    rw [wedgeBasis]
    change ((Module.Basis.exteriorPower r (Pi.basisFun ℚ (Fin N))).repr
        (exteriorPower.ιMulti ℚ r (fun a : Fin r => fun k : Fin N =>
          V k ((Set.powersetCard.ofFinEmbEquiv.symm S) a)))) T
      = (Commons.LinearAlgebra.Matrix.compound r V) T S
    rw [Commons.LinearAlgebra.Plucker.repr_exteriorPower_ιMulti (Pi.basisFun ℚ (Fin N)) T]
    have hm : (Matrix.of fun i j => (Pi.basisFun ℚ (Fin N)).coord
          ((Set.powersetCard.ofFinEmbEquiv.symm T) j)
          ((fun j : Fin N => fun k : Fin N => V k j)
            ((Set.powersetCard.ofFinEmbEquiv.symm S) i)))
        = Matrix.transpose (V.submatrix (T.1.orderEmbOfFin T.2) (S.1.orderEmbOfFin S.2)) := by
      ext i j
      simp only [Matrix.of_apply, Module.Basis.coord_apply, Pi.basisFun_repr,
        Matrix.transpose_apply, Matrix.submatrix_apply]
      have hT : ((Set.powersetCard.ofFinEmbEquiv.symm T) : Fin r → Fin N)
          = ((T.1.orderEmbOfFin T.2) : Fin r → Fin N) := rfl
      have hS : ((Set.powersetCard.ofFinEmbEquiv.symm S) : Fin r → Fin N)
          = ((S.1.orderEmbOfFin S.2) : Fin r → Fin N) := rfl
      rw [hT, hS]
    rw [hm, Matrix.det_transpose (V.submatrix (T.1.orderEmbOfFin T.2)
      (S.1.orderEmbOfFin S.2))]
    rfl
  have hsum := Module.Basis.sum_repr (wedgeBasis N r)
    (exteriorPower.ιMulti_family ℚ r (fun j : Fin N => fun k : Fin N => V k j) S)
  rw [wedgeEquiv_apply, ← hsum]
  exact Finset.sum_congr rfl fun T _ => by rw [hrepr T]

end Submission.Subspace.RealRank
