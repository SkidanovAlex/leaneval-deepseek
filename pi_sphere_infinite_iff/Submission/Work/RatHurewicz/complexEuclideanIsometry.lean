import Mathlib

set_option synthInstance.maxHeartbeats 400000

/-!
# `ℂ^K` and `ℝ^{2K}` are isometric as real inner product spaces

`EuclideanSpace ℂ (Fin K)`, regarded as a real inner product space, has the real
orthonormal basis `(e_i, I • e_i)_{i : Fin K}`, indexed by `Fin K × Fin 2`: it is
`Pi.orthonormalBasis` applied to the real orthonormal basis `![1, I]` of `ℂ`
(`Complex.orthonormalBasisOneI`).  Transporting this basis along the equivalence
`Fin K × Fin 2 ≃ Fin (2 * K)` and applying `OrthonormalBasis.equiv` against the
standard basis of `EuclideanSpace ℝ (Fin (2 * K))` gives a real linear isometry
equivalence between the two spaces.
-/

namespace Work.RatHurewicz

/-- The real orthonormal basis of `ℂ^K` consisting of the vectors `e_i` and
`I • e_i` for `i : Fin K`. -/
noncomputable def complexEuclideanBasis (K : ℕ) :
    OrthonormalBasis (Fin K × Fin 2) ℝ (EuclideanSpace ℂ (Fin K)) :=
  (Pi.orthonormalBasis (fun _ : Fin K => Complex.orthonormalBasisOneI)).reindex
    (Equiv.sigmaEquivProd (Fin K) (Fin 2))

theorem complexEuclideanIsometry (K : ℕ) :
    Nonempty (EuclideanSpace ℂ (Fin K) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2 * K))) := by
  refine ⟨?_⟩
  let e : Fin K × Fin 2 ≃ Fin (2 * K) :=
    finProdFinEquiv.trans (finCongr (Nat.mul_comm K 2))
  exact OrthonormalBasis.equiv (complexEuclideanBasis K)
    (EuclideanSpace.basisFun (Fin (2 * K)) ℝ) e

end Work.RatHurewicz
