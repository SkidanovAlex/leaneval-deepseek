import Mathlib
import Submission.Work.SG.AffCoord

namespace Work.SG

/-- The entries of a real matrix which sends every integer vector to an integer vector are
themselves integers. -/
theorem exists_intCast_of_mulVec_intVec {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hM : ∀ n : Fin 3 → ℤ, ∃ k : Fin 3 → ℤ, Matrix.mulVec M (intVec n) = intVec k) :
    ∀ i j, ∃ z : ℤ, M i j = (z : ℝ) := by
  intro i j
  obtain ⟨k, hk⟩ := hM (Pi.single j (1 : ℤ))
  refine ⟨k i, ?_⟩
  have := congrFun hk i
  rwa [intVec_single, Matrix.mulVec_single_one] at this

/-- If a real `3 × 3` matrix `M` and a real inverse `N` of it (`M * N = N * M = 1`) both send
every integer vector to an integer vector, then `M` and `N` are the real matrices of integer
matrices `U`, `V` which are mutually inverse (`U * V = V * U = 1`); in particular `U` is
unimodular. -/
theorem intMat_lattice {M N : Matrix (Fin 3) (Fin 3) ℝ} (hMN : M * N = 1) (hNM : N * M = 1)
    (hM : ∀ n : Fin 3 → ℤ, ∃ k : Fin 3 → ℤ,
      Matrix.mulVec M (Work.SG.intVec n) = Work.SG.intVec k)
    (hN : ∀ n : Fin 3 → ℤ, ∃ k : Fin 3 → ℤ,
      Matrix.mulVec N (Work.SG.intVec n) = Work.SG.intVec k) :
    ∃ U V : Work.SG.IMat, M = Work.SG.matR U ∧ N = Work.SG.matR V ∧ U * V = 1 ∧ V * U = 1 := by
  have hM' := exists_intCast_of_mulVec_intVec hM
  have hN' := exists_intCast_of_mulVec_intVec hN
  let U : IMat := fun i j => Classical.choose (hM' i j)
  let V : IMat := fun i j => Classical.choose (hN' i j)
  have hU : matR U = M := by
    ext i j
    exact (Classical.choose_spec (hM' i j)).symm
  have hV : matR V = N := by
    ext i j
    exact (Classical.choose_spec (hN' i j)).symm
  refine ⟨U, V, hU.symm, hV.symm, ?_, ?_⟩
  · apply matR_injective
    rw [matR_mul, hU, hV, hMN, matR_one]
  · apply matR_injective
    rw [matR_mul, hV, hU, hNM, matR_one]

end Work.SG
