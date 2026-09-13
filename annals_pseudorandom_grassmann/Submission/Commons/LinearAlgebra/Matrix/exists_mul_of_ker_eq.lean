import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.RingTheory.TotallySplit

namespace Commons.LinearAlgebra.Matrix

open _root_.Matrix

/-- Two surjective matrices with the same kernel: the one with more rows is a left multiple of the
other by an injective matrix. -/
theorem exists_mul_of_ker_eq {K : Type*} [Field K] {a b n : ℕ}
    (A : Matrix (Fin a) (Fin n) K) (B : Matrix (Fin b) (Fin n) K)
    (hker : LinearMap.ker A.mulVecLin = LinearMap.ker B.mulVecLin)
    (hA : LinearMap.range A.mulVecLin = ⊤) (hB : LinearMap.range B.mulVecLin = ⊤) :
    ∃ M : Matrix (Fin a) (Fin b) K, Function.Injective M.mulVecLin ∧ A = M * B := by
  obtain ⟨l, hl⟩ := LinearMap.exists_rightInverse_of_surjective B.mulVecLin hB
  have hBl : ∀ x, B.mulVecLin (l x) = x := by
    intro x
    have := congrArg (fun f => f x) hl
    simpa using this
  refine ⟨LinearMap.toMatrix' (A.mulVecLin.comp l), ?_, ?_⟩
  · rw [← Matrix.toLin'_apply' (LinearMap.toMatrix' (A.mulVecLin.comp l)),
      Matrix.toLin'_toMatrix']
    intro x y hxy
    have hmem : l x - l y ∈ LinearMap.ker A.mulVecLin := by
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
      exact hxy
    rw [hker] at hmem
    have hB0 : B.mulVecLin (l x - l y) = 0 := LinearMap.mem_ker.mp hmem
    rw [map_sub, hBl x, hBl y, sub_eq_zero] at hB0
    exact hB0
  · have hAB : A.mulVecLin = (A.mulVecLin.comp l).comp B.mulVecLin := by
      apply LinearMap.ext
      intro x
      show A.mulVecLin x = A.mulVecLin (l (B.mulVecLin x))
      have hmem : l (B.mulVecLin x) - x ∈ LinearMap.ker B.mulVecLin := by
        rw [LinearMap.mem_ker, map_sub, hBl (B.mulVecLin x), sub_self]
      rw [← hker] at hmem
      have h0 := LinearMap.mem_ker.mp hmem
      rw [map_sub, sub_eq_zero] at h0
      exact h0.symm
    have htoM : Matrix.toLin' (LinearMap.toMatrix' (A.mulVecLin.comp l)) = A.mulVecLin.comp l :=
      Matrix.toLin'_toMatrix' _
    have htoB : Matrix.toLin' B = B.mulVecLin := Matrix.toLin'_apply' B
    have htoA : Matrix.toLin' A = A.mulVecLin := Matrix.toLin'_apply' A
    have hprod : Matrix.toLin' (LinearMap.toMatrix' (A.mulVecLin.comp l) * B) = Matrix.toLin' A := by
      rw [Matrix.toLin'_mul, htoM, htoB, htoA]
      exact hAB.symm
    exact (Matrix.toLin'.injective hprod).symm

end Commons.LinearAlgebra.Matrix