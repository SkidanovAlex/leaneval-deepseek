import Mathlib.Analysis.RCLike.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

namespace Commons.LinearAlgebra.Dimension

theorem intVec_linearIndependent_rat_of_real {N : ℕ} {ι : Type*} [Fintype ι]
    (x : ι → Fin N → ℤ)
    (h : LinearIndependent ℝ (fun i => fun k => (x i k : ℝ))) :
    LinearIndependent ℚ (fun i => fun k => (x i k : ℚ)) := by
  have hli : LinearIndependent ℚ (fun i => fun k => (x i k : ℝ)) :=
    h.restrict_scalars' ℚ
  let f : (Fin N → ℚ) →ₗ[ℚ] (Fin N → ℝ) :=
    { toFun := fun y => fun k => (y k : ℝ)
      map_add' := by intro a b; funext k; simp
      map_smul' := by intro c a; funext k; simp [Algebra.smul_def] }
  have hcomp : f ∘ (fun i => fun k => (x i k : ℚ)) = (fun i => fun k => (x i k : ℝ)) := by
    funext i k; simp [f]
  exact LinearIndependent.of_comp f (by rw [hcomp]; exact hli)

end Commons.LinearAlgebra.Dimension