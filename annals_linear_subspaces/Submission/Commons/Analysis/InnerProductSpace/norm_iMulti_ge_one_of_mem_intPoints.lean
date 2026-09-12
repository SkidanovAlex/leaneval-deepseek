import Mathlib
import Submission.Commons.Analysis.InnerProductSpace.intWedge_norm_ge_one
import Submission.Commons.Analysis.InnerProductSpace.intCoords_linearIndependent_real

namespace Commons.Analysis.InnerProductSpace

/-- Coordinates of a point of the standard integer lattice are integers. -/
lemma intCoords_of_mem_intPoints {d : ℕ} (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin d) ℝ))) :
    ∀ t : Fin d, ∃ z : ℤ, x t = z := by
  intro t
  have hb := (Module.Basis.mem_span_iff_repr_mem (R := ℤ) (S := ℝ)
    (M := EuclideanSpace ℝ (Fin d))
    (b := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis) (m := x)).mp hx t
  obtain ⟨z, hz⟩ := hb
  refine ⟨z, ?_⟩
  have hz' : (z : ℝ) = ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis.repr x) t := hz
  rw [hz', OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]

theorem norm_iMulti_ge_one_of_mem_intPoints {d k : ℕ} (u : Fin k → EuclideanSpace ℝ (Fin d)) (hmem : ∀ i : Fin k, u i ∈ Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin d) ℝ))) (hli : LinearIndependent ℤ u) : 1 ≤ ‖exteriorPower.ιMulti ℝ k u‖ := by
  have hliℝ : LinearIndependent ℝ u := intCoords_linearIndependent_real hmem hli
  have hcoord : ∀ r t, ∃ z : ℤ, u r t = z := fun r => intCoords_of_mem_intPoints (u r) (hmem r)
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hsq : ‖exteriorPower.ιMulti ℝ 0 u‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, exteriorPower.inner_ιMulti_self]
      simp [Matrix.det_fin_zero]
    nlinarith [norm_nonneg (exteriorPower.ιMulti ℝ 0 u)]
  · exact intWedge_norm_ge_one hk u hcoord hliℝ

end Commons.Analysis.InnerProductSpace
