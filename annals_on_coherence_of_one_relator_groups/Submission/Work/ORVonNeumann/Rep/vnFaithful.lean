import Mathlib
import Submission.Work.ORVonNeumann.Rep.vnCore
import Submission.Work.ORVonNeumann.Rep.vnHdimCompl
import Submission.Work.ORVonNeumann.Rep.vnMatOpAdjoint

set_option synthInstance.maxHeartbeats 200000

namespace Work.ORVonNeumann.Rep

open scoped InnerProductSpace

variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-- For `n = 1`, the von Neumann dimension `hdim K` of a subspace
`K ⊆ ℓ²(G) = HSum 1` is `‖K.starProjection δ₁‖ ^ 2`, and the single unit vector `δ₁`
detects it: `hdim K = 1` forces `δ₁ ∈ K`.

Indeed `‖δ₁‖ ^ 2 = ‖P_K δ₁‖ ^ 2 + ‖P_{Kᗮ} δ₁‖ ^ 2` (Pythagoras), so `hdim K = 1` gives
`P_{Kᗮ} δ₁ = 0` and hence `P_K δ₁ = δ₁`. -/
theorem hdim_one_mem {K : Submodule ℂ (HSum (G := G) 1)} [K.HasOrthogonalProjection]
    (h : hdim K = 1) : hdelta (G := G) 1 0 ∈ K := by
  have hsum : hdim K = ‖K.starProjection (hdelta (G := G) 1 0)‖ ^ 2 := by
    rw [hdim, Fin.sum_univ_one]
  have hP : ‖K.starProjection (hdelta (G := G) 1 0)‖ ^ 2 = 1 := by
    rw [← hsum]; exact h
  have hpyth := Submodule.norm_sq_eq_add_norm_sq_starProjection (hdelta (G := G) 1 0) K
  rw [vnNormSqHdelta, hP] at hpyth
  have hQ : ‖Kᗮ.starProjection (hdelta (G := G) 1 0)‖ ^ 2 = 0 := by linarith
  have hQzero : Kᗮ.starProjection (hdelta (G := G) 1 0) = 0 := by
    rw [← norm_eq_zero]
    exact (pow_eq_zero_iff (n := 2) (by norm_num)).mp hQ
  rw [← Submodule.starProjection_eq_self_iff]
  have hdecomp :=
    Submodule.starProjection_add_starProjection_orthogonal (K := K) (hdelta (G := G) 1 0)
  rw [hQzero, add_zero] at hdecomp
  exact hdecomp

theorem vnFaithful {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] (x : ↥(Work.ORVonNeumann.groupVonNeumann G)) : Work.ORVonNeumann.Rep.hdim ((ContinuousLinearMap.adjoint (Work.ORVonNeumann.Rep.matOp (G := G) (!![x] : Matrix (Fin 1) (Fin 1) (↥(Work.ORVonNeumann.groupVonNeumann G))))).ker) = 1 → x = 0 := by
  intro h
  -- The `1 × 1` matrix operator `matOp !![x]` is left multiplication by `x` on `ℓ²(G)`; its
  -- adjoint is left multiplication by `x⋆` (`vnMatOpAdjoint`).  The single vector `δ₁` sees
  -- this: if `δ₁` lies in the kernel, then `x⋆ δ₁ = 0`, so `x⋆ = 0` (`delta1_separating`).
  have hmem : hdelta (G := G) 1 0 ∈
      (ContinuousLinearMap.adjoint (matOp (G := G)
        (!![x] : Matrix (Fin 1) (Fin 1) (↥(groupVonNeumann G))))).ker := hdim_one_mem h
  have hT0 : (ContinuousLinearMap.adjoint (matOp (G := G)
        (!![x] : Matrix (Fin 1) (Fin 1) (↥(groupVonNeumann G)))))
        (hdelta (G := G) 1 0) = 0 := by
    simpa using hmem
  have h1 : hcoord (G := G) 1 0
      ((ContinuousLinearMap.adjoint (matOp (G := G)
        (!![x] : Matrix (Fin 1) (Fin 1) (↥(groupVonNeumann G)))))
        (hdelta (G := G) 1 0)) = 0 := by
    rw [hT0, map_zero]
  have hentry : ((Matrix.conjTranspose
      (!![x] : Matrix (Fin 1) (Fin 1) (↥(groupVonNeumann G)))) 0 0 :
        ↥(groupVonNeumann G)) = star x := by
    simp [Matrix.conjTranspose_apply]
  rw [vnMatOpAdjoint, hcoord_matOp_apply, Fin.sum_univ_one,
    hentry, hcoord_hdelta, if_pos rfl] at h1
  have hstar : star x = 0 := delta1_separating (star x) h1
  exact star_eq_zero.mp hstar

end Work.ORVonNeumann.Rep
