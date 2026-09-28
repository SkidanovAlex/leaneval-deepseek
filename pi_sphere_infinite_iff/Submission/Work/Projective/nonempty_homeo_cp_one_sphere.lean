import Mathlib
import Submission.Work.Projective.Basic
import Submission.Work.Projective.Atlas
import Submission.Work.Projective.Hopf

set_option synthInstance.maxHeartbeats 400000

/-!
# `ℂP¹ ≅ S²`

The complex projective line `ℂP¹` (with the quotient topology of `Work.Projective.Basic`) is
homeomorphic to the unit sphere `S² ⊆ ℝ³`.  The homeomorphism is the explicit "Hopf-type" map
`hopfProj` of `Work.Projective.Hopf` (continuous by `continuous_hopfProj`), and its inverse is the
stereographic parametrisation `sphereToCP` defined below:

* `(x, y, z) ↦ [x + i y : 1 + z]` away from the south pole,
* the south pole `(0, 0, -1) ↦ [1 : 0]`.

The two round trips are `sphereToCP_hopfProj` (the fibre computation: `hopfZ v = (v 0/v 1)(1 +
hopfW v)`) and `hopfProj_sphereToCP` (the inverse chart computation `hopfPt_cover`).  Compactness of
`ℂP¹` (`Work.Projective.compactSpace_CP`) and Hausdorffness of the sphere then turn the continuous
bijection into a homeomorphism via `Continuous.homeoOfEquivCompactToT2`.
-/

open scoped LinearAlgebra.Projectivization Manifold ContDiff Topology

namespace Work.Projective

noncomputable section

/-! ## The inverse map -/

/-- **The inverse of `hopfProj`**: stereographic coordinates, `(x, y, z) ↦ [x + iy : 1 + z]`
(and `[1 : 0]` at the south pole `z = -1`). -/
def sphereToCP (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : CP 1 :=
  if (x : EuclideanSpace ℝ (Fin 3)) 2 = -1 then
    cpMk 1 ⟨![1, 0], fun h => by
      have := congrFun h 0; simp at this⟩
  else
    cpMk 1 ⟨![(((x : EuclideanSpace ℝ (Fin 3)) 0 : ℂ)
        + (((x : EuclideanSpace ℝ (Fin 3)) 1 : ℂ)) * Complex.I)
        / (1 + ((x : EuclideanSpace ℝ (Fin 3)) 2 : ℂ)), 1], fun h => by
      have := congrFun h 1; simp at this⟩

/-! ## The two round trips -/

/-- **The south pole case**: `hopfProj` maps `[1 : 0]` (which is `sphereToCP` of the south pole) to
the south pole. -/
theorem hopfProj_sphereToCP (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    hopfProj (sphereToCP x) = x := by
  have hx : ‖(x : EuclideanSpace ℝ (Fin 3))‖ ^ 2 = 1 := by
    have h := x.2
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at h
    rw [h]
    norm_num
  have hx3 : (x : EuclideanSpace ℝ (Fin 3)) 0 ^ 2 + (x : EuclideanSpace ℝ (Fin 3)) 1 ^ 2
      + (x : EuclideanSpace ℝ (Fin 3)) 2 ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq] at hx
    simpa [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs] using hx
  by_cases h2 : (x : EuclideanSpace ℝ (Fin 3)) 2 = -1
  · have h0 : (x : EuclideanSpace ℝ (Fin 3)) 0 = 0 := by nlinarith [hx3]
    have h1 : (x : EuclideanSpace ℝ (Fin 3)) 1 = 0 := by nlinarith [hx3]
    rw [sphereToCP, if_pos h2, hopfProj_cpMk]
    refine Subtype.ext ?_
    change hopfPt ![1, 0] = (x : EuclideanSpace ℝ (Fin 3))
    rw [hopfPt_zero_cons]
    rw [show (x : EuclideanSpace ℝ (Fin 3)) =
        WithLp.toLp 2 ![(x : EuclideanSpace ℝ (Fin 3)) 0, (x : EuclideanSpace ℝ (Fin 3)) 1,
          (x : EuclideanSpace ℝ (Fin 3)) 2] from by ext i; fin_cases i <;> rfl, h0, h1, h2]
  · rw [sphereToCP, if_neg h2, hopfProj_cpMk]
    refine Subtype.ext ?_
    exact hopfPt_cover (x : EuclideanSpace ℝ (Fin 3)) hx3 h2

/-- **The fibre computation**: `sphereToCP` inverts `hopfProj`.  On the point `[v₀ : v₁]` this is
the identity `hopfZ v = (v 0 / v 1) * (1 + hopfW v)` (`hopfZ_eq_ratio_mul`). -/
theorem sphereToCP_hopfProj (p : CP 1) : sphereToCP (hopfProj p) = p := by
  obtain ⟨v, rfl⟩ := cpMk_surjective 1 p
  rw [hopfProj_cpMk]
  by_cases h1 : v.1 1 = 0
  · have hW1 : hopfW v.1 = -1 := hopfW_eq_neg_one_of_second_eq_zero v.2 h1
    have hif : (hopfSphere v : EuclideanSpace ℝ (Fin 3)) 2 = -1 := by
      simp only [hopfSphere, hopfPt_apply_2, hW1]
    rw [sphereToCP, if_pos hif]
    refine (cpMk_eq_iff 1 _ v).mpr ⟨(v.1 0)⁻¹, ?_⟩
    have hv0 : v.1 0 ≠ 0 := fun h0 => v.2 (funext fun i => by fin_cases i <;> simp_all)
    funext i
    fin_cases i <;> simp [h1, hv0, Pi.smul_apply, smul_eq_mul]
  · have hWne : hopfW v.1 ≠ -1 := by
      have := one_add_hopfW_pos h1
      intro hc
      rw [hc] at this
      norm_num at this
    have hif : (hopfSphere v : EuclideanSpace ℝ (Fin 3)) 2 ≠ -1 := by
      simp only [hopfSphere, hopfPt_apply_2]
      exact hWne
    rw [sphereToCP, if_neg hif]
    have hne := one_add_hopfW_ne_zero h1
    have hw : ((((hopfSphere v : EuclideanSpace ℝ (Fin 3)) 0 : ℂ)
          + (((hopfSphere v : EuclideanSpace ℝ (Fin 3)) 1 : ℂ)) * Complex.I)
        / (1 + ((hopfSphere v : EuclideanSpace ℝ (Fin 3)) 2 : ℂ))) = v.1 0 / v.1 1 := by
      simp only [hopfSphere, hopfPt_apply_0, hopfPt_apply_1, hopfPt_apply_2]
      rw [Complex.re_add_im, hopfZ_eq_ratio_mul h1]
      field_simp
    refine (cpMk_eq_iff 1 _ v).mpr ⟨(v.1 1)⁻¹, ?_⟩
    funext i
    fin_cases i
    · show (v.1 1)⁻¹ * v.1 0 = _
      rw [show (v.1 1)⁻¹ * v.1 0 = v.1 0 / v.1 1 by rw [div_eq_mul_inv, mul_comm], ← hw]
      simp
    · show (v.1 1)⁻¹ * v.1 1 = _
      rw [inv_mul_cancel₀ h1]
      simp

/-! ## The homeomorphism -/

/-- The bijection `ℂP¹ ≃ S²` underlying the homeomorphism. -/
def hopfEquiv : CP 1 ≃ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 where
  toFun := hopfProj
  invFun := sphereToCP
  left_inv := sphereToCP_hopfProj
  right_inv := hopfProj_sphereToCP

theorem nonempty_homeo_cp_one_sphere :
    Nonempty (CP 1 ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  have hcomp : CompactSpace (CP 1) := compactSpace_CP 1
  exact ⟨@Continuous.homeoOfEquivCompactToT2 _ _ _ _ hcomp _ hopfEquiv continuous_hopfProj⟩

end

end Work.Projective
