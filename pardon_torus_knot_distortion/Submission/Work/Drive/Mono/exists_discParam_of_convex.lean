import Mathlib
import Submission.Work.CoreTopology.Disk

namespace Work.Drive.Mono

open Set

/-- A compact convex set in `ℝ²` with non-empty interior is homeomorphic to the closed unit
disc, by a homeomorphism that carries the unit circle onto the frontier.  The map is obtained
by rescaling: the gauge-rescale homeomorphism of `exists_homeomorph_image_eq` straightens `K`
to the unit ball, and the canonical linear isometry `ℂ ≃ₗᵢ[ℝ] ℝ²` identifies the discs. -/
theorem exists_discParam_of_convex (K : Set (EuclideanSpace ℝ (Fin 2))) (hKc : IsCompact K)
    (hK : Convex ℝ K) (hne : (interior K).Nonempty) :
    ∃ e : C(Metric.closedBall (0 : ℂ) 1, EuclideanSpace ℝ (Fin 2)),
      Function.Injective e ∧ Set.range e = K ∧
      Set.range (fun θ : ℝ => e (Work.CoreTopology.circlePoint θ)) = frontier K := by
  obtain ⟨h, _, h2, h3⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hK hne hKc.isBounded
  let φ : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) := Complex.orthonormalBasisOneI.repr
  have hφ0 : φ (0 : ℂ) = 0 := map_zero φ
  have hKcl : closure K = K := hKc.isClosed.closure_eq
  have hhK : h '' K = Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    rw [← hKcl]; exact h2
  have himgC : φ '' Metric.closedBall (0 : ℂ) 1
      = Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    ext y
    simp only [Set.mem_image, Metric.mem_closedBall, dist_zero_right]
    constructor
    · rintro ⟨x, hx, rfl⟩; rwa [φ.norm_map]
    · intro hy; exact ⟨φ.symm y, by rwa [φ.symm.norm_map], φ.apply_symm_apply y⟩
  have himgS : φ '' Metric.sphere (0 : ℂ) 1
      = Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    ext y
    simp only [Set.mem_image, Metric.mem_sphere, dist_zero_right]
    constructor
    · rintro ⟨x, hx, rfl⟩; rwa [φ.norm_map]
    · intro hy; exact ⟨φ.symm y, by rwa [φ.symm.norm_map], φ.apply_symm_apply y⟩
  have hsymmD : h.symm '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 = K := by
    rw [← hhK, Set.image_image]; simp
  have hsymmS : h.symm '' Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 = frontier K := by
    rw [← h3, Set.image_image]; simp
  -- the exponential parametrization sweeps out exactly the unit circle
  have hsphere : Set.range
        (fun θ : ℝ => ((Work.CoreTopology.circlePoint θ : Metric.closedBall (0 : ℂ) 1) : ℂ))
      = Metric.sphere (0 : ℂ) 1 := by
    have hfun : (fun θ : ℝ =>
          ((Work.CoreTopology.circlePoint θ : Metric.closedBall (0 : ℂ) 1) : ℂ))
        = fun θ : ℝ => Complex.exp (θ * Complex.I) := by
      funext θ; rw [Work.CoreTopology.circlePoint_coe]
    rw [hfun]
    ext z
    rw [Set.mem_range, Metric.mem_sphere, dist_zero_right, Complex.norm_eq_one_iff]
  refine ⟨⟨fun z : Metric.closedBall (0 : ℂ) 1 => h.symm (φ (z : ℂ)),
      h.symm.continuous.comp (φ.continuous.comp continuous_subtype_val)⟩, ?_, ?_, ?_⟩
  · intro a b hab
    exact Subtype.ext (φ.injective (h.symm.injective hab))
  · calc Set.range (fun z : Metric.closedBall (0 : ℂ) 1 => h.symm (φ (z : ℂ)))
        = (fun w : ℂ => h.symm (φ w)) '' Metric.closedBall (0 : ℂ) 1 :=
          (Set.image_eq_range (fun w : ℂ => h.symm (φ w)) (Metric.closedBall (0 : ℂ) 1)).symm
      _ = h.symm '' (φ '' Metric.closedBall (0 : ℂ) 1) := (Set.image_image h.symm φ _).symm
      _ = h.symm '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by rw [himgC]
      _ = K := hsymmD
  · calc Set.range (fun θ : ℝ =>
          h.symm (φ ((Work.CoreTopology.circlePoint θ : Metric.closedBall (0 : ℂ) 1) : ℂ)))
        = (fun w : ℂ => h.symm (φ w)) '' Set.range (fun θ : ℝ =>
            ((Work.CoreTopology.circlePoint θ : Metric.closedBall (0 : ℂ) 1) : ℂ)) :=
          Set.range_comp (fun w : ℂ => h.symm (φ w))
            (fun θ : ℝ => ((Work.CoreTopology.circlePoint θ : Metric.closedBall (0 : ℂ) 1) : ℂ))
      _ = (fun w : ℂ => h.symm (φ w)) '' Metric.sphere (0 : ℂ) 1 := by rw [hsphere]
      _ = h.symm '' (φ '' Metric.sphere (0 : ℂ) 1) := (Set.image_image h.symm φ _).symm
      _ = h.symm '' Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by rw [himgS]
      _ = frontier K := hsymmS

end Work.Drive.Mono
