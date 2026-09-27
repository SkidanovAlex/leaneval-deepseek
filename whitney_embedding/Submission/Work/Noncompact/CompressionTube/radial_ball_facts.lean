import Mathlib

namespace Work.Noncompact.CompressionTube

open Real

noncomputable section

/-- The map `u ↦ (√(1 + ‖u‖²))⁻¹ • u` is the "radial compression" identifying `ℝ^m` with the open
unit ball.  It is smooth, injective, lands in the open unit ball, fixes `0`, and at every point its
derivative is surjective (indeed invertible): it is the `OpenPartialHomeomorph.univUnitBall` of
Mathlib. -/
theorem radial_ball_facts (m : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : EuclideanSpace ℝ (Fin m) => (Real.sqrt (1 + ‖u‖ ^ 2))⁻¹ • u) ∧ Function.Injective (fun u : EuclideanSpace ℝ (Fin m) => (Real.sqrt (1 + ‖u‖ ^ 2))⁻¹ • u) ∧ (∀ u : EuclideanSpace ℝ (Fin m), ‖(Real.sqrt (1 + ‖u‖ ^ 2))⁻¹ • u‖ < 1) ∧ ((fun u : EuclideanSpace ℝ (Fin m) => (Real.sqrt (1 + ‖u‖ ^ 2))⁻¹ • u) 0 = 0) ∧ (∀ u : EuclideanSpace ℝ (Fin m), Function.Surjective (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin m) => (Real.sqrt (1 + ‖u‖ ^ 2))⁻¹ • u) u)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h := OpenPartialHomeomorph.contDiff_univUnitBall (E := EuclideanSpace ℝ (Fin m)) (n := ⊤)
    simpa only [← OpenPartialHomeomorph.univUnitBall_apply] using h
  · apply Function.LeftInverse.injective
      (g := fun y : EuclideanSpace ℝ (Fin m) => OpenPartialHomeomorph.univUnitBall.symm y)
    intro x
    exact OpenPartialHomeomorph.left_inv _ (by trivial)
  · intro u
    have h := OpenPartialHomeomorph.map_source OpenPartialHomeomorph.univUnitBall
      (x := u) (by trivial)
    rw [OpenPartialHomeomorph.univUnitBall_target] at h
    exact mem_ball_zero_iff.mp h
  · simp
  · intro u
    have hfu_ball : (OpenPartialHomeomorph.univUnitBall (u : EuclideanSpace ℝ (Fin m)))
        ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1 := by
      have h := OpenPartialHomeomorph.map_source OpenPartialHomeomorph.univUnitBall
        (x := u) (by trivial)
      rwa [OpenPartialHomeomorph.univUnitBall_target] at h
    have hgd : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin m) =>
          OpenPartialHomeomorph.univUnitBall.symm y)
        (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin m) => OpenPartialHomeomorph.univUnitBall.symm y)
          (OpenPartialHomeomorph.univUnitBall u))
        (OpenPartialHomeomorph.univUnitBall u) :=
      (((OpenPartialHomeomorph.contDiffOn_univUnitBall_symm
          (E := EuclideanSpace ℝ (Fin m)) (n := ⊤)).contDiffAt
        (Metric.isOpen_ball.mem_nhds hfu_ball)).differentiableAt (by simp)).hasFDerivAt
    have hfd : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin m) =>
          OpenPartialHomeomorph.univUnitBall y)
        (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin m) => OpenPartialHomeomorph.univUnitBall y)
          (OpenPartialHomeomorph.univUnitBall.symm (OpenPartialHomeomorph.univUnitBall u)))
        (OpenPartialHomeomorph.univUnitBall.symm (OpenPartialHomeomorph.univUnitBall u)) :=
      (((OpenPartialHomeomorph.contDiff_univUnitBall
          (E := EuclideanSpace ℝ (Fin m)) (n := ⊤)).contDiffAt).differentiableAt (by simp)).hasFDerivAt
    have hchain : HasFDerivAt
        ((fun y : EuclideanSpace ℝ (Fin m) => OpenPartialHomeomorph.univUnitBall y) ∘
          (fun y : EuclideanSpace ℝ (Fin m) => OpenPartialHomeomorph.univUnitBall.symm y))
        ((fderiv ℝ (fun y : EuclideanSpace ℝ (Fin m) => OpenPartialHomeomorph.univUnitBall y)
            (OpenPartialHomeomorph.univUnitBall.symm (OpenPartialHomeomorph.univUnitBall u))).comp
          (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin m) => OpenPartialHomeomorph.univUnitBall.symm y)
            (OpenPartialHomeomorph.univUnitBall u)))
        (OpenPartialHomeomorph.univUnitBall u) :=
      hfd.comp _ hgd
    have hev : ((fun y : EuclideanSpace ℝ (Fin m) => OpenPartialHomeomorph.univUnitBall y) ∘
        (fun y : EuclideanSpace ℝ (Fin m) => OpenPartialHomeomorph.univUnitBall.symm y))
        =ᶠ[nhds (OpenPartialHomeomorph.univUnitBall u)] id := by
      refine Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hfu_ball) ?_
      intro y hy
      exact OpenPartialHomeomorph.right_inv _ hy
    have hid : HasFDerivAt
        ((fun y : EuclideanSpace ℝ (Fin m) => OpenPartialHomeomorph.univUnitBall y) ∘
          (fun y : EuclideanSpace ℝ (Fin m) => OpenPartialHomeomorph.univUnitBall.symm y))
        (1 : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
        (OpenPartialHomeomorph.univUnitBall u) :=
      (hasFDerivAt_id _).congr_of_eventuallyEq hev
    have hL := hchain.unique hid
    rw [OpenPartialHomeomorph.left_inv _
      (show u ∈ OpenPartialHomeomorph.univUnitBall.source by trivial)] at hL
    intro w
    refine ⟨(fderiv ℝ (fun y : EuclideanSpace ℝ (Fin m) => OpenPartialHomeomorph.univUnitBall.symm y)
      (OpenPartialHomeomorph.univUnitBall u)) w, ?_⟩
    change (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin m) => OpenPartialHomeomorph.univUnitBall y) u)
      ((fderiv ℝ (fun y : EuclideanSpace ℝ (Fin m) => OpenPartialHomeomorph.univUnitBall.symm y)
        (OpenPartialHomeomorph.univUnitBall u)) w) = w
    rw [← ContinuousLinearMap.comp_apply, hL]
    simp

end

end Work.Noncompact.CompressionTube
