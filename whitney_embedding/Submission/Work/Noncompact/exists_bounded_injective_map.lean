import Mathlib

namespace Work.Noncompact

open scoped Manifold ContDiff

open Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The partial homeomorphism `OpenPartialHomeomorph.univUnitBall : E → E`,
`y ↦ (√(1 + ‖y‖²))⁻¹ • y`, is smooth. -/
theorem contMDiff_univUnitBall :
    ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞
      (OpenPartialHomeomorph.univUnitBall : E → E) := by
  rw [contMDiff_iff_contDiff]
  exact OpenPartialHomeomorph.contDiff_univUnitBall

/-- `OpenPartialHomeomorph.univUnitBall` is injective. -/
theorem injective_univUnitBall :
    Function.Injective (OpenPartialHomeomorph.univUnitBall : E → E) := by
  have hleft : Function.LeftInverse
      (((OpenPartialHomeomorph.univUnitBall : OpenPartialHomeomorph E E).symm : E → E))
      ((OpenPartialHomeomorph.univUnitBall : E → E)) := by
    intro x
    exact OpenPartialHomeomorph.left_inv _ (by
      rw [OpenPartialHomeomorph.univUnitBall_source]; exact Set.mem_univ x)
  exact hleft.injective

/-- `OpenPartialHomeomorph.univUnitBall` takes values in the closed unit ball. -/
theorem norm_univUnitBall_le_one (y : E) :
    ‖(OpenPartialHomeomorph.univUnitBall : E → E) y‖ ≤ 1 := by
  have h : (OpenPartialHomeomorph.univUnitBall : E → E) y ∈
      (OpenPartialHomeomorph.univUnitBall : OpenPartialHomeomorph E E).target :=
    OpenPartialHomeomorph.map_source _ (x := y) (by
      rw [OpenPartialHomeomorph.univUnitBall_source]; exact Set.mem_univ y)
  rw [OpenPartialHomeomorph.univUnitBall_target, Metric.mem_ball, dist_eq_norm, sub_zero] at h
  exact le_of_lt h

/-- The differential of `OpenPartialHomeomorph.univUnitBall` is injective everywhere.  This is
proved by differentiating its smooth two-sided inverse `z ↦ (√(1 - ‖z‖²))⁻¹ • z` (which is smooth
on the open unit ball, and the value of `univUnitBall` always lies there). -/
theorem fderiv_univUnitBall_injective (y : E) :
    Function.Injective (fderiv ℝ (OpenPartialHomeomorph.univUnitBall : E → E) y) := by
  intro u v huv
  have hsrc : ∀ x : E,
      x ∈ (OpenPartialHomeomorph.univUnitBall : OpenPartialHomeomorph E E).source := by
    intro x; rw [OpenPartialHomeomorph.univUnitBall_source]; exact Set.mem_univ x
  have hGy : (OpenPartialHomeomorph.univUnitBall : E → E) y ∈ ball (0 : E) 1 := by
    have h := OpenPartialHomeomorph.map_source
      (OpenPartialHomeomorph.univUnitBall : OpenPartialHomeomorph E E) (x := y) (hsrc y)
    rwa [OpenPartialHomeomorph.univUnitBall_target] at h
  have hH : ContDiffOn ℝ ∞
      (((OpenPartialHomeomorph.univUnitBall : OpenPartialHomeomorph E E).symm : E → E))
      (ball 0 1) := OpenPartialHomeomorph.contDiffOn_univUnitBall_symm
  have hdiffH : DifferentiableAt ℝ
      (((OpenPartialHomeomorph.univUnitBall : OpenPartialHomeomorph E E).symm : E → E))
      ((OpenPartialHomeomorph.univUnitBall : E → E) y) :=
    (hH.contDiffAt (isOpen_ball.mem_nhds hGy)).differentiableAt (by simp)
  have hdiffG : DifferentiableAt ℝ (OpenPartialHomeomorph.univUnitBall : E → E) y :=
    (OpenPartialHomeomorph.contDiff_univUnitBall (E := E) :
        ContDiff ℝ ∞ (OpenPartialHomeomorph.univUnitBall : E → E)).differentiable (by simp) y
  have hfun :
      (((OpenPartialHomeomorph.univUnitBall : OpenPartialHomeomorph E E).symm : E → E)) ∘
        ((OpenPartialHomeomorph.univUnitBall : E → E)) = id := by
    funext x; exact OpenPartialHomeomorph.left_inv _ (hsrc x)
  have key :
      (fderiv ℝ (((OpenPartialHomeomorph.univUnitBall : OpenPartialHomeomorph E E).symm :
            E → E)) ((OpenPartialHomeomorph.univUnitBall : E → E) y)).comp
          (fderiv ℝ (OpenPartialHomeomorph.univUnitBall : E → E) y) =
        ContinuousLinearMap.id ℝ E := by
    rw [← fderiv_comp y hdiffH hdiffG, hfun, fderiv_id]
  have h1 := congrArg (fun L : E →L[ℝ] E => L u) key
  have h2 := congrArg (fun L : E →L[ℝ] E => L v) key
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h1 h2
  rw [← h1, ← h2, huv]

/-- The manifold derivative of `OpenPartialHomeomorph.univUnitBall` is injective everywhere. -/
theorem mfderiv_univUnitBall_injective (y : E) :
    Function.Injective
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E))
        (OpenPartialHomeomorph.univUnitBall : E → E) y) := by
  rw [mfderiv_eq_fderiv]
  exact fderiv_univUnitBall_injective y

/-- There is a smooth self-map of `ℝ^N` that is injective, has injective derivative everywhere and
takes values in the closed unit ball.  Witness: `g y = (√(1 + ‖y‖²))⁻¹ • y`, whose inverse
`z ↦ (√(1 - ‖z‖²))⁻¹ • z` is smooth on the open unit ball; derive smoothness of `g` and injectivity
of `mfderiv g y` (via the chain rule applied to a smooth left inverse) from that. -/
theorem exists_bounded_injective_map (N : ℕ) :
    ∃ g : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N),
      ContMDiff (𝓡 N) (𝓡 N) ∞ g ∧ Function.Injective g ∧
      (∀ y, Function.Injective (mfderiv (𝓡 N) (𝓡 N) g y)) ∧ ∀ y, ‖g y‖ ≤ 1 := by
  refine ⟨(OpenPartialHomeomorph.univUnitBall :
      EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)), ?_, ?_, ?_, ?_⟩
  · exact contMDiff_univUnitBall
  · exact injective_univUnitBall
  · exact fun y => mfderiv_univUnitBall_injective y
  · exact fun y => norm_univUnitBall_le_one y

end Work.Noncompact
