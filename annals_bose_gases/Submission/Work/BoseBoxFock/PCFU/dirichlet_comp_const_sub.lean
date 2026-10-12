import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

open MeasureTheory

/-- The (pointwise) derivative of the reflected function `u ↦ F (c - u)`: by the chain rule the
reflection `u ↦ c - u` contributes the linear map `-1`, so

    `fderiv ℝ (fun u => F (c - u)) u = -(fderiv ℝ F (c - u))`. -/
private lemma fderiv_comp_const_sub {F : EuclideanSpace ℝ (Fin 3) → ℂ} (hF : ContDiff ℝ 1 F)
    (c u : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (fun u : EuclideanSpace ℝ (Fin 3) => F (c - u)) u
      = -(fderiv ℝ F (c - u)) := by
  have h1 : HasFDerivAt (fun u : EuclideanSpace ℝ (Fin 3) => c - u)
      (-(1 : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))) u := by
    fun_prop
  have hFd : HasFDerivAt F (fderiv ℝ F (c - u)) (c - u) :=
    (hF.contDiffAt (x := c - u)).differentiableAt_one.hasFDerivAt
  have hd : HasFDerivAt (fun u : EuclideanSpace ℝ (Fin 3) => F (c - u))
      ((fderiv ℝ F (c - u)).comp
        (-(1 : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)))) u := by
    simpa [Function.comp_def] using hFd.comp u h1
  rw [hd.fderiv]
  ext x
  simp

/-- **Change of variables `u ↦ c - u` for the Dirichlet energy.**  The reflection
`u ↦ c - u` of the argument of a `C¹` function `F` preserves the full-space integral of the
squared norm of the directional derivative in any fixed coordinate direction.  Indeed the
reflection has derivative `-1`, so the integrands agree pointwise up to sign, and the reflection
is a measure preserving transformation of `ℝ³` (`volume` is both left-translation and negation
invariant). -/
theorem dirichlet_comp_const_sub {F : EuclideanSpace ℝ (Fin 3) → ℂ} (hF : ContDiff ℝ 1 F)
    (c : EuclideanSpace ℝ (Fin 3)) (j : Fin 3) :
    (∫ u : EuclideanSpace ℝ (Fin 3),
        ‖fderiv ℝ (fun u => F (c - u)) u (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
      = ∫ v : EuclideanSpace ℝ (Fin 3),
          ‖fderiv ℝ F v (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
  -- pointwise identification of the integrands
  have hpt : ∀ u : EuclideanSpace ℝ (Fin 3),
      fderiv ℝ (fun u : EuclideanSpace ℝ (Fin 3) => F (c - u)) u
          (EuclideanSpace.single j (1 : ℝ))
        = - fderiv ℝ F (c - u) (EuclideanSpace.single j (1 : ℝ)) := by
    intro u
    rw [fderiv_comp_const_sub hF c u]
    simp
  have hfun : (fun u : EuclideanSpace ℝ (Fin 3) =>
        ‖fderiv ℝ (fun u : EuclideanSpace ℝ (Fin 3) => F (c - u)) u
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
      = fun u : EuclideanSpace ℝ (Fin 3) =>
          ‖fderiv ℝ F (c - u) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
    funext u
    rw [hpt u, norm_neg]
  rw [hfun]
  -- and the change of variables `v = c - u`
  exact integral_sub_left_eq_self
    (fun v : EuclideanSpace ℝ (Fin 3) =>
      ‖fderiv ℝ F v (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) volume c

end Work.BoseBoxFock.PCFU
