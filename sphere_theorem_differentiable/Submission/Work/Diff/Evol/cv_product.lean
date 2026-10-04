import Mathlib
import Submission.Work.Diff.Evol.cv_prelim
import Submission.Work.Diff.Evol.cv_section
import Submission.Work.Diff.Evol.cv_dLC
import Submission.Work.Diff.GE.curv_var_prelim

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The derivative of the pairing of the composed connection

`cv_Rj_deriv`: for fixed smooth fields `X`, `Y`, `Z` and a smooth field `Fj`, the curve
`s ↦ (G s)⟨∇^{G s}_X(∇^{G s}_Y Z), Fj⟩(x)` has an explicit derivative; the derivative is packaged
as the `noncomputable def cv_RjPrime`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.Diff.Evol

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M]

/-- The value of the derivative of `s ↦ (G s)⟨∇^{G s}_X(∇^{G s}_Y Z), Fj⟩(x)`. -/
noncomputable def cv_RjPrime (G : ℝ → SMet I M) (t₀ : ℝ)
    (X Y Z Fj : Π y : M, TangentSpace I y) (x : M) : ℝ :=
  mvfderiv I (fun y : M ↦ dtMet G t₀ y (lcOf (G t₀) Z y (Y y)) (Fj y)
      + (G t₀).inner y (dLC G t₀ Y Z y) (Fj y)) x (X x)
    - (dtMet G t₀ x (lcOf (G t₀) Z x (Y x)) (lcOf (G t₀) Fj x (X x))
      + (G t₀).inner x (dLC G t₀ Y Z x) (lcOf (G t₀) Fj x (X x))
      + (G t₀).inner x (lcOf (G t₀) Z x (Y x)) (dLC G t₀ X Fj x))

/-- **Derivative of the pairing of the composed connection.** -/
theorem cv_Rj_deriv
    (hLC : LCSmooth I M) (hLV : LCVariation I M)
    {G : ℝ → SMet I M} {J : Set ℝ} (hJopen : IsOpen J) (hJs : JointSmooth G J)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (X Y Z : Π y : M, TangentSpace I y) (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y))
    (hZ : CMDiff ∞ (T% Z)) (x : M)
    (Fj : Π y : M, TangentSpace I y) (hFj : CMDiff ∞ (T% Fj)) :
    HasDerivAt (fun s : ℝ ↦ (G s).inner x
        (lcOf (G s) (fun y : M ↦ lcOf (G s) Z y (Y y)) x (X x)) (Fj x))
      (cv_RjPrime G t₀ X Y Z Fj x) t₀ := by
  classical
  -- the joint smoothness of the pairing family
  have hjoint : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ (G p.1).inner p.2 (lcOf (G p.1) Z p.2 (Y p.2)) (Fj p.2)) (t₀, x) :=
    cv_lcOf_pairing_joint (I := I) (M := M) hJopen hJs ht₀ Y Z Fj hY hZ hFj x
  -- Clairaut: the derivative of the `mvfderiv` term
  have hcl := clairaut_mvfderiv (I := I) (M := M)
    (Φ := fun s y ↦ (G s).inner y (lcOf (G s) Z y (Y y)) (Fj y)) (t₀ := t₀) (x := x)
    (v := X x) hjoint
  have hinner : (fun y : M ↦
        deriv (fun s : ℝ ↦ (G s).inner y (lcOf (G s) Z y (Y y)) (Fj y)) t₀)
      = fun y : M ↦ dtMet G t₀ y (lcOf (G t₀) Z y (Y y)) (Fj y)
          + (G t₀).inner y (dLC G t₀ Y Z y) (Fj y) := by
    funext y
    exact HasDerivAt.deriv (Work.Diff.T.hasDerivAt_metric_inner_moving (G := G) (J := J)
      (x := y) hJopen hJs ht₀
      (Work.Diff.GE.hasDerivAt_lcOf_fixed (I := I) (M := M) hLV hJopen hJs ht₀ hY hZ y) (Fj y))
  have h1 : HasDerivAt (fun s : ℝ ↦
        mvfderiv I (fun y : M ↦ (G s).inner y (lcOf (G s) Z y (Y y)) (Fj y)) x (X x))
      (mvfderiv I (fun y : M ↦ dtMet G t₀ y (lcOf (G t₀) Z y (Y y)) (Fj y)
          + (G t₀).inner y (dLC G t₀ Y Z y) (Fj y)) x (X x)) t₀ := by
    rw [hinner] at hcl
    exact hcl
  -- the product rule for the second term
  have hFd : HasDerivAt (fun s : ℝ ↦ lcOf (G s) Z x (Y x)) (dLC G t₀ Y Z x) t₀ :=
    Work.Diff.GE.hasDerivAt_lcOf_fixed (I := I) (M := M) hLV hJopen hJs ht₀ hY hZ x
  have hHd : HasDerivAt (fun s : ℝ ↦ lcOf (G s) Fj x (X x)) (dLC G t₀ X Fj x) t₀ :=
    Work.Diff.GE.hasDerivAt_lcOf_fixed (I := I) (M := M) hLV hJopen hJs ht₀ hX hFj x
  have h2 : HasDerivAt (fun s : ℝ ↦
        (G s).inner x (lcOf (G s) Z x (Y x)) (lcOf (G s) Fj x (X x)))
      (dtMet G t₀ x (lcOf (G t₀) Z x (Y x)) (lcOf (G t₀) Fj x (X x))
        + (G t₀).inner x (dLC G t₀ Y Z x) (lcOf (G t₀) Fj x (X x))
        + (G t₀).inner x (lcOf (G t₀) Z x (Y x)) (dLC G t₀ X Fj x)) t₀ :=
    cv_metric_inner_moving_pair (I := I) (M := M) hJopen hJs ht₀ hFd hHd
  -- the metric-compatibility identity, pointwise in `s`
  have hk : ∀ s : ℝ, (G s).inner x
        (lcOf (G s) (fun y : M ↦ lcOf (G s) Z y (Y y)) x (X x)) (Fj x)
      = mvfderiv I (fun y : M ↦ (G s).inner y (lcOf (G s) Z y (Y y)) (Fj y)) x (X x)
        - (G s).inner x (lcOf (G s) Z x (Y x)) (lcOf (G s) Fj x (X x)) := fun s ↦
    Work.Diff.GE.lcOf_metric_pairing (I := I) (M := M) hLC (G s) hX
      (cv_lcOf_arg_smooth (I := I) (M := M) hLC (G s) hY hZ) hFj x
  refine (h1.sub h2).congr_deriv ?_ |>.congr_of_eventuallyEq ?_
  · simp only [cv_RjPrime]
  · filter_upwards with s
    exact hk s

end Work.Diff.Evol
