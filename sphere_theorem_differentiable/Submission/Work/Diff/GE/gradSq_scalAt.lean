import Mathlib
import Submission.Work.Diff.GE.gradSq_rmoNormSq
import Submission.Work.Diff.GE.rot_invariance

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## The linearity of `scalAlg`

`scalAlg R = ∑ᵢⱼ Rᵢⱼᵢⱼ` is linear in the curvature array, so its Fréchet derivative at `R`,
evaluated on the array `A`, is `∑ᵢⱼ Aᵢⱼᵢⱼ`.  This is the chain-rule ingredient in the
computation of the derivative of `y ↦ scalAlg (rmFrame g y (Ef · y))`. -/

/-- The Fréchet derivative of the linear functional `R ↦ ∑ᵢⱼ Rᵢⱼᵢⱼ`. -/
lemma hasFDerivAt_scalAlg_sum {n : ℕ} (R : Curv4 n) :
    HasFDerivAt (fun X : Curv4 n => ∑ i, ∑ j, X i j i j) (∑ i, ∑ j, projC4 i j i j) R := by
  have h := (∑ i, ∑ j, projC4 i j i j).hasFDerivAt (x := R)
  rw [show (⇑(∑ i, ∑ j, projC4 i j i j) : Curv4 n → ℝ) = fun X => ∑ i, ∑ j, X i j i j from by
    funext X; simp only [_root_.sum_apply, projC4_apply]] at h
  exact h

/-- The Fréchet derivative of `scalAlg` at `R`, evaluated on `A`. -/
theorem fderiv_scalAlg {n : ℕ} (R A : Curv4 n) :
    fderiv ℝ scalAlg R A = ∑ i, ∑ j, A i j i j := by
  have h : scalAlg = fun X : Curv4 n => ∑ i, ∑ j, X i j i j := rfl
  rw [h, (hasFDerivAt_scalAlg_sum R).fderiv]
  simp only [_root_.sum_apply, projC4_apply]

/-- `scalAlg` is differentiable (it is linear). -/
theorem differentiableAt_scalAlg {n : ℕ} (R : Curv4 n) : DifferentiableAt ℝ scalAlg R := by
  have h : scalAlg = fun X : Curv4 n => ∑ i, ∑ j, X i j i j := rfl
  rw [h]
  exact (hasFDerivAt_scalAlg_sum R).differentiableAt

/-! ## Frame independence of the scalar curvature

`scalAt g y = scalAlg (rmFrame g y (onFrame g y))` is computed with the `Classical.epsilon`-chosen
frame `onFrame g y`, which is not known to be smooth in `y`.  Two `g`-orthonormal frames at `y`
differ by an orthogonal matrix (`Work.Diff.GE.onFrame_orthogonal_change`), the curvature components
change by `rot A` (`Work.Diff.GE.rmFrame_eq_rot`) and `scalAlg` is `rot A`-invariant
(`Work.Diff.GE.rot_invariance`); hence the value is the same in every orthonormal frame, and
`scalAt g` agrees near `x` with the smooth expression computed in a smooth orthonormal frame
*field*. -/

/-- `scalAlg (rmFrame g x e)` does not depend on the choice of `g`-orthonormal frame `e`. -/
theorem scalAlg_rmFrame_eq_of_isONFrame (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (e e' : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (he : IsONFrame g x e) (he' : IsONFrame g x e') :
    scalAlg (rmFrame g x e) = scalAlg (rmFrame g x e') := by
  obtain ⟨A, hA, hAe⟩ := onFrame_orthogonal_change g x e e' he he'
  rw [rmFrame_eq_rot hLC g x e e' A hAe]
  exact (rot_invariance A hA (rmFrame g x e)).1.symm

/-- Near `x`, the frozen `scalAt g` agrees with the expression computed in the frame field `Ef`. -/
theorem scalAt_eventuallyEq_scalAlg_rmFrameField (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (Ef : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (hON : ∀ᶠ y in 𝓝 x, IsONFrame g y (fun i => Ef i y)) :
    scalAt g =ᶠ[𝓝 x] fun y => scalAlg (rmFrame g y (fun i => Ef i y)) := by
  filter_upwards [hON] with y hy
  show scalAlg (rmFrame g y (onFrame g y)) = scalAlg (rmFrame g y (fun i => Ef i y))
  exact scalAlg_rmFrame_eq_of_isONFrame hLC g y (onFrame g y) (fun i => Ef i y)
    (isONFrame_onFrame g y) hy

/-! ## The derivative of the scalar curvature in a geodesic frame field -/

/-- **The derivative of `scalAt` is the trace of `∇Rm`.**  For a geodesic frame field `Ef` (globally
smooth, `g`-orthonormal near `x`, `Ef i x = onFrame g x i`, and `∇_v Ef i = 0` for every
`v = Ef m x`), the derivative of `scalAt g` at `x` in the direction `e_m = onFrame g x m` is the
trace `∑ᵢⱼ (∇_m Rm)(eᵢ,eⱼ,eᵢ,eⱼ)` of `∇Rm`.

Route: `scalAt g` agrees near `x` with the smooth function `y ↦ scalAlg (rmFrame g y (Ef · y))`
(frame independence), so the derivative may be computed with the latter.  Its derivative is the
chain rule applied to `y ↦ RmArray(y)` — whose derivative is the array of `covRm`, the four
frame-rotation corrections being killed by geodesicity at `x`
(`Work.Diff.GE.mvfderiv_rmFrameField_eq_covRm`) — and to the linear functional `scalAlg`
(`Work.Diff.GE.fderiv_scalAlg`). -/
theorem mvfderiv_scalAt_eq_sum (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (Ef : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (hEf : ∀ i, Rxn.SmoothField (fun y : M => Ef i y))
    (hON : ∀ᶠ y in 𝓝 x, IsONFrame g y (fun i => Ef i y))
    (hx : ∀ i, Ef i x = onFrame g x i)
    (hconn : ∀ (i m : Fin (Module.finrank ℝ E)),
      lcOf g (fun y : M => Ef i y) x (onFrame g x m) = 0)
    (m : Fin (Module.finrank ℝ E)) :
    mvfderiv I (scalAt g) x (onFrame g x m)
      = ∑ i, ∑ j,
          covRm g x (onFrame g x m) (onFrame g x i) (onFrame g x j) (onFrame g x i)
            (onFrame g x j) := by
  let W : Π y : M, Fin (Module.finrank ℝ E) → TangentSpace I y := fun y i => Ef i y
  have hWsm : ∀ i, Rxn.SmoothField (fun y : M => W y i) := fun i => hEf i
  have hWON : ∀ᶠ y in 𝓝 x, IsONFrame g y (W y) := hON
  have hWx : ∀ i, W x i = onFrame g x i := fun i => hx i
  -- localise `scalAt g`
  have hev : scalAt g =ᶠ[𝓝 x] fun y : M => scalAlg (Rxn.rmFrameField g W y) := by
    filter_upwards [scalAt_eventuallyEq_scalAlg_rmFrameField (I := I) (M := M) hLC g x Ef hON]
      with y hy
    exact hy
  have hder : mvfderiv I (scalAt g) x
      = mvfderiv I (fun y : M => scalAlg (Rxn.rmFrameField g W y)) x :=
    mvfderiv_congr_of_eventuallyEq (I := I) hev
  -- the curvature array is differentiable at `x`
  have hRm_mdiff : MDifferentiableAt I 𝓘(ℝ, Curv4 (Module.finrank ℝ E))
      (fun y : M => Rxn.rmFrameField g W y) x :=
    (covRxn.contMDiffAt_rmFrameField (I := I) (M := M) hLC g W hWsm x).mdifferentiableAt (by simp)
  -- the chain rule: `scalAlg` of the derivative of the curvature array
  have hchain : mvfderiv I (fun y : M => scalAlg (Rxn.rmFrameField g W y)) x (onFrame g x m)
      = fderiv ℝ scalAlg (Rxn.rmFrameField g W x)
          (mvfderiv I (fun y : M => Rxn.rmFrameField g W y) x (onFrame g x m)) := by
    have hG : MDifferentiableAt 𝓘(ℝ, Curv4 (Module.finrank ℝ E)) 𝓘(ℝ, ℝ) scalAlg
        (Rxn.rmFrameField g W x) :=
      (differentiableAt_scalAlg (Rxn.rmFrameField g W x)).mdifferentiableAt
    rw [show (fun y : M => scalAlg (Rxn.rmFrameField g W y))
        = scalAlg ∘ (fun y : M => Rxn.rmFrameField g W y) from rfl]
    rw [mvfderiv_comp_apply (I := 𝓘(ℝ, Curv4 (Module.finrank ℝ E))) (I' := I)
      (f := fun y : M => Rxn.rmFrameField g W y) (g := scalAlg) x hG hRm_mdiff (onFrame g x m)]
    rw [mvfderiv_eq_fderiv]
    rfl
  rw [show mvfderiv I (scalAt g) x (onFrame g x m)
      = mvfderiv I (fun y : M => scalAlg (Rxn.rmFrameField g W y)) x (onFrame g x m) from by
        rw [hder],
    hchain,
    mvfderiv_rmFrameField_eq_covRm (I := I) (M := M) hLC g x W hWsm (onFrame g x m) hWx
      (fun i => hconn i m),
    fderiv_scalAlg]

/-- **The gradient of the scalar curvature is the trace of `∇Rm`.** The frozen
`gradSq g (scalAt g) x` is `∑ₘ (∂ₘ S)²` computed with the `Classical.epsilon`-chosen orthonormal
frame `onFrame g x`; it equals the sum of squares of the traces `∑ᵢⱼ ⟪(∇ₘRm)(eᵢ,eⱼ)eⱼ,eᵢ⟫` of the
covariant derivative of the curvature tensor, again in `onFrame g x`.
Proof route: take a smooth field `G i` of orthonormal frames near `x` with `G x = onFrame g x`
(`Work.Diff.GE.smooth_onframe` for existence, then rotate by the constant orthogonal change of frame
at `x`); `scalAt g` agrees near `x` with `y ↦ scalAlg (rmFrame g y (G y))` because the trace is
frame-independent for orthonormal frames (`Work.Diff.L.ConnDefs.conn_scalAlg_rmFrame_eq`,
`Work.Diff.GE.rot_invariance`, `Work.Diff.GE.rmFrame_eq_rot`,
`Work.Diff.GE.onFrame_orthogonal_change`); differentiate that with the product rule for
`MetricCompat g` (`rmP g y A B C D = ⟪curv A B D y, C y⟫` plus metric compatibility), and cancel the
frame-derivative terms using the antisymmetry of the `ω_{ip} = ⟪∇_v G i, G p⟫` (which follows from
`∂_v ⟪G i, G p⟫ = 0`) together with the symmetries of the curvature. -/
theorem gradSq_scalAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    (hLC : LCSmooth I M) (g : SMet I M) (x : M) :
    gradSq g (scalAt g) x
      = ∑ m, (∑ i, ∑ j, covRm g x (onFrame g x m) (onFrame g x i) (onFrame g x j)
          (onFrame g x i) (onFrame g x j)) ^ 2 := by
  classical
  simp only [gradSq]
  by_cases hn : 0 < Module.finrank ℝ E
  · -- a geodesic orthonormal frame field at `x`
    obtain ⟨W, hWsm, hWON, hWx, hWgeo⟩ := geodesicFrame (I := I) (M := M) g x
    have hWconn : ∀ (i m : Fin (Module.finrank ℝ E)),
        lcOf g (fun y : M => W i y) x (onFrame g x m) = 0 := by
      intro i m
      rw [← hWx m]
      exact hWgeo m i
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [mvfderiv_scalAt_eq_sum (I := I) (M := M) hLC g x W hWsm hWON hWx hWconn m]
  · -- degenerate case: there are no frame vectors at all
    haveI : IsEmpty (Fin (Module.finrank ℝ E)) := ⟨fun i => absurd i.isLt (by omega)⟩
    simp

end Work.Diff.GE
