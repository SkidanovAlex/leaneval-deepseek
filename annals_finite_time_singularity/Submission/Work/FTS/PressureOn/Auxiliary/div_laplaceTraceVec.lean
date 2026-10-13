/-
# `div (ΔW) = Δ(div W)`

`Work.FTS.PressureOn.Auxiliary.div_laplaceTraceVec` is the classical commutation identity for the
Euclidean Laplacian and the divergence on `ℝ³`,

  `div (Δ W) = Δ (div W)`,

for a smooth vector field `W`, in the workspace vocabulary (`FiniteTimeSingularity.div`, the
componentwise Laplacian `Work.FTS.PressureOn.laplaceTraceVec`, and the trace of the Hessian
`Work.FTS.PressureOn.laplaceTrace`).

## Route

The classical vector identity `ΔW = ∇(div W) − ∇×∇×W` (`laplaceTraceVec_identity`) writes

  `laplaceTraceVec W = ∇(div W) − vorticity (vorticity W)`.

Taking `div` of both sides reduces the claim to the two standard facts

* `div (∇u) = laplaceTrace u` (`Work.FTS.PressureOn.Green.div_gradient_eq_laplaceTrace`), and
* `div (∇×V) = 0` for a smooth vector field `V` (`div_vorticity_eq_zero` below),

together with the additivity of `div` (`Work.FTS.PressureOn.Green.div_sub_eq`).

The second fact is proved in coordinates: the three components of the curl are the classical
`∂₁V₂ − ∂₂V₁`, `∂₂V₀ − ∂₀V₂`, `∂₀V₁ − ∂₁V₀`, and the sum of their divergences cancels pairwise by
Clairaut's theorem (`IsSymmSndFDerivAt`).
-/
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Trace
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.vorticity_cross_eq
import Submission.Work.FTS.PressureOn.Auxiliary.fderiv_fderiv_comm
import Submission.Work.FTS.PressureOn.Auxiliary.laplaceTraceVec_identity
import Submission.Work.FTS.PressureOn.Green.integral_mul_laplaceTrace_comm
import Submission.Work.FTS.Physical.Pressure.CurlCLM

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity
open scoped Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FTS.PressureOn.Auxiliary

/-! ## Calculus preliminaries -/

/-- **The coordinate of a derivative is the derivative of the coordinate**: for a vector field `g`
differentiable at `x`, `(Dg(x) v) i = D(y ↦ g(y)_i)(x) v`. -/
theorem fderiv_coord (g : R3 → R3) {x : R3} (hg : DifferentiableAt ℝ g x) (i : Fin 3) (v : R3) :
    (fderiv ℝ g x v) i = fderiv ℝ (fun y => (g y) i) x v := by
  have h := (hasFDerivWithinAt_piLp (𝕜 := ℝ) (p := (2 : ENNReal)) (E := fun _ : Fin 3 => ℝ)
      (f := g) (f' := fderiv ℝ g x) (t := Set.univ) (y := x)).mp
      hg.hasFDerivAt.hasFDerivWithinAt i
  rw [hasFDerivWithinAt_univ] at h
  rw [h.fderiv]
  simp [PiLp.proj_apply, ContinuousLinearMap.comp_apply]

/-- **Clairaut's theorem for scalar functions.**  For a smooth `φ : ℝ³ → ℝ` the two mixed second
derivatives in the directions `a`, `b` coincide. -/
theorem fderiv_fderiv_comm_scalar (φ : R3 → ℝ) (hφ : ∀ n : ℕ, ContDiff ℝ n φ) (x : R3)
    (a b : R3) :
    fderiv ℝ (fun y => fderiv ℝ φ y a) x b = fderiv ℝ (fun y => fderiv ℝ φ y b) x a := by
  have hcd : ContDiff ℝ 1 (fderiv ℝ φ) := (hφ 2).fderiv_right (by norm_num)
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    (hcd.differentiable (by norm_num)).differentiableAt
  have hsymm : IsSymmSndFDerivAt ℝ φ x := ((hφ 2).contDiffAt).isSymmSndFDerivAt (by simp)
  have hfun_a : (fun y : R3 => fderiv ℝ φ y a)
      = (ContinuousLinearMap.apply ℝ ℝ a) ∘ (fderiv ℝ φ) := by
    funext y
    simp [ContinuousLinearMap.apply_apply]
  have hfun_b : (fun y : R3 => fderiv ℝ φ y b)
      = (ContinuousLinearMap.apply ℝ ℝ b) ∘ (fderiv ℝ φ) := by
    funext y
    simp [ContinuousLinearMap.apply_apply]
  have hfa : fderiv ℝ (fun y : R3 => fderiv ℝ φ y a) x
      = (ContinuousLinearMap.apply ℝ ℝ a).comp (fderiv ℝ (fderiv ℝ φ) x) := by
    rw [hfun_a]
    exact ((ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.apply ℝ ℝ a)).comp x
      hd.hasFDerivAt).fderiv
  have hfb : fderiv ℝ (fun y : R3 => fderiv ℝ φ y b) x
      = (ContinuousLinearMap.apply ℝ ℝ b).comp (fderiv ℝ (fderiv ℝ φ) x) := by
    rw [hfun_b]
    exact ((ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.apply ℝ ℝ b)).comp x
      hd.hasFDerivAt).fderiv
  have hkey := hsymm.eq b a
  rw [hfa, hfb, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, ContinuousLinearMap.apply_apply]
  exact hkey

/-! ## The coordinates of the curl

In the standard basis the three components of `∇ × V` are the classical expressions. -/

/-- First coordinate of the curl: `(∇×V)₀ = ∂₁V₂ − ∂₂V₁`. -/
theorem vorticity_coord_zero (V : R3 → R3) (y : R3) :
    (vorticity V y) 0 = (fderiv ℝ V y (e 1)) 2 - (fderiv ℝ V y (e 2)) 1 := by
  show (vorticity V y).ofLp 0 = _
  rw [show (vorticity V y).ofLp
        = ∑ i : Fin 3, ((e i : Fin 3 → ℝ) ⨯₃ (fderiv ℝ V y (e i) : Fin 3 → ℝ)) from rfl,
      Fin.sum_univ_three]
  simp only [cross_apply, FiniteTimeSingularity.e, WithLp.ofLp_toLp]
  norm_num [PiLp.single_apply]
  ring

/-- Second coordinate of the curl: `(∇×V)₁ = ∂₂V₀ − ∂₀V₂`. -/
theorem vorticity_coord_one (V : R3 → R3) (y : R3) :
    (vorticity V y) 1 = (fderiv ℝ V y (e 2)) 0 - (fderiv ℝ V y (e 0)) 2 := by
  show (vorticity V y).ofLp 1 = _
  rw [show (vorticity V y).ofLp
        = ∑ i : Fin 3, ((e i : Fin 3 → ℝ) ⨯₃ (fderiv ℝ V y (e i) : Fin 3 → ℝ)) from rfl,
      Fin.sum_univ_three]
  simp only [cross_apply, FiniteTimeSingularity.e, WithLp.ofLp_toLp]
  norm_num [PiLp.single_apply]
  ring

/-- Third coordinate of the curl: `(∇×V)₂ = ∂₀V₁ − ∂₁V₀`. -/
theorem vorticity_coord_two (V : R3 → R3) (y : R3) :
    (vorticity V y) 2 = (fderiv ℝ V y (e 0)) 1 - (fderiv ℝ V y (e 1)) 0 := by
  show (vorticity V y).ofLp 2 = _
  rw [show (vorticity V y).ofLp
        = ∑ i : Fin 3, ((e i : Fin 3 → ℝ) ⨯₃ (fderiv ℝ V y (e i) : Fin 3 → ℝ)) from rfl,
      Fin.sum_univ_three]
  simp only [cross_apply, FiniteTimeSingularity.e, WithLp.ofLp_toLp]
  norm_num [PiLp.single_apply]
  ring

/-! ## Differentiating a coordinate of a derivative

The scalar maps `y ↦ (DV(y) · a) b` are the composites of the continuous linear functionals
`L ↦ (L a) b` with `DV`, so they are differentiable as soon as `DV` is, with the chain-rule
derivative `(D²V(x) · a) b`. -/

/-- The `b`-th coordinate of `ℝ³` as a continuous linear functional. -/
noncomputable def coordCLM (b : Fin 3) : R3 →L[ℝ] ℝ :=
  PiLp.proj (p := 2) (β := fun _ : Fin 3 => ℝ) b

theorem coordCLM_apply (b : Fin 3) (v : R3) : coordCLM b v = v b := by
  simp only [coordCLM, PiLp.proj_apply]

/-- Differentiability of `y ↦ (DV(y) · a) b`. -/
theorem differentiableAt_fderiv_coord (V : R3 → R3) {x : R3}
    (hΦd : DifferentiableAt ℝ (fderiv ℝ V) x) (a : R3) (b : Fin 3) :
    DifferentiableAt ℝ (fun y : R3 => (fderiv ℝ V y a) b) x := by
  have heq : (fun y : R3 => (fderiv ℝ V y a) b)
      = (coordCLM b) ∘ ((ContinuousLinearMap.apply ℝ R3 a) ∘ (fderiv ℝ V)) := by
    funext y
    simp only [Function.comp_apply, coordCLM_apply, ContinuousLinearMap.apply_apply]
  rw [heq]
  exact ((ContinuousLinearMap.hasFDerivAt (coordCLM b)).comp x
    ((ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.apply ℝ R3 a)).comp x
      hΦd.hasFDerivAt)).differentiableAt

/-- The chain rule for a coordinate of a derivative:
`D(y ↦ (DV(y) · a) b)(x) · v = (D²V(x) · v · a) b`. -/
theorem fderiv_fderiv_V_coord (V : R3 → R3) {x : R3}
    (hΦd : DifferentiableAt ℝ (fderiv ℝ V) x) (a : R3) (b : Fin 3) (k : Fin 3) :
    fderiv ℝ (fun y : R3 => (fderiv ℝ V y a) b) x (e k)
      = ((fderiv ℝ (fderiv ℝ V) x (e k)) a) b := by
  have heq : (fun y : R3 => (fderiv ℝ V y a) b)
      = (coordCLM b) ∘ ((ContinuousLinearMap.apply ℝ R3 a) ∘ (fderiv ℝ V)) := by
    funext y
    simp only [Function.comp_apply, coordCLM_apply, ContinuousLinearMap.apply_apply]
  have h := (ContinuousLinearMap.hasFDerivAt (coordCLM b)).comp x
    ((ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.apply ℝ R3 a)).comp x
      hΦd.hasFDerivAt)
  rw [heq, h.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, coordCLM_apply]

/-! ## Smoothness of `div` and of the curl -/

/-- The trace as a continuous linear functional on `ℝ³ →L[ℝ] ℝ³`. -/
noncomputable def divTraceCLM : (R3 →L[ℝ] R3) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap ((LinearMap.trace ℝ R3).comp (ContinuousLinearMap.coeLM ℝ))

/-- `div` is the trace of the derivative. -/
theorem div_eq_divTraceCLM (W : R3 → R3) (x : R3) :
    div W x = divTraceCLM (fderiv ℝ W x) := rfl

/-- The divergence of a smooth vector field is smooth. -/
theorem contDiff_div (W : R3 → R3) (hW : ∀ n : ℕ, ContDiff ℝ n W) :
    ∀ n : ℕ, ContDiff ℝ n (div W) := by
  intro n
  have h : div W = fun x => divTraceCLM (fderiv ℝ W x) :=
    funext fun x => div_eq_divTraceCLM W x
  rw [h]
  exact (ContinuousLinearMap.contDiff divTraceCLM).comp
    ((hW (n + 1)).fderiv_right (by simp))

/-- The curl of a smooth vector field is smooth. -/
theorem contDiff_vorticity (V : R3 → R3) (hV : ∀ n : ℕ, ContDiff ℝ n V) :
    ∀ n : ℕ, ContDiff ℝ n (vorticity V) := by
  intro n
  have h : vorticity V = fun x => Work.FTS.Physical.Pressure.curlCLM (fderiv ℝ V x) :=
    funext fun x => Work.FTS.Physical.Pressure.vorticity_eq_curlCLM V x
  rw [h]
  exact (ContinuousLinearMap.contDiff Work.FTS.Physical.Pressure.curlCLM).comp
    ((hV (n + 1)).fderiv_right (by simp))

/-- The `k`-th coordinate of the derivative of the `k`-th coordinate of the curl, in closed form. -/
theorem fderiv_vorticity_coord (V : R3 → R3) (hV : ∀ n : ℕ, ContDiff ℝ n V) (x : R3)
    (k a b : Fin 3)
    (hcoord : (fun y : R3 => (vorticity V y) k)
        = fun y => (fderiv ℝ V y (e a)) b - (fderiv ℝ V y (e b)) a) :
    (fderiv ℝ (vorticity V) x (e k)) k
      = ((fderiv ℝ (fderiv ℝ V) x (e k) (e a)) b)
        - ((fderiv ℝ (fderiv ℝ V) x (e k) (e b)) a) := by
  have hΦd : DifferentiableAt ℝ (fderiv ℝ V) x := by
    have h : ContDiff ℝ 1 (fderiv ℝ V) := (hV 2).fderiv_right (by norm_num)
    exact (h.differentiable (by norm_num)).differentiableAt
  have hvortd : DifferentiableAt ℝ (vorticity V) x :=
    ((contDiff_vorticity V hV 1).differentiable (by norm_num)).differentiableAt
  rw [fderiv_coord (vorticity V) hvortd k (e k), hcoord,
    fderiv_fun_sub (differentiableAt_fderiv_coord V hΦd (e a) b)
      (differentiableAt_fderiv_coord V hΦd (e b) a)]
  change fderiv ℝ (fun y : R3 => (fderiv ℝ V y (e a)) b) x (e k)
      - fderiv ℝ (fun y : R3 => (fderiv ℝ V y (e b)) a) x (e k) = _
  rw [fderiv_fderiv_V_coord V hΦd (e a) b k, fderiv_fderiv_V_coord V hΦd (e b) a k]

/-! ## `div (∇×V) = 0` -/

/-- **The divergence of a curl vanishes.** -/
theorem div_vorticity_eq_zero (V : R3 → R3) (hV : ∀ n : ℕ, ContDiff ℝ n V) :
    div (vorticity V) = 0 := by
  funext x
  change div (vorticity V) x = 0
  have hS : IsSymmSndFDerivAt ℝ V x := ((hV 2).contDiffAt).isSymmSndFDerivAt (by simp)
  have hsymm : ∀ u w : R3,
      fderiv ℝ (fderiv ℝ V) x u w = fderiv ℝ (fderiv ℝ V) x w u := fun u w => hS.eq u w
  have h0 := fderiv_vorticity_coord V hV x 0 1 2 (funext (vorticity_coord_zero V))
  have h1 := fderiv_vorticity_coord V hV x 1 2 0 (funext (vorticity_coord_one V))
  have h2 := fderiv_vorticity_coord V hV x 2 0 1 (funext (vorticity_coord_two V))
  rw [vorticityCross_div_eq_sum_diag, Fin.sum_univ_three]
  rw [h0, h1, h2]
  have hD : ((fderiv ℝ (fderiv ℝ V) x (e 1)) (e 0)) 2
      = ((fderiv ℝ (fderiv ℝ V) x (e 0)) (e 1)) 2 :=
    congrArg (fun v : R3 => v 2) (hsymm (e 1) (e 0))
  have hE : ((fderiv ℝ (fderiv ℝ V) x (e 2)) (e 0)) 1
      = ((fderiv ℝ (fderiv ℝ V) x (e 0)) (e 2)) 1 :=
    congrArg (fun v : R3 => v 1) (hsymm (e 2) (e 0))
  have hF : ((fderiv ℝ (fderiv ℝ V) x (e 2)) (e 1)) 0
      = ((fderiv ℝ (fderiv ℝ V) x (e 1)) (e 2)) 0 :=
    congrArg (fun v : R3 => v 0) (hsymm (e 2) (e 1))
  rw [hD, hE, hF]
  ring

/-! ## The target -/

theorem div_laplaceTraceVec (W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hW : ∀ n : ℕ, ContDiff ℝ n W) (x : EuclideanSpace ℝ (Fin 3)) :
    FiniteTimeSingularity.div (Work.FTS.PressureOn.laplaceTraceVec W) x
      = Work.FTS.PressureOn.laplaceTrace (FiniteTimeSingularity.div W) x := by
  have hsub : laplaceTraceVec W = fun y => gradient (div W) y - vorticity (vorticity W) y :=
    funext fun y => laplaceTraceVec_identity W hW y
  have hdiv2 : ContDiff ℝ 2 (div W) := contDiff_div W hW 2
  have hdiff1 : DifferentiableAt ℝ (fun y => gradient (div W) y) x :=
    ((Green.contDiff_gradient (div W) hdiv2).differentiable (by norm_num)).differentiableAt
  have hdiff2 : DifferentiableAt ℝ (fun y => vorticity (vorticity W) y) x :=
    ((contDiff_vorticity (vorticity W) (contDiff_vorticity W hW) 1).differentiable
      (by norm_num)).differentiableAt
  rw [hsub, Green.div_sub_eq (fun y => gradient (div W) y)
        (fun y => vorticity (vorticity W) y) x hdiff1 hdiff2,
      Green.div_gradient_eq_laplaceTrace (div W) hdiv2,
      div_vorticity_eq_zero (vorticity W) (contDiff_vorticity W hW)]
  simp

end Work.FTS.PressureOn.Auxiliary
