/-
# `Work.FTS.PressureOn.Auxiliary.laplaceTraceVec_identity`

The classical vector identity

  `ΔW = ∇(div W) - ∇ × (∇ × W)`

for a smooth vector field `W` on `ℝ³`, in the vocabulary of the workspace: with
`laplaceTraceVec W x = ∑ᵢ ∂ᵢ∂ᵢW(x)` (the componentwise Laplacian, `PressureOn/Defs.lean`), `div` the
trace of the derivative and `vorticity u x = ∑ᵢ eᵢ × ∂ᵢu(x)` the curl (`ChallengeDeps.lean`), and
`gradient` the Riesz representative of the derivative, the identity reads

  `laplaceTraceVec W x = gradient (div W) x - vorticity (vorticity W) x`.

It is one of the ingredients of the Newtonian reconstruction of the pressure
(`PressureOn/Green/…`, `green_identity`): it lets the Hessian trace of the Newtonian kernel be
recognised as `∇(div ·) - ∇×∇×·`.

## Proof outline

Write `S i k := (fderiv ℝ (fun w => fderiv ℝ W w (e i)) x) (e k) : ℝ³`, so that `(S i k) l` is the
second partial `∂ₖ∂ᵢW_l`, and `S` is symmetric in its first two indices (`fderiv_fderiv_comm`).
Taking the `j`-th coordinate of both sides:

* `(laplaceTraceVec W x) j = ∑ i, (S i i) j` (definition);
* `(gradient (div W) x) j = ∑ i, (S i j) i` (`gradient` is the Riesz representative of `fderiv`,
  `div` is `∑ i, (∂ᵢW)_i`, and a coordinate of a derivative is the derivative of the coordinate);
* `(vorticity (vorticity W) x) j = ∑ k, (e k × (∑ i, e i × S i k)) j` (the curl in coordinates,
  twice).

What is left is the finite algebraic identity `curlCurl_apply`, the `Fin 3` computation
`∑ i S(i,i) = ∑ i S(i,j)_i - ∑ k (e_k × (∑ i e_i × S(i,k)))_j` for an array `S` symmetric in its
first two indices.
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.vorticity_cross_eq
import Submission.Work.FTS.PressureOn.Auxiliary.fderiv_fderiv_comm
import Submission.Work.FTS.PressureOn.Auxiliary.curlCurl_apply

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

/-! ## Preliminaries: the standard basis and the gradient -/

/-- Dotting with the standard basis vector `e j` gives the `j`-th coordinate. -/
private lemma inner_e_left (j : Fin 3) (v : R3) : inner ℝ (e j) v = v j := by
  simp [FiniteTimeSingularity.e, PiLp.inner_apply]

/-- The version of `inner_e_left` with the arguments swapped. -/
private lemma inner_e_right (j : Fin 3) (v : R3) : inner ℝ v (e j) = v j := by
  rw [real_inner_comm, inner_e_left]

/-- `∇f x` is the Riesz representative of `fderiv ℝ f x`. -/
private lemma inner_gradient (f : R3 → ℝ) (x y : R3) :
    inner ℝ (gradient f x) y = fderiv ℝ f x y := by
  rw [← InnerProductSpace.toDual_apply_apply, toDual_gradient]

/-- The `j`-th component of the gradient is the derivative in the direction `e j`. -/
private lemma gradient_apply_e (f : R3 → ℝ) (x : R3) (j : Fin 3) :
    (gradient f x) j = fderiv ℝ f x (e j) := by
  rw [← inner_e_right j (gradient f x), inner_gradient]

/-! ## Coordinates of derivatives and of the curl -/

/-- **The coordinate of a derivative is the derivative of the coordinate**: for a vector field `g`
differentiable at `x`, `(Dg(x) v) i = D(y ↦ g(y)_i)(x) v`. -/
private lemma fderiv_apply_ofLp (g : R3 → R3) {x : R3} (hg : DifferentiableAt ℝ g x)
    (i : Fin 3) (v : R3) :
    (fderiv ℝ g x v) i = fderiv ℝ (fun y => (g y) i) x v := by
  have h := (hasFDerivWithinAt_piLp (𝕜 := ℝ) (p := (2 : ENNReal)) (E := fun _ : Fin 3 => ℝ)
      (f := g) (f' := fderiv ℝ g x) (t := Set.univ) (y := x)).mp
      hg.hasFDerivAt.hasFDerivWithinAt i
  rw [hasFDerivWithinAt_univ] at h
  rw [h.fderiv]
  simp [PiLp.proj_apply, ContinuousLinearMap.comp_apply]

/-- Evaluation commutes with finite sums of continuous linear maps. -/
private lemma clm_sum_apply {ι : Type*} [Fintype ι] (L : ι → R3 →L[ℝ] ℝ) (v : R3) :
    (∑ i, L i) v = ∑ i, L i v := by
  rw [← ContinuousLinearMap.apply_apply v, map_sum]
  exact Finset.sum_congr rfl fun i _ => ContinuousLinearMap.apply_apply v (L i)

/-- The derivative of a finite sum of scalar functions, evaluated on a vector. -/
private lemma fderiv_fun_sum_apply {A : Fin 3 → R3 → ℝ} {x v : R3}
    (h : ∀ i, DifferentiableAt ℝ (A i) x) :
    fderiv ℝ (fun y : R3 => ∑ i : Fin 3, A i y) x v = ∑ i : Fin 3, fderiv ℝ (A i) x v := by
  have hsum : HasFDerivAt (fun y : R3 => ∑ i : Fin 3, A i y)
      (∑ i : Fin 3, fderiv ℝ (A i) x) x :=
    HasFDerivAt.fun_sum (u := Finset.univ) fun i _ => (h i).hasFDerivAt
  rw [hsum.fderiv, clm_sum_apply]

/-- **The curl in coordinates**: `(∇ × V) j = ∑ i, (e i × ∂ᵢV) j`. -/
private lemma vorticity_apply (V : R3 → R3) (x : R3) (j : Fin 3) :
    (vorticity V x) j = ∑ i : Fin 3, (e i ⨯₃ (fderiv ℝ V x (e i))) j := by
  simp only [FiniteTimeSingularity.vorticity, WithLp.ofLp_toLp, Finset.sum_apply]

/-! ## Differentiability of the pieces -/

private lemma contDiff_one_fderiv (W : R3 → R3) (hW : ∀ n : ℕ, ContDiff ℝ n W) :
    ContDiff ℝ 1 (fderiv ℝ W) :=
  (hW 2).fderiv_right (m := 1) (by norm_num)

private lemma contDiff_one_fderiv_apply (W : R3 → R3) (hW : ∀ n : ℕ, ContDiff ℝ n W) (i : Fin 3) :
    ContDiff ℝ 1 (fun y : R3 => fderiv ℝ W y (e i)) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ W) := contDiff_one_fderiv W hW
  simpa [Function.comp_def] using
    (ContinuousLinearMap.apply ℝ R3 (e i)).contDiff.comp h1

private lemma differentiableAt_fderiv_apply (W : R3 → R3) (hW : ∀ n : ℕ, ContDiff ℝ n W)
    (x : R3) (i : Fin 3) : DifferentiableAt ℝ (fun y : R3 => fderiv ℝ W y (e i)) x :=
  (contDiff_one_fderiv_apply W hW i).differentiable one_ne_zero x

/-- The same, for a single coordinate of the derivative. -/
private lemma differentiableAt_fderiv_apply_coord (W : R3 → R3) (hW : ∀ n : ℕ, ContDiff ℝ n W)
    (x : R3) (i j : Fin 3) : DifferentiableAt ℝ (fun y : R3 => (fderiv ℝ W y (e i)) j) x :=
  ((differentiableAt_piLp (𝕜 := ℝ) (p := (2 : ENNReal)) (E := fun _ : Fin 3 => ℝ)
    (f := fun y : R3 => fderiv ℝ W y (e i)) (y := x)).mp
      (differentiableAt_fderiv_apply W hW x i)) j

/-- The composed form of `crossVec` with a constant first argument. -/
private lemma crossVec_comp' (c : R3) (h : R3 → R3) :
    (fun y : R3 => crossVec c (h y))
      = (fun p : R3 × R3 => crossVec p.1 p.2) ∘ (fun y : R3 => ((fun _ : R3 => c) y, h y)) :=
  rfl

/-- Differentiability of a cross product with a constant vector. -/
private lemma hasFDerivAt_crossVec_const (c : R3) (h : R3 → R3) {x : R3}
    (hh : HasFDerivAt h (fderiv ℝ h x) x) :
    HasFDerivAt (fun y : R3 => crossVec c (h y))
      ((vorticityCross_isBoundedBilinearMap.deriv (c, h x)).comp
        ((0 : R3 →L[ℝ] R3).prod (fderiv ℝ h x))) x := by
  rw [crossVec_comp' c h]
  exact (vorticityCross_isBoundedBilinearMap.hasFDerivAt (c, h x)).comp x
    ((hasFDerivAt_const c x).prodMk hh)

/-- **Derivative of a cross product with a constant vector.**  The `l`-th component of
`y ↦ c × h y` has derivative `(c × (Dh(x) v))_l` in the direction `v`. -/
private lemma fderiv_cross_const (c : R3) (h : R3 → R3) {x : R3}
    (hh : HasFDerivAt h (fderiv ℝ h x) x) (v : R3) (l : Fin 3) :
    fderiv ℝ (fun y : R3 => (crossProduct (WithLp.ofLp c) (WithLp.ofLp (h y))) l) x v
      = (crossProduct (WithLp.ofLp c) (WithLp.ofLp (fderiv ℝ h x v))) l := by
  have hcomp := hasFDerivAt_crossVec_const c h hh
  have h1 : fderiv ℝ (fun y : R3 => crossVec c (h y)) x v = crossVec c (fderiv ℝ h x v) := by
    rw [hcomp.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      IsBoundedBilinearMap.deriv_apply]
    simp
  have h2 := fderiv_apply_ofLp (fun y : R3 => crossVec c (h y)) hcomp.differentiableAt l v
  have h3 : (fun y : R3 => (crossProduct (WithLp.ofLp c) (WithLp.ofLp (h y))) l)
      = fun y : R3 => (crossVec c (h y)) l := by
    funext y
    simp [crossVec]
  rw [h3, ← h2, h1]
  simp [crossVec]

/-- Differentiability of the `l`-th component of a cross product with a constant vector. -/
private lemma differentiableAt_cross_apply (c : R3) (h : R3 → R3) {x : R3}
    (hh : HasFDerivAt h (fderiv ℝ h x) x) (l : Fin 3) :
    DifferentiableAt ℝ (fun y : R3 => (crossProduct (WithLp.ofLp c) (WithLp.ofLp (h y))) l) x := by
  have hcv : (fun y : R3 => (crossProduct (WithLp.ofLp c) (WithLp.ofLp (h y))) l)
      = fun y : R3 => (crossVec c (h y)) l := by
    funext y
    simp [crossVec]
  rw [hcv]
  have hdiff : DifferentiableAt ℝ (fun y : R3 => crossVec c (h y)) x :=
    (hasFDerivAt_crossVec_const c h hh).differentiableAt
  exact ((differentiableAt_piLp (𝕜 := ℝ) (p := (2 : ENNReal)) (E := fun _ : Fin 3 => ℝ)
    (f := fun y : R3 => crossVec c (h y)) (y := x)).mp hdiff) l

/-- The curl as a sum of cross products with the basis vectors. -/
private lemma vorticity_eq_sum_crossVec (V : R3 → R3) :
    vorticity V = fun y : R3 => ∑ i : Fin 3, crossVec (e i) (fderiv ℝ V y (e i)) := by
  funext y
  rw [WithLp.ext_iff]
  simp only [WithLp.ofLp_sum, FiniteTimeSingularity.vorticity, WithLp.ofLp_toLp, crossVec]

/-- The curl of a smooth vector field is differentiable. -/
private lemma differentiableAt_vorticity (V : R3 → R3) (hV : ∀ n : ℕ, ContDiff ℝ n V) (x : R3) :
    DifferentiableAt ℝ (vorticity V) x := by
  rw [vorticity_eq_sum_crossVec V]
  refine DifferentiableAt.fun_sum fun i _ => ?_
  exact (hasFDerivAt_crossVec_const (e i) (fun y : R3 => fderiv ℝ V y (e i))
    (differentiableAt_fderiv_apply V hV x i).hasFDerivAt).differentiableAt

/-! ## The identity -/

theorem laplaceTraceVec_identity (W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hW : ∀ n : ℕ, ContDiff ℝ n W) (x : EuclideanSpace ℝ (Fin 3)) :
    Work.FTS.PressureOn.laplaceTraceVec W x
      = gradient (FiniteTimeSingularity.div W) x
        - FiniteTimeSingularity.vorticity (FiniteTimeSingularity.vorticity W) x := by
  set S : Fin 3 → Fin 3 → R3 := fun i k => fderiv ℝ (fun w => fderiv ℝ W w (e i)) x (e k) with hS
  -- the second derivatives are symmetric
  have hsymm : ∀ i k l : Fin 3, (S i k) l = (S k i) l := by
    intro i k l
    rw [hS]
    exact congrArg (fun v : R3 => v l) (fderiv_fderiv_comm W hW x (e i) (e k))
  -- the Laplacian in coordinates
  have hLHS : ∀ j : Fin 3, (laplaceTraceVec W x) j = ∑ i : Fin 3, (S i i) j := by
    intro j
    rw [hS]
    simp only [laplaceTraceVec, WithLp.ofLp_sum, Finset.sum_apply]
  -- the gradient of the divergence in coordinates
  have hgrad : ∀ j : Fin 3, (gradient (div W) x) j = ∑ i : Fin 3, (S i j) i := by
    intro j
    have hdiv : div W = fun y : R3 => ∑ i : Fin 3, (fderiv ℝ W y (e i)) i := by
      funext y
      exact vorticityCross_div_eq_sum_diag W y
    rw [gradient_apply_e, hdiv, fderiv_fun_sum_apply (fun i =>
      differentiableAt_fderiv_apply_coord W hW x i i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [← fderiv_apply_ofLp (fun y : R3 => fderiv ℝ W y (e i))
      (differentiableAt_fderiv_apply W hW x i) i (e j)]
  -- the curl of the curl in coordinates
  have hcurl : ∀ j : Fin 3, (vorticity (vorticity W) x) j
      = ∑ k : Fin 3, (e k ⨯₃ (fun l : Fin 3 => ∑ i : Fin 3, (e i ⨯₃ (S i k)) l)) j := by
    intro j
    rw [vorticity_apply]
    apply Finset.sum_congr rfl
    intro k _
    have hfun : fderiv ℝ (vorticity W) x (e k)
        = fun l : Fin 3 => ∑ i : Fin 3, (e i ⨯₃ (S i k)) l := by
      funext l
      rw [fderiv_apply_ofLp (vorticity W) (differentiableAt_vorticity W hW x) l (e k)]
      have hv : (fun y : R3 => (vorticity W y) l)
          = fun y : R3 => ∑ i : Fin 3, (e i ⨯₃ (fderiv ℝ W y (e i))) l := by
        funext y
        rw [vorticity_apply]
      rw [hv, fderiv_fun_sum_apply (fun i => differentiableAt_cross_apply (e i)
        (fun y : R3 => fderiv ℝ W y (e i)) (differentiableAt_fderiv_apply W hW x i).hasFDerivAt l)]
      apply Finset.sum_congr rfl
      intro i _
      rw [fderiv_cross_const (e i) (fun y : R3 => fderiv ℝ W y (e i))
        (differentiableAt_fderiv_apply W hW x i).hasFDerivAt (e k) l]
    rw [hfun]
  -- the components agree
  have hcomp : ∀ j : Fin 3, (laplaceTraceVec W x) j
      = (gradient (div W) x) j - (vorticity (vorticity W) x) j := by
    intro j
    rw [hLHS j, hgrad j, hcurl j]
    exact curlCurl_apply S hsymm j
  -- conclude the vector identity
  rw [WithLp.ext_iff]
  funext j
  rw [WithLp.ofLp_sub, Pi.sub_apply, ← hcomp j]

end Work.FTS.PressureOn.Auxiliary
