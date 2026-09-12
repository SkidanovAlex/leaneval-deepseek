import Mathlib.Analysis.Calculus.FDeriv.Add
import Submission.PaperBand.Developable

open OptimalMoebius Topology ContDiff
open scoped BigOperators Matrix
open InnerProductGeometry

set_option autoImplicit false
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# The second-derivative bridge for the bend foliation, part 2

(Roadmap item (1), continue.)  This module closes the second-order bridge of
the bend-foliation layer: the second directional derivative of the immersion,
`D²f(x)(v,w) := fderiv ℝ (fun y ↦ fderiv ℝ f y v) x w`, is a pure multiple of
the unit normal whose coefficient is (minus) the quadratic form of the shape
matrix:

    D²f(x)(v,w) = −(Σᵢⱼ vⁱ wʲ S_{j i}) · N x .

Consequently, along a kernel direction `v` of the shape operator at an
interior point (`dN f x v = 0`) the second derivative vanishes in *every*
direction `w`:

    fderiv ℝ (fun y ↦ fderiv ℝ f y v) x w = 0.

This is the infinitesimal statement behind "the tangent map `y ↦ df(y) v` is
locally constant where `v` stays in the kernel", which yields that the image
of a kernel segment is affine — i.e. that bends are straight.
-/

noncomputable section
namespace Submission.PaperBand

/-- Application of a continuous linear map to a vector decomposed in the
standard basis of `ℝ²`. -/
lemma clm_apply_vec_decomp (L : ℝ² →L[ℝ] ℝ³) : ∀ v : ℝ²,
    L v = (v 0) • L !₂[1, 0] + (v 1) • L !₂[0, 1] := by
  intro v
  let e0 : ℝ² := !₂[1, 0]
  let e1 : ℝ² := !₂[0, 1]
  have hve : v = (v 0) • e0 + (v 1) • e1 := by simpa [e0, e1] using vec_eq_basis v
  calc
    L v = L ((v 0) • e0 + (v 1) • e1) := by
      exact congrArg (fun u : ℝ² => L u) hve
    _ = (v 0) • L e0 + (v 1) • L e1 := by
      rw [map_add]
      rw [map_smul]
      rw [map_smul]

/-- Pointwise linearity of the derivative of `f` in its direction argument. -/
lemma fderiv_apply_vec_decomp {f : ℝ² → ℝ³} :
    ∀ y : ℝ², ∀ v : ℝ²,
      fderiv ℝ f y v = (v 0) • (fderiv ℝ f y !₂[1, 0]) +
                        (v 1) • (fderiv ℝ f y !₂[0, 1]) := by
  intro y v
  exact clm_apply_vec_decomp (fderiv ℝ f y) v

/-- Scalar–vector combination: `a • (-p • n) + b • (-q • n) = -(ap + bq) • n`. -/
lemma frame_scalar_comb (a b p q : ℝ) (n : ℝ³) :
    a • (-p • n) + b • (-q • n) = -(a * p + b * q) • n := by
  rw [neg_smul, neg_smul]
  rw [smul_neg, smul_neg]
  rw [smul_smul, smul_smul]
  rw [← neg_add]
  rw [← add_smul]
  rw [neg_smul]

/-- The derivative families `y ↦ fderiv f y eᵢ` are differentiable at interior
points of the strip (they agree with the smooth tangent fields there). -/
lemma differentiableAt_fderiv_dir₀ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior, DifferentiableAt ℝ (fun y : ℝ² => fderiv ℝ f y !₂[1, 0]) x := by
  intro x hx
  exact ((contDiffOn_fderiv_dir₀ hf).differentiableOn (by simp) x hx).differentiableAt
    (IsOpen.mem_nhds stripInterior_isOpen hx)

/-- The derivative families `y ↦ fderiv f y eᵢ` are differentiable at interior
points of the strip (they agree with the smooth tangent fields there). -/
lemma differentiableAt_fderiv_dir₁ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior, DifferentiableAt ℝ (fun y : ℝ² => fderiv ℝ f y !₂[0, 1]) x := by
  intro x hx
  exact ((contDiffOn_fderiv_dir₁ hf).differentiableOn (by simp) x hx).differentiableAt
    (IsOpen.mem_nhds stripInterior_isOpen hx)

/-- The mixed derivative `∂₀ tangent₁ = ∂₁ tangent₀` is the same normal
multiple `−S₁₀ N` (`fderiv ℝ (fun y ↦ tangent₁ f y) x e₀ = −S₁₀ N x`). -/
lemma tangent₁_e0_deriv {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior,
      fderiv ℝ (fun y : ℝ² => tangent₁ f y) x !₂[1, 0] =
        - dNentry f x 1 0 • unitNormal f x := by
  intro x hx
  calc
    fderiv ℝ (fun y : ℝ² => tangent₁ f y) x !₂[1, 0]
        = fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[0, 1] := mixedSym_tangent hf x hx
    _ = - dNentry f x 1 0 • unitNormal f x := secondDeriv_dNentry₁ hf x hx

/-- General-direction second derivative of `tangent₀`: the derivative of
`y ↦ tangent₀ f y` at an interior point in any direction `v` is
`−(v₀ S₀₀ + v₁ S₁₀) N`. -/
lemma fderiv_tangent₀_vec {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior, ∀ v : ℝ²,
      fderiv ℝ (fun y : ℝ² => tangent₀ f y) x v =
        - ((v 0) * dNentry f x 0 0 + (v 1) * dNentry f x 1 0) • unitNormal f x := by
  intro x hx v
  let L : ℝ² →L[ℝ] ℝ³ := fderiv ℝ (fun y : ℝ² => tangent₀ f y) x
  calc
    fderiv ℝ (fun y : ℝ² => tangent₀ f y) x v
        = (v 0) • (fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[1, 0]) +
          (v 1) • (fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[0, 1]) := by
          simpa [L] using clm_apply_vec_decomp L v
    _ = (v 0) • (- dNentry f x 0 0 • unitNormal f x) +
        (v 1) • (- dNentry f x 1 0 • unitNormal f x) := by
          rw [secondDeriv_dNentry₀ hf x hx, secondDeriv_dNentry₁ hf x hx]
    _ = - ((v 0) * dNentry f x 0 0 + (v 1) * dNentry f x 1 0) • unitNormal f x := by
          exact frame_scalar_comb (v 0) (v 1) (dNentry f x 0 0) (dNentry f x 1 0)
            (unitNormal f x)

/-- General-direction second derivative of `tangent₁`: the derivative of
`y ↦ tangent₁ f y` at an interior point in any direction `v` is
`−(v₀ S₁₀ + v₁ S₁₁) N`. -/
lemma fderiv_tangent₁_vec {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior, ∀ v : ℝ²,
      fderiv ℝ (fun y : ℝ² => tangent₁ f y) x v =
        - ((v 0) * dNentry f x 1 0 + (v 1) * dNentry f x 1 1) • unitNormal f x := by
  intro x hx v
  let L : ℝ² →L[ℝ] ℝ³ := fderiv ℝ (fun y : ℝ² => tangent₁ f y) x
  calc
    fderiv ℝ (fun y : ℝ² => tangent₁ f y) x v
        = (v 0) • (fderiv ℝ (fun y : ℝ² => tangent₁ f y) x !₂[1, 0]) +
          (v 1) • (fderiv ℝ (fun y : ℝ² => tangent₁ f y) x !₂[0, 1]) := by
          simpa [L] using clm_apply_vec_decomp L v
    _ = (v 0) • (- dNentry f x 1 0 • unitNormal f x) +
        (v 1) • (- dNentry f x 1 1 • unitNormal f x) := by
          rw [tangent₁_e0_deriv hf x hx, secondDeriv_dNentry₂ hf x hx]
    _ = - ((v 0) * dNentry f x 1 0 + (v 1) * dNentry f x 1 1) • unitNormal f x := by
          exact frame_scalar_comb (v 0) (v 1) (dNentry f x 1 0) (dNentry f x 1 1)
            (unitNormal f x)



/-- **The second-derivative bridge**: for an isometric immersion of the flat
strip, the second directional derivative of `f` at an interior point in two
directions `v, w` is a pure multiple of the unit normal,

    D²f(x)(v, w) = −(v₀w₀S₀₀ + v₀w₁S₁₀ + v₁w₀S₁₀ + v₁w₁S₁₁) · N x,

the coefficient being (minus) the shape-matrix contraction `Σᵢⱼ vⁱwʲ S_{j i}`
(so, by symmetry of `S`, `−vᵀ S w`). -/
lemma secondDeriv_vec_general {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior, ∀ v w : ℝ²,
      fderiv ℝ (fun y : ℝ² => fderiv ℝ f y v) x w =
        - ((v 0) * (w 0) * dNentry f x 0 0 + (v 0) * (w 1) * dNentry f x 1 0 +
           (v 1) * (w 0) * dNentry f x 1 0 + (v 1) * (w 1) * dNentry f x 1 1) •
          unitNormal f x := by
  intro x hx v w
  let A : ℝ² → ℝ³ := fun y : ℝ² => fderiv ℝ f y !₂[1, 0]
  let B : ℝ² → ℝ³ := fun y : ℝ² => fderiv ℝ f y !₂[0, 1]
  have hdA : DifferentiableAt ℝ A x := by simpa [A] using differentiableAt_fderiv_dir₀ hf x hx
  have hdB : DifferentiableAt ℝ B x := by simpa [B] using differentiableAt_fderiv_dir₁ hf x hx
  have hg : (fun y : ℝ² => fderiv ℝ f y v) = fun y => (v 0) • A y + (v 1) • B y := by
    funext y
    dsimp [A, B]
    exact fderiv_apply_vec_decomp (f := f) y v
  have hdA' : DifferentiableAt ℝ (fun y : ℝ² => (v 0) • A y) x := hdA.const_smul (v 0)
  have hdB' : DifferentiableAt ℝ (fun y : ℝ² => (v 1) • B y) x := hdB.const_smul (v 1)
  have hsum : DifferentiableAt ℝ (fun y : ℝ² => (v 0) • A y + (v 1) • B y) x := hdA'.add hdB'
  have hfsum : fderiv ℝ (fun y : ℝ² => (v 0) • A y + (v 1) • B y) x =
      (v 0) • fderiv ℝ A x + (v 1) • fderiv ℝ B x := by
    rw [fderiv_fun_add hdA' hdB']
    congr 1
    · rw [fderiv_fun_const_smul hdA]
    · rw [fderiv_fun_const_smul hdB]
  have hfg : fderiv ℝ (fun y : ℝ² => fderiv ℝ f y v) x =
      (v 0) • fderiv ℝ A x + (v 1) • fderiv ℝ B x := by
    rw [hg]
    exact hfsum
  -- convert fderiv of A and B into fderiv of the tangent fields:
  have hconvA : fderiv ℝ A x = fderiv ℝ (fun y : ℝ² => tangent₀ f y) x := by
    have heA : A =ᶠ[𝓝 x] (fun y : ℝ² => tangent₀ f y) := by
      filter_upwards [IsOpen.mem_nhds stripInterior_isOpen hx] with y hy
      dsimp [A]
      exact (tangent₀_eq_fderiv hy).symm
    rw [Filter.EventuallyEq.fderiv_eq heA]
  have hconvB : fderiv ℝ B x = fderiv ℝ (fun y : ℝ² => tangent₁ f y) x := by
    have heB : B =ᶠ[𝓝 x] (fun y : ℝ² => tangent₁ f y) := by
      filter_upwards [IsOpen.mem_nhds stripInterior_isOpen hx] with y hy
      dsimp [B]
      exact (tangent₁_eq_fderiv hy).symm
    rw [Filter.EventuallyEq.fderiv_eq heB]
  calc
    fderiv ℝ (fun y : ℝ² => fderiv ℝ f y v) x w
        = ((v 0) • fderiv ℝ A x + (v 1) • fderiv ℝ B x) w := by
            exact congrArg (fun L : ℝ² →L[ℝ] ℝ³ => L w) hfg
    _ = (v 0) • (fderiv ℝ A x w) + (v 1) • (fderiv ℝ B x w) := by
            simp
    _ = (v 0) • (fderiv ℝ (fun y : ℝ² => tangent₀ f y) x w) +
        (v 1) • (fderiv ℝ (fun y : ℝ² => tangent₁ f y) x w) := by
            rw [hconvA, hconvB]
    _ = (v 0) • (- ((w 0) * dNentry f x 0 0 + (w 1) * dNentry f x 1 0) •
          unitNormal f x) +
        (v 1) • (- ((w 0) * dNentry f x 1 0 + (w 1) * dNentry f x 1 1) •
          unitNormal f x) := by
            rw [fderiv_tangent₀_vec hf x hx w, fderiv_tangent₁_vec hf x hx w]
    _ = - ((v 0) * (w 0) * dNentry f x 0 0 + (v 0) * (w 1) * dNentry f x 1 0 +
           (v 1) * (w 0) * dNentry f x 1 0 + (v 1) * (w 1) * dNentry f x 1 1) •
          unitNormal f x := by
          let p : ℝ := (w 0) * dNentry f x 0 0 + (w 1) * dNentry f x 1 0
          let q : ℝ := (w 0) * dNentry f x 1 0 + (w 1) * dNentry f x 1 1
          have h1 : (v 0) • (-p • unitNormal f x) + (v 1) • (-q • unitNormal f x) =
              - ((v 0) * p + (v 1) * q) • unitNormal f x := by
                exact frame_scalar_comb (v 0) (v 1) p q (unitNormal f x)
          have hsc : (v 0) * p + (v 1) * q =
              (v 0) * (w 0) * dNentry f x 0 0 + (v 0) * (w 1) * dNentry f x 1 0 +
                (v 1) * (w 0) * dNentry f x 1 0 + (v 1) * (w 1) * dNentry f x 1 1 := by
              dsimp [p, q]
              ring
          calc
            (v 0) • (- ((w 0) * dNentry f x 0 0 + (w 1) * dNentry f x 1 0) • unitNormal f x) +
                (v 1) • (- ((w 0) * dNentry f x 1 0 + (w 1) * dNentry f x 1 1) •
                  unitNormal f x)
                = (v 0) • (-p • unitNormal f x) + (v 1) • (-q • unitNormal f x) := by
                    simp [p, q]
            _ = - ((v 0) * p + (v 1) * q) • unitNormal f x := h1
            _ = - ((v 0) * (w 0) * dNentry f x 0 0 + (v 0) * (w 1) * dNentry f x 1 0 +
                  (v 1) * (w 0) * dNentry f x 1 0 + (v 1) * (w 1) * dNentry f x 1 1) •
                  unitNormal f x := by
                    rw [hsc]

/-- **Kernel directions annihilate the second derivative in every direction**:
if `dN f x v = 0` at an interior point then
`fderiv ℝ (fun y ↦ fderiv ℝ f y v) x w = 0` for all `w`. -/
lemma secondDeriv_vec_zero_all {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior, ∀ v : ℝ²,
      dN f x v = 0 → ∀ w : ℝ²,
        fderiv ℝ (fun y : ℝ² => fderiv ℝ f y v) x w = 0 := by
  intro x hx v hv0 w
  rw [secondDeriv_vec_general hf x hx v w]
  rcases (kernel_inner_relations hf x hx v hv0) with ⟨r0, r1⟩
  have hsym := shapeOperator_symm hf x hx (0 : Fin 2) (1 : Fin 2)
  rw [hsym] at r1
  have hr0 : (w 0) * ((v 0) * dNentry f x 0 0 + (v 1) * dNentry f x 1 0) = 0 := by
    rw [r0]
    ring
  have hr1 : (w 1) * ((v 0) * dNentry f x 1 0 + (v 1) * dNentry f x 1 1) = 0 := by
    rw [r1]
    ring
  have hsc : (v 0) * (w 0) * dNentry f x 0 0 + (v 0) * (w 1) * dNentry f x 1 0 +
        (v 1) * (w 0) * dNentry f x 1 0 + (v 1) * (w 1) * dNentry f x 1 1 = 0 := by
    nlinarith [hr0, hr1]
  rw [hsc]
  simp

/-- **Vector-half bridge** (same-direction kernel): if `dN f x v = 0` at an
interior point then the second directional derivative of `f` in the kernel
direction vanishes, `fderiv ℝ (fun y ↦ fderiv ℝ f y v) x v = 0`. -/
lemma secondDeriv_vec_kernel {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior, ∀ v : ℝ²,
      dN f x v = 0 →
      fderiv ℝ (fun y : ℝ² => fderiv ℝ f y v) x v = 0 := by
  intro x hx v hv0
  exact secondDeriv_vec_zero_all hf x hx v hv0 v

end Submission.PaperBand
end
