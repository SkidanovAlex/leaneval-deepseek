import Mathlib
import Submission.Work.AlmostComplex.Types.Defs

namespace Work.AlmostComplex.Types

open LeanEval.Geometry.NewlanderNirenberg
open scoped ContDiff

/-!
# The `(0,2)`-part of `d(∂̄u)`

This file proves `dbarSq_eq_four_proj02`: the `(0,2)`-part `dbarSq J u X Y x` of the exterior
derivative of the `(0,1)`-form `∂̄u` is four times the value of the `(0,2)`-projection `proj02`
of `dExterior (∂̄u)` on the vectors `X x`, `Y y`.

The verification is a purely computational first-order calculus identity: expanding both
occurrences of `dbarSq` using the product/chain rule for `fderiv` produces, on the nose, the four
components of `proj02`.  Notably it does *not* use `J² = -1`; only differentiability of the data
at `x` is needed.
-/

/-- Application of a continuous linear map to a constant commutes with `fderiv`: for
`c : E → G →L[ℝ] H`, the derivative of `y ↦ c y B` at `x` in direction `A` is
`(fderiv c x A) B`. -/
theorem fderiv_apply_const {E G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    {c : E → G →L[ℝ] H} {x : E} (hc : DifferentiableAt ℝ c x) (B : G) (A : E) :
    fderiv ℝ (fun y => c y B) x A = (fderiv ℝ c x A) B := by
  rw [fderiv_clm_apply hc (differentiableAt_const (c := B))]
  simp

/-- The chain rule for `y ↦ c y (V y)`, evaluated in a direction `W`: the "product rule" for a
continuous linear map applied to a vector field. -/
theorem fderiv_clm_apply_apply {E G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    {c : E → G →L[ℝ] H} {V : E → G} {x : E}
    (hc : DifferentiableAt ℝ c x) (hV : DifferentiableAt ℝ V x) (W : E) :
    fderiv ℝ (fun y => c y (V y)) x W = c x (fderiv ℝ V x W) + (fderiv ℝ c x W) (V x) := by
  rw [fderiv_clm_apply hc hV]
  simp

/-- Expanded form of the `(0,1)`-pairing `y ↦ ⟨θ_y, (V y) + i·J_y(V y)⟩`, whose derivative in a
direction `W` is computed by the product rule in all three arguments `θ`, `V`, `J`. -/
theorem cpair_Z01_fderiv {n : ℕ} {θ : E n → E n →L[ℝ] ℂ} {J : E n → E n →L[ℝ] E n}
    {V : E n → E n} {x : E n} (hθ : DifferentiableAt ℝ θ x) (hJ : DifferentiableAt ℝ J x)
    (hV : DifferentiableAt ℝ V x) (W : E n) :
    fderiv ℝ (fun y => θ y (V y) + Complex.I * θ y (J y (V y))) x W
      = (fderiv ℝ θ x W) (V x) + θ x (fderiv ℝ V x W)
        + Complex.I * ((fderiv ℝ θ x W) (J x (V x))
            + θ x (J x (fderiv ℝ V x W) + (fderiv ℝ J x W) (V x))) := by
  have hg1 : DifferentiableAt ℝ (fun y => θ y (V y)) x := hθ.clm_apply hV
  have hM : DifferentiableAt ℝ (fun y => J y (V y)) x := hJ.clm_apply hV
  have hg2 : DifferentiableAt ℝ (fun y => θ y (J y (V y))) x := hθ.clm_apply hM
  have hg2c : DifferentiableAt ℝ (fun y => Complex.I * θ y (J y (V y))) x := hg2.const_mul Complex.I
  change fderiv ℝ ((fun y => θ y (V y)) + (fun y => Complex.I * θ y (J y (V y)))) x W = _
  rw [fderiv_add hg1 hg2c, fderiv_const_mul hg2 Complex.I]
  rw [add_apply, smul_apply, smul_eq_mul]
  rw [fderiv_clm_apply_apply hθ hV W, fderiv_clm_apply_apply hθ hM W]
  rw [fderiv_clm_apply_apply hJ hV W]
  ring

/-- `∂̄u` is differentiable wherever `u` is `C²` and `J` is `C¹`. -/
theorem dbar_differentiableAt {n : ℕ} {J : E n → E n →L[ℝ] E n} {u : E n → ℂ} {x : E n}
    (hu : ContDiffAt ℝ 2 u x) (hJ : ContDiffAt ℝ 1 J x) :
    DifferentiableAt ℝ (Submission.dbar J u) x := by
  have hu1 : ContDiffAt ℝ 1 (fderiv ℝ u) x := hu.fderiv_right (m := 1) (by norm_num)
  have hdu : DifferentiableAt ℝ (fderiv ℝ u) x := hu1.differentiableAt (by norm_num)
  have hJd : DifferentiableAt ℝ J x := hJ.differentiableAt (by norm_num)
  have hcomp : DifferentiableAt ℝ (fun y => (fderiv ℝ u y).comp (J y)) x := hdu.clm_comp hJd
  have h1 : DifferentiableAt ℝ (fun y => Complex.I • ((fderiv ℝ u y).comp (J y))) x :=
    hcomp.const_smul Complex.I
  have hsum : DifferentiableAt ℝ
      (fun y => fderiv ℝ u y + Complex.I • ((fderiv ℝ u y).comp (J y))) x := hdu.add h1
  have hfin := hsum.const_smul (1/2 : ℝ)
  convert hfin using 1
  ext y
  simp [Submission.dbar]

/-- `dExterior` of a `1`-form in terms of the second derivative: applied to constant vectors it is
the antisymmetrisation of `fderiv θ`. -/
theorem dExterior_apply {n : ℕ} {θ : E n → E n →L[ℝ] ℂ} {x : E n}
    (hθ : DifferentiableAt ℝ θ x) (A B : E n) :
    dExterior θ x A B = (fderiv ℝ θ x A) B - (fderiv ℝ θ x B) A := by
  simp only [dExterior]
  rw [fderiv_apply_const hθ B A, fderiv_apply_const hθ A B]

/-- `dbarSq` with the `(0,1)`-form `∂̄u` replaced by an arbitrary `1`-form `θ`; by construction
`dbarSq J u = dbarSqOf J (∂̄u)`. -/
noncomputable def dbarSqOf {n : ℕ} (J : E n → E n →L[ℝ] E n) (θ : E n → E n →L[ℝ] ℂ)
    (X Y : E n → E n) (x : E n) : ℂ :=
  Submission.czderiv (fun y => Submission.cpair (θ y) (Submission.Z01 J Y y)) (Submission.Z01 J X) x
    - Submission.czderiv (fun y => Submission.cpair (θ y) (Submission.Z01 J X y)) (Submission.Z01 J Y) x
    - Submission.cpair (θ x) (Submission.cbracket (Submission.Z01 J X) (Submission.Z01 J Y) x)

/-- The isotypic decomposition of `dbarSqOf` into the four components of a `(0,2)`-tensor, before
projecting: the sum of the antisymmetrisations `θ'(A)(B) - θ'(B)(A)` with the weights forced by
the `(0,1)`-directions `X + iJX`, `Y + iJY`. -/
theorem dbarSqOf_eq {n : ℕ} {J : E n → E n →L[ℝ] E n} {θ : E n → E n →L[ℝ] ℂ}
    {X Y : E n → E n} {x : E n} (hθ : DifferentiableAt ℝ θ x) (hJ : DifferentiableAt ℝ J x)
    (hX : DifferentiableAt ℝ X x) (hY : DifferentiableAt ℝ Y x) :
    dbarSqOf J θ X Y x
      = (fderiv ℝ θ x (X x)) (Y x) - (fderiv ℝ θ x (Y x)) (X x)
        + Complex.I * ((fderiv ℝ θ x (J x (X x))) (Y x) - (fderiv ℝ θ x (Y x)) (J x (X x)))
        + Complex.I * ((fderiv ℝ θ x (X x)) (J x (Y x)) - (fderiv ℝ θ x (J x (Y x))) (X x))
        - ((fderiv ℝ θ x (J x (X x))) (J x (Y x)) - (fderiv ℝ θ x (J x (Y x))) (J x (X x))) := by
  simp only [dbarSqOf, Submission.czderiv, Submission.Z01, Submission.cpair]
  rw [cpair_Z01_fderiv hθ hJ hY (X x), cpair_Z01_fderiv hθ hJ hY (J x (X x)),
      cpair_Z01_fderiv hθ hJ hX (Y x), cpair_Z01_fderiv hθ hJ hX (J x (Y x))]
  simp only [Submission.cbracket, Submission.Z01, VectorField.lieBracket]
  rw [fderiv_clm_apply_apply hJ hY (J x (X x)), fderiv_clm_apply_apply hJ hX (J x (Y x)),
      fderiv_clm_apply_apply hJ hY (X x), fderiv_clm_apply_apply hJ hX (Y x)]
  simp only [map_sub, map_add]
  ring_nf
  simp only [pow_two, Complex.I_mul_I]
  ring

/-- **The `(0,2)`-part of `d(∂̄u)`.**  `dbarSq J u X Y x` is four times the `(0,2)`-part of the
exterior derivative of the `(0,1)`-form `∂̄u`: it is the value of `proj02` on the exterior
derivative `dExterior (dbar J u) x` of `∂̄u`, evaluated on the vectors `X x`, `Y x`. -/
theorem dbarSq_eq_four_proj02 {n : ℕ} {J : E n → E n →L[ℝ] E n} {u : E n → ℂ}
    {X Y : E n → E n} {x : E n} (hu : ContDiffAt ℝ 2 u x) (hJ : ContDiffAt ℝ 1 J x)
    (hX : ContDiffAt ℝ 1 X x) (hY : ContDiffAt ℝ 1 Y x) :
    Submission.dbarSq J u X Y x
      = (4 : ℂ) * proj02 (J x) (fun A B => dExterior (Submission.dbar J u) x A B) (X x) (Y x) := by
  have hθ : DifferentiableAt ℝ (Submission.dbar J u) x := dbar_differentiableAt hu hJ
  have hJd : DifferentiableAt ℝ J x := hJ.differentiableAt (by norm_num)
  have hXd : DifferentiableAt ℝ X x := hX.differentiableAt (by norm_num)
  have hYd : DifferentiableAt ℝ Y x := hY.differentiableAt (by norm_num)
  rw [show Submission.dbarSq J u X Y x = dbarSqOf J (Submission.dbar J u) X Y x from rfl]
  rw [dbarSqOf_eq hθ hJd hXd hYd]
  simp only [proj02]
  rw [dExterior_apply hθ (X x) (Y x), dExterior_apply hθ (J x (X x)) (Y x),
      dExterior_apply hθ (X x) (J x (Y x)), dExterior_apply hθ (J x (X x)) (J x (Y x))]
  ring

end Work.AlmostComplex.Types
