import Mathlib
import Submission.Work.RPA3.theta_columns_defs
import Submission.Work.RPA3.contDiff_thetaP

namespace Work.RPA3

/-! ## The four coordinate unit vectors of `ℝ × PS`

The four columns of the tubular map are obtained by differentiating `w ↦ thTheta L w` along the four
coordinate directions of the second factor `PS` of `ℝ × PS`.  This section records those four fixed
vectors. -/

/-- The four unit vectors `e 0 = (0,((1,0),(0,0)))`, `e 1 = (0,((0,1),(0,0)))`,
`e 2 = (0,((0,0),(1,0)))`, `e 3 = (0,((0,0),(0,1)))` of `ℝ × PS`. -/
def thUnit : Fin 4 → ℝ × PS :=
  ![((0 : ℝ), (((1 : ℝ), 0), (0, 0))),
    ((0 : ℝ), (((0 : ℝ), 1), (0, 0))),
    ((0 : ℝ), (((0 : ℝ), 0), (1, 0))),
    ((0 : ℝ), (((0 : ℝ), 0), (0, 1)))]

@[simp] theorem thUnit_zero : thUnit 0 = ((0 : ℝ), (((1 : ℝ), 0), (0, 0))) := rfl
@[simp] theorem thUnit_one : thUnit 1 = ((0 : ℝ), (((0 : ℝ), 1), (0, 0))) := rfl
@[simp] theorem thUnit_two : thUnit 2 = ((0 : ℝ), (((0 : ℝ), 0), (1, 0))) := rfl
@[simp] theorem thUnit_three : thUnit 3 = ((0 : ℝ), (((0 : ℝ), 0), (0, 1))) := rfl

/-! ## The chain rule along the affine coordinate lines

Each of the four one-dimensional functions whose derivative defines `thCol L j` is `y ↦ thTheta L w`
composed with the affine line `y ↦ c + y • e j` through `w`.  This sections proves the elementary
`HasDerivAt` statements for those affine lines and performs the chain rule once and for all. -/

/-- The affine line `y ↦ c + y • e` has derivative `e` everywhere. -/
theorem hasDerivAt_affine (c e : ℝ × PS) (x : ℝ) :
    HasDerivAt (fun y : ℝ => c + y • e) e x := by
  have h := ContinuousLinearMap.hasDerivAt (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) e)
    (x := x)
  simpa using h.const_add c

/-- Every column of the tubular map is the Fréchet derivative of `thTheta L` at `w`, applied to the
corresponding fixed coordinate vector `thUnit j`:
`thCol L j w = fderiv ℝ (thTheta L) w (thUnit j)`. -/
theorem thCol_eq_fderiv (L : LagFamilyAll) (j : Fin 4) (w : ℝ × PS) :
    thCol L j w = fderiv ℝ (thTheta L) w (thUnit j) := by
  have hθ : HasFDerivAt (thTheta L) (fderiv ℝ (thTheta L) w) w :=
    ((contDiff_thetaZ L).differentiable (by norm_num)).differentiableAt.hasFDerivAt
  fin_cases j
  · have hφ : HasDerivAt (fun y : ℝ => (w.1, ((y, w.2.1.2), w.2.2))) (thUnit 0) w.2.1.1 := by
      have h := hasDerivAt_affine ((w.1, (((0 : ℝ), w.2.1.2), w.2.2)) : ℝ × PS) (thUnit 0)
        w.2.1.1
      convert h using 1
      funext y
      simp [thUnit, Prod.ext_iff]
    have hc := hθ.comp_hasDerivAt w.2.1.1 hφ
    simp only [Function.comp_def, thTheta_apply] at hc
    exact hc.deriv
  · have hφ : HasDerivAt (fun y : ℝ => (w.1, ((w.2.1.1, y), w.2.2))) (thUnit 1) w.2.1.2 := by
      have h := hasDerivAt_affine ((w.1, ((w.2.1.1, (0 : ℝ)), w.2.2)) : ℝ × PS) (thUnit 1)
        w.2.1.2
      convert h using 1
      funext y
      simp [thUnit, Prod.ext_iff]
    have hc := hθ.comp_hasDerivAt w.2.1.2 hφ
    simp only [Function.comp_def, thTheta_apply] at hc
    exact hc.deriv
  · have hφ : HasDerivAt (fun y : ℝ => (w.1, ((w.2.1.1, w.2.1.2), (y, w.2.2.2)))) (thUnit 2)
        w.2.2.1 := by
      have h := hasDerivAt_affine ((w.1, ((w.2.1.1, w.2.1.2), ((0 : ℝ), w.2.2.2))) : ℝ × PS)
        (thUnit 2) w.2.2.1
      convert h using 1
      funext y
      simp [thUnit, Prod.ext_iff]
    have hc := hθ.comp_hasDerivAt w.2.2.1 hφ
    simp only [Function.comp_def, thTheta_apply] at hc
    exact hc.deriv
  · have hφ : HasDerivAt (fun y : ℝ => (w.1, ((w.2.1.1, w.2.1.2), (w.2.2.1, y)))) (thUnit 3)
        w.2.2.2 := by
      have h := hasDerivAt_affine ((w.1, ((w.2.1.1, w.2.1.2), (w.2.2.1, (0 : ℝ)))) : ℝ × PS)
        (thUnit 3) w.2.2.2
      convert h using 1
      funext y
      simp [thUnit, Prod.ext_iff]
    have hc := hθ.comp_hasDerivAt w.2.2.2 hφ
    simp only [Function.comp_def, thTheta_apply] at hc
    exact hc.deriv

/-- `w ↦ fderiv ℝ (thTheta L) w (thUnit j)` is continuous, because `thTheta L` is `C⁷` and the
Fréchet derivative of a `C¹` map is continuous in both variables. -/
theorem continuous_fderiv_thUnit (L : LagFamilyAll) (j : Fin 4) :
    Continuous (fun w : ℝ × PS => fderiv ℝ (thTheta L) w (thUnit j)) := by
  have hc := (contDiff_thetaZ L).continuous_fderiv_apply (by norm_num : (7 : WithTop ℕ∞) ≠ 0)
  exact hc.comp (continuous_id.prodMk continuous_const)

/-- **D2, continuity of the four columns of the tubular map.**  Each of `∂_xθ, ∂_tθ, ∂_{ξ₁}θ,
∂_{ξ₂}θ`, as a function of `w = (τ,((x,t),ξ)) : ℝ × PS` (where `PS = (ℝ×ℝ)×(ℝ×ℝ)`), is
continuous.

Proof sketch.  `Work.RPA3.thCol L j` is `deriv (fun y => theta L w.1 y w.2.1.2 w.2.2) w.2.1.1`
for `j = 0` and similarly for `j = 1,2,3` (see the `simp` lemmas `thCol_zero` ... `thCol_three`;
beware that `fin_cases` produces `Fin.mk 0 ⋯`, which may need `Fin.reduceFinMk` or an explicit
`show`/`convert`).  Also `Work.RPA3.thTheta L w = theta L w.1 w.2.1.1 w.2.1.2 w.2.2` is
definitionally `thetaZ L w.1 w.2`, so `contDiff_thetaZ` from
`Submission.Work.RPA3.contDiff_thetaP` gives `ContDiff ℝ 7 (thTheta L)`.

By the chain rule along the affine embedding `y ↦ (w.1, ((y, w.2.1.2), w.2.2))`
(`HasFDerivAt.comp_hasDerivAt`, the affine map having derivative the constant vector
`(0,((1,0),(0,0)))`), each column equals `fderiv ℝ (thTheta L) w` applied to a *fixed* vector
`e j`: `e 0 = (0,((1,0),(0,0)))`, `e 1 = (0,((0,1),(0,0)))`, `e 2 = (0,((0,0),(1,0)))`,
`e 3 = (0,((0,0),(0,1)))` in `ℝ × PS`.  `ContDiff.continuous_fderiv_apply` applied to
`ContDiff ℝ 7 (thTheta L)` gives continuity of `(w,v) ↦ fderiv ℝ (thTheta L) w v`; composing with
`w ↦ (w, e j)` gives continuity of each column. -/
theorem continuous_thCol (L : Work.RPA3.LagFamilyAll) :
    ∀ j : Fin 4, Continuous (Work.RPA3.thCol L j) := by
  intro j
  rw [funext (thCol_eq_fderiv L j)]
  exact continuous_fderiv_thUnit L j

end Work.RPA3
