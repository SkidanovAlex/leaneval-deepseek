import Submission.Work.BoxShrink.PinchOff.Basic

/-!
# The rotation of `ℝ³` about the `x`-axis, and its effect on the plane coordinate

`README.md` §26 records the (numerical) claim that for `ψ` = the rotation of `ℝ³` about the
`x`-axis by `α = 1/4`, with the box centre `c = 0`, the cyclic permutation `σ = (0 2 1)` and
`u = 0`, "the trace of the cutting plane is a single contractible circle".  §27 corrects that
claim: the trace of `{y (σ 2) = u}` on the rotated torus is the zero set of

  `G(θ, φ) = cos α · (2 + cos φ) · sin θ − sin α · sin φ − u`,

whose level `0` is never a single contractible circle: the two points of the parameter torus at
which `G` is critical are *outside* the box, and the level set consists of the two graphs
`θ = ±arcsin (sin α · sin φ / (cos α · (2 + cos φ)))`, each of which closes up after one turn in
`φ` and therefore realises the winding vector `(0, 1) ≠ 0` (see `RotationTrace.lean`).

This module supplies the diffeomorphism and the formula.  Nothing here depends on the box.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-! ## The rotation as a diffeomorphism of `ℝ³` -/

/-- **The rotation of `ℝ³` about the `x`-axis by the angle `α`**, in coordinates. -/
def rotFun (α : ℝ) : R3 → R3 := fun p =>
  WithLp.toLp 2 (fun i : Fin 3 =>
    if i.val = 0 then p 0
    else if i.val = 1 then Real.cos α * p 1 - Real.sin α * p 2
    else Real.sin α * p 1 + Real.cos α * p 2)

@[simp] theorem rotFun_coord_zero (α : ℝ) (p : R3) : rotFun α p 0 = p 0 := by
  rw [rotFun, PiLp.toLp_apply]; simp

@[simp] theorem rotFun_coord_one (α : ℝ) (p : R3) :
    rotFun α p 1 = Real.cos α * p 1 - Real.sin α * p 2 := by
  rw [rotFun, PiLp.toLp_apply]; simp

@[simp] theorem rotFun_coord_two (α : ℝ) (p : R3) :
    rotFun α p 2 = Real.sin α * p 1 + Real.cos α * p 2 := by
  rw [rotFun, PiLp.toLp_apply]; simp

/-- The rotation by `−α` inverts the rotation by `α`. -/
theorem rotFun_comp_neg (α : ℝ) (p : R3) : rotFun α (rotFun (-α) p) = p := by
  ext i
  fin_cases i
  · show rotFun α (rotFun (-α) p) 0 = p 0
    rw [rotFun_coord_zero, rotFun_coord_zero]
  · show rotFun α (rotFun (-α) p) 1 = p 1
    rw [rotFun_coord_one, rotFun_coord_one, rotFun_coord_two, Real.cos_neg, Real.sin_neg]
    have h : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
    linear_combination (norm := ring) (p.ofLp 1) * h
  · show rotFun α (rotFun (-α) p) 2 = p 2
    rw [rotFun_coord_two, rotFun_coord_one, rotFun_coord_two, Real.cos_neg, Real.sin_neg]
    have h : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
    linear_combination (norm := ring) (p.ofLp 2) * h

theorem contDiff_rotFun (α : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (rotFun α) := by
  unfold rotFun
  refine (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.contDiff.comp ?_
  rw [contDiff_pi]
  intro i
  fin_cases i <;>
    (simp only [Fin.isValue, Fin.mk_one, Fin.val_zero, Fin.val_one, Fin.val_two, ↓reduceIte,
      show ¬ ((1 : ℕ) = 0) from by norm_num, show ¬ ((2 : ℕ) = 0) from by norm_num,
      show ¬ ((2 : ℕ) = 1) from by norm_num, reduceCtorEq] ; fun_prop)

/-- **The rotation of `ℝ³` about the `x`-axis, as a diffeomorphism of `ℝ³`.** -/
def rotDiffeo (α : ℝ) : Submission.Diffeo where
  toFun := rotFun α
  invFun := rotFun (-α)
  smooth_toFun := contDiff_rotFun α
  smooth_invFun := contDiff_rotFun (-α)
  left_inv := fun p => by simpa using rotFun_comp_neg (-α) p
  right_inv := fun p => rotFun_comp_neg α p

@[simp] theorem rotDiffeo_apply (α : ℝ) (p : R3) : rotDiffeo α p = rotFun α p := rfl

/-! ## The permutation which puts the cutting plane in the `y`-coordinate -/

/-- **The cyclic permutation `σ = (0 2 1)`**: `σ 0 = 2`, `σ 1 = 0`, `σ 2 = 1`.  Its point is that
`σ 2 = 1`, so that the cutting plane `{y (σ 2) = u}` is the coordinate plane `{y = u}`. -/
def sigmaY : Equiv.Perm (Fin 3) := Equiv.swap (0 : Fin 3) 1 * Equiv.swap (0 : Fin 3) 2

@[simp] theorem sigmaY_zero : sigmaY 0 = 2 := by decide
@[simp] theorem sigmaY_one : sigmaY 1 = 0 := by decide
@[simp] theorem sigmaY_two : sigmaY 2 = 1 := by decide

/-! ## The plane coordinate of the rotated torus -/

/-- **The plane coordinate on the rotated torus, explicitly.**  At `c = 0` and `σ = sigmaY`
(so the cutting plane is `{y = u}`), the pull-back of the plane coordinate to the parameter plane
of `F = ψ(F_standard)`, `ψ = rotDiffeo α`, is

  `(θ, φ) ↦ cos α · (2 + cos φ) · sin θ − sin α · sin φ − u`.

Its gradient is `(cos α · (2 + cos φ) · cos θ, −cos α · sin φ · sin θ − sin α · cos φ)`, which
vanishes only at `θ ∈ {π/2, 3π/2}` with `φ ≡ −α`, `π − α`, `α`, `π + α`; at those points the value
of the plane coordinate is `±(2 cos α + 1)` or `±(2 cos α − 1)`, all of which are nonzero as soon as
`cos α ≠ 1/2`, `cos α ≠ −1/2` (see `_check_rot.py` and `README.md` §27.1). -/
theorem planeG_rotDiffeo (α : ℝ) (u : ℝ) (θ φ : ℝ) :
    Work.BoxShrink.Pinch.planeG (rotDiffeo α) 0 sigmaY u (θ, φ) =
      Real.cos α * (2 + Real.cos φ) * Real.sin θ - Real.sin α * Real.sin φ - u := by
  simp only [Work.BoxShrink.Pinch.planeG_apply, Work.BoxShrink.Bubble.planeCoord_apply,
    Work.BoxShrink.Pinch.par_apply, rotDiffeo_apply, rotFun_coord_one, sigmaY_two,
    Work.CoreTopology.torusMap_apply_one, Work.CoreTopology.torusMap_apply_two]
  simp
  ring

end

end Work.BoxShrink.PinchOff
