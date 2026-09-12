import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Mirror of the kernel-field straightening algebra

Let `a, b, c : ℝ² → ℝ` be `C¹` on an open set `U` satisfying, at every
`x ∈ U`, the Gauss relation `a x * c x = (b x) ^ 2` (the shape operator has
zero determinant) and the two Codazzi relations
`∂₁a = ∂₀b`  (`fderiv a e₁ = fderiv b e₀`) and
`∂₀c = ∂₁b`  (`fderiv c e₀ = fderiv b e₁`).

For the *mirror* kernel vector field `y ↦ c(y)•e₀ − b(y)•e₁` (a kernel
vector of the symmetric shape matrix, since `c·(b,−c)ᵀ = 0` by Gauss), the
directional derivative of the field along itself is perpendicular to
`(b,c)`:

    b · (dw(w))₀ + c · (dw(w))₁ = 0.

This is the algebraic heart of the straightening lemma for the mirror
branch (`(a,b) ≠ (0,0)` fails); see `McStraight.Vf_deriv_parallel` for the
companion statement.  The proof is a first-order computation: expand the
derivative in the coordinate basis, use the two Codazzi relations, the
differentiated Gauss relation (obtained by differentiating the identity
`a·c − b² = 0`, which holds on the open neighbourhood `U` of `x`), and the
Gauss relation itself; the rest is polynomial arithmetic.
-/

namespace Commons.Analysis.Calculus.FDeriv

open Topology Filter

abbrev R2 := EuclideanSpace ℝ (Fin 2)

/-- Derivative of the mirror kernel field `y ↦ c(y)•e₀ − b(y)•e₁` applied to
the kernel direction at `x`, first coordinate. -/
lemma kernelFieldMirror_direction_perp_aux0 (c b : R2 → ℝ) (x : R2)
    (hdc : DifferentiableAt ℝ c x) (hdb : DifferentiableAt ℝ b x) :
    (fderiv ℝ (fun y : R2 =>
        (c y) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
        (-(b y)) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) x
        ((c x) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) -
         (b x) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) (0 : Fin 2)
      = c x * (fderiv ℝ c x (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)))
        - b x * (fderiv ℝ c x (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) := by
  have hdG0 : DifferentiableAt ℝ
      (fun y : R2 => (c y) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) x := by
    simpa using (hdc.smul_const (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)))
  have hdG1 : DifferentiableAt ℝ
      (fun y : R2 => (b y) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) x := by
    simpa using (hdb.smul_const (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)))
  have hfield :
      (fun y : R2 =>
        (c y) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
        (-(b y)) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) =
      (fun y : R2 => (c y) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) -
      (fun y : R2 => (b y) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) := by
    funext y
    simp [neg_smul, sub_eq_add_neg]
  rw [hfield]
  rw [fderiv_sub hdG0 hdG1]
  rw [fderiv_smul_const hdc (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))]
  rw [fderiv_smul_const hdb (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))]
  simp only [sub_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.map_sub, ContinuousLinearMap.map_smul]
  simp [EuclideanSpace.single]

/-- Derivative of the mirror kernel field `y ↦ c(y)•e₀ − b(y)•e₁` applied to
the kernel direction at `x`, second coordinate. -/
lemma kernelFieldMirror_direction_perp_aux1 (c b : R2 → ℝ) (x : R2)
    (hdc : DifferentiableAt ℝ c x) (hdb : DifferentiableAt ℝ b x) :
    (fderiv ℝ (fun y : R2 =>
        (c y) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
        (-(b y)) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) x
        ((c x) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) -
         (b x) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) (1 : Fin 2)
      = -(c x * (fderiv ℝ b x (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)))
          - b x * (fderiv ℝ b x (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)))) := by
  have hdG0 : DifferentiableAt ℝ
      (fun y : R2 => (c y) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) x := by
    simpa using (hdc.smul_const (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)))
  have hdG1 : DifferentiableAt ℝ
      (fun y : R2 => (b y) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) x := by
    simpa using (hdb.smul_const (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)))
  have hfield :
      (fun y : R2 =>
        (c y) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
        (-(b y)) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) =
      (fun y : R2 => (c y) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) -
      (fun y : R2 => (b y) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) := by
    funext y
    simp [neg_smul, sub_eq_add_neg]
  rw [hfield]
  rw [fderiv_sub hdG0 hdG1]
  rw [fderiv_smul_const hdc (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))]
  rw [fderiv_smul_const hdb (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))]
  simp only [sub_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.map_sub, ContinuousLinearMap.map_smul]
  simp [EuclideanSpace.single]

/-- Differentiate the Gauss identity `a·c = b²` (which holds on a
neighbourhood of `x`) in the second coordinate direction: at `x`,

`c·∂₁a + a·∂₁c = 2b·∂₁b`.

Here `s₁ := EuclideanSpace.single (1 : Fin 2) (1 : ℝ)` is the second basis
vector. -/
lemma kernelFieldMirror_direction_perp_gauss_deriv (a c b : R2 → ℝ) (x : R2)
    (hda : DifferentiableAt ℝ a x) (hdb : DifferentiableAt ℝ b x)
    (hdc : DifferentiableAt ℝ c x)
    (hGzero : ∀ᶠ y in 𝓝 x, a y * c y - b y * b y = 0) :
    c x * (fderiv ℝ a x (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) +
    a x * (fderiv ℝ c x (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) =
    2 * b x * (fderiv ℝ b x (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) := by
  have hdG1 : DifferentiableAt ℝ (fun y : R2 => a y * c y) x := hda.mul hdc
  have hdG2 : DifferentiableAt ℝ (fun y : R2 => b y * b y) x := hdb.mul hdb
  have hfderivG : fderiv ℝ (fun y : R2 => a y * c y - b y * b y) x = 0 := by
    have hev : (fun y : R2 => a y * c y - b y * b y) =ᶠ[𝓝 x] (fun _ : R2 => (0 : ℝ)) := by
      filter_upwards [hGzero] with y hy
      exact hy
    calc
      fderiv ℝ (fun y : R2 => a y * c y - b y * b y) x
          = fderiv ℝ (fun _ : R2 => (0 : ℝ)) x := hev.fderiv_eq
      _ = 0 := by simp
  have hGapp :
      fderiv ℝ (fun y : R2 => a y * c y - b y * b y) x
        (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) = 0 := by
    rw [hfderivG]
    simp
  have hGexpand :
      fderiv ℝ (fun y : R2 => a y * c y - b y * b y) x =
      fderiv ℝ (fun y : R2 => a y * c y) x -
        fderiv ℝ (fun y : R2 => b y * b y) x := by
    change fderiv ℝ ((fun y : R2 => a y * c y) - (fun y : R2 => b y * b y)) x =
      fderiv ℝ (fun y : R2 => a y * c y) x -
        fderiv ℝ (fun y : R2 => b y * b y) x
    exact fderiv_sub hdG1 hdG2
  have hprod1 : fderiv ℝ (fun y : R2 => a y * c y) x =
      a x • fderiv ℝ c x + c x • fderiv ℝ a x :=
    fderiv_mul hda hdc
  have hprod2 : fderiv ℝ (fun y : R2 => b y * b y) x =
      b x • fderiv ℝ b x + b x • fderiv ℝ b x :=
    fderiv_mul hdb hdb
  have hGapp' :
      (fderiv ℝ (fun y : R2 => a y * c y) x -
        fderiv ℝ (fun y : R2 => b y * b y) x)
        (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) = 0 := by
    rwa [← hGexpand]
  have hfinal :
      a x * (fderiv ℝ c x (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) +
      c x * (fderiv ℝ a x (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) -
      (b x * (fderiv ℝ b x (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) +
       b x * (fderiv ℝ b x (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)))) = 0 := by
    rw [hprod1, hprod2] at hGapp'
    simpa [sub_apply, add_apply] using hGapp'
  nlinarith

theorem kernelFieldMirror_direction_perp
    {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsOpen U)
    (a b c : EuclideanSpace ℝ (Fin 2) → ℝ)
    (ha : ContDiffOn ℝ 1 a U) (hb : ContDiffOn ℝ 1 b U) (hc : ContDiffOn ℝ 1 c U)
    (hgauss : ∀ x ∈ U, a x * c x = (b x) ^ 2)
    (hcod1 : ∀ x ∈ U,
      fderiv ℝ a x (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) =
      fderiv ℝ b x (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)))
    (hcod2 : ∀ x ∈ U,
      fderiv ℝ c x (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) =
      fderiv ℝ b x (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) :
    ∀ x ∈ U, let w : EuclideanSpace ℝ (Fin 2) :=
        (c x) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
        (-b x) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)
      b x * ((fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
        (c y) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
        (-b y) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) x w) (0 : Fin 2)) +
      c x * ((fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
        (c y) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
        (-b y) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) x w) (1 : Fin 2)) = 0 := by
  intro x hx
  -- differentiability of a, b, c at x (U is open and contains x)
  have hda : DifferentiableAt ℝ a x :=
    (ha.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)).differentiableAt
      (hU.mem_nhds hx)
  have hdb : DifferentiableAt ℝ b x :=
    (hb.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)).differentiableAt
      (hU.mem_nhds hx)
  have hdc : DifferentiableAt ℝ c x :=
    (hc.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)).differentiableAt
      (hU.mem_nhds hx)
  -- rewrite the kernel direction (c x)•e₀ + (-b x)•e₁ in difference form
  have hw : (c x) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
      (-(b x)) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) =
      (c x) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) -
      (b x) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) := by
    simp [neg_smul, sub_eq_add_neg]
  dsimp
  rw [hw]
  -- component 0 and component 1 of the directional derivative
  have hD0 :
      (fderiv ℝ (fun y : R2 =>
        (c y) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
        (-(b y)) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) x
        ((c x) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) -
         (b x) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) (0 : Fin 2)
      = c x * (fderiv ℝ c x (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)))
        - b x * (fderiv ℝ c x (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) :=
    kernelFieldMirror_direction_perp_aux0 c b x hdc hdb
  have hD1 :
      (fderiv ℝ (fun y : R2 =>
        (c y) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
        (-(b y)) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) x
        ((c x) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) -
         (b x) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) (1 : Fin 2)
      = -(c x * (fderiv ℝ b x (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)))
          - b x * (fderiv ℝ b x (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)))) :=
    kernelFieldMirror_direction_perp_aux1 c b x hdc hdb
  rw [hD0, hD1]
  -- Codazzi relations at x
  have hcod2x : fderiv ℝ c x (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) =
      fderiv ℝ b x (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) := hcod2 x hx
  have hcod1x : fderiv ℝ b x (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) =
      fderiv ℝ a x (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) :=
    (hcod1 x hx).symm
  rw [hcod2x, hcod1x]
  -- Gauss relation and its derivative in the second coordinate direction
  have hgaussx : a x * c x = (b x) ^ 2 := hgauss x hx
  have hGzero : ∀ᶠ y in 𝓝 x, a y * c y - b y * b y = 0 := by
    filter_upwards [hU.mem_nhds hx] with y hy
    have := hgauss y hy
    nlinarith
  have hGd :
      c x * (fderiv ℝ a x (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) +
      a x * (fderiv ℝ c x (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) =
      2 * b x * (fderiv ℝ b x (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) :=
    kernelFieldMirror_direction_perp_gauss_deriv a c b x hda hdb hdc hGzero
  -- pure algebra
  calc
    b x * (c x * (fderiv ℝ b x (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) -
        b x * (fderiv ℝ c x (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)))) +
      c x * (-(c x * (fderiv ℝ a x (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) -
          b x * (fderiv ℝ b x (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)))))
        = 2 * b x * c x *
            (fderiv ℝ b x (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) -
          (b x) ^ 2 * (fderiv ℝ c x (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) -
          (c x) ^ 2 * (fderiv ℝ a x (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) := by
          ring
    _ = c x * (2 * b x *
            (fderiv ℝ b x (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)))) -
          (b x) ^ 2 * (fderiv ℝ c x (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) -
          (c x) ^ 2 * (fderiv ℝ a x (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) := by
          ring
    _ = c x * (c x * (fderiv ℝ a x (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) +
            a x * (fderiv ℝ c x (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)))) -
          (b x) ^ 2 * (fderiv ℝ c x (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) -
          (c x) ^ 2 * (fderiv ℝ a x (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) := by
          rw [← hGd]
    _ = (c x) ^ 2 * (fderiv ℝ a x (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) +
          a x * c x * (fderiv ℝ c x (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) -
          (b x) ^ 2 * (fderiv ℝ c x (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) -
          (c x) ^ 2 * (fderiv ℝ a x (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) := by
          ring
    _ = 0 := by
          rw [hgaussx]
          ring

end Commons.Analysis.Calculus.FDeriv