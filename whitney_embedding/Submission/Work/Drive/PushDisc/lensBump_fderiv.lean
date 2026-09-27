import Mathlib
import Submission.Work.Drive.PushDisc.lensRegularDefs

/-!
# The Fréchet derivative of the lens bumps

`lensBump ρ k p = lensChi ρ p.1 * lensAlpha k.2 p.1 * lensZeta k.1 p.2 (arch p.1)` is a product of
a function of `p.1` alone with a function of `p.2` and `arch p.1`.  This file computes its Fréchet
derivative at an arbitrary point `p`, in the two coordinate directions:

    ∂ₓ (lensBump ρ k) p
      = (lensChi ρ · * lensAlpha k.2 ·)' p.1 * lensZeta k.1 p.2 (arch p.1)
        + (lensChi ρ p.1 * lensAlpha k.2 p.1) * arch' p.1
            * (∂₂ lensZeta k.1) p.2 (arch p.1),
    ∂_y (lensBump ρ k) p
      = (lensChi ρ p.1 * lensAlpha k.2 p.1) * (∂₁ lensZeta k.1) p.2 (arch p.1).

The only general input is `fderiv_apply_one_zero` / `fderiv_apply_zero_one`: for `f : ℝ × ℝ → ℝ`
the Fréchet derivative applied to a coordinate vector is the corresponding (one-variable) partial
derivative.  Both are obtained from the chain rule `HasFDerivAt.comp_hasDerivAt` along the axis
curve, so no bivariate FDeriv calculus is needed.

Note that the hypothesis `ρ > 0` is not used: the identity holds for every `ρ`.
-/

namespace Work.Drive.PushDisc

open scoped Manifold ContDiff ENNReal
open Set Metric MeasureTheory Topology Filter

/-- The first partial derivative of a function on `ℝ × ℝ`, as the derivative of the section
`t ↦ f (t, p.2)` at `p.1`. -/
private lemma fderiv_apply_one_zero {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hf : DifferentiableAt ℝ f p) :
    fderiv ℝ f p (1, 0) = deriv (fun t : ℝ => f (t, p.2)) p.1 := by
  have hg : HasDerivAt (fun t : ℝ => (t, p.2)) (1, 0) p.1 :=
    (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  have h := hf.hasFDerivAt.comp_hasDerivAt p.1 hg
  rw [← h.deriv]
  rfl

/-- The second partial derivative of a function on `ℝ × ℝ`, as the derivative of the section
`t ↦ f (p.1, t)` at `p.2`. -/
private lemma fderiv_apply_zero_one {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hf : DifferentiableAt ℝ f p) :
    fderiv ℝ f p (0, 1) = deriv (fun t : ℝ => f (p.1, t)) p.2 := by
  have hg : HasDerivAt (fun t : ℝ => (p.1, t)) (0, 1) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  have h := hf.hasFDerivAt.comp_hasDerivAt p.2 hg
  rw [← h.deriv]
  rfl

/-- `arch x = 1 - x ^ 2` is differentiable. -/
private lemma differentiableAt_arch (x : ℝ) : DifferentiableAt ℝ arch x := by
  show DifferentiableAt ℝ (fun x : ℝ => 1 - x ^ 2) x
  fun_prop

/-- `lensZeta i y ·` is differentiable (it is a polynomial in the last variable). -/
private lemma differentiableAt_lensZeta_left (i : Fin 2) (y v : ℝ) :
    DifferentiableAt ℝ (fun u : ℝ => lensZeta i y u) v := by
  by_cases h : i = 0
  · rw [h]; simp only [lensZeta_zero_fun]; fun_prop
  · have hi : i = 1 := by omega
    rw [hi]; simp only [lensZeta_one_fun]; fun_prop

/-- `lensZeta i · u` is differentiable (it is a polynomial in the first variable). -/
private lemma differentiableAt_lensZeta_right (i : Fin 2) (u v : ℝ) :
    DifferentiableAt ℝ (fun y : ℝ => lensZeta i y u) v := by
  by_cases h : i = 0
  · rw [h]; simp only [lensZeta_zero_fun]; fun_prop
  · have hi : i = 1 := by omega
    rw [hi]; simp only [lensZeta_one_fun]; fun_prop

/-- `lensChi ρ · * lensAlpha j ·` is differentiable. -/
private lemma differentiableAt_lensChi_mul_lensAlpha (ρ : ℝ) (j : Fin 2) (x : ℝ) :
    DifferentiableAt ℝ (fun t : ℝ => lensChi ρ t * lensAlpha j t) x :=
  ((contDiff_lensChi (ρ := ρ)).mul (contDiff_lensAlpha j)).contDiffAt.differentiableAt (by simp)

/-- `lensBump ρ k` is differentiable everywhere. -/
private lemma differentiableAt_lensBump (ρ : ℝ) (k : Fin 2 × Fin 2) (p : ℝ × ℝ) :
    DifferentiableAt ℝ (lensBump ρ k) p :=
  (contDiff_lensBump ρ k).contDiffAt.differentiableAt (by simp)

/-- **The Fréchet derivative of the lens bumps** in the two coordinate directions. -/
theorem lensBump_fderiv {ρ : ℝ} (hρ : 0 < ρ) (k : Fin 2 × Fin 2) (p : ℝ × ℝ) :
    fderiv ℝ (lensBump ρ k) p (1, 0)
      = deriv (fun t : ℝ => lensChi ρ t * lensAlpha k.2 t) p.1 * lensZeta k.1 p.2 (arch p.1)
        + (lensChi ρ p.1 * lensAlpha k.2 p.1) * deriv arch p.1
            * deriv (fun t : ℝ => lensZeta k.1 p.2 t) (arch p.1)
    ∧ fderiv ℝ (lensBump ρ k) p (0, 1)
      = (lensChi ρ p.1 * lensAlpha k.2 p.1)
          * deriv (fun t : ℝ => lensZeta k.1 t (arch p.1)) p.2 := by
  have hdiff : DifferentiableAt ℝ (lensBump ρ k) p := differentiableAt_lensBump ρ k p
  have darch : DifferentiableAt ℝ arch p.1 := differentiableAt_arch p.1
  have dZ : DifferentiableAt ℝ (fun t : ℝ => lensZeta k.1 p.2 t) (arch p.1) :=
    differentiableAt_lensZeta_left k.1 p.2 (arch p.1)
  have d1 : DifferentiableAt ℝ (fun t : ℝ => lensChi ρ t * lensAlpha k.2 t) p.1 :=
    differentiableAt_lensChi_mul_lensAlpha ρ k.2 p.1
  constructor
  · rw [fderiv_apply_one_zero hdiff]
    rw [show (fun t : ℝ => lensBump ρ k (t, p.2))
        = (fun t : ℝ => lensChi ρ t * lensAlpha k.2 t)
          * (fun t : ℝ => lensZeta k.1 p.2 (arch t)) from rfl]
    have d2 : DifferentiableAt ℝ (fun t : ℝ => lensZeta k.1 p.2 (arch t)) p.1 :=
      dZ.comp p.1 darch
    rw [deriv_mul d1 d2]
    have hZchain : deriv (fun t : ℝ => lensZeta k.1 p.2 (arch t)) p.1
        = deriv (fun t : ℝ => lensZeta k.1 p.2 t) (arch p.1) * deriv arch p.1 := by
      rw [show (fun t : ℝ => lensZeta k.1 p.2 (arch t))
          = (fun t : ℝ => lensZeta k.1 p.2 t) ∘ arch from rfl]
      rw [deriv_comp p.1 dZ darch]
    rw [hZchain]
    ring
  · rw [fderiv_apply_zero_one hdiff]
    rw [show (fun t : ℝ => lensBump ρ k (p.1, t))
        = fun t : ℝ => (lensChi ρ p.1 * lensAlpha k.2 p.1) * lensZeta k.1 t (arch p.1) from rfl]
    have d3 : DifferentiableAt ℝ (fun t : ℝ => lensZeta k.1 t (arch p.1)) p.2 :=
      differentiableAt_lensZeta_right k.1 (arch p.1) p.2
    rw [deriv_const_mul (lensChi ρ p.1 * lensAlpha k.2 p.1) d3]

end Work.Drive.PushDisc
