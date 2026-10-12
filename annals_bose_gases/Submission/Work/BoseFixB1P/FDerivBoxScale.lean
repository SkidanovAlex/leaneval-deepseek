import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1P.IntegralBoxScaleImage
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The chain rule for the box rescaling

`Work.BoseFixB1P.boxScale a p q` is the affine map whose `j`-th coordinate is
`p_j + (y_j + a/2)·(q_j - p_j)/a`.  This module computes the directional derivative of the
pullback `u ∘ boxScale a p q` along the standard basis vector `kcStdBasis k`:

    `∂_k (u ∘ boxScale a p q)(y) = ((q_k - p_k)/a) · (∂_k u)(boxScale a p q y)`.

This is the second input of the rescaling step reducing `Work.BoseFixB1P.boxPoincareSharp` to its
cube case.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators
open Submission.BoseGases

namespace Work.BoseFixB1P

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The coordinatewise multiplication on `Fin 3 → ℝ` is smooth. -/
lemma contDiff_coordMul (c : Fin 3 → ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun f : Fin 3 → ℝ => fun j => c j * f j) := by
  rw [contDiff_pi]
  intro j
  fun_prop

/-- `cgEuc3` is smooth. -/
lemma contDiff_cgEuc3 {n : WithTop ℕ∞} : ContDiff ℝ n (⇑cgEuc3) :=
  PiLp.contDiff_toLp

/-- `cgEuc3.symm` is smooth. -/
lemma contDiff_cgEuc3_symm {n : WithTop ℕ∞} : ContDiff ℝ n (⇑cgEuc3.symm) :=
  PiLp.contDiff_ofLp

/-- The diagonal scaling is smooth. -/
lemma contDiff_diagScale (c : Fin 3 → ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (diagScale c) :=
  (contDiff_cgEuc3 (n := n)).comp ((contDiff_coordMul c (n := n)).comp contDiff_cgEuc3_symm)

/-- The box rescaling is smooth. -/
lemma contDiff_boxScale (a : ℝ) (p q : Fin 3 → ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (boxScale a p q) := by
  have h : boxScale a p q
      = fun y : E3 => diagScale (fun j => (q j - p j) / a) y
          + cgEuc3 (fun j => p j + (a / 2) * ((q j - p j) / a)) := by
    funext y
    exact boxScale_eq_diagScale_add a p q y
  rw [h]
  exact (contDiff_diagScale (fun j => (q j - p j) / a) (n := n)).add
    (contDiff_const : ContDiff ℝ n (fun _ : E3 => cgEuc3
      (fun j => p j + (a / 2) * ((q j - p j) / a))))

/-- The pullback of a smooth function under the rescaling is smooth. -/
lemma contDiff_comp_boxScale {u : E3 → ℝ} (hu : ContDiff ℝ (⊤ : ENat) u)
    (a : ℝ) (p q : Fin 3 → ℝ) :
    ContDiff ℝ (⊤ : ENat) (fun y : E3 => u (boxScale a p q y)) :=
  hu.comp (contDiff_boxScale a p q (n := (⊤ : ENat)))

/-- The rescaling is differentiable. -/
lemma differentiable_boxScale (a : ℝ) (p q : Fin 3 → ℝ) : Differentiable ℝ (boxScale a p q) :=
  (contDiff_boxScale a p q (n := (⊤ : ENat))).differentiable (by simp)

/-- **The curve formula** for the rescaling along a coordinate direction: moving `t` in the
direction `kcStdBasis k` moves the image along `((q_k - p_k)/a) • kcStdBasis k`. -/
lemma boxScale_add_smul_basis (a : ℝ) (p q : Fin 3 → ℝ) (y : E3) (k : Fin 3) (t : ℝ) :
    boxScale a p q (y + t • kcStdBasis k)
      = boxScale a p q y + t • (((q k - p k) / a) • kcStdBasis k) := by
  ext j
  simp only [boxScale_apply, PiLp.add_apply, PiLp.smul_apply, WithLp.ofLp_smul, Pi.smul_apply,
    kcStdBasis, PiLp.single_apply]
  split_ifs with hjk
  · subst hjk
    ring
  · ring

/-- **The chain rule for the box rescaling.** -/
theorem fderiv_boxScale {a : ℝ} (ha : 0 < a) (p q : Fin 3 → ℝ) {u : E3 → ℝ}
    (hu : ContDiff ℝ (⊤ : ENat) u) (k : Fin 3) (y : E3) :
    fderiv ℝ (fun y => u (boxScale a p q y)) y (kcStdBasis k)
      = ((q k - p k) / a) * fderiv ℝ u (boxScale a p q y) (kcStdBasis k) := by
  set c : ℝ := (q k - p k) / a with hc
  have hdiff : DifferentiableAt ℝ (fun y : E3 => u (boxScale a p q y)) y :=
    ((contDiff_comp_boxScale hu a p q).differentiable (by simp)) y
  have hγ : HasDerivAt (fun t : ℝ => y + t • kcStdBasis k) (kcStdBasis k) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (kcStdBasis k)).const_add y
  have hdiff' : HasFDerivAt (fun y : E3 => u (boxScale a p q y))
      (fderiv ℝ (fun y : E3 => u (boxScale a p q y))
        ((fun t : ℝ => y + t • kcStdBasis k) 0))
      ((fun t : ℝ => y + t • kcStdBasis k) 0) := by
    simpa only [zero_smul, add_zero] using hdiff.hasFDerivAt
  have hcomp := HasFDerivAt.comp_hasDerivAt (0 : ℝ) hdiff' hγ
  have hlin : fderiv ℝ (fun y : E3 => u (boxScale a p q y)) y (kcStdBasis k)
      = deriv (fun t : ℝ => u (boxScale a p q (y + t • kcStdBasis k))) 0 := by
    have h := hcomp.deriv.symm
    rw [show ((fun y : E3 => u (boxScale a p q y)) ∘ (fun t : ℝ => y + t • kcStdBasis k))
        = (fun t : ℝ => u (boxScale a p q (y + t • kcStdBasis k))) from rfl] at h
    simpa only [zero_smul, add_zero] using h
  rw [hlin]
  rw [show (fun t : ℝ => u (boxScale a p q (y + t • kcStdBasis k)))
      = fun t : ℝ => u (boxScale a p q y + t • (c • kcStdBasis k)) from
    funext (fun t => by rw [hc, boxScale_add_smul_basis])]
  have hγ2 : HasDerivAt (fun t : ℝ => boxScale a p q y + t • (c • kcStdBasis k))
      (c • kcStdBasis k) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (c • kcStdBasis k)).const_add
      (boxScale a p q y)
  have hu' : HasFDerivAt u (fderiv ℝ u ((fun t : ℝ => boxScale a p q y + t • (c • kcStdBasis k)) 0))
      ((fun t : ℝ => boxScale a p q y + t • (c • kcStdBasis k)) 0) := by
    simpa only [zero_smul, add_zero] using
      ((hu.differentiable (by simp)) (boxScale a p q y)).hasFDerivAt
  have hcomp2 := HasFDerivAt.comp_hasDerivAt (0 : ℝ) hu' hγ2
  have hderiv : deriv (fun t : ℝ => u (boxScale a p q y + t • (c • kcStdBasis k))) 0
      = (fderiv ℝ u (boxScale a p q y)) (c • kcStdBasis k) := by
    have h := hcomp2.deriv
    rw [show (u ∘ (fun t : ℝ => boxScale a p q y + t • (c • kcStdBasis k)))
        = (fun t : ℝ => u (boxScale a p q y + t • (c • kcStdBasis k))) from rfl] at h
    simpa only [zero_smul, add_zero] using h
  rw [hderiv, map_smul, smul_eq_mul, hc]

end Work.BoseFixB1P
