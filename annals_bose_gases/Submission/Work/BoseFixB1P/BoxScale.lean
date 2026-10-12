import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1P.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1P` — the diagonal rescaling of a box onto a cube

This module fixes the vocabulary for the reduction of

`Work.BoseFixB1P.boxPoincareSharp`

(the sharp mean-free Poincaré inequality `π²/a² ∫_B u² ≤ ∫_B Σ_k (∂_k u)²` on an
axis-parallel box `B = Box3 p q` with all sides `≤ a`) to the case of the centred cube
`acube a`, where the two proved Neumann Parseval identities are available.

The box `Box3 p q` is the image of the cube `acube a` under the diagonal affine map
`boxScale a p q`, whose `j`-th coordinate is `p_j + (y_j + a/2)·(q_j - p_j)/a`; the
associated *linear* part is the diagonal scaling `diagScale c` with `c_j = (q_j-p_j)/a`.

## Contents

* `diagScale c` — the diagonal scaling `x ↦ (c_j x_j)_j` on `E3 = EuclideanSpace ℝ (Fin 3)`;
* `boxScale a p q` — the affine map taking `acube a` onto `Box3 p q`;
* the coordinate formulas `diagScale_apply`, `boxScale_apply`.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1P

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The Euclidean space `ℝ³` used throughout. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- **The diagonal scaling** `x ↦ (c_j · x_j)_j` of `ℝ³`.  It is written through the
measurable equivalence `cgEuc3 : (Fin 3 → ℝ) ≃ᵐ ℝ³` so that the coordinate formula is
available by `simp`. -/
def diagScale (c : Fin 3 → ℝ) (x : E3) : E3 :=
  cgEuc3 (fun j => c j * cgEuc3.symm x j)

/-- **The affine map taking the cube `acube a` onto the box `Box3 p q`**: its `j`-th
coordinate is `p_j + (y_j + a/2)·((q_j - p_j)/a)`. -/
def boxScale (a : ℝ) (p q : Fin 3 → ℝ) (y : E3) : E3 :=
  cgEuc3 (fun j => p j + (cgEuc3.symm y j + a / 2) * ((q j - p j) / a))

@[simp] lemma cgEuc3_apply (f : Fin 3 → ℝ) (j : Fin 3) : cgEuc3 f j = f j := by
  simp [cgEuc3, WithLp.ofLp_toLp]

@[simp] lemma cgEuc3_symm_apply (x : E3) (j : Fin 3) : cgEuc3.symm x j = x j := by
  simp [cgEuc3, WithLp.ofLp_toLp]

@[simp] lemma diagScale_apply (c : Fin 3 → ℝ) (x : E3) (j : Fin 3) :
    diagScale c x j = c j * x j := by
  simp [diagScale, cgEuc3, WithLp.ofLp_toLp]

@[simp] lemma diagScale_zero (c : Fin 3 → ℝ) : diagScale c 0 = 0 := by
  ext j; simp

@[simp] lemma boxScale_apply (a : ℝ) (p q : Fin 3 → ℝ) (y : E3) (j : Fin 3) :
    boxScale a p q y j = p j + (y j + a / 2) * ((q j - p j) / a) := by
  simp [boxScale, cgEuc3, WithLp.ofLp_toLp]

/-- The affine map `boxScale a p q` as a diagonal scaling followed by a translation. -/
lemma boxScale_eq_diagScale_add (a : ℝ) (p q : Fin 3 → ℝ) (y : E3) :
    boxScale a p q y
      = diagScale (fun j => (q j - p j) / a) y
        + cgEuc3 (fun j => p j + (a / 2) * ((q j - p j) / a)) := by
  ext j
  simp only [PiLp.add_apply, diagScale_apply, boxScale_apply, cgEuc3_apply, cgEuc3_symm_apply]
  ring

lemma cgEuc3_symm_cgEuc3 (f : Fin 3 → ℝ) : cgEuc3.symm (cgEuc3 f) = f :=
  cgEuc3.symm_apply_apply f

/-- The value of `boxScale` at a point of the coordinate picture. -/
@[simp] lemma boxScale_cgEuc3_apply (a : ℝ) (p q : Fin 3 → ℝ) (g : Fin 3 → ℝ) (j : Fin 3) :
    boxScale a p q (cgEuc3 g) j = p j + (g j + a / 2) * ((q j - p j) / a) := by
  simp [boxScale]

/-- `boxScale a p q` is measurable. -/
lemma measurable_boxScale (a : ℝ) (p q : Fin 3 → ℝ) : Measurable (boxScale a p q) := by
  refine cgEuc3.measurable.comp ?_
  refine Measurable.of_eval (fun j => ?_)
  have h1 : Measurable (fun y : E3 => cgEuc3.symm y j) :=
    (measurable_pi_apply j).comp cgEuc3.symm.measurable
  exact measurable_const.add ((h1.add measurable_const).mul measurable_const)

end Work.BoseFixB1P
