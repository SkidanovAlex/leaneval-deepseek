/-
Copyright: work module for the Elgindi finite-time singularity project.

# The Möbius chart for the `Zop`-iterates of `φ(z) = z/(1+z)²`

The one-dimensional operator `Zop u = z ↦ z·u'(z)` (`Work.Spaces.Zop`) acting on the
profile `φ(z) = z/(1+z)²` of the fundamental model.  Under the Möbius chart

    `zchart z = (z - 1)/(z + 1)`   (z > 0  ↦  (-1,1)),

`Zop` becomes the polynomial map

    `Tmul P = ½(1 - X²)·P'`,

in the sense that `Zop (gpoly P) = gpoly (Tmul P)` on `(-1,∞)`, where
`gpoly P z = P.eval (zchart z)`.  Since `z > 0` forces `|zchart z| < 1`, this makes every
`Zop`-iterate of `φ = gpoly Pphi` a polynomial in the bounded chart variable, hence bounded
on `(0,∞)` — the content of `zop_phi_bound`.

This file only contains the definitions and the elementary chart facts; the intertwining
identity and the polynomial evaluation bound live in `ZopPhiAux/`.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Submission.Work.Spaces.MixedMulDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter Polynomial

namespace Work.FTS.CoercivityFix.E2Bound

/-- The Möbius chart `z ↦ (z - 1)/(z + 1)`, mapping `(0,∞)` onto `(-1,1)`. -/
def zchart (z : ℝ) : ℝ := (z - 1) / (z + 1)

/-- Evaluation of a polynomial in the chart variable: `z ↦ P.eval (zchart z)`. -/
def gpoly (P : Polynomial ℝ) : ℝ → ℝ := fun z => P.eval (zchart z)

/-- The polynomial map induced by `Zop` on the chart side: `P ↦ ½(1 - X²)·P'`. -/
def Tmul (P : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.C (1 / 2) * (1 - Polynomial.X ^ 2) * Polynomial.derivative P

/-- The polynomial whose chart-side evaluation is `φ(z) = z/(1+z)²`, namely `¼(1 - X²)`. -/
def Pphi : Polynomial ℝ := Polynomial.C (1 / 4) * (1 - Polynomial.X ^ 2)

@[simp] lemma zchart_apply (z : ℝ) : zchart z = (z - 1) / (z + 1) := rfl

@[simp] lemma gpoly_apply (P : Polynomial ℝ) (z : ℝ) : gpoly P z = P.eval (zchart z) := rfl

@[simp] lemma Tmul_apply (P : Polynomial ℝ) :
    Tmul P = Polynomial.C (1 / 2) * (1 - Polynomial.X ^ 2) * Polynomial.derivative P := rfl

@[simp] lemma Pphi_eq : Pphi = Polynomial.C (1 / 4) * (1 - Polynomial.X ^ 2) := rfl

/-- For `z > 0` the chart variable lies in `(-1,1)`. -/
lemma abs_zchart_lt_one {z : ℝ} (hz : 0 < z) : |zchart z| < 1 := by
  have h1 : (0 : ℝ) < z + 1 := by linarith
  rw [zchart, abs_div, abs_of_pos h1, div_lt_one h1]
  rw [abs_lt]
  constructor <;> linarith

lemma abs_zchart_le_one {z : ℝ} (hz : 0 < z) : |zchart z| ≤ 1 :=
  le_of_lt (abs_zchart_lt_one hz)

lemma zchart_ne_neg_one {z : ℝ} (hz : 0 < z) : z ≠ -1 := by linarith

end Work.FTS.CoercivityFix.E2Bound
