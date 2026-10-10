/-
Copyright (c) 2026 the annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.CrauderKatz
-/
import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CrauderKatz.BlowUp.LineDefs` — the thickened blow-up of `𝔸³` along a coordinate line

This file starts the *three-dimensional* analogue of `Submission/Work/CrauderKatz/BlowUp/ThickDefs.lean`:
the blow-up of the affine three-space `𝔸³ = Spec 𝕜[X,Y,Z]` along the `z`-axis, thickened along its
exceptional surface by a square-zero nilpotent so that the generic point of the exceptional surface
is provably not an isomorphism point of the modification.

The two charts of the classical blow-up are both affine with ring

`R 𝕜 := 𝕜[x,t,z,ε]/(ε², x·ε)`   (`lineRing 𝕜`, coordinates `lineX`, `lineT`, `lineZ`, `lineE`),

where `(x,t,z)` are the chart coordinates and `ε` the nilpotent thickening the surface `{x = 0}`.
The overlap of the two charts is `R 𝕜[1/t] =: ovRing 𝕜`, and the transition is
`x ↦ x·t`, `t ↦ t⁻¹`, `z ↦ z`, `ε ↦ ε` (the third coordinate `z` of the line is inert).

The one-dimensional analogue (`ThickDefs.lean`) lives in the same namespace; everything here is
prefixed `line` to keep the two developments apart.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace Work.CrauderKatz.BlowUp

noncomputable section

variable (𝕜 : Type) [Field 𝕜]

/-- The ideal `(ε², x·ε)` of `𝕜[x,t,z,ε]`, where `x = X 0`, `t = X 1`, `z = X 2`, `ε = X 3`. -/
def lineI : Ideal (MvPolynomial (Fin 4) 𝕜) :=
  Ideal.span {MvPolynomial.X 3 ^ 2, MvPolynomial.X 0 * MvPolynomial.X 3}

/-- The chart ring `R 𝕜 = 𝕜[x,t,z,ε]/(ε², x·ε)` of the thickened blow-up of `𝔸³` along a line. -/
abbrev lineRing : Type := (MvPolynomial (Fin 4) 𝕜) ⧸ lineI 𝕜

/-- The coordinate `x` (first chart) resp. `y` (second chart) in `R 𝕜`, the exceptional
coordinate. -/
def lineX : lineRing 𝕜 := Ideal.Quotient.mk _ (MvPolynomial.X 0)

/-- The coordinate `t` (first chart) resp. `s` (second chart) in `R 𝕜`, the overlap coordinate. -/
def lineT : lineRing 𝕜 := Ideal.Quotient.mk _ (MvPolynomial.X 1)

/-- The line coordinate `z`, in both charts. -/
def lineZ : lineRing 𝕜 := Ideal.Quotient.mk _ (MvPolynomial.X 2)

/-- The nilpotent `ε` of the thickening. -/
def lineE : lineRing 𝕜 := Ideal.Quotient.mk _ (MvPolynomial.X 3)

lemma mem_lineI_sq : MvPolynomial.X 3 ^ 2 ∈ lineI 𝕜 :=
  Ideal.subset_span (s := ({MvPolynomial.X 3 ^ 2, MvPolynomial.X 0 * MvPolynomial.X 3} :
    Set (MvPolynomial (Fin 4) 𝕜))) (by simp [Set.mem_insert_iff])

lemma mem_lineI_mul : MvPolynomial.X 0 * MvPolynomial.X 3 ∈ lineI 𝕜 :=
  Ideal.subset_span (s := ({MvPolynomial.X 3 ^ 2, MvPolynomial.X 0 * MvPolynomial.X 3} :
    Set (MvPolynomial (Fin 4) 𝕜))) (by simp [Set.mem_insert_iff])

lemma lineI_le_span : lineI 𝕜 ≤ Ideal.span {MvPolynomial.X 0, MvPolynomial.X 3} := by
  rw [lineI, Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  refine ⟨?_, ?_⟩
  · rw [sq]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (s := ({MvPolynomial.X 0, MvPolynomial.X 3} :
      Set (MvPolynomial (Fin 4) 𝕜))) (by simp [Set.mem_insert_iff]))
  · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (s := ({MvPolynomial.X 0, MvPolynomial.X 3} :
      Set (MvPolynomial (Fin 4) 𝕜))) (by simp [Set.mem_insert_iff]))

@[simp] lemma lineX_mul_lineE : lineX 𝕜 * lineE 𝕜 = 0 := by
  rw [lineX, lineE, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact mem_lineI_mul 𝕜

@[simp] lemma lineE_mul_lineX : lineE 𝕜 * lineX 𝕜 = 0 := by
  rw [mul_comm, lineX_mul_lineE]

@[simp] lemma lineE_sq : lineE 𝕜 ^ 2 = 0 := by
  rw [lineE, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact mem_lineI_sq 𝕜

/-- The generic point of the exceptional surface inside a chart: the ideal `(x, ε)`, where `x` is
the exceptional coordinate (`lineX`) and `ε` the nilpotent (`lineE`). -/
def lineK : Ideal (lineRing 𝕜) := Ideal.span {lineX 𝕜, lineE 𝕜}

/-- One chart of the thickened blow-up of `𝔸³` along a line: `Spec R`,
`R = 𝕜[x,t,z,ε]/(ε², x·ε)`.

In the first chart the coordinates are `(x,t,z,ε) = (X0,X1,X2,X3)` with exceptional surface `V(x)`
and overlap `D(t)`; in the second chart they are `(y,s,z,η) = (X0,X1,X2,X3)` with exceptional
surface `V(y) = V(X0)` and overlap `D(s) = D(X1)`. -/
abbrev lineChartS : Scheme.{0} := Spec (CommRingCat.of (lineRing 𝕜))

/-- The overlap ring `R[1/t]` of the two charts (in each chart, the second variable is inverted). -/
abbrev lineOvRing : Type := Localization.Away (lineT 𝕜)

/-- The overlap `Spec R[1/t]` of the two charts. -/
abbrev lineOvS : Scheme.{0} := Spec (CommRingCat.of (lineOvRing 𝕜))

end

end Work.CrauderKatz.BlowUp
