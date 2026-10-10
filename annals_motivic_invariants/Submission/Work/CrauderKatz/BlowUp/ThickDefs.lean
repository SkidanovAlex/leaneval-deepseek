/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.CrauderKatz
-/
import Mathlib

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CrauderKatz.BlowUp.ThickDefs` — the thickened blow-up of the plane: definitions

We construct here the scheme-theoretic input for the witness of `PlaneBlowUp 𝕜`: the blow-up of
the affine plane at the origin, with the exceptional curve `ℙ¹` *thickened* (a square-zero
nilpotent along it).  The thickening is what makes the generic point `E` of the exceptional curve
provably *not* a partial-isomorphism point: its local ring carries a nilpotent, while every local
ring of `𝔸²` is reduced.

Both charts of the classical blow-up are copies of the same ring

`R 𝕜 := 𝕜[x,t,ε]/(ε², x·ε)`      (`thickRing 𝕜`, variables `thickX`, `thickT`, `thickE`),

the `(x,t)` coordinates of the chart `(x,t) ↦ (x, x t)`.  On the overlap, `t` is inverted in the
first chart and the transition is the classical one; the nilpotent `ε` already vanishes there
(since `x ∉ (t)` and `x·ε = 0`), so the two thickened charts glue along the *classical* overlap
`D(t) ≅ D(s)`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace Work.CrauderKatz.BlowUp

noncomputable section

variable (𝕜 : Type) [Field 𝕜]

/-- The ideal `(ε², x·ε)` of `𝕜[x,t,ε]`, where `x = X 0`, `t = X 1`, `ε = X 2`. -/
def thickI : Ideal (MvPolynomial (Fin 3) 𝕜) :=
  Ideal.span {MvPolynomial.X 2 ^ 2, MvPolynomial.X 0 * MvPolynomial.X 2}

/-- The chart ring `R 𝕜 = 𝕜[x,t,ε]/(ε², x·ε)`. -/
abbrev thickRing : Type := (MvPolynomial (Fin 3) 𝕜) ⧸ thickI 𝕜

/-- The coordinate `x` (first chart) resp. `s` (second chart) in `R 𝕜`. -/
def thickX : thickRing 𝕜 := Ideal.Quotient.mk _ (MvPolynomial.X 0)

/-- The coordinate `t` (first chart) resp. `y` (second chart) in `R 𝕜`. -/
def thickT : thickRing 𝕜 := Ideal.Quotient.mk _ (MvPolynomial.X 1)

/-- The nilpotent `ε` of the thickening. -/
def thickE : thickRing 𝕜 := Ideal.Quotient.mk _ (MvPolynomial.X 2)

lemma mem_thickI_sq : MvPolynomial.X 2 ^ 2 ∈ thickI 𝕜 :=
  Ideal.subset_span (s := ({MvPolynomial.X 2 ^ 2, MvPolynomial.X 0 * MvPolynomial.X 2} :
    Set (MvPolynomial (Fin 3) 𝕜))) (by simp [Set.mem_insert_iff])

lemma mem_thickI_mul : MvPolynomial.X 0 * MvPolynomial.X 2 ∈ thickI 𝕜 :=
  Ideal.subset_span (s := ({MvPolynomial.X 2 ^ 2, MvPolynomial.X 0 * MvPolynomial.X 2} :
    Set (MvPolynomial (Fin 3) 𝕜))) (by simp [Set.mem_insert_iff])

lemma thickI_le_span : thickI 𝕜 ≤ Ideal.span {MvPolynomial.X 0, MvPolynomial.X 2} := by
  rw [thickI, Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  refine ⟨?_, ?_⟩
  · rw [sq]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (s := ({MvPolynomial.X 0, MvPolynomial.X 2} :
      Set (MvPolynomial (Fin 3) 𝕜))) (by simp [Set.mem_insert_iff]))
  · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (s := ({MvPolynomial.X 0, MvPolynomial.X 2} :
      Set (MvPolynomial (Fin 3) 𝕜))) (by simp [Set.mem_insert_iff]))

@[simp] lemma thickX_mul_thickE : thickX 𝕜 * thickE 𝕜 = 0 := by
  rw [thickX, thickE, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact mem_thickI_mul 𝕜

@[simp] lemma thickE_mul_thickX : thickE 𝕜 * thickX 𝕜 = 0 := by
  rw [mul_comm, thickX_mul_thickE]

@[simp] lemma thickE_sq : thickE 𝕜 ^ 2 = 0 := by
  rw [thickE, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact mem_thickI_sq 𝕜

/-- The generic point of the exceptional curve inside a chart: the ideal `(x, ε)`, where `x` is
the exceptional coordinate (`thickX`) and `ε` the nilpotent (`thickE`). -/
def thickK : Ideal (thickRing 𝕜) := Ideal.span {thickX 𝕜, thickE 𝕜}

/-- One chart of the thickened blow-up: `Spec R`, `R = 𝕜[x,t,ε]/(ε², x·ε)`.

In the first chart the coordinates are `(x,t,ε) = (X0,X1,X2)` with exceptional curve `V(x)` and
overlap `D(t)`; in the second chart they are `(y,s,η) = (X0,X1,X2)` with exceptional curve
`V(y) = V(X0)` and overlap `D(s) = D(X1)`. -/
abbrev chartS : Scheme.{0} := Spec (CommRingCat.of (thickRing 𝕜))

/-- The overlap ring `R[1/t]` of the two charts (in each chart, the second variable is inverted). -/
abbrev ovRing : Type := Localization.Away (thickT 𝕜)

/-- The overlap `Spec R[1/t]` of the two charts. -/
abbrev ovS : Scheme.{0} := Spec (CommRingCat.of (ovRing 𝕜))

end

end Work.CrauderKatz.BlowUp
