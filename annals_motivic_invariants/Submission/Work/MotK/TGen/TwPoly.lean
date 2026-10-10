/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Mathlib
import Submission.Work.MotK.TwAmbh
import Submission.Work.MotK.KleinTwLink

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The link data of the T-twist as **polynomials** in the homogeneous coordinates

The dehomogenised (chart) equations `Work.MotK.GambT`, `Work.MotK.FambT` of `TwAmbh` are the
`ChartIsoT` step's two divisor polynomials.  The chart isomorphism is induced by the two rational
maps `f = kleinTwP ∘ kleinTwStereo` and `χ = kleinTwPi ∘ kleinTwR`, whose coordinate functions on
the affine chart `V₀ = 0, V₄ = 1` are the *fractions* `f̂_{j+1}/f̂₄` and `ǧ_{j+1}/ǧ₄`.

To build the induced `K`-algebra homomorphisms of the localisations as `MvPolynomial.aeval` of a
chart point, one has to compare

* the *homogeneous* polynomial expression (`kleinTwFhom`, `kleinTwGhomV`, `kleinTwP ∘
  kleinTwStereo`, `kleinTwPi ∘ kleinTwR`) in the five coordinates `V₀,…,V₄`, with
* its *dehomogenisation* in `K[x₀,x₁,x₂]` (the substitutions `V₀ ↦ 0`, `V₁ ↦ x₀`, `V₂ ↦ x₁`,
  `V₃ ↦ x₂`, `V₄ ↦ 1`).

This file collects the *homogeneous* versions of the four expressions as polynomials in
`K[V₀,…,V₄]` together with the chart point `chartPt3`; the companion file
`Submission/Work/MotK/TGen/AevalTw` proves that `MvPolynomial.aeval` computes them in the
concrete form (the "evaluation" lemmas), and `Submission/Work/MotK/LinkCertTGenInf` assembles the
chart isomorphism from them.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.MotK

variable (K : Type*) [Field K]

/-- The `K`-rational point `p = kleinPointT a b h` of the twisted quadric, as a vector of
constants of `K[V₀,…,V₄]`. -/
noncomputable def pX5 (a b h : K) : Fin 5 → MvPolynomial (Fin 5) K :=
  fun i => MvPolynomial.C (kleinPointT a b h i)

/-- The **source equation of the link** as a polynomial in the homogeneous coordinates:
`F_hom(V) = b(p,V)·s(y(V))` (`FhomPoly` specialised at `chart3` is `GambT`). -/
noncomputable def FhomPoly (a b h : K) : MvPolynomial (Fin 5) K :=
  kleinTwFhom (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (pX5 K a b h)
    (fun i => MvPolynomial.X i)

/-- The **target equation of the link** as a polynomial in the homogeneous coordinates:
`G_hom(W) = b(p,R(W))·s'(W)` (`GhomPoly` specialised at `chart3` is `FambT`). -/
noncomputable def GhomPoly (a b h : K) : MvPolynomial (Fin 5) K :=
  kleinTwGhomV (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (pX5 K a b h)
    (fun i => MvPolynomial.X i)

/-- The forward link map `f = kleinTwP ∘ kleinTwStereo` as a vector of polynomials in the
homogeneous coordinates.  Its fourth component `fwPoly 4` is the denominator of the affine chart
coordinates of `f`. -/
noncomputable def fwPoly (a b h : K) : Fin 5 → MvPolynomial (Fin 5) K :=
  kleinTwP (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
    (kleinTwStereo (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (pX5 K a b h)
      (fun i => MvPolynomial.X i))

/-- The inverse link map `χ = kleinTwPi p ∘ kleinTwR` as a vector of polynomials in the
homogeneous coordinates.  Its fourth component `bwPoly 4` is the denominator of the affine chart
coordinates of `χ`. -/
noncomputable def bwPoly (a b h : K) : Fin 5 → MvPolynomial (Fin 5) K :=
  kleinTwPi (pX5 K a b h)
    (kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (fun i => MvPolynomial.X i))

variable {K}

/-- The affine chart point `(0, z₀, z₁, z₂, 1)` of the hyperplane `{V₀ = 0}` in `ℙ⁴`, for a
point `z` of the three-dimensional chart `V₄ = 1`. -/
def chartPt3 {R : Type*} [CommRing R] (z : Fin 3 → R) : Fin 5 → R := ![0, z 0, z 1, z 2, 1]

@[simp] theorem chartPt3_apply_zero {R : Type*} [CommRing R] (z : Fin 3 → R) :
    chartPt3 z 0 = 0 := rfl

@[simp] theorem chartPt3_apply_four {R : Type*} [CommRing R] (z : Fin 3 → R) :
    chartPt3 z 4 = 1 := rfl

@[simp] theorem chartPt3_apply_one {R : Type*} [CommRing R] (z : Fin 3 → R) :
    chartPt3 z 1 = z 0 := rfl

@[simp] theorem chartPt3_apply_two {R : Type*} [CommRing R] (z : Fin 3 → R) :
    chartPt3 z 2 = z 1 := rfl

@[simp] theorem chartPt3_apply_three {R : Type*} [CommRing R] (z : Fin 3 → R) :
    chartPt3 z 3 = z 2 := rfl

end Work.MotK
