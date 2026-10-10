/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Mathlib
import Submission.Work.MotK.TwRule
import Submission.Work.MotK.KleinTwData
import Submission.Work.MotK.TwDataMod5
import Submission.Work.MotK.LinkCertGen
import Submission.Work.MotK.KleinTwRulingQuinticMem
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Shared definitions for the "generic point of the ruling sextic" argument

`Work.MotK.TwRuling.sdW_kleinTwR_ne_zero_charNeTwo` shows that the twisted inverse map
`kleinTwR` does not vanish on the ruling point `sdW` of the target ruling divisor, in
characteristic `≠ 2`.  The proof splits into

* a **twisted/untwisted transport** `kleinTwR0 a b h (RulePt h c l m) = w³ · kleinTwR0 a b 1
  (RulePt 1 (wⁱ cᵢ) l (w m))` (`SdSextTransport`),
* the **generic-point non-vanishing** of the untwisted sextic (this file's `sdGform`): the
  polynomial `S ↦ kleinTwR0 a b 1 (A(κ) + S·B(κ))` is not identically zero on the Klein curve,
* the **evaluation at the explicit point** `(a,0,-a,-b,b)` of the Klein quintic, which produces
  four concrete values whose simultaneous vanishing is impossible in characteristic `≠ 2`
  (`SdSextValues`).

This module collects the definitions shared by those pieces.

* `sdGform a b σ` : the sextic form `R0(A + σ·B)` in the five coordinates, with the ruling
  parameter `σ` as a *scalar* (so that the form is homogeneous of degree six in the five
  variables; this is what lets the degree-six kernel lemma apply);
* `sdDpoly a b` : the sextic form `R0(A(x) + S·B(x))` at the explicit point `x = (a,0,-a,-b,b)`,
  as a polynomial in the ruling parameter `S`;
* `sdYF K D h` : the twisted Klein coordinates `twCoordG K D h` as elements of the twist field
  `twistFieldTG K D h` (over which the target `sdA K D h = RatFunc ↥(twistFieldTG K D h)`
  is a rational function field).
-/

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Work.MotK.TwRuling

open WeierstrassCurve WeierstrassCurve.Affine

/-- The ruling sextic form in the untwisted (`h = 1`) coordinates, with the ruling parameter `σ`
taken as a scalar: `R0 (A(X) + σ·B(X))` where `A, B` are the two ruling vectors of the Klein
curve. -/
noncomputable def sdGform {R : Type*} [CommRing R] (a b σ : R) : MvPolynomial (Fin 5) R :=
  Work.MotK.kleinTwR0 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C 1)
    (fun i => Work.MotK.kleinTwRuleA (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C 1)
        (fun j => MvPolynomial.X j) i
      + MvPolynomial.C σ * Work.MotK.kleinTwRuleB (MvPolynomial.C a) (MvPolynomial.C b)
        (MvPolynomial.C 1) (fun j => MvPolynomial.X j) i)

/-- The ruling sextic form evaluated at the explicit point `(a,0,-a,-b,b)` of the Klein quintic,
as a polynomial in the ruling parameter. -/
noncomputable def sdDpoly {R : Type*} [CommRing R] (a b : R) : Polynomial R :=
  Work.MotK.kleinTwR0 (Polynomial.C a) (Polynomial.C b) (Polynomial.C 1)
    (fun i => Polynomial.C (Work.MotK.kleinTwRuleA a b 1 ![a, 0, -a, -b, b] i)
      + Polynomial.X * Polynomial.C (Work.MotK.kleinTwRuleB a b 1 ![a, 0, -a, -b, b] i))

/-- The twisted Klein coordinates in the twist field `F₁ = twistFieldTG K D h`. -/
noncomputable def sdYF (K : Type) [Field K] (D : Work.MotV.KleinData K) (h : K) :
    Fin 5 → ↥(Work.MotK.twistFieldTG K D h) :=
  fun i => ⟨Work.MotK.twCoordG K D h i,
    IntermediateField.subset_adjoin K (Set.range (Work.MotK.twCoordG K D h))
      (Set.mem_range_self i)⟩

/-- `kleinTwR0` is homogeneous of degree three. -/
theorem kleinTwR0_homog_aux {R : Type*} [CommRing R] (a b h lam : R) (z : Fin 5 → R) :
    Work.MotK.kleinTwR0 a b h (fun i => lam * z i) = lam ^ 3 * Work.MotK.kleinTwR0 a b h z := by
  have hh := congrFun (Work.MotK.kleinTwR_homog a b h lam z) 0
  simpa [Work.MotK.kleinTwR_zero] using hh

/-- In the split case `h = 1` the twisted Pfaffians are the (untwisted) Pfaffians of the Klein
data. -/
theorem kleinTwP_one_eq_kleinP {R : Type*} [CommRing R] (a b : R) (x : Fin 5 → R) :
    Work.MotK.kleinTwP a b 1 x = Work.MotK.kleinP a b x := by
  funext k
  fin_cases k <;>
    simp only [Work.MotK.kleinTwP, Work.MotK.kleinTwP0, Work.MotK.kleinTwP1,
      Work.MotK.kleinTwP2, Work.MotK.kleinTwP3, Work.MotK.kleinTwP4, Work.MotK.kleinP,
      Work.MotK.kleinP0, Work.MotK.kleinP1, Work.MotK.kleinP2, Work.MotK.kleinP3,
      Work.MotK.kleinP4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons] <;>
    ring_nf

/-- The four coefficient values of the ruling sextic at the point `(a,0,-a,-b,b)` cannot
simultaneously vanish, in characteristic `≠ 2` and away from the char-5 degenerate locus
`b⁵ = 2a⁵` (`a ≠ 0`). -/
theorem sdFour_values_ne {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) (a b : K) (ha : a ≠ 0)
    (h5ne : (5 : K) = 0 → b ^ 5 ≠ 2 * a ^ 5) :
    ¬ ((27 : K) * a ^ 5 - 11 * b ^ 5 = 0 ∧ (57 : K) * a ^ 5 - b ^ 5 = 0
        ∧ (29 : K) * a ^ 5 + 3 * b ^ 5 = 0) := by
  rintro ⟨h1, h2', h3⟩
  have h200 : (200 : K) * a ^ 5 = 0 := by
    linear_combination (norm := first | refl_ring1 | ring1) h3 + 3 * h2'
  by_cases h200ne : (200 : K) ≠ 0
  · have haz : a ^ 5 = 0 := (mul_eq_zero.mp h200).resolve_left h200ne
    exact ha ((pow_eq_zero_iff (by norm_num : (5 : ℕ) ≠ 0)).mp haz)
  · have h200z : (200 : K) = 0 := not_not.mp h200ne
    have hfac : (2 : K) ^ 3 * (5 : K) ^ 2 = (200 : K) := by norm_num
    have hz : (2 : K) ^ 3 * (5 : K) ^ 2 = 0 := by rw [hfac, h200z]
    rcases mul_eq_zero.mp hz with h2c | h5c
    · exact absurd ((pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp h2c) h2
    · have h5z : (5 : K) = 0 := (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h5c
      have h57 : (57 : K) = 2 := by
        have hcast : (57 : K) = 11 * (5 : K) + 2 := by norm_num
        rw [hcast, h5z, mul_zero, zero_add]
      refine h5ne h5z ?_
      have h2'' := h2'
      rw [h57] at h2''
      have hfin : (2 : K) * a ^ 5 = b ^ 5 := sub_eq_zero.mp h2''
      exact hfin.symm

/-- `kleinTwRuleA` commutes with `MvPolynomial.aeval`. -/
theorem aeval_kleinTwRuleA {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (a b h : R)
    (x : Fin 5 → A) (i : Fin 5) :
    MvPolynomial.aeval x
        (Work.MotK.kleinTwRuleA (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
          (fun j => MvPolynomial.X j) i)
      = Work.MotK.kleinTwRuleA (algebraMap R A a) (algebraMap R A b) (algebraMap R A h) x i := by
  have h := congrFun (Work.MotK.kleinTwRuleA_map (MvPolynomial.aeval x).toRingHom
    (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
    (fun j => MvPolynomial.X j)) i
  simpa using h

/-- `kleinTwRuleB` commutes with `MvPolynomial.aeval`. -/
theorem aeval_kleinTwRuleB {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (a b h : R)
    (x : Fin 5 → A) (i : Fin 5) :
    MvPolynomial.aeval x
        (Work.MotK.kleinTwRuleB (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
          (fun j => MvPolynomial.X j) i)
      = Work.MotK.kleinTwRuleB (algebraMap R A a) (algebraMap R A b) (algebraMap R A h) x i := by
  have h := congrFun (Work.MotK.kleinTwRuleB_map (MvPolynomial.aeval x).toRingHom
    (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
    (fun j => MvPolynomial.X j)) i
  simpa using h

end Work.MotK.TwRuling
