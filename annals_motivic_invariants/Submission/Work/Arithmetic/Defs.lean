/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.Arithmetic
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The arithmetic of genus-one curves of index five

Interface layer for the area `Submission/Work/Arithmetic` (Part B of
`annals_motivic_invariants`; Lin–Shinder, *Motivic invariants of birational maps*,
Annals of Math. 199 (1), 2024, §"Elliptic curves" (`ssec-dim3`), Lemma `lem:torsors`,
Theorem `thm:ell-curves`, together with Shinder–Zhang, *L-equivalence for degree five
elliptic curves*, Lemma 2.7 (`lem:iso`)).

## Background

Mathlib has Weierstrass curves `W/𝕜`, their group law and their `j`-invariant, but it has
no genus-one curves, no Jacobian varieties `Jac^k(C)`, no Weil–Châtelet groups `H¹(𝕜,E)`
and no period/index theory.  This file therefore *carries* that missing data explicitly,
in the two layers that the L-link construction of the paper consumes:

* `Work.Arithmetic.Torsor`: an elliptic curve `E/𝕜` with `j(E) ≠ 1728`, the Weil–Châtelet
  group `W = H¹(𝕜,E)` (an abstract `CommGroup`), the action of `Aut(E)` on `W`, and the
  class `cls` of the genus-one curve.  Writing the group law of `W` multiplicatively, the
  paper's `d · [X] = [Jac^d(X)]` becomes `cls ^ d` (multiplicative notation in `W`), i.e.
  `Torsor.jacPow T d` (`Torsor.jacSq := Torsor.jacPow T 2`).
* `Work.Arithmetic.GenOneCurve`: a *geometric* realization of a genus-one curve: the scheme
  `C`, smooth/proper/geometrically integral/one-dimensional over `𝕜`, together with its
  `Torsor` data and the two bridge facts

  * `cls = 1 ↔ C(𝕜) ≠ ∅` (the class of a torsor is trivial iff it has a rational point),
  * `cls ^ n = 1 ↔ ∃ D, D` is a `𝕜`-rational divisor of degree `n` on `C`
    (equivalently `Jac^n C ≅ Jac⁰ C = E`).

## Main results (proved in the sibling files of this directory)

* `Work.Arithmetic.Torsor.period_eq_five_iff` — `period = 5` is equivalent to "has a
  divisor of degree 5 and no rational point" (the paper's `index | 5` with `period 5`).
* `Work.Arithmetic.Torsor.not_isIso_jacSq` — Shinder–Zhang Lemma 2.7: `C ≇ Jac²C` for
  `j ≠ 1728`.
* `Work.Arithmetic.Aut.orderOf_dvd_of_short` — Silverman, *AEC*, Prop. A.1.2 for short
  Weierstrass models in characteristic `≠ 2, 3`.
* (TORS) per field class: `Torsor.exists_of_clarkLacy` and its four instances
  `Torsor.exists_numberField`, `Torsor.exists_functionField_numberField`,
  `Torsor.exists_functionField_finite`, `Torsor.exists_functionField_algClosed`.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Order

namespace Work.Arithmetic

noncomputable section

/-! ## 1. Rational points and rational divisors on a curve over `𝕜` -/

/-- The structure morphism `𝕜 → κ(x)` of a scheme over `Spec 𝕜`, evaluated on the residue
field of a point. -/
noncomputable def resMap (𝕜 : Type) [Field 𝕜] {X : Scheme}
    [X.Over (Spec (CommRingCat.of 𝕜))] (x : X) : 𝕜 →+* X.residueField x :=
  ((Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv ≫ (X ↘ Spec (CommRingCat.of 𝕜)).appTop ≫
    X.presheaf.germ ⊤ x trivial ≫ X.residue x).hom

/-- The residue degree `[κ(x) : 𝕜]` of a point of a scheme over `𝕜`. -/
noncomputable def resDeg (𝕜 : Type) [Field 𝕜] {X : Scheme}
    [X.Over (Spec (CommRingCat.of 𝕜))] (x : X) : ℕ :=
  letI : Algebra 𝕜 (X.residueField x) := (resMap 𝕜 x).toAlgebra
  Module.finrank 𝕜 (X.residueField x)

/-- `C` carries a `𝕜`-rational divisor of degree `n`: a `ℤ`-linear combination of closed
points of `C` whose total residue degree is `n`.  This is Clark–Lacy's "degree of a
`𝕜`-rational zero-cycle"; the least such `n` is the *index* of `C`.

**Repaired (`Submission/Work/ArithFix`).**  This definition previously used the support condition
`Order.coheight x = 0`, which on a scheme selects the *generic* points of the irreducible components
(`Order.coheight_eq_zero ↔ IsMax x`), where `resDeg` vanishes — the opposite end of the
specialisation order from the closed points the docstring asks for.  On an integral curve of positive
dimension that made the predicate `n = 0`-only, so the bridge field `divisorOfDegree_iff` of
`GenOneCurve` was unsatisfiable at `n = 5` and every layer of the CK-link area quantified over a
curve of index five was vacuously provable (`Submission/Work/CKLink5/NOTES.md` §1, before the
repair).  The support condition is now `Order.height x = 0` (equivalently `IsClosed ({x} : Set C)`),
i.e. the divisor is supported on closed points; the pre-fix predicate survives as the named
definition `Work.ArithFix.HasRatDivisorOfDegreeCoheight`, and the repoint of every consumer is
recorded in `Submission/Work/ArithFix/LEDGER.md`. -/
def HasRatDivisorOfDegree (𝕜 : Type) [Field 𝕜] (C : Scheme)
    [C.Over (Spec (CommRingCat.of 𝕜))] (n : ℕ) : Prop :=
  ∃ D : C →₀ ℤ, (∀ x ∈ D.support, height x = 0) ∧
    D.sum (fun x m => m * (resDeg 𝕜 x : ℤ)) = (n : ℤ)

/-- The empty divisor is `𝕜`-rational of degree `0`: `HasRatDivisorOfDegree` is not vacuous
for any `C`. -/
theorem hasRatDivisorOfDegree_zero (𝕜 : Type) [Field 𝕜] (C : Scheme)
    [C.Over (Spec (CommRingCat.of 𝕜))] : HasRatDivisorOfDegree 𝕜 C 0 := by
  refine ⟨0, ?_, ?_⟩
  · intro x hx
    simp at hx
  · simp

/-- Degrees of `𝕜`-rational divisors are additive. -/
theorem HasRatDivisorOfDegree.add {𝕜 : Type} [Field 𝕜] {C : Scheme}
    [C.Over (Spec (CommRingCat.of 𝕜))] {m n : ℕ}
    (h : HasRatDivisorOfDegree 𝕜 C m) (h' : HasRatDivisorOfDegree 𝕜 C n) :
    HasRatDivisorOfDegree 𝕜 C (m + n) := by
  obtain ⟨D, hD, hdeg⟩ := h
  obtain ⟨D', hD', hdeg'⟩ := h'
  refine ⟨D + D', ?_, ?_⟩
  · intro x hx
    rw [Finsupp.mem_support_iff] at hx
    rcases eq_or_ne (D x) 0 with h0 | h0
    · rw [Finsupp.add_apply, h0, zero_add] at hx
      exact hD' x (Finsupp.mem_support_iff.mpr hx)
    · exact hD x (Finsupp.mem_support_iff.mpr h0)
  · rw [Finsupp.sum_add_index']
    · rw [hdeg, hdeg']
      push_cast
      first | refl_ring1 | ring
    · intro a
      simp
    · intro a b₁ b₂
      first | refl_ring1 | ring

/-- `C` has a `𝕜`-rational point, i.e. the structure morphism `C → Spec 𝕜` has a section. -/
def HasRatPoint (𝕜 : Type) [Field 𝕜] (C : Scheme)
    [C.Over (Spec (CommRingCat.of 𝕜))] : Prop :=
  ∃ p : Spec (CommRingCat.of 𝕜) ⟶ C,
    p ≫ (C ↘ Spec (CommRingCat.of 𝕜)) = 𝟙 (Spec (CommRingCat.of 𝕜))

/-! ## 2. `Aut(E)`: automorphisms of a Weierstrass model

Mathlib's group of admissible variable changes `WeierstrassCurve.VariableChange 𝕜` acts on
Weierstrass curves; the automorphism group of a model `E` is the stabilizer of `E`.  This
is the group denoted `Aut(E)` in Silverman, *AEC* III.§1 and A.§1. -/

/-- The automorphism group of a Weierstrass model `E/𝕜`: the admissible variable changes
fixing `E` (Silverman, *AEC*, III.1.3). -/
def Aut (𝕜 : Type) [Field 𝕜] (E : WeierstrassCurve 𝕜) :
    Subgroup (WeierstrassCurve.VariableChange 𝕜) where
  carrier := {C | C • E = E}
  one_mem' := one_smul _ _
  mul_mem' := by
    intro C C' hC hC'
    change (C * C') • E = E
    rw [mul_smul, hC', hC]
  inv_mem' := by
    intro C hC
    have h : E = C⁻¹ • E := by
      have h1 := congrArg (fun W : WeierstrassCurve 𝕜 => C⁻¹ • W) hC
      rwa [← mul_smul, inv_mul_cancel, one_smul] at h1
    exact h.symm

/-! ## 3. Genus-one curves via their class in the Weil–Châtelet group -/

/-- A genus-one curve over `𝕜`, presented by the data that the L-link construction needs:
an elliptic curve `E/𝕜` with `j(E) ≠ 1728` (its Jacobian `Jac⁰C`), the Weil–Châtelet group
`W = H¹(𝕜,E)`, the action of `Aut(E)` on `W`, and the class `cls` of `C`.

The paper's `d · [X] = [Jac^d(X)]` (Shinder–Zhang, §2) is the transport of the group law of
`W`: `Jac^d(C)` is `Torsor.jacPow T d`, so `Jac²C = Torsor.jacSq T` and `cls ^ n = 1`
exactly when `C` carries a `𝕜`-rational divisor of degree `n`. -/
structure Torsor (𝕜 : Type) [Field 𝕜] where
  /-- The Jacobian `Jac⁰(C)`, as a Weierstrass model. -/
  E : WeierstrassCurve 𝕜
  [isElliptic : E.IsElliptic]
  /-- The hypothesis `j(Jac⁰C) ≠ 1728` of Shinder–Zhang Lemma 2.7. -/
  j_ne : E.j ≠ 1728
  /-- The Weil–Châtelet group `H¹(𝕜,E)`, written multiplicatively. -/
  W : Type
  [commGroup : CommGroup W]
  /-- The action of `Aut(E)` on `H¹(𝕜,E)` (twisting of torsors). -/
  act : Aut 𝕜 E →* MulAut W
  /-- The class of `C` in `H¹(𝕜,E)`. -/
  cls : W
  /-- Silverman, *AEC*, Proposition A.1.2: for `j(E) ≠ 1728` every automorphism of `E` has
  order dividing `2` or `6` (in characteristics `2` and `3` the exceptional case `j = 0`
  coincides with `j = 1728`).  In particular `Aut(E)` has no element of order `4`, which is
  exactly the input used in the proof of Shinder–Zhang Lemma 2.7. -/
  order_aut : ∀ σ : Aut 𝕜 E, orderOf σ ∣ 2 ∨ orderOf σ ∣ 6

namespace Torsor

variable {𝕜 : Type} [Field 𝕜]

instance instIsElliptic (T : Torsor 𝕜) : T.E.IsElliptic := T.isElliptic

instance instCommGroup (T : Torsor 𝕜) : CommGroup T.W := T.commGroup

/-- The `j`-invariant `j(Jac⁰C)`. -/
def j (T : Torsor 𝕜) : 𝕜 := T.E.j

/-- The *period* of `C`: the order of its class in the Weil–Châtelet group `H¹(𝕜,E)`
(Clark–Lacy, §1.1, for `i = 1` and `M = E(𝕜ˢ)`). -/
def period (T : Torsor 𝕜) : ℕ := orderOf T.cls

/-- The *index* of `C`: the least positive degree of a `𝕜`-rational divisor on `C`.  The
classical theorem for genus-one curves is `index = period` (Lang–Tate); in this presentation
`cls ^ n = 1` says that `C` carries a `𝕜`-rational divisor of degree `n`, so the index is the
least positive `n` with `cls ^ n = 1`, i.e. the order of `cls`; equivalently, by
`Torsor.divisorOfDegree_iff_dvd`, the least positive multiple of the period. -/
def index (T : Torsor 𝕜) : ℕ := orderOf T.cls

/-- `C` carries a `𝕜`-rational divisor of degree `n`; equivalently `Jac^n(C) ≅ E`. -/
def DivisorOfDegree (T : Torsor 𝕜) (n : ℕ) : Prop := T.cls ^ n = 1

/-- `C` has a `𝕜`-rational point, equivalently its class in `H¹(𝕜,E)` is trivial. -/
def HasPoint (T : Torsor 𝕜) : Prop := T.cls = 1

/-- `C(𝕜) = ∅`. -/
def Pointless (T : Torsor 𝕜) : Prop := T.cls ≠ 1

/-- `Jac^d(C)`: the genus-one curve whose class is `d` times the class of `C`
(Shinder–Zhang, §2: `d · [X] = [Jac^k(X)]`). -/
def jacPow (T : Torsor 𝕜) (d : ℤ) : Torsor 𝕜 := { T with cls := T.cls ^ d }

/-- `Jac²C`, the dual elliptic quintic of `C` (Shinder–Zhang, §2). -/
def jacSq (T : Torsor 𝕜) : Torsor 𝕜 := T.jacPow 2

@[simp]
theorem jacPow_cls (T : Torsor 𝕜) (d : ℤ) : (T.jacPow d).cls = T.cls ^ d := rfl

@[simp]
theorem jacSq_cls (T : Torsor 𝕜) : T.jacSq.cls = T.cls ^ (2 : ℤ) := rfl

@[simp]
theorem jacPow_E (T : Torsor 𝕜) (d : ℤ) : (T.jacPow d).E = T.E := rfl

@[simp]
theorem jacSq_E (T : Torsor 𝕜) : T.jacSq.E = T.E := rfl

/-- `η` is the class of a curve isomorphic to `C`.  By Silverman, *AEC*, Exercise 10.4
(X.§3), two genus-one curves with the same Jacobian `E` are isomorphic if and only if their
classes in `H¹(𝕜,E)` lie in the same `Aut(E)`-orbit; this is the definition of the
isomorphism relation used throughout. -/
def IsIso (T : Torsor 𝕜) (η : T.W) : Prop := ∃ σ : Aut 𝕜 T.E, T.act σ T.cls = η

/-- The isomorphism relation is reflexive: `C ≅ C`. -/
theorem isIso_cls (T : Torsor 𝕜) : T.IsIso T.cls :=
  ⟨1, by simp⟩

/-- `C ≇ Jac²C`. -/
def NotIsoJacSq (T : Torsor 𝕜) : Prop := ¬ T.IsIso T.jacSq.cls

/-- Silverman, *AEC*, A.1.2, in the form used by the paper: for `j ≠ 1728`, `Aut(E)` has no
element of order `4`. -/
theorem orderOf_ne_four (T : Torsor 𝕜) (σ : Aut 𝕜 T.E) : orderOf σ ≠ 4 := by
  intro h
  rcases T.order_aut σ with hd | hd
  · exact absurd (h ▸ hd) (by decide)
  · exact absurd (h ▸ hd) (by decide)

end Torsor

/-! ## 4. The geometric layer -/

/-- A genus-one curve over `𝕜`, realized as a smooth, proper, geometrically integral
one-dimensional scheme, together with its `Torsor` data and the two bridge statements
between the geometry of `C` and its class in `H¹(𝕜, Jac⁰C)`. -/
structure GenOneCurve (𝕜 : Type) [Field 𝕜] where
  /-- The curve itself. -/
  C : Scheme
  [isVariety : MotivicInvariants.Variety 𝕜 C]
  [isProper : IsProper (C ↘ Spec (CommRingCat.of 𝕜))]
  [isSmooth : Smooth (C ↘ Spec (CommRingCat.of 𝕜))]
  [isGeomIntegral : GeometricallyIntegral (C ↘ Spec (CommRingCat.of 𝕜))]
  /-- A curve is one-dimensional. -/
  dim_eq_one : topologicalKrullDim C = 1
  /-- The Jacobian, the Weil–Châtelet group and the class of `C`. -/
  torsor : Torsor 𝕜
  /-- The class of a torsor is trivial if and only if the torsor has a rational point. -/
  cls_eq_one_iff : torsor.cls = 1 ↔ HasRatPoint 𝕜 C
  /-- `C` carries a `𝕜`-rational divisor of degree `n` iff `Jac^n C ≅ Jac⁰ C = E`. -/
  divisorOfDegree_iff : ∀ n : ℕ, HasRatDivisorOfDegree 𝕜 C n ↔ torsor.DivisorOfDegree n

namespace GenOneCurve

variable {𝕜 : Type} [Field 𝕜]

/-! The structure fields of `GenOneCurve` are not automatically registered as instances, so
we register them here; this is what allows `HasRatDivisorOfDegree 𝕜 X.C n` and friends to
elaborate for `X : GenOneCurve 𝕜`. -/

instance instVariety (X : GenOneCurve 𝕜) : MotivicInvariants.Variety 𝕜 X.C := X.isVariety

instance instOver (X : GenOneCurve 𝕜) : X.C.Over (Spec (CommRingCat.of 𝕜)) :=
  MotivicInvariants.Variety.over

instance instIsProper (X : GenOneCurve 𝕜) : IsProper (X.C ↘ Spec (CommRingCat.of 𝕜)) :=
  X.isProper

instance instSmooth (X : GenOneCurve 𝕜) : Smooth (X.C ↘ Spec (CommRingCat.of 𝕜)) :=
  X.isSmooth

instance instGeomIntegral (X : GenOneCurve 𝕜) :
    GeometricallyIntegral (X.C ↘ Spec (CommRingCat.of 𝕜)) := X.isGeomIntegral


/-- The Jacobian `Jac⁰C` of the curve. -/
def E (X : GenOneCurve 𝕜) : WeierstrassCurve 𝕜 := X.torsor.E

/-- `j(Jac⁰C)`. -/
def j (X : GenOneCurve 𝕜) : 𝕜 := X.torsor.E.j

/-- The class of `C` in the Weil–Châtelet group of its Jacobian. -/
def cls (X : GenOneCurve 𝕜) : X.torsor.W := X.torsor.cls

/-- The period of `C` (see `Torsor.period`). -/
def period (X : GenOneCurve 𝕜) : ℕ := X.torsor.period

/-- The index of `C` (see `Torsor.index`). -/
def index (X : GenOneCurve 𝕜) : ℕ := X.torsor.index

/-- `C(𝕜) = ∅`. -/
def Pointless (X : GenOneCurve 𝕜) : Prop := X.torsor.Pointless

/-- `C` carries a `𝕜`-rational divisor of degree `n`. -/
def HasDivisorOfDegree (X : GenOneCurve 𝕜) (n : ℕ) : Prop := X.torsor.DivisorOfDegree n

/-- `C ≇ Jac²C`, where `Jac²C` is the dual elliptic quintic of Shinder–Zhang §2. -/
def NotIsoJacSq (X : GenOneCurve 𝕜) : Prop := X.torsor.NotIsoJacSq

end GenOneCurve

/-! ## 5. The arithmetic inputs of the four field classes

The two external theorems used in the proof of Lemma `lem:torsors` are Clark–Lacy
(J. reine angew. Math. 749 (2019), Theorem 1.10) and Lang–Tate (Amer. J. Math. 80 (1958),
Theorem 7).  Both are stated here in the *only* form that the rest of the argument uses:
the existence of a genus-one curve of period `5` over `𝕜` whose Jacobian has `j ≠ 1728`.
The "infinitely many" clause of the paper's Lemma `lem:torsors` is not needed. -/

/-- **Clark–Lacy, Theorem 1.10** (with Section 4 for `j(E) ≠ 1728`): every infinite,
finitely generated field `𝕜` admits an elliptic curve `E/𝕜` with `j(E) ≠ 1728` and a class
`η ∈ H¹(𝕜,E)` of period (and index) `5`.  The theorem of Clark–Lacy produces infinitely many
such classes; we record one. -/
def ClarkLacyFive (𝕜 : Type) [Field 𝕜] : Prop := ∃ T : Torsor 𝕜, T.period = 5

/-- The residual *geometric* input for a field class: a genus-one curve over `𝕜`, realized
as a scheme, whose class in the Weil–Châtelet group of its Jacobian has period `5`.  The
first half of the paper's Theorem `thm:ell-curves` (together with Lemma `lem:torsors`)
produces such a curve; the arithmetic part of that existence is `ClarkLacyFive` or
`LangTateFive`, and the scheme-theoretic realization is the geometry layer. -/
def GenOneCurveFive (𝕜 : Type) [Field 𝕜] : Prop := ∃ X : GenOneCurve 𝕜, X.period = 5

/-- **Lang–Tate, Theorem 7** (the version used for function fields over an algebraically
closed field): `𝕜` admits a genus-one curve of period `5` with `j(Jac⁰) ≠ 1728`.  The paper
derives this from: `𝕜` Hilbertian (hence having infinitely many cyclic extensions of degree
`5`), the weak Mordell–Weil finiteness of `E(𝕜)/5E(𝕜)` for the constant elliptic curve
`E_𝕜` (Clark–Lacy, Remark 1.3 and Proposition 1.4), and non-trivial `5`-torsion in
`E(𝕜)` for an ordinary `E/𝔽` with `j ≠ 1728`. -/
def LangTateFive (𝕜 : Type) [Field 𝕜] : Prop := ∃ T : Torsor 𝕜, T.period = 5

end

end Work.Arithmetic
