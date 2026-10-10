/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.TorsorExistence
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Arithmetic.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Torsor existence: the interface

This is the interface layer of the area `Submission/Work/TorsorExistence`, whose target is
`Work.Arithmetic.HasLLinkCurve 𝕜` (the paper's Lemma `lem:torsors`) for the four field classes
of Lin–Shinder, *Motivic invariants of birational maps*, Annals of Math. 199 (1), 2024,
Theorem 1.2 (1) (a)–(d).

`Work.Arithmetic.GenOneCurve` carries the genus-one curve of the paper's Lemma `lem:torsors`
together with the *abstract* Weil–Châtelet data (`Torsor`: the group `W = H¹(𝕜,E)`, the class
`cls` of the curve, the action of `Aut(E)`), but ties that data to the geometry of the scheme
`C` only through two bridge fields (`cls_eq_one_iff`, `divisorOfDegree_iff`).  The content of
this area is (i) to exhibit the *arithmetic* objects that the paper's proof of `lem:torsors`
produces — a cyclic quintic extension `L/𝕜`, an elliptic curve `E/𝕜` with a rational point of
order `5` and `j ≠ 1728`, and the quintic twist `C` of `E` by the corresponding cocycle — and
(ii) to isolate exactly what remains of the *geometry*.

## Conventions

* `CyclicExtension 𝕜 n`: a field `L` with `𝕜 → L` finite Galois and cyclic Galois group of
  order `n`, together with a chosen generator `gen` of `Gal(L/𝕜)`.  This is the "cyclic
  extension of degree `5`" of the paper's proof (obtained for the four field classes by Kummer
  theory, by Artin–Schreier theory, and for number fields from the cyclotomic field `ℚ(ζ_{5^k})`;
  see `Extensions.lean`).
* `FiveTorsionCurve 𝕜`: an elliptic curve `E/𝕜` (`E.IsElliptic`), with `j(E) ≠ 1728`, and a
  point `P ∈ E(𝕜)` with `5 • P = 0`, `P ≠ 0` (so `P` has exact order `5`).  The field
  `order_aut` records Silverman, *AEC*, Proposition A.1.2 (no automorphism of order `4` when
  `j ≠ 1728`), exactly as `Work.Arithmetic.Torsor` does.
* `QuinticTwist 𝕜`: a `FiveTorsionCurve` together with a cyclic quintic extension `L/𝕜`; this is
  the input of the *twist* construction of `Twist.lean`: the class of `P` in
  `H¹(ℤ/5, E(L)) = ker(N)/(σ-1)E(L)`, whose non-vanishing is the statement "the twist `C` has
  no `𝕜`-point".
* `PointlessIndexFiveCurve 𝕜`: **the geometric residual**.  A smooth, proper, geometrically
  integral curve of dimension `1` over `𝕜` with no `𝕜`-point, carrying a `𝕜`-rational divisor of
  degree `5`, and with *every* `𝕜`-rational divisor of degree divisible by `5`.  This is the
  minimal scheme-theoretic input for `HasLLinkCurve`; see `Main.lean` for
  `HasLLinkCurve 𝕜 ← HasPointlessIndexFiveCurve 𝕜` and `NOTES.md` §2 for why the scheme cannot
  be constructed with the current library.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory AlgebraicGeometry

namespace Work.TorsorExistence

noncomputable section

/-! ## 1. Cyclic extensions of degree `n` -/

/-- A *cyclic extension of degree `n` of the field `𝕜`*: a field `L` with `𝕜 → L` finite
Galois whose Galois group is cyclic of order `n`, together with a chosen generator `gen`.

This is the structure produced by the paper's proof of Lemma `lem:torsors` in each field class
(see `Extensions.lean`). -/
structure CyclicExtension (𝕜 : Type u) [Field 𝕜] (n : ℕ) where
  /-- The top field of the extension. -/
  L : Type u
  [field : Field L]
  [algebra : Algebra 𝕜 L]
  [finiteDimensional : FiniteDimensional 𝕜 L]
  [isGalois : IsGalois 𝕜 L]
  /-- The degree of the extension is `n`. -/
  finrank_eq : Module.finrank 𝕜 L = n
  /-- A generator of the (cyclic) Galois group. -/
  gen : L ≃ₐ[𝕜] L
  /-- `gen` generates `Gal(L/𝕜)`. -/
  gen_generator : ∀ g : L ≃ₐ[𝕜] L, ∃ k : ℕ, g = gen ^ k
  /-- The order of `gen` is `n`. -/
  orderOf_gen : orderOf gen = n

/-- The assertion `Nonempty (CyclicExtension 𝕜 n)` in `Prop` form. -/
def ExistsCyclicExtension (𝕜 : Type u) [Field 𝕜] (n : ℕ) : Prop := Nonempty (CyclicExtension 𝕜 n)

namespace CyclicExtension

variable {𝕜 : Type u} [Field 𝕜] {n : ℕ}

instance (E : CyclicExtension 𝕜 n) : Field E.L := E.field
instance (E : CyclicExtension 𝕜 n) : Algebra 𝕜 E.L := E.algebra
instance (E : CyclicExtension 𝕜 n) : FiniteDimensional 𝕜 E.L := E.finiteDimensional
instance (E : CyclicExtension 𝕜 n) : IsGalois 𝕜 E.L := E.isGalois

/-- The Galois group of a cyclic extension has `n` elements. -/
theorem natCard_gal (E : CyclicExtension 𝕜 n) : Nat.card (E.L ≃ₐ[𝕜] E.L) = n := by
  rw [IsGalois.card_aut_eq_finrank, E.finrank_eq]

/-- The Galois group of a cyclic extension of degree `n` is finite. -/
theorem finite_gal (E : CyclicExtension 𝕜 n) : Finite (E.L ≃ₐ[𝕜] E.L) :=
  Finite.of_fintype _

/-- The Galois group of a cyclic extension of degree `n` is cyclic. -/
theorem isCyclic_gal (E : CyclicExtension 𝕜 n) : IsCyclic (E.L ≃ₐ[𝕜] E.L) :=
  ⟨⟨E.gen, fun g => by obtain ⟨k, hk⟩ := E.gen_generator g; exact ⟨k, hk.symm⟩⟩⟩

/-- Every element of the Galois group of a cyclic extension is a power of the chosen
generator, in the form used by the twist construction. -/
theorem eq_gen_pow (E : CyclicExtension 𝕜 n) (g : E.L ≃ₐ[𝕜] E.L) :
    ∃ k : ℕ, g = E.gen ^ k :=
  E.gen_generator g

/-- The Galois group of a cyclic extension of degree `5` has exactly `5` elements. -/
theorem card_gal_five (E : CyclicExtension 𝕜 5) : Nat.card (E.L ≃ₐ[𝕜] E.L) = 5 :=
  E.natCard_gal

/-- `gen` is a generator of the Galois group: its powers exhaust the group. -/
theorem zpowers_gen (E : CyclicExtension 𝕜 n) :
    Subgroup.zpowers E.gen = ⊤ := by
  ext g
  simp only [Subgroup.mem_zpowers_iff, Subgroup.mem_top, iff_true]
  obtain ⟨k, hk⟩ := E.gen_generator g
  exact ⟨k, hk.symm⟩

end CyclicExtension

/-! ## 2. Elliptic curves with a rational point of order five -/

/-- An elliptic curve `E/𝕜` with `j(E) ≠ 1728`, together with Silverman, *AEC*, Proposition
A.1.2 recorded as data.

The field `order_aut` is *not* a mathematical hypothesis: for `j ≠ 1728` every automorphism of
`E` has order dividing `2` or `6`, over any field (Silverman, *AEC*, A.1.2).  It is a field of
the structure for the same reason as in `Work.Arithmetic.Torsor`: Mathlib has no classification
of `Aut(E)` for general Weierstrass models.  `CurveOrderAut.lean` proves that such a curve
exists over every infinite field (by splitting on the characteristic).

This is exactly the elliptic-curve data that a `Work.Arithmetic.Torsor` needs, so
`OrderAutCurve.toTorsor` below produces one. -/
structure OrderAutCurve (𝕜 : Type) [Field 𝕜] where
  /-- The curve. -/
  E : WeierstrassCurve 𝕜
  [isElliptic : E.IsElliptic]
  /-- The hypothesis of Shinder–Zhang, Lemma 2.7. -/
  j_ne : E.j ≠ 1728
  /-- Silverman, *AEC*, Proposition A.1.2 (see the docstring). -/
  order_aut : ∀ σ : Work.Arithmetic.Aut 𝕜 E, orderOf σ ∣ 2 ∨ orderOf σ ∣ 6

namespace OrderAutCurve

variable {𝕜 : Type} [Field 𝕜]

instance (D : OrderAutCurve 𝕜) : D.E.IsElliptic := D.isElliptic

/-- Silverman, *AEC*, A.1.2 in the form used by Shinder–Zhang: no automorphism of order `4`. -/
theorem orderOf_ne_four (D : OrderAutCurve 𝕜) (σ : Work.Arithmetic.Aut 𝕜 D.E) :
    orderOf σ ≠ 4 := by
  intro h
  rcases D.order_aut σ with hd | hd
  · exact absurd (h ▸ hd) (by decide)
  · exact absurd (h ▸ hd) (by decide)

end OrderAutCurve

/-- An elliptic curve over `𝕜` with `j ≠ 1728` and a rational point of exact order `5`.

This is the output of the Tate normal form for `X₁(5)` (`TateCurve.lean`); it is
`FiveTorsionCurve` without the Silverman A.1.2 datum.

The `DecidableEq 𝕜` hypothesis is a technical requirement of Mathlib's group law on affine
points of a Weierstrass curve (`WeierstrassCurve.Affine.Point.instAddCommGroup` needs it); it is
always dischargeable by `Classical.decEq`. -/
structure FiveTorsionPoint (𝕜 : Type) [Field 𝕜] [DecidableEq 𝕜] where
  /-- The curve (its Jacobian). -/
  E : WeierstrassCurve 𝕜
  [isElliptic : E.IsElliptic]
  /-- The hypothesis of Shinder–Zhang, Lemma 2.7. -/
  j_ne : E.j ≠ 1728
  /-- The rational point of order five. -/
  P : WeierstrassCurve.Affine.Point E
  /-- `P` is not the origin, so with `five_smul` it has exact order `5`. -/
  P_ne_zero : P ≠ 0
  /-- `P` is `5`-torsion. -/
  five_smul : (5 : ℕ) • P = 0

/-- An elliptic curve over `𝕜` with `j ≠ 1728`, a rational point of exact order `5`, and
Silverman, *AEC*, Proposition A.1.2 recorded as data.

The field `order_aut` is *not* a mathematical hypothesis: for `j ≠ 1728` every automorphism of
`E` has order dividing `2` or `6`, over any field (Silverman, *AEC*, A.1.2).  It is a field of
the structure for the same reason as in `Work.Arithmetic.Torsor`: Mathlib has no classification
of `Aut(E)` for general Weierstrass models. -/
structure FiveTorsionCurve (𝕜 : Type) [Field 𝕜] [DecidableEq 𝕜] extends FiveTorsionPoint 𝕜 where
  /-- Silverman, *AEC*, Proposition A.1.2 (see the docstring). -/
  order_aut : ∀ σ : Work.Arithmetic.Aut 𝕜 E, orderOf σ ∣ 2 ∨ orderOf σ ∣ 6

namespace FiveTorsionCurve

variable {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]

instance (D : FiveTorsionCurve 𝕜) : D.E.IsElliptic := D.isElliptic

/-- The order of the marked point is exactly `5`. -/
theorem addOrderOf_P (D : FiveTorsionCurve 𝕜) : addOrderOf D.P = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact addOrderOf_eq_prime D.five_smul D.P_ne_zero

/-- The nonzero small multiples of the marked point; in particular `P` has order exactly `5`. -/
theorem nsmul_P_ne_zero (D : FiveTorsionCurve 𝕜) {k : ℕ} (hk : k < 5) (hk0 : 0 < k) :
    k • D.P ≠ 0 := by
  intro h
  have hdvd : addOrderOf D.P ∣ k := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h
  rw [D.addOrderOf_P] at hdvd
  have := Nat.le_of_dvd hk0 hdvd
  omega

end FiveTorsionCurve

/-! ## 3. The quintic twist data -/

/-- The input of the quintic twist construction: an elliptic curve over `𝕜` with a rational
point of order `5` and `j ≠ 1728`, together with a cyclic extension of degree `5` of `𝕜`.

The twist `C` of `E` by the cocycle `σ ↦ P` is a genus-one curve over `𝕜` with a `𝕜`-rational
divisor of degree `5` and with `C(𝕜) = ∅` iff the class of `P` in `H¹(ℤ/5, E(L))` is non-zero
(`Twist.lean`). -/
structure QuinticTwist (𝕜 : Type) [Field 𝕜] [DecidableEq 𝕜] extends FiveTorsionCurve 𝕜 where
  /-- The cyclic quintic extension `L/𝕜`. -/
  ext : CyclicExtension 𝕜 5
  /-- Technical: the group law on affine points of a Weierstrass curve over `L` needs a
  `DecidableEq L` instance (dischargeable by `Classical.decEq`). -/
  [decEq_ext : DecidableEq ext.L]

namespace QuinticTwist

variable {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]

instance (D : QuinticTwist 𝕜) : Field D.ext.L := D.ext.field
instance (D : QuinticTwist 𝕜) : Algebra 𝕜 D.ext.L := D.ext.algebra
instance (D : QuinticTwist 𝕜) : FiniteDimensional 𝕜 D.ext.L := D.ext.finiteDimensional
instance (D : QuinticTwist 𝕜) : IsGalois 𝕜 D.ext.L := D.ext.isGalois
instance (D : QuinticTwist 𝕜) : DecidableEq D.ext.L := D.decEq_ext

/-- The generator of the cyclic Galois group of the quintic extension. -/
def sigma (D : QuinticTwist 𝕜) : D.ext.L ≃ₐ[𝕜] D.ext.L := D.ext.gen

/-- The Galois group of the quintic twist data is `ℤ/5`. -/
theorem sigma_orderOf (D : QuinticTwist 𝕜) : orderOf D.sigma = 5 := D.ext.orderOf_gen

end QuinticTwist

/-! ## 4. The geometric residual -/

/-- **The geometric residual for `HasLLinkCurve`.**  A smooth, proper, geometrically integral
curve of dimension one over `𝕜` with no `𝕜`-rational point, with a `𝕜`-rational divisor of
degree `5`, and such that every degree of a `𝕜`-rational divisor is divisible by `5`.

Equivalently (given the other fields): a curve of *index* `5` with `C(𝕜) = ∅`.  Mathematically
this is exactly what the paper's Lemma `lem:torsors` produces (the genus-one curve of period
and index `5` without rational points); the reason it is a *named residual* is that no smooth
proper curve over a field is constructible in the current Mathlib (see `NOTES.md` §2).

`Main.lean` proves `HasLLinkCurve 𝕜` from `Nonempty (PointlessIndexFiveCurve 𝕜)`. -/
structure PointlessIndexFiveCurve (𝕜 : Type) [Field 𝕜] where
  /-- The curve. -/
  C : Scheme
  [variety : MotivicInvariants.Variety 𝕜 C]
  [isProper : IsProper (C ↘ Spec (CommRingCat.of 𝕜))]
  [isSmooth : Smooth (C ↘ Spec (CommRingCat.of 𝕜))]
  [isGeomIntegral : GeometricallyIntegral (C ↘ Spec (CommRingCat.of 𝕜))]
  /-- A curve is one-dimensional. -/
  dim_eq_one : topologicalKrullDim C = 1
  /-- `C(𝕜) = ∅`. -/
  no_point : ¬ Work.Arithmetic.HasRatPoint 𝕜 C
  /-- The curve carries a `𝕜`-rational divisor of degree `5`. -/
  five : Work.Arithmetic.HasRatDivisorOfDegree 𝕜 C 5
  /-- Every degree of a `𝕜`-rational divisor is divisible by `5`. -/
  dvd : ∀ n : ℕ, Work.Arithmetic.HasRatDivisorOfDegree 𝕜 C n → 5 ∣ n

namespace PointlessIndexFiveCurve

variable {𝕜 : Type} [Field 𝕜]

instance (X : PointlessIndexFiveCurve 𝕜) : MotivicInvariants.Variety 𝕜 X.C := X.variety
instance (X : PointlessIndexFiveCurve 𝕜) : X.C.Over (Spec (CommRingCat.of 𝕜)) :=
  MotivicInvariants.Variety.over
instance (X : PointlessIndexFiveCurve 𝕜) : IsProper (X.C ↘ Spec (CommRingCat.of 𝕜)) :=
  X.isProper
instance (X : PointlessIndexFiveCurve 𝕜) : Smooth (X.C ↘ Spec (CommRingCat.of 𝕜)) :=
  X.isSmooth
instance (X : PointlessIndexFiveCurve 𝕜) :
    GeometricallyIntegral (X.C ↘ Spec (CommRingCat.of 𝕜)) := X.isGeomIntegral

/-- The "divisor degrees are the multiples of `5`" half of the residual, in the `↔` form used by
`GenOneCurve.divisorOfDegree_iff`. -/
theorem hasRatDivisorOfDegree_iff (X : PointlessIndexFiveCurve 𝕜) (n : ℕ) :
    Work.Arithmetic.HasRatDivisorOfDegree 𝕜 X.C n ↔ 5 ∣ n := by
  refine ⟨X.dvd n, fun h => ?_⟩
  obtain ⟨k, rfl⟩ := h
  induction k with
  | zero => simpa using Work.Arithmetic.hasRatDivisorOfDegree_zero 𝕜 X.C
  | succ k ih =>
    have : 5 * (k + 1) = 5 * k + 5 := by ring
    rw [this]
    exact ih.add X.five

end PointlessIndexFiveCurve

/-- The residual `Nonempty (PointlessIndexFiveCurve 𝕜)` in `Prop` form. -/
def HasPointlessIndexFiveCurve (𝕜 : Type) [Field 𝕜] : Prop :=
  Nonempty (PointlessIndexFiveCurve 𝕜)

end

end Work.TorsorExistence
