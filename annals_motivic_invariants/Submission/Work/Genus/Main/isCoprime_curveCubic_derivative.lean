import Mathlib
import Submission.Work.Genus.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.Main

open Polynomial

/-- **A cubic over a field is separable as soon as its leading coefficient and its discriminant
are non-zero.**  Transport to an algebraically closed field `K ⊇ F`: there `P.toPoly` splits, the
condition `P.discr ≠ 0` is exactly "the multiset of roots of `P.toPoly` has no repetitions"
(`Cubic.discr_ne_zero_iff_roots_nodup`), a non-zero split polynomial without repeated roots is
separable (`Polynomial.nodup_roots_iff_of_splits`), and separability descends along the injective
map `F → K` (`Polynomial.separable_map`). -/
theorem separable_toPoly_of_discr_ne_zero {F K : Type*} [Field F] [Field K] [Algebra F K]
    [IsAlgClosed K] (P : Cubic F) (ha : P.a ≠ 0) (h : P.discr ≠ 0) :
    P.toPoly.Separable := by
  have hsplit : (Polynomial.map (algebraMap F K) P.toPoly).Splits := IsAlgClosed.splits _
  have hne : Polynomial.map (algebraMap F K) P.toPoly ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap F K).injective).mpr (Cubic.ne_zero_of_a_ne_zero ha)
  have hnodup : (Polynomial.map (algebraMap F K) P.toPoly).roots.Nodup := by
    have h1 := (Cubic.discr_ne_zero_iff_roots_nodup (φ := algebraMap F K) ha hsplit).mp h
    rwa [Cubic.map_roots] at h1
  exact (Polynomial.separable_map (algebraMap F K)).mp
    ((Polynomial.nodup_roots_iff_of_splits hne hsplit).mp hnodup)

/-- The "completed square" cubic `4X³ + b₂X² + 2b₄X + b₆` of a Weierstrass curve is the
`toPoly` of its 2-torsion polynomial `⟨4, b₂, 2b₄, b₆⟩`. -/
theorem curveCubic_eq_twoTorsionPolynomial_toPoly {R : Type*} [CommRing R]
    (E : WeierstrassCurve R) :
    Work.Genus.curveCubic E = E.twoTorsionPolynomial.toPoly :=
  rfl

/-- **The cubic `4X³ + b₂X² + 2b₄X + b₆` of a non-singular Weierstrass curve is squarefree**
(in the form `IsCoprime A A'`, which is what the Bezout argument of the genus chapter consumes),
in characteristic `≠ 2`.

Route: `Polynomial.discr (curveCubic E) = 16 * E.Δ` (a computation with `discr`, or by transporting
along a `VariableChange` to short Weierstrass form); since `(2 : F) ≠ 0` and `E.Δ ≠ 0` this
discriminant is non-zero, and a cubic with non-zero discriminant has no repeated root, so `A` and
`A'` are coprime (`IsCoprime`, i.e. Bézout, in the PID `F[X]`).  Equivalently: a common irreducible
factor of `A` and `A'` would give a repeated root in `AlgebraicClosure F`. -/
theorem isCoprime_curveCubic_derivative {F : Type*} [Field F] (E : WeierstrassCurve F)
    (h2 : (2 : F) ≠ 0) (hΔ : E.Δ ≠ 0) :
    IsCoprime (Work.Genus.curveCubic E) (Polynomial.derivative (Work.Genus.curveCubic E)) := by
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have ha : E.twoTorsionPolynomial.a ≠ 0 := by
    simpa [WeierstrassCurve.twoTorsionPolynomial] using h4
  have h16 : (16 : F) ≠ 0 := by
    rw [show (16 : F) = 4 * 4 by norm_num]
    exact mul_ne_zero h4 h4
  have hdiscr : E.twoTorsionPolynomial.discr ≠ 0 := by
    rw [WeierstrassCurve.twoTorsionPolynomial_discr]
    exact mul_ne_zero h16 hΔ
  have hsep : E.twoTorsionPolynomial.toPoly.Separable :=
    separable_toPoly_of_discr_ne_zero (K := AlgebraicClosure F) E.twoTorsionPolynomial ha hdiscr
  rw [curveCubic_eq_twoTorsionPolynomial_toPoly]
  exact (Polynomial.separable_def _).mp hsep

end Work.Genus.Main
