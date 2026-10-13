/-
  Area `WilC4aTS`: the `PolynomialSignSet` interface used by the Tarski--Seidenberg bridge.

  `PolynomialSignSet c S` (a finite Boolean combination of zero sets and positivity sets of real
  polynomials, pulled back along a coordinate map `c`) is the vocabulary of the projection theorem.
  The inductive itself is *not* redefined here: it lives in the ported upstream library of the
  subproject `WilLibTS`, module `Submission.Work.WilLibTS.TS.PolynomialEmptyInterior`, and the
  projection theorem is `Work.WilLibTS.TS.SignElimination.polynomialSignSet_projection_finite`
  (module `...PolynomialSignSetProjection2`).  Using that single definition keeps this area and the
  `WilLibTS` port speaking the same language.

  `PSS S` abbreviates the case of the *identity* coordinate map on `Fin m → ℝ`, which is the case
  needed by the frozen area `E` (`WilkiesDesign.E.SA`, semialgebraic sets in DNF).

  Main consumer: `Submission.Work.WilC4aTS.TS`.
-/
import Submission.Work.WilLibTS.TS.PolynomialSignSetFinite

set_option autoImplicit false

noncomputable section
open Classical
namespace Work.WilC4aTS
open Set
open Work.WilLibTS.TS (PolynomialSignSet)

/-- `PSS S`: `S ⊆ ℝᵐ` is a finite Boolean combination of zero sets and positivity sets of real
polynomials in the coordinates.  (Identity coordinate map; the general coordinate map version is
`Work.WilLibTS.TS.PolynomialSignSet` itself.) -/
abbrev PSS {m : ℕ} (S : Set (Fin m → ℝ)) : Prop :=
  PolynomialSignSet (id : (Fin m → ℝ) → Fin m → ℝ) S

/-- The whole space is a `PolynomialSignSet`. -/
theorem pss_univ {m : ℕ} : PSS (Set.univ : Set (Fin m → ℝ)) :=
  PolynomialSignSet.univ

/-- The empty set is a `PolynomialSignSet`. -/
theorem pss_empty {m : ℕ} : PSS (∅ : Set (Fin m → ℝ)) :=
  PolynomialSignSet.empty

/-- `PolynomialSignSet` is closed under intersection. -/
theorem pss_inter {m : ℕ} {S T : Set (Fin m → ℝ)} (hS : PSS S) (hT : PSS T) :
    PSS (S ∩ T) :=
  hS.inter hT

/-- `PolynomialSignSet` is closed under complement. -/
theorem pss_compl {m : ℕ} {S : Set (Fin m → ℝ)} (hS : PSS S) : PSS Sᶜ :=
  hS.compl

/-- `PolynomialSignSet` is closed under (binary) union. -/
theorem pss_union {m : ℕ} {S T : Set (Fin m → ℝ)} (hS : PSS S) (hT : PSS T) :
    PSS (S ∪ T) :=
  hS.union hT

/-- The zero set of a polynomial is a `PolynomialSignSet`. -/
theorem pss_zero {m : ℕ} (p : MvPolynomial (Fin m) ℝ) :
    PSS {x : Fin m → ℝ | MvPolynomial.eval x p = 0} :=
  PolynomialSignSet.zero p

/-- The positivity set of a polynomial is a `PolynomialSignSet`. -/
theorem pss_positive {m : ℕ} (p : MvPolynomial (Fin m) ℝ) :
    PSS {x : Fin m → ℝ | 0 < MvPolynomial.eval x p} :=
  PolynomialSignSet.positive p

end Work.WilC4aTS
