import Mathlib
import Submission.Work.ClassFieldTower.Defs
import Submission.Work.ClassFieldTower.Tower
import Submission.Work.ClassFieldTower.ProTwoGenus
import Submission.Work.ClassFieldTower.proTwoShafarevichKochInput_of_no_unramified

/-!
# `Work.ClassFieldTower.proTwoShafarevichKochInput_rat` -- the wall's interface is CONSISTENT

`Work.ClassFieldTower.ProTwoShafarevichKochInput F` (the interface of the single remaining wall of
this chapter, see `Wall.lean`) is an existential over a finitely presented abstract group `G` with
`rel.card ≤ #α + 1` relators, minimal generators, residual `2`-finiteness and a description of the
unramified `2`-extensions of `F` by the finite `2`-quotients of `G`.

This module proves that the interface is **satisfiable**, i.e. that it is a consistent classical
statement and not an unsatisfiable packaging (contrast `Vacuity.lean`, which machine-checked that
the *earlier* interface of this chapter — built on an abstract finite presentation of the infinite
profinite group `G_∅` — was inconsistent).  Two results:

* `no_nontrivial_unramified_rat`: `ℚ` has no nontrivial finite extension unramified at all finite
  primes.  An everywhere-unramified extension `L/ℚ` has `|disc L| = |disc ℚ| ^ [L : ℚ] = 1`
  (`natAbs_discr_eq_pow_of_differentIdeal_eq_top`), which contradicts the Hermite--Minkowski
  theorem `NumberField.abs_discr_gt_two` when `[L : ℚ] > 1`.  Hence its Galois group is trivial.
  (The proof sidesteps the well-known `ℚ`-instance ambiguity between an arbitrary
  `Algebra ℚ L` and the canonical one: all `Algebra ℚ L` structures are equal,
  `algebra_rat_subsingleton`, so we may replace the algebra structure by the canonical one.)
* `proTwoShafarevichKochInput_rat`: hence the wall's interface is satisfiable for `F = ℚ`, with
  witnesses `α = PEmpty`, `rel = ∅`, `G` trivial
  (`proTwoShafarevichKochInput_of_no_unramified`).

Concretely, `ProTwoShafarevichKochInput F` fails to be satisfiable *only* because `F_∅ ≠ F`, i.e.
only because `F` has a nontrivial finite unramified `2`-extension.  The whole of the remaining
arithmetic content of the chapter is therefore in the *relation count* of that group, not in the
shape of the interface.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ClassFieldTower

/-- **`ℚ` has no nontrivial finite extension unramified at all finite primes** (Hermite--Minkowski),
in the form needed for the wall's interface: every finite Galois `L/ℚ` with trivial relative
different has trivial Galois group. -/
theorem no_nontrivial_unramified_rat {L : Type} [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L] (h : differentIdeal (𝓞 ℚ) (𝓞 L) = ⊤) :
    Subsingleton (L ≃ₐ[ℚ] L) := by
  -- every `Algebra ℚ L` is the canonical one, so we may use the canonical algebra structure
  have hA : (inferInstance : Algebra ℚ L) = (DivisionRing.toRatAlgebra : Algebra ℚ L) :=
    Subsingleton.elim _ _
  subst hA
  -- an everywhere-unramified extension of `ℚ` has discriminant `±1`
  have hdisc : (NumberField.discr L).natAbs = 1 := by
    have := natAbs_discr_eq_pow_of_differentIdeal_eq_top (F := ℚ) (L := L) h
    simpa using this
  have hcard : Nat.card (L ≃ₐ[ℚ] L) = Module.finrank ℚ L := IsGalois.card_aut_eq_finrank ℚ L
  -- Hermite--Minkowski: a nontrivial number field has `|disc| > 2`
  have hle : Nat.card (L ≃ₐ[ℚ] L) ≤ 1 := by
    by_contra hcon
    have h2 : 1 < Module.finrank ℚ L := by rw [← hcard]; omega
    have hgt := NumberField.abs_discr_gt_two (K := L) h2
    rw [Int.abs_eq_natAbs] at hgt
    omega
  have hone : Nat.card (L ≃ₐ[ℚ] L) = 1 := by
    have hne : Nat.card (L ≃ₐ[ℚ] L) ≠ 0 := by
      intro h0
      rcases (Nat.card_eq_zero.mp h0) with hE | hI
      · exact hE.false (1 : L ≃ₐ[ℚ] L)
      · exact (not_finite_iff_infinite.mpr hI) inferInstance
    omega
  exact (Nat.card_eq_one_iff_unique.mp hone).1

/-- **The wall's interface is satisfiable.**  `ProTwoShafarevichKochInput ℚ` holds with the
trivial group (`α = PEmpty`, `rel = ∅`): by `no_nontrivial_unramified_rat` the unramified
extensions of `ℚ` are trivial.  This is the positive counterpart of `Vacuity.lean`. -/
theorem proTwoShafarevichKochInput_rat : ProTwoShafarevichKochInput ℚ :=
  proTwoShafarevichKochInput_of_no_unramified (F := ℚ)
    (fun L _iF _iN _iA _iFD _iGal h _ => no_nontrivial_unramified_rat h)

end Work.ClassFieldTower
