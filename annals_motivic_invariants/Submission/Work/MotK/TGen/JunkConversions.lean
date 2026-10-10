/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Mathlib
import Submission.Work.MotK.TGen.CensusFactors
import Submission.Work.MotK.TGen.FwVec4Rational
import Submission.Work.MotK.TGen.CubTRational
import Submission.Work.MotK.CensusPrime.eq_span_of_height_one
import Submission.Work.MotK.JunkClassLinearThree
import Submission.Work.MotV.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# From the "prime element" form of a census clause to its divisor form

The census `Work.MotK.TGenCensus` (`Submission/Work/MotK/LinkCertTGenInf.lean`) asks, for two of its
prime factors (`fwVec a b h 4`, the quartic chart denominator, and `cubT`, the cubic cone factor),
that *every* codimension-one point above them be junk.  The natural way to prove such a clause is
the *stronger* statement that the factor is a prime element of the UFD `K[x₀,x₁,x₂]` and that its
principal prime has residue field the rational surface `RatFunc (RatFunc K)`; the two conversions
here turn that stronger form into the divisor form.

This module exists separately from `LinkCertTGenInf.lean` on purpose: `TGen/STRulingDiv.lean`
imports `Work.MotK.fwVec4JunkAll`, and `LinkCertTGenInf.lean` must (in order to state the target
theorem there) import the class clauses `TGen.STClass`/`TGen.SdualTClass`, which sit *above*
`STRulingDiv`.  Keeping the conversions here breaks that cycle.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotK

open MvPolynomial

/-- **From the prime form of a census clause to the divisor form.**  If the *principal prime* `(g)`
is a height-one prime whose residue field is the rational surface `RatFunc (RatFunc K)`, then *every*
codimension-one point above `g` is junk: it equals `(g)` by
`Work.MotK.CensusPrime.eq_span_of_height_one`.

This is the conversion used when a census clause is available in the stronger "`g` is a prime
element" form; the degenerate cases (e.g. `sT 1 1 1 = 13·(x₁+x₂)·(degree 9)`, see
`TGen/GUIDE_CENSUS.md`) are covered by the divisor form and not by the prime form. -/
theorem junkAll_of_prime {K : Type} [Field K] {g : MvPolynomial (Fin 3) K}
    (hpr : (Ideal.span {g} : Ideal (MvPolynomial (Fin 3) K)).IsPrime)
    (hht : Ideal.height (Ideal.span {g} : Ideal (MvPolynomial (Fin 3) K)) = 1)
    (hres : Nonempty (Work.MotV.resF K ⟨Ideal.span {g}, hpr⟩ ≃ₐ[K] RatFunc (RatFunc K))) :
    ∀ x : Work.MotA.polySpec K 3, Order.coheight x = 1 → g ∈ x.asIdeal →
      Work.MotV.JunkClass K x := by
  intro x hcx hg
  haveI : x.asIdeal.IsPrime := x.2
  have hx : x.asIdeal = Ideal.span {g} :=
    CensusPrime.eq_span_of_height_one g hpr hht x.asIdeal
      ((AlgebraicGeometry.idealHeight_eq_coheight (CommRingCat.of (MvPolynomial (Fin 3) K))
        x).trans hcx) hg
  rw [show x = ⟨Ideal.span {g}, hpr⟩ from PrimeSpectrum.ext hx]
  exact junkClass_of_resF_ratFunc_ratFunc K _ hres

/-- **The quartic `f̂₄` clause of the census in divisor form**, from the proved prime form
`Work.MotK.TGen.FwVec4Rational`. -/
theorem fwVec4JunkAll {K : Type} [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    ∀ x : Work.MotA.polySpec K 3, Order.coheight x = 1 → TGen.fwVec a b h 4 ∈ x.asIdeal →
      Work.MotV.JunkClass K x := by
  obtain ⟨hpr, hht, hres⟩ := TGen.FwVec4Rational K a b h ha hb hh
  exact junkAll_of_prime hpr hht hres

/-- **The cubic `cubT` clause of the census in divisor form**, from the proved prime form
`Work.MotK.TGen.CubTRational`. -/
theorem cubTJunkAll {K : Type} [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    ∀ x : Work.MotA.polySpec K 3, Order.coheight x = 1 → TGen.cubT a b h ∈ x.asIdeal →
      Work.MotV.JunkClass K x := by
  obtain ⟨hpr, hht, hres⟩ := TGen.CubTRational K a b h ha hb hh
  exact junkAll_of_prime hpr hht hres

/-- **From the prime form of a class clause to the divisor form**, with an arbitrary target field:
if `(g)` is a height-one prime with residue field `RatFunc F`, then every codimension-one point above
`g` is of class `RatFunc F` (indeed it *is* `(g)`). -/
theorem classAll_of_prime {K : Type} [Field K] {g : MvPolynomial (Fin 3) K} {F : Type} [Field F]
    [Algebra K F]
    (hpr : (Ideal.span {g} : Ideal (MvPolynomial (Fin 3) K)).IsPrime)
    (hht : Ideal.height (Ideal.span {g} : Ideal (MvPolynomial (Fin 3) K)) = 1)
    (hres : Nonempty (Work.MotV.resF K ⟨Ideal.span {g}, hpr⟩ ≃ₐ[K] RatFunc F)) :
    ∀ x : Work.MotA.polySpec K 3, Order.coheight x = 1 → g ∈ x.asIdeal →
      Nonempty (Work.MotV.resF K x ≃ₐ[K] RatFunc F) ∨ Work.MotV.JunkClass K x := by
  intro x hcx hg
  haveI : x.asIdeal.IsPrime := x.2
  have hx : x.asIdeal = Ideal.span {g} :=
    CensusPrime.eq_span_of_height_one g hpr hht x.asIdeal
      ((AlgebraicGeometry.idealHeight_eq_coheight (CommRingCat.of (MvPolynomial (Fin 3) K))
        x).trans hcx) hg
  rw [show x = ⟨Ideal.span {g}, hpr⟩ from PrimeSpectrum.ext hx]
  exact Or.inl hres

end Work.MotK
