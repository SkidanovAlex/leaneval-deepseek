/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.PointlessIndexFive
-/
import Mathlib
import Submission.Work.PointlessIndexFive.Defs
import Submission.Work.TorsorExistence.nonempty_fiveTorsionPoint
import Submission.Work.PointlessIndexFive.nonempty_fiveTorsionCurve
import Submission.Work.PointlessIndexFive.nonempty_fiveTorsionCurve_of_two_three_invertible
import Submission.Work.TorsorExistence.existsCyclicExtension_of_zeta5
import Submission.Work.TorsorExistence.existsCyclicExtension_of_charP_five
import Submission.Work.TorsorExistence.existsCyclicExtension_numberField

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Assembling the twist data from steps (A) and (B)

The arithmetic residual `HasPointlessTwist 𝕜` is `∃ D : QuinticTwist 𝕜, D.Pointless`.  A
`QuinticTwist 𝕜` is *exactly* the paper's data for the twist construction: an elliptic curve with a
rational point of exact order `5` and `j ≠ 1728` (`FiveTorsionCurve`, step (B)) together with a
cyclic quintic extension `L/𝕜` (`CyclicExtension 𝕜 5`, step (A)).  This file makes that
identification explicit by *constructing* the `QuinticTwist` from the two pieces, so that the only
content left in `HasPointlessTwist 𝕜` is the non-vanishing of the class — i.e. the Clark–Lacy /
Lang–Tate step.

Steps (A) and (B) themselves are proved in `Submission/Work/TorsorExistence`:

* (A) `existsCyclicExtension_of_zeta5` (Kummer, char `≠ 5`), `existsCyclicExtension_of_charP_five`
  (Artin–Schreier, char `5`), `existsCyclicExtension_numberField`;
* (B) `nonempty_fiveTorsionPoint` (the Tate normal form for `X₁(5)`), for every infinite field.

The one field-theoretic gap for the function-field classes — producing `ζ₅ ∈ 𝕜` / `a ∉ 𝕜^5` /
`a ∉ ℘(𝕜)` from `0 < topologicalKrullDim X` — is recorded in `NOTES.md` §3.3; it is inherited from
`TorsorExistence/NOTES.md` §4.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry

namespace Work.PointlessIndexFive

noncomputable section

/-- **The twist data of the paper's proof.**  A `FiveTorsionCurve` (step (B): `E/𝕜` with `j ≠ 1728`
and a rational point of exact order `5`) together with a cyclic quintic extension `L/𝕜` (step (A))
*is* a `QuinticTwist 𝕜`; no further data is needed. -/
noncomputable def quinticTwistOf {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (C₅ : Work.TorsorExistence.FiveTorsionCurve 𝕜)
    (L : Work.TorsorExistence.CyclicExtension 𝕜 5) : QuinticTwist 𝕜 where
  E := C₅.E
  isElliptic := C₅.isElliptic
  j_ne := C₅.j_ne
  P := C₅.P
  P_ne_zero := C₅.P_ne_zero
  five_smul := C₅.five_smul
  order_aut := C₅.order_aut
  ext := L
  decEq_ext := Classical.decEq L.L

/-- The underlying curve of `quinticTwistOf` is the given one. -/
@[simp]
theorem quinticTwistOf_E {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (C₅ : Work.TorsorExistence.FiveTorsionCurve 𝕜)
    (L : Work.TorsorExistence.CyclicExtension 𝕜 5) : (quinticTwistOf C₅ L).E = C₅.E := rfl

/-- **The residual `HasPointlessTwist 𝕜` is exactly the non-vanishing of `cls` for the twist
built from steps (A) and (B).**  Given a curve with a rational `5`-torsion point and `j ≠ 1728`
and a cyclic quintic extension, the twist data is `quinticTwistOf C₅ L`, and the residual holds as
soon as its class is non-zero. -/
theorem hasPointlessTwist_of_pointless_data {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (C₅ : Work.TorsorExistence.FiveTorsionCurve 𝕜)
    (L : Work.TorsorExistence.CyclicExtension 𝕜 5) (h : (quinticTwistOf C₅ L).Pointless) :
    HasPointlessTwist 𝕜 :=
  ⟨quinticTwistOf C₅ L, h⟩

/-! ## Assembling a `QuinticTwist` per field class

Step (B) is `nonempty_fiveTorsionCurve` (Silverman A.1.2 for the Tate normal form, in every
characteristic) and step (A) is the appropriate `existsCyclicExtension_*` of the parent chapter;
combining them with `quinticTwistOf` gives the twist data.  For the function-field classes the
remaining input is the transcendental element (Kummer: `a ∉ 𝕜^5`; Artin–Schreier: `a ∉ ℘(𝕜)`),
which `NOTES.md` §3.3 records as the one inherited field-theoretic gap. -/

/-- **The twist data over any infinite field of characteristic `≠ 2, 3`**: a `FiveTorsionCurve` and
a Kummer cyclic quintic extension. -/
theorem nonempty_quinticTwist_of_zeta5 {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] [Infinite 𝕜]
    (h2 : (2 : 𝕜) ≠ 0) (h3 : (3 : 𝕜) ≠ 0) {ζ : 𝕜} (hζ : IsPrimitiveRoot ζ 5) {a : 𝕜}
    (ha : ¬ ∃ b : 𝕜, b ^ 5 = a) : Nonempty (QuinticTwist 𝕜) := by
  obtain ⟨C₅⟩ := nonempty_fiveTorsionCurve_of_two_three_invertible (𝕜 := 𝕜) h2 h3
  obtain ⟨L⟩ := Work.TorsorExistence.existsCyclicExtension_of_zeta5 ζ hζ a ha
  exact ⟨quinticTwistOf C₅ L⟩

/-- **The twist data over any infinite field of characteristic `5`**: a `FiveTorsionCurve` and an
Artin–Schreier cyclic quintic extension. -/
theorem nonempty_quinticTwist_of_charP_five {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] [Infinite 𝕜]
    [CharP 𝕜 5] {a : 𝕜} (ha : ¬ ∃ b : 𝕜, b ^ 5 - b = a) : Nonempty (QuinticTwist 𝕜) := by
  obtain ⟨C₅⟩ := nonempty_fiveTorsionCurve (𝕜 := 𝕜)
  obtain ⟨L⟩ := Work.TorsorExistence.existsCyclicExtension_of_charP_five a ha
  exact ⟨quinticTwistOf C₅ L⟩

/-- **The twist data over a number field.**  Both steps are unconditional here: the Tate normal
form (with Silverman A.1.2 attached) and `existsCyclicExtension_numberField`. -/
theorem nonempty_quinticTwist_numberField {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] [NumberField 𝕜] :
    Nonempty (QuinticTwist 𝕜) := by
  obtain ⟨C₅⟩ := nonempty_fiveTorsionCurve (𝕜 := 𝕜)
  obtain ⟨L⟩ := Work.TorsorExistence.existsCyclicExtension_numberField (𝕜 := 𝕜)
  exact ⟨quinticTwistOf C₅ L⟩

/-- **Class (a), assembled.**  Over a number field, steps (A) and (B) are available
(`existsCyclicExtension_numberField`, `nonempty_fiveTorsionPoint`), so the arithmetic residual
reduces to the non-vanishing of one concrete twist class. -/
theorem hasPointlessTwist_of_numberField {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] [NumberField 𝕜]
    (C₅ : Work.TorsorExistence.FiveTorsionCurve 𝕜) (L : Work.TorsorExistence.CyclicExtension 𝕜 5)
    (h : (quinticTwistOf C₅ L).Pointless) : HasPointlessTwist 𝕜 :=
  hasPointlessTwist_of_pointless_data C₅ L h

/-- **Class (a), with the twist chosen for us.**  Over a number field a `FiveTorsionCurve` and a
cyclic quintic extension both exist, so the residual `ClarkLacyPointless 𝕜` reduces to the
single statement `∃ C₅ L, (quinticTwistOf C₅ L).Pointless`, i.e. to Clark–Lacy's choice of the
Kummer class. -/
theorem clarkLacyPointless_of_exists_pointless {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (h : ∃ (C₅ : Work.TorsorExistence.FiveTorsionCurve 𝕜)
      (L : Work.TorsorExistence.CyclicExtension 𝕜 5), (quinticTwistOf C₅ L).Pointless) :
    ClarkLacyPointless 𝕜 := by
  obtain ⟨C₅, L, hL⟩ := h
  exact hasPointlessTwist_of_pointless_data C₅ L hL

/-- The `DecidableEq`-free form: an existential over the two pieces of data with the instance
quantified.  `quinticTwistOf` is applied with the quantified instance explicitly. -/
theorem hasPointlessTwistAny_of_exists_pointless {𝕜 : Type} [Field 𝕜]
    (h : ∃ (d : DecidableEq 𝕜) (C₅ : @Work.TorsorExistence.FiveTorsionCurve 𝕜 _ d)
      (L : Work.TorsorExistence.CyclicExtension 𝕜 5),
      @Work.TorsorExistence.QuinticTwist.Pointless 𝕜 _ d (@quinticTwistOf 𝕜 _ d C₅ L)) :
    HasPointlessTwistAny 𝕜 := by
  obtain ⟨d, C₅, L, hL⟩ := h
  exact ⟨d, hasPointlessTwist_of_pointless_data C₅ L hL⟩

end

end Work.PointlessIndexFive
