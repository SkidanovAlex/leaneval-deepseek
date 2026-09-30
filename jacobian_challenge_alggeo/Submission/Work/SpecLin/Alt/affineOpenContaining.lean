import Mathlib
import Submission.Work.CurveBasics.All
import Submission.Work.CurveBasics.exists_separating_element
import Submission.Work.SpecLin.Chart.Regular
import Submission.Work.SpecLin.Alt.CurveAffine
import Submission.Work.SpecLin.Alt.exists_regular_transcendental
import Submission.Work.SpecLin.Alt.exists_section_regularOpens
import Submission.Work.SpecLin.Alt.valuativeCriterion_uniqueness
import Submission.Work.SpecLin.Alt.valuativeCriterion_existence
import Submission.Work.SpecLin.Alt.locallyQuasiFinite_phi

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SpecLin.Alt

variable {K : Type u} [Field K]

open Work.CurveBasics in
/-- `regularOpens C x` is nonempty: it contains the generic point. -/
theorem nonempty_regularOpens (C : Work.CurveBasics.Curve K) (x : C.functionField) : Nonempty (regularOpens C x) :=
  ⟨genericPoint C.left, by
    rw [Work.SpecLin.Chart.mem_regularOpens]
    intro Q hQ
    exact absurd hQ (by
      intro h
      have h1 := Q.eq_coheight_one
      rw [h, C.coheight_genericPoint] at h1
      exact one_ne_zero h1.symm)⟩

instance (C : Work.CurveBasics.Curve K) (x : C.functionField) : Nonempty (regularOpens C x) :=
  nonempty_regularOpens C x

open Work.CurveBasics in
/-- **`phi W s` is proper.**  This is the valuative criterion, using the properness of the curve
and the fact that the closed point of a valuation ring cannot be sent to a pole of `x`. -/
theorem isProper_phi {C : Curve K} {x : C.functionField} (hx : Transcendental K x)
    (s : Γ(C.left, regularOpens C x)) [Nonempty (regularOpens C x)]
    (hs : (C.germToFunctionField (regularOpens C x)).hom s = x) :
    IsProper (phi (regularOpens C x) s) := by
  haveI : QuasiCompact (phi (regularOpens C x) s) := quasiCompact_phi C s
  haveI : LocallyOfFiniteType (phi (regularOpens C x) s) := locallyOfFiniteType_phi C s
  refine IsProper.of_valuativeCriterion (phi (regularOpens C x) s)
    ((ValuativeCriterion.iff).mpr ⟨valuativeCriterion_existence hx s hs, ?_⟩)
  exact valuativeCriterion_uniqueness (regularOpens C x) s

open Work.CurveBasics in
/-- **`phi W s` is finite.** -/
theorem isFinite_phi {C : Curve K} {x : C.functionField} (hx : Transcendental K x)
    (s : Γ(C.left, regularOpens C x)) [Nonempty (regularOpens C x)]
    (hs : (C.germToFunctionField (regularOpens C x)).hom s = x) :
    IsFinite (phi (regularOpens C x) s) := by
  haveI : IsProper (phi (regularOpens C x) s) := isProper_phi hx s hs
  haveI : LocallyQuasiFinite (phi (regularOpens C x) s) := locallyQuasiFinite_phi hx s hs
  exact IsFinite.of_isProper_of_locallyQuasiFinite (phi (regularOpens C x) s)

open Work.CurveBasics in
/-- **The open subscheme on which a transcendental rational function is regular is affine.**

`regularOpens C x = C ∖ (poles of x)` is the preimage of the affine line under the morphism
`phi` given by `x`, which is proper and locally quasi-finite, hence finite; a scheme finite over
an affine scheme is affine. -/
theorem isAffineOpen_regularOpens {C : Curve K} {x : C.functionField}
    (hx : Transcendental K x) : IsAffineOpen (regularOpens C x) := by
  obtain ⟨s, hs⟩ := exists_section_regularOpens C x
  haveI : IsFinite (phi (regularOpens C x) s) := isFinite_phi hx s hs
  exact isAffine_of_isAffineHom (phi (regularOpens C x) s)

open Work.CurveBasics in
/-- **Every finite set of points of a smooth proper curve lies in an affine open subset.** -/
theorem affineOpenContaining {K : Type*} [Field K] (C : Work.CurveBasics.Curve K)
    (S : Set C.left) (hS : S.Finite) :
    ∃ W : C.left.Opens, AlgebraicGeometry.IsAffineOpen W ∧ S ⊆ (W : Set C.left) := by
  obtain ⟨x, hx, hSx⟩ := exists_regular_transcendental C S hS
  exact ⟨regularOpens C x, isAffineOpen_regularOpens hx, hSx⟩

end Work.SpecLin.Alt
