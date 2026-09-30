import Mathlib
import Submission.Work.CurveBasics.BCSquare
import Submission.Work.CurveBasics.Linear
import Submission.Work.CurveBasics.Curve.BCSquare.fieldMap_injective
import Submission.Work.CurveBasics.Divisor
import Submission.Work.RiemannRoch.Canonical
import Submission.Work.RiemannRoch.Canonical.Properties
import Submission.Work.RiemannRoch.Canonical.ExistsCanonical
import Submission.Work.RiemannRoch.RR.l_sub_l_le
import Submission.Work.RiemannRoch.RR8.IsCanonicalDivMap
import Submission.Work.RiemannRoch.RR8.i_divMap
import Submission.Work.CurveBasics.Linear.finiteDimensional_L

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.RiemannRoch.RR6

open Work.CurveBasics

universe u

/-- If `F ≤ E` are divisors on a curve with `deg E - deg F = 1`, and `g` is a nonzero element of
`L E` which does not lie in `L F`, then the dimension of `L` increases by exactly one:
`l F + 1 = l E`.  Indeed `L F < L E` is a strict inclusion of finite dimensional `k`-spaces, so
`l F < l E`, while `l E - l F ≤ deg E - deg F = 1` by `l_sub_l_le`. -/
theorem l_add_one_eq_of_mem_not_mem {k : Type u} [Field k] (C : Curve k) {E F : C.Div}
    (hFE : F ≤ E) (hdeg : C.deg E - C.deg F = 1) {g : C.functionField}
    (hgE : g ∈ C.L E) (hgF : g ∉ C.L F) :
    C.l F + 1 = C.l E := by
  have hle : C.L F ≤ C.L E :=
    C.L_mono (Work.CurveBasics.Curve.Div.le_iff.mpr (Finsupp.le_def.mp hFE))
  have hne : C.L F ≠ C.L E := by
    intro h
    rw [h] at hgF
    exact hgF hgE
  have hlt : C.L F < C.L E := lt_of_le_of_ne hle hne
  haveI : FiniteDimensional k ↥(C.L E) := Work.CurveBasics.Linear.finiteDimensional_L C E
  have hlt' : C.l F < C.l E := Submodule.finrank_lt_finrank_of_lt hlt
  have hub := Work.RiemannRoch.RR.l_sub_l_le C hFE
  rw [hdeg] at hub
  omega

/-- **RR6, base-change-square form.**  Let `S : BCSquare C C'` be a base-change square, `A` a
divisor on `C` with `i A > 0`, and `Q` a place of `C'` of degree one, lying over a non-closed
point of `C` (hence over the generic point), such that the pullback of every nonzero rational
function of `C` is a unit at `Q`.  Then adding `Q` to the pullback of `A` drops the index of
speciality by exactly one.

The proof uses a canonical divisor `W` of `C`: its pullback `W' = S.divMap W` is canonical on
`C'`, so `i (A' ) = l (W' - A')` and `i (A' + [Q]) = l (W' - A' - [Q])`.  Since `i A = l (W - A)`
is positive, there is a nonzero `f ∈ L(W - A)`; its pullback lies in `L(W' - A')` but not in
`L(W' - A' - [Q])`, because the coefficients of `W'` and `A'` at `Q` vanish while `ord_Q (ι f) = 0`
— so `L(W' - A' - [Q]) < L(W' - A')` is strict, and `l_sub_l_le` bounds the drop by
`deg [Q] = 1`. -/
theorem i_add_generic_aux {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
    {C : Curve k} {C' : Curve F} (S : Curve.BCSquare C C') (A : C.Div)
    (hA : 0 < Work.RiemannRoch.Curve.i C A) (Q : C'.Place) (hQdeg : Q.degree = 1)
    (hQord : ∀ f : C.functionField, f ≠ 0 → C'.ordAt (S.fieldMap.hom f) Q = 0)
    (hQnc : ¬ IsClosed ({S.π Q.point} : Set C.left))
    (hl : ∀ D : C.Div, C'.l (S.divMap D) = C.l D)
    (hmem : ∀ {D : C.Div} {f : C.functionField}, f ∈ C.L D →
      S.fieldMap.hom f ∈ C'.L (S.divMap D)) :
    Work.RiemannRoch.Curve.i C' (S.divMap A + Work.CurveBasics.Curve.Div.place Q) + 1
      = Work.RiemannRoch.Curve.i C A := by
  classical
  -- a canonical divisor `W` of `C`, whose pullback is canonical on `C'`
  let W : C.Div := Work.RiemannRoch.Curve.canonical C
  have hW : Work.RiemannRoch.Curve.IsCanonical C W :=
    Work.RiemannRoch.Curve.isCanonical_canonical C
  have hW' : Work.RiemannRoch.Curve.IsCanonical C' (S.divMap W) :=
    Work.RiemannRoch.RR8.isCanonical_divMap S hl hW
  -- `i A = l (W - A) > 0`, so there is a nonzero section of `W - A`
  have hpos : 0 < C.l (W - A) := by
    rw [← hW A]
    exact hA
  have hbot : C.L (W - A) ≠ ⊥ := by
    intro h
    have h2 : C.l (W - A) = 0 := by
      rw [Work.CurveBasics.Curve.l, h]
      simp
    omega
  obtain ⟨f, hfmem, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  -- its pullback is a section of `W' - A'`
  have hfmem' : S.fieldMap.hom f ∈ C'.L (S.divMap W - S.divMap A) := by
    have h2 := hmem hfmem
    rwa [map_sub] at h2
  -- the coefficients of `divMap W` and `divMap A` at `Q` vanish
  have hcoeff : ∀ D : C.Div, (S.divMap D) Q = 0 := by
    intro D
    rw [S.divMap_apply, Curve.BCSquare.divMapCoeff, dif_neg hQnc]
  -- but the pullback of `f` is *not* a section of `W' - A' - [Q]`
  have hnotmem : S.fieldMap.hom f ∉ C'.L (S.divMap W - S.divMap A
      - Work.CurveBasics.Curve.Div.place Q) := by
    intro hmem2
    rw [Work.CurveBasics.Curve.mem_L_iff] at hmem2
    rcases hmem2 with h0 | heff
    · have hz0 : f = 0 := by
        apply Curve.BCSquare.fieldMap_injective S
        simpa using h0
      exact hf0 hz0
    · have hQ0 := heff Q
      have hord : Scheme.ord (S.fieldMap.hom f) Q.point = 0 := hQord f hf0
      rw [Finsupp.add_apply, Finsupp.sub_apply, Finsupp.sub_apply,
        Work.CurveBasics.Curve.div_apply, hord, hcoeff W, hcoeff A,
        Work.CurveBasics.Curve.Div.place, Finsupp.single_eq_same] at hQ0
      omega
  -- `W' - A' - [Q] ≤ W' - A'`
  have hle : S.divMap W - S.divMap A - Work.CurveBasics.Curve.Div.place Q
      ≤ S.divMap W - S.divMap A := by
    rw [Finsupp.le_def]
    intro R
    rw [Finsupp.sub_apply, Finsupp.sub_apply]
    have h1 : (0 : ℤ) ≤ (Work.CurveBasics.Curve.Div.place Q) R := by
      rw [Work.CurveBasics.Curve.Div.place, Finsupp.single_apply]
      split_ifs <;> norm_num
    linarith
  -- the degrees differ by `deg [Q] = 1`
  have hdeg : C'.deg (S.divMap W - S.divMap A)
      - C'.deg (S.divMap W - S.divMap A - Work.CurveBasics.Curve.Div.place Q) = 1 := by
    have h1 : C'.deg (S.divMap W - S.divMap A)
        = C'.deg (S.divMap W - S.divMap A - Work.CurveBasics.Curve.Div.place Q)
          + C'.deg (Work.CurveBasics.Curve.Div.place Q) := by
      rw [← C'.deg_add, sub_add_cancel]
    have h2 : C'.deg (Work.CurveBasics.Curve.Div.place Q) = 1 := by
      rw [Work.CurveBasics.Curve.deg_place]
      have hrd : Scheme.Hom.residueDegree C'.hom Q.point = 1 := hQdeg
      rw [hrd]
      norm_num
    linarith
  -- hence `l` drops by exactly one
  have hl1 : C'.l (S.divMap W - S.divMap A - Work.CurveBasics.Curve.Div.place Q) + 1
      = C'.l (S.divMap W - S.divMap A) :=
    l_add_one_eq_of_mem_not_mem C' hle hdeg hfmem' hnotmem
  -- duality on `C'` computes both indices of speciality
  have hA' : Work.RiemannRoch.Curve.i C' (S.divMap A) = C'.l (S.divMap W - S.divMap A) :=
    hW' (S.divMap A)
  have hB' : Work.RiemannRoch.Curve.i C' (S.divMap A + Work.CurveBasics.Curve.Div.place Q)
      = C'.l (S.divMap W - S.divMap A - Work.CurveBasics.Curve.Div.place Q) := by
    have h := hW' (S.divMap A + Work.CurveBasics.Curve.Div.place Q)
    rwa [← sub_sub] at h
  have hi : Work.RiemannRoch.Curve.i C' (S.divMap A) = Work.RiemannRoch.Curve.i C A :=
    Work.RiemannRoch.RR8.i_divMap S hl A
  calc Work.RiemannRoch.Curve.i C' (S.divMap A
        + Work.CurveBasics.Curve.Div.place Q) + 1
      = C'.l (S.divMap W - S.divMap A - Work.CurveBasics.Curve.Div.place Q) + 1 := by rw [hB']
    _ = C'.l (S.divMap W - S.divMap A) := hl1
    _ = Work.RiemannRoch.Curve.i C' (S.divMap A) := hA'.symm
    _ = Work.RiemannRoch.Curve.i C A := hi

theorem i_add_generic {k : Type u} [Field k] (C : Work.CurveBasics.Curve k) (A : C.Div)
    (hA : 0 < Work.RiemannRoch.Curve.i C A)
    (Q : (C.baseChange (C.functionField : Type u)).Place)
    (hQdeg : Q.degree = 1)
    (hQord : ∀ f : C.functionField, f ≠ 0 →
      (C.baseChange (C.functionField : Type u)).ordAt
        ((Work.CurveBasics.Curve.bcSquare C (C.functionField : Type u)).fieldMap.hom f) Q = 0)
    (hQnc : ¬ IsClosed ({(C.baseChangeFst (C.functionField : Type u)) Q.point} : Set C.left))
    (hl : ∀ D : C.Div, (C.baseChange (C.functionField : Type u)).l
      ((Work.CurveBasics.Curve.bcSquare C (C.functionField : Type u)).divMap D) = C.l D)
    (hmem : ∀ {D : C.Div} {f : C.functionField}, f ∈ C.L D →
      (Work.CurveBasics.Curve.bcSquare C (C.functionField : Type u)).fieldMap.hom f
        ∈ (C.baseChange (C.functionField : Type u)).L
            ((Work.CurveBasics.Curve.bcSquare C (C.functionField : Type u)).divMap D)) :
    Work.RiemannRoch.Curve.i (C.baseChange (C.functionField : Type u))
        ((Work.CurveBasics.Curve.bcSquare C (C.functionField : Type u)).divMap A
          + Work.CurveBasics.Curve.Div.place Q) + 1
      = Work.RiemannRoch.Curve.i C A :=
  i_add_generic_aux (Work.CurveBasics.Curve.bcSquare C (C.functionField : Type u))
    A hA Q hQdeg hQord hQnc hl hmem

end Work.RiemannRoch.RR6
