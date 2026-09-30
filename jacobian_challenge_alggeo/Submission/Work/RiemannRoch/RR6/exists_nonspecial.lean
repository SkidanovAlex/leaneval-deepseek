import Mathlib
import Submission.Work.RiemannRoch.Canonical
import Submission.Work.RiemannRoch.Canonical.Properties
import Submission.Work.RiemannRoch.RRLib
import Submission.Work.RiemannRoch.RR6.finite_setOf_i_add_place_eq
import Submission.Work.RiemannRoch.RR6.i_add_place_of_degree_one
import Submission.Work.CurveBasics.Divisor

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.RiemannRoch.RR6

open Work.CurveBasics

/-- **RR6, existence of a non-special divisor of degree the genus.**

Since `{P | P.degree = 1}` is infinite while, for any `D` with `i D ≠ 0`, the set of places
`P` at which `i` does *not* drop is finite, we may add such a place and lose exactly one unit
of index (`i (D + [P]) + 1 = i D`).  Starting from `D = 0` (effective, with `deg 0 = 0` and
`i 0 = g`) and iterating `g` times, we obtain an effective divisor `D` with
`deg D = g` and `i D = 0`.  Riemann–Roch then gives `l D = 1`. -/
theorem exists_nonspecial {k : Type*} [Field k] (C : Work.CurveBasics.Curve k)
    (h : {P : C.Place | P.degree = 1}.Infinite) :
    ∃ D : C.Div, D.IsEffective ∧ C.deg D = (Work.RiemannRoch.Curve.genus C : ℤ)
      ∧ Work.RiemannRoch.Curve.i C D = 0 ∧ C.l D = 1 := by
  classical
  -- One step: given `D` with `i D ≠ 0`, add a degree-one place `P` outside the finite set of
  -- places at which `i` does not drop; then `i (D + [P]) + 1 = i D`.
  have step : ∀ (D : C.Div), Work.RiemannRoch.Curve.i C D ≠ 0 →
      ∃ P : C.Place, P.degree = 1 ∧
        Work.RiemannRoch.Curve.i C (D + Work.CurveBasics.Curve.Div.place P) + 1
          = Work.RiemannRoch.Curve.i C D := by
    intro D hD
    have hfin : {P : C.Place |
        Work.RiemannRoch.Curve.i C (D + Work.CurveBasics.Curve.Div.place P)
          = Work.RiemannRoch.Curve.i C D}.Finite :=
      finite_setOf_i_add_place_eq C hD
    obtain ⟨P, hPdeg, hPne⟩ := h.exists_notMem_finite hfin
    exact ⟨P, hPdeg, i_add_place_of_degree_one C hPdeg hPne⟩
  -- A single place is an effective divisor.
  have hplace_eff : ∀ P : C.Place,
      (Work.CurveBasics.Curve.Div.place P).IsEffective := by
    intro P Q
    rw [Work.CurveBasics.Curve.Div.place, Finsupp.single_apply]
    split_ifs <;> norm_num
  -- Induction: from an effective `D` with `i D = n` we reach an effective `D' ≥ D` with
  -- `deg D' = deg D + n` and `i D' = 0`.
  have main : ∀ n : ℕ, ∀ D : C.Div, D.IsEffective → Work.RiemannRoch.Curve.i C D = n →
      ∃ D' : C.Div, D ≤ D' ∧ D'.IsEffective ∧
        C.deg D' = C.deg D + n ∧ Work.RiemannRoch.Curve.i C D' = 0 := by
    intro n
    induction n with
    | zero =>
      intro D hD hDi
      exact ⟨D, le_refl D, hD, by simp, hDi⟩
    | succ m ih =>
      intro D hD hDi
      have hDne : Work.RiemannRoch.Curve.i C D ≠ 0 := by
        rw [hDi]; exact Nat.succ_ne_zero m
      obtain ⟨P, hPdeg, hPplus⟩ := step D hDne
      have hPm : Work.RiemannRoch.Curve.i C (D + Work.CurveBasics.Curve.Div.place P)
          = m := by
        have hh := hPplus
        rw [hDi] at hh
        omega
      obtain ⟨D', hDD', hD'eff, hD'deg, hD'i⟩ :=
        ih (D + Work.CurveBasics.Curve.Div.place P) (hD.add (hplace_eff P)) hPm
      have hDle : D ≤ D + Work.CurveBasics.Curve.Div.place P := by
        rw [Finsupp.le_def]
        intro Q
        rw [Finsupp.add_apply]
        have := hplace_eff P Q
        linarith
      refine ⟨D', le_trans hDle hDD', hD'eff, ?_, hD'i⟩
      have hdegplace : C.deg (Work.CurveBasics.Curve.Div.place P) = 1 := by
        have hp : C.hom.residueDegree P.point = 1 := hPdeg
        have hh := Work.CurveBasics.Curve.deg_place C P
        rw [hp] at hh
        simpa using hh
      rw [hD'deg, C.deg_add, hdegplace]
      push_cast
      ring
  obtain ⟨D, _h0D, hDeff, hDdeg, hDi⟩ :=
    main (Work.RiemannRoch.Curve.genus C) 0
      Work.CurveBasics.Curve.Div.isEffective_zero rfl
  have hdeg : C.deg D = (Work.RiemannRoch.Curve.genus C : ℤ) := by
    rw [hDdeg, C.deg_zero, zero_add]
  have hl : C.l D = 1 := by
    have hrr := Work.RiemannRoch.Curve.riemannRoch C D
    rw [hDi, Nat.cast_zero, sub_zero, hdeg] at hrr
    have hlz : (C.l D : ℤ) = 1 := by rw [hrr]; ring
    omega
  exact ⟨D, hDeff, hdeg, hDi, hl⟩

end Work.RiemannRoch.RR6
