import Mathlib
import Submission.Work.RiemannRoch.RR6.exists_nonspecial

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

namespace Work.Charts

open Work.CurveBasics

/-- **A non-special effective divisor of degree the genus with support in a prescribed open
subscheme.**

This is `Work.RiemannRoch.RR6.exists_nonspecial` with the additional requirement that the
divisor be supported in a fixed open `U`, which is possible as soon as the places of degree one
lying in `U` are infinite.

The argument is the same induction as in `exists_nonspecial`.  Start from `D = 0` (effective,
`deg 0 = 0`, `i 0 = g`).  For a divisor `D` with `i D ≠ 0`, the places `P` with
`i (D + [P]) = i D` form a finite set (finiteness of the places at which `i` does not drop), so
among the infinitely many degree-one places contained in `U` one finds a `P ∈ U` at which `i`
does drop; by `i_add_place_of_degree_one` it drops by exactly one:
`i (D + [P]) + 1 = i D`.  Repeating this `g` times produces an effective divisor supported in
`U` with `deg D = g` and `i D = 0`. -/
theorem exists_nonspecial_support {k : Type u} [Field k] (C : Work.CurveBasics.Curve k)
    (U : C.left.Opens)
    (h : {P : C.Place | P.degree = 1 ∧ P.point ∈ U}.Infinite) :
    ∃ D : C.Div, D.IsEffective ∧ C.deg D = (Work.RiemannRoch.Curve.genus C : ℤ) ∧
      Work.RiemannRoch.Curve.i C D = 0 ∧ ∀ P : C.Place, D P ≠ 0 → P.point ∈ U := by
  classical
  -- One step: given `D` with `i D ≠ 0`, find a degree-one place `P` lying in `U` at which `i`
  -- drops (hence drops by exactly one).
  have step : ∀ (D : C.Div), Work.RiemannRoch.Curve.i C D ≠ 0 →
      ∃ P : C.Place, P.degree = 1 ∧ P.point ∈ U ∧
        Work.RiemannRoch.Curve.i C (D + Work.CurveBasics.Curve.Div.place P) + 1
          = Work.RiemannRoch.Curve.i C D := by
    intro D hD
    have hfin : {P : C.Place |
        Work.RiemannRoch.Curve.i C (D + Work.CurveBasics.Curve.Div.place P)
          = Work.RiemannRoch.Curve.i C D}.Finite :=
      Work.RiemannRoch.RR6.finite_setOf_i_add_place_eq C hD
    obtain ⟨P, ⟨hPdeg, hPmem⟩, hPne⟩ := h.exists_notMem_finite hfin
    exact ⟨P, hPdeg, hPmem,
      Work.RiemannRoch.RR6.i_add_place_of_degree_one C hPdeg hPne⟩
  -- A single place is an effective divisor.
  have hplace_eff : ∀ P : C.Place,
      (Work.CurveBasics.Curve.Div.place P).IsEffective := by
    intro P Q
    rw [Work.CurveBasics.Curve.Div.place, Finsupp.single_apply]
    split_ifs <;> norm_num
  -- The support of `[P]` is `{P}`.
  have hplace_supp : ∀ (P Q : C.Place),
      Work.CurveBasics.Curve.Div.place P Q ≠ 0 → Q = P := by
    intro P Q hQ
    by_contra hne
    exact hQ (by
      rw [Work.CurveBasics.Curve.Div.place, Finsupp.single_eq_of_ne hne])
  -- Induction: from an effective `D` supported in `U` with `i D = n` we reach an effective `D'`
  -- supported in `U` with `deg D' = deg D + n` and `i D' = 0`.
  have main : ∀ n : ℕ, ∀ D : C.Div, D.IsEffective →
      (∀ P : C.Place, D P ≠ 0 → P.point ∈ U) →
      Work.RiemannRoch.Curve.i C D = n →
      ∃ D' : C.Div, D'.IsEffective ∧
        (∀ P : C.Place, D' P ≠ 0 → P.point ∈ U) ∧
        C.deg D' = C.deg D + n ∧ Work.RiemannRoch.Curve.i C D' = 0 := by
    intro n
    induction n with
    | zero =>
      intro D hD hsupp hDi
      exact ⟨D, hD, hsupp, by simp, hDi⟩
    | succ m ih =>
      intro D hD hsupp hDi
      have hDne : Work.RiemannRoch.Curve.i C D ≠ 0 := by
        rw [hDi]; exact Nat.succ_ne_zero m
      obtain ⟨P, hPdeg, hPmem, hPplus⟩ := step D hDne
      have hEi : Work.RiemannRoch.Curve.i C (D + Work.CurveBasics.Curve.Div.place P)
          = m := by
        have hh := hPplus
        rw [hDi] at hh
        omega
      have hEeff : (D + Work.CurveBasics.Curve.Div.place P).IsEffective :=
        hD.add (hplace_eff P)
      have hEsupp : ∀ Q : C.Place,
          (D + Work.CurveBasics.Curve.Div.place P) Q ≠ 0 → Q.point ∈ U := by
        intro Q hQ
        rw [Finsupp.add_apply] at hQ
        by_cases hQP : Q = P
        · subst hQP; exact hPmem
        · have hzero : Work.CurveBasics.Curve.Div.place P Q = 0 := by
            rw [Work.CurveBasics.Curve.Div.place, Finsupp.single_eq_of_ne hQP]
          rw [hzero, add_zero] at hQ
          exact hsupp Q hQ
      obtain ⟨D', hD'eff, hD'supp, hD'deg, hD'i⟩ :=
        ih (D + Work.CurveBasics.Curve.Div.place P) hEeff hEsupp hEi
      refine ⟨D', hD'eff, hD'supp, ?_, hD'i⟩
      have hdegplace : C.deg (Work.CurveBasics.Curve.Div.place P) = 1 := by
        have hp : C.hom.residueDegree P.point = 1 := hPdeg
        have hh := Work.CurveBasics.Curve.deg_place C P
        rw [hp] at hh
        simpa using hh
      rw [hD'deg, C.deg_add, hdegplace]
      push_cast
      ring
  obtain ⟨D, hDeff, hDsupp, hDdeg, hDi⟩ :=
    main (Work.RiemannRoch.Curve.genus C) 0
      Work.CurveBasics.Curve.Div.isEffective_zero (fun P hP => by simp at hP) rfl
  have hdeg : C.deg D = (Work.RiemannRoch.Curve.genus C : ℤ) := by
    rw [hDdeg, C.deg_zero, zero_add]
  exact ⟨D, hDeff, hdeg, hDi, hDsupp⟩

end Work.Charts
