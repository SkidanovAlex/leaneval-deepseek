import Mathlib
import Submission.Work.Charts.exists_nonspecial_support

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

namespace Work.BNChart

/-- **A reduced non-special effective divisor of degree the genus, supported in a prescribed
open.**

This is `Work.Charts.exists_nonspecial_support` with two strengthenings: every coefficient is
`1` on the support, and every place of the support has degree one.  Run the same induction as in
`exists_nonspecial_support` (start from `D = 0`, `i 0 = g`; while `i D ≠ 0` find a degree-one
place `P` in `U` at which `i` drops by one, using `Work.RiemannRoch.RR6.finite_setOf_i_add_place_eq`
and `Work.RiemannRoch.RR6.i_add_place_of_degree_one`), but additionally avoid the finitely many
places already in the support at each step; the hypothesis that the degree-one places in `U` are
infinite provides such a place. -/
theorem reduced_nonspecial_support {k : Type u} [Field k] (C : Work.CurveBasics.Curve k)
    (U : C.left.Opens)
    (h : {P : C.Place | P.degree = 1 ∧ P.point ∈ U}.Infinite) :
    ∃ D : C.Div, D.IsEffective ∧ C.deg D = (Work.RiemannRoch.Curve.genus C : ℤ) ∧
      Work.RiemannRoch.Curve.i C D = 0 ∧
      ∀ P : C.Place, D P ≠ 0 → P.degree = 1 ∧ P.point ∈ U ∧ D P = 1 := by
  classical
  -- One step: given `D` with `i D ≠ 0`, find a degree-one place `P` lying in `U`, outside the
  -- finite support of `D`, at which `i` drops (hence drops by exactly one).
  have step : ∀ (D : C.Div), Work.RiemannRoch.Curve.i C D ≠ 0 →
      ∃ P : C.Place, P.degree = 1 ∧ P.point ∈ U ∧ D P = 0 ∧
        Work.RiemannRoch.Curve.i C (D + Work.CurveBasics.Curve.Div.place P) + 1
          = Work.RiemannRoch.Curve.i C D := by
    intro D hD
    have hfin : {P : C.Place |
        Work.RiemannRoch.Curve.i C (D + Work.CurveBasics.Curve.Div.place P)
          = Work.RiemannRoch.Curve.i C D}.Finite :=
      Work.RiemannRoch.RR6.finite_setOf_i_add_place_eq C hD
    have hsupp : (↑D.support : Set C.Place).Finite := Finset.finite_toSet D.support
    obtain ⟨P, ⟨hPdeg, hPmem⟩, hPnotin⟩ := h.exists_notMem_finite (hfin.union hsupp)
    simp only [Set.mem_union, not_or] at hPnotin
    obtain ⟨hPbad, hPsupp⟩ := hPnotin
    have hDP0 : D P = 0 := by
      by_contra hc
      exact hPsupp (by simpa using (Finsupp.mem_support_iff.mpr hc))
    exact ⟨P, hPdeg, hPmem, hDP0,
      Work.RiemannRoch.RR6.i_add_place_of_degree_one C hPdeg hPbad⟩
  -- A single place is an effective divisor.
  have hplace_eff : ∀ P : C.Place,
      (Work.CurveBasics.Curve.Div.place P).IsEffective := by
    intro P Q
    rw [Work.CurveBasics.Curve.Div.place, Finsupp.single_apply]
    split_ifs <;> norm_num
  -- Induction: from an effective `D` all of whose support places are degree one in `U` with
  -- coefficient one, and with `i D = n`, we reach `D'` with the same properties,
  -- `deg D' = deg D + n` and `i D' = 0`.
  have main : ∀ n : ℕ, ∀ D : C.Div, D.IsEffective →
      (∀ P : C.Place, D P ≠ 0 → P.degree = 1 ∧ P.point ∈ U ∧ D P = 1) →
      Work.RiemannRoch.Curve.i C D = n →
      ∃ D' : C.Div, D'.IsEffective ∧
        (∀ P : C.Place, D' P ≠ 0 → P.degree = 1 ∧ P.point ∈ U ∧ D' P = 1) ∧
        C.deg D' = C.deg D + n ∧ Work.RiemannRoch.Curve.i C D' = 0 := by
    intro n
    induction n with
    | zero =>
      intro D hD hred hDi
      exact ⟨D, hD, hred, by simp, hDi⟩
    | succ m ih =>
      intro D hD hred hDi
      have hDne : Work.RiemannRoch.Curve.i C D ≠ 0 := by
        rw [hDi]; exact Nat.succ_ne_zero m
      obtain ⟨P, hPdeg, hPmem, hDP0, hPplus⟩ := step D hDne
      have hEi : Work.RiemannRoch.Curve.i C (D + Work.CurveBasics.Curve.Div.place P)
          = m := by
        have hh := hPplus
        rw [hDi] at hh
        omega
      have hEeff : (D + Work.CurveBasics.Curve.Div.place P).IsEffective :=
        hD.add (hplace_eff P)
      -- The new divisor is again "reduced with degree-one support in `U`".
      have hEred : ∀ Q : C.Place,
          (D + Work.CurveBasics.Curve.Div.place P) Q ≠ 0 →
            Q.degree = 1 ∧ Q.point ∈ U ∧
              (D + Work.CurveBasics.Curve.Div.place P) Q = 1 := by
        intro Q hQ
        by_cases hQP : Q = P
        · rw [hQP]
          have hvalP : (D + Work.CurveBasics.Curve.Div.place P) P = D P + 1 := by
            rw [Finsupp.add_apply, Work.CurveBasics.Curve.Div.place,
              Finsupp.single_eq_same]
          exact ⟨hPdeg, hPmem, by rw [hvalP, hDP0]; norm_num⟩
        · have hplace0 : Work.CurveBasics.Curve.Div.place P Q = 0 := by
            rw [Work.CurveBasics.Curve.Div.place, Finsupp.single_eq_of_ne hQP]
          have hvalQ : (D + Work.CurveBasics.Curve.Div.place P) Q = D Q := by
            rw [Finsupp.add_apply, hplace0, add_zero]
          have hDQ : D Q ≠ 0 := by rw [← hvalQ]; exact hQ
          obtain ⟨hQdeg, hQmem, hQ1⟩ := hred Q hDQ
          exact ⟨hQdeg, hQmem, by rw [hvalQ, hQ1]⟩
      obtain ⟨D', hD'eff, hD'red, hD'deg, hD'i⟩ :=
        ih (D + Work.CurveBasics.Curve.Div.place P) hEeff hEred hEi
      refine ⟨D', hD'eff, hD'red, ?_, hD'i⟩
      have hdegplace : C.deg (Work.CurveBasics.Curve.Div.place P) = 1 := by
        have hp : C.hom.residueDegree P.point = 1 := hPdeg
        have hh := Work.CurveBasics.Curve.deg_place C P
        rw [hp] at hh
        simpa using hh
      rw [hD'deg, C.deg_add, hdegplace]
      push_cast
      ring
  obtain ⟨D, hDeff, hDred, hDdeg, hDi⟩ :=
    main (Work.RiemannRoch.Curve.genus C) 0
      Work.CurveBasics.Curve.Div.isEffective_zero (fun P hP => by simp at hP) rfl
  have hdeg : C.deg D = (Work.RiemannRoch.Curve.genus C : ℤ) := by
    rw [hDdeg, C.deg_zero, zero_add]
  exact ⟨D, hDeff, hdeg, hDi, hDred⟩

end Work.BNChart
