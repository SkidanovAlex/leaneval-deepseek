import Mathlib
import Submission.Work.RiemannRoch.RRLib
import Submission.Work.RiemannRoch.RR.l_sub_l_le
import Submission.Work.RiemannRoch.RR.i_anti
import Submission.Work.CurveBasics.Linear.finiteDimensional_L

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option linter.style.haveILetI false

namespace Work.RiemannRoch.RR6

/-- **RR6 at a place of degree one.**  Adding a place `P` of degree one to a divisor `D` drops the
index of speciality by at most the change in `l`:
`i D - i (D + [P]) = deg [P] - (l (D + [P]) - l D) = 1 - (l (D + [P]) - l D)`
(`Curve.i_sub_i`), and `l (D + [P]) - l D ≤ deg [P] = 1` (`RR.l_sub_l_le`).  Since `l` is
monotone the right hand side is `1 - m` with `0 ≤ m ≤ 1`, so `i D - i (D + [P]) ∈ {0, 1}`.  Given
that the two indices differ, the difference cannot be `0`; it is `1`. -/
theorem i_add_place_of_degree_one {k : Type*} [Field k] (C : Work.CurveBasics.Curve k)
    {D : C.Div} {P : C.Place} (hP : P.degree = 1)
    (h : Work.RiemannRoch.Curve.i C (D + Work.CurveBasics.Curve.Div.place P)
      ≠ Work.RiemannRoch.Curve.i C D) :
    Work.RiemannRoch.Curve.i C (D + Work.CurveBasics.Curve.Div.place P) + 1
      = Work.RiemannRoch.Curve.i C D := by
  set E := D + Work.CurveBasics.Curve.Div.place P with hE
  -- `D ≤ D + [P]` for the pointwise (Finsupp) order on divisors.
  have hle : D ≤ E := by
    rw [hE, Finsupp.le_def]
    intro Q
    by_cases hQ : Q = P
    · subst hQ
      rw [Finsupp.add_apply, Work.CurveBasics.Curve.Div.place, Finsupp.single_eq_same]
      omega
    · rw [Finsupp.add_apply, Work.CurveBasics.Curve.Div.place,
        Finsupp.single_eq_of_ne hQ, add_zero]
  -- Anti-monotonicity of `i`: `i (D + [P]) ≤ i D`.
  have hanti : Work.RiemannRoch.Curve.i C E ≤ Work.RiemannRoch.Curve.i C D :=
    Work.RiemannRoch.RR.i_anti C hle
  -- Since the two indices differ, `i (D + [P]) + 1 ≤ i D`.
  have hlt : Work.RiemannRoch.Curve.i C E + 1 ≤ Work.RiemannRoch.Curve.i C D :=
    Nat.succ_le_of_lt (lt_of_le_of_ne hanti h)
  -- Riemann–Roch for the pair `D ≤ D + [P]`.
  have hsub := Work.RiemannRoch.Curve.i_sub_i C hle
  -- `deg (D + [P]) - deg D = deg [P] = P.degree = 1`.
  have hdeg : C.deg E - C.deg D = 1 := by
    have h1 : C.deg E = C.deg D + C.deg (Work.CurveBasics.Curve.Div.place P) := by
      rw [hE]; exact C.deg_add D _
    have h4 : C.hom.residueDegree P.point = 1 := hP
    have h2 : C.deg (Work.CurveBasics.Curve.Div.place P) = 1 := by
      rw [Work.CurveBasics.Curve.deg_place]; rw [h4]; norm_num
    linarith
  -- `l` is monotone in the divisor.
  have hlmono : C.l D ≤ C.l E := by
    haveI : FiniteDimensional k (C.L E) := Work.CurveBasics.Linear.finiteDimensional_L C E
    exact Submodule.finrank_mono (C.L_mono (Work.CurveBasics.Curve.Div.le_iff.mpr hle))
  -- Rewrite the Riemann–Roch difference using `deg (D + [P]) - deg D = 1`.
  have hsub' : (Work.RiemannRoch.Curve.i C D : ℤ) - Work.RiemannRoch.Curve.i C E
      = 1 - ((C.l E : ℤ) - C.l D) := by
    rw [hsub]; linarith
  -- Hence `i D - i (D + [P]) ≤ 1`.
  have hle1 : (Work.RiemannRoch.Curve.i C D : ℤ) - Work.RiemannRoch.Curve.i C E ≤ 1 := by
    have : (0 : ℤ) ≤ (C.l E : ℤ) - C.l D := by omega
    linarith
  have key : Work.RiemannRoch.Curve.i C D ≤ Work.RiemannRoch.Curve.i C E + 1 := by omega
  exact le_antisymm hlt key

end Work.RiemannRoch.RR6
