import Mathlib
import Submission.Work.RiemannRoch.Canonical
import Submission.Work.RiemannRoch.Canonical.ExistsCanonical
import Submission.Work.RiemannRoch.Duality.Basic
import Submission.Work.RiemannRoch.Duality.exists_isDivW
import Submission.Work.RiemannRoch.Duality.isCanonical_divW
import Submission.Work.RiemannRoch.RRLib
import Submission.Work.RiemannRoch.RR.i_anti
import Submission.Work.RiemannRoch.RR.L_eq_bot_of_deg_neg

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.RiemannRoch.RR6

open Work.RiemannRoch

/-- **RR6, finiteness of the places at which `i` does not drop.**

Fix `D` with `i D ≠ 0`, so that `WD C D ≠ 0`, and pick `0 ≠ ω ∈ WD C D`.  Hence `ω` has a
divisor `W = divW ω`, the largest divisor with `ω ∈ WD C W`.

If `i (D + [P]) = i D` for a place `P` then `D ≤ D + [P]` gives `WD (D + [P]) ≤ WD D`, and
`finrank_WD` turns the equality of indices into an equality of `finrank`s; since `WD D` is
finite dimensional this forces `WD (D + [P]) = WD D`, so `ω ∈ WD (D + [P])`.  Maximality of `W`
then gives `D + [P] ≤ W`, i.e. `P` lies in the (finite) support of `W - D`.

Consequently the set of such `P` is contained in a finite set. -/
theorem finite_setOf_i_add_place_eq {k : Type*} [Field k] (C : Work.CurveBasics.Curve k)
    {D : C.Div} (hD : Work.RiemannRoch.Curve.i C D ≠ 0) :
    {P : C.Place | Work.RiemannRoch.Curve.i C (D + Work.CurveBasics.Curve.Div.place P)
      = Work.RiemannRoch.Curve.i C D}.Finite := by
  classical
  -- The divisor `[P]` is nonnegative, so `D ≤ D + [P]`.
  have hplace_nonneg : ∀ (Q P : C.Place),
      (0 : ℤ) ≤ Work.CurveBasics.Curve.Div.place P Q :=
    fun Q P => by
      rw [Work.CurveBasics.Curve.Div.place, Finsupp.single_apply]
      split_ifs <;> norm_num
  -- A nonzero Weil differential in `WD C D`.
  have hne : Work.RiemannRoch.Curve.WD C D ≠ ⊥ := by
    intro hbot
    have h0 : Module.finrank k ↥(Work.RiemannRoch.Curve.WD C D) = 0 := by
      rw [hbot]; simp
    rw [Work.RiemannRoch.Duality.finrank_WD] at h0
    exact hD h0
  obtain ⟨ω, hωmem, hω0⟩ := (Submodule.ne_bot_iff _).mp hne
  have hωOmega : ω ∈ Work.RiemannRoch.Curve.Omega C :=
    Work.RiemannRoch.Curve.le_Omega C D hωmem
  obtain ⟨W, hW⟩ := Work.RiemannRoch.Duality.exists_isDivW C hωOmega hω0
  -- `WD C D` is finite dimensional, so inclusion plus equality of `finrank` is equality.
  haveI : FiniteDimensional k ↥(Work.RiemannRoch.Curve.WD C D) :=
    (Work.RiemannRoch.Curve.WDequiv C D).finiteDimensional
  refine (Finset.finite_toSet ((W - D).support)).subset ?_
  intro P hP
  have hPeq : Work.RiemannRoch.Curve.i C (D + Work.CurveBasics.Curve.Div.place P)
      = Work.RiemannRoch.Curve.i C D := hP
  -- `D ≤ D + [P]`.
  have hdP : D ≤ D + Work.CurveBasics.Curve.Div.place P := by
    rw [Finsupp.le_def]
    intro Q
    rw [Finsupp.add_apply]
    have := hplace_nonneg Q P
    linarith
  -- Since the indices agree, `WD (D + [P]) = WD D`.
  have heq : Work.RiemannRoch.Curve.WD C (D + Work.CurveBasics.Curve.Div.place P)
      = Work.RiemannRoch.Curve.WD C D := by
    refine Submodule.eq_of_le_of_finrank_eq (Work.RiemannRoch.Curve.WD_anti C hdP) ?_
    rw [Work.RiemannRoch.Duality.finrank_WD C (D + Work.CurveBasics.Curve.Div.place P),
      Work.RiemannRoch.Duality.finrank_WD C D, hPeq]
  have hmem : ω ∈ Work.RiemannRoch.Curve.WD C (D + Work.CurveBasics.Curve.Div.place P) := by
    rw [heq]; exact hωmem
  -- Maximality of `W` then forces `D + [P] ≤ W`.
  have hleW : D + Work.CurveBasics.Curve.Div.place P ≤ W := hW.2 _ hmem
  -- Hence the coefficient of `W - D` at `P` is positive, so `P ∈ supp (W - D)`.
  rw [Finset.mem_coe, Finsupp.mem_support_iff]
  intro hzero
  have h1 : (1 : ℤ) ≤ (W - D) P := by
    have h2 := hleW P
    rw [Finsupp.add_apply, Work.CurveBasics.Curve.Div.place, Finsupp.single_eq_same] at h2
    rw [Finsupp.sub_apply]
    linarith
  rw [hzero] at h1
  norm_num at h1

end Work.RiemannRoch.RR6
