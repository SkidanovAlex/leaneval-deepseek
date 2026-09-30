import Mathlib
import Submission.Work.CurveBasics.Place.valuationSubring_ne_top
import Submission.Work.CurveBasics.Order.Bridge
import Submission.Work.CurveBasics.Place.mem_valuationSubring_iff
import Submission.Work.RiemannRoch.RR.riemann_exists_polynomial_ordAt_pos

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.CurveBasics.Order

/-- The prime of `k[h]^int` attached to a place `Q` at which `h` is *regular* (`0 ≤ ord_Q h`)
is nonzero.

If `ord_Q h > 0` this follows from the fact that `h` itself lies in the maximal ideal of the
valuation ring at `Q`.  In the boundary case `ord_Q h = 0` the argument is different: `h` is a
unit at `Q`, so some nonzero polynomial expression `μ(h)` in `h` vanishes at `Q`
(`Work.RiemannRoch.RR.riemann_exists_polynomial_ordAt_pos`, which uses that the residue field of
a closed point of a curve is finite, hence algebraic, over `k`).  This element `μ(h)` lies in
`k[h] ⊆ k[h]^int` and in the maximal ideal of the valuation ring, hence is a nonzero element of
the prime, which therefore is not `⊥`. -/
theorem kxPrimeOfPlace_ne_bot_of_nonneg {k : Type*} [Field k] (C : Work.CurveBasics.Curve k) (h : C.functionField)
    (hht : Transcendental k h)
    [FiniteDimensional (IntermediateField.adjoin k ({h} : Set C.functionField)) C.functionField]
    (Q : C.Place) (hQ : 0 ≤ C.ordAt h Q) :
    Work.CurveBasics.kxPrimeOfPlace C h Q hQ ≠ ⊥ := by
  classical
  -- a nonzero polynomial expression in `h` vanishing at `Q`
  obtain ⟨μ, hμne, hμpos⟩ :=
    Work.RiemannRoch.RR.riemann_exists_polynomial_ordAt_pos C h hht Q hQ
  have hy_mem : (Polynomial.aeval h) μ ∈ Algebra.adjoin k ({h} : Set C.functionField) := by
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨μ, rfl⟩
  -- `μ(h)` as an element of `k[h]` and of its integral closure `k[h]^int`
  let s : ↥(Algebra.adjoin k ({h} : Set C.functionField)) := ⟨(Polynomial.aeval h) μ, hy_mem⟩
  let a : C.kxClosure h := algebraMap ↥(Algebra.adjoin k ({h} : Set C.functionField))
    (C.kxClosure h) s
  have ha_coe : (a : C.functionField) = (Polynomial.aeval h) μ := by
    rw [Subalgebra.coe_algebraMap]
    rfl
  -- `μ(h)` is nonzero because `h` is transcendental
  have ha_ne : a ≠ 0 := by
    intro h0
    have h1 : (Polynomial.aeval h) μ = 0 := by rw [← ha_coe, h0]; rfl
    exact hμne ((transcendental_iff.mp hht) μ h1)
  -- `μ(h)` lies in the prime, being in the maximal ideal of the valuation ring
  have hmem : a ∈ Work.CurveBasics.kxPrimeOfPlace C h Q hQ := by
    show Subring.inclusion (kxClosure_le_valuationSubring C h Q hQ) a ∈
      IsLocalRing.maximalIdeal ↥(Q.valuationSubring)
    set b := Subring.inclusion (kxClosure_le_valuationSubring C h Q hQ) a with hb
    have hbcoe : (b : C.functionField) = (Polynomial.aeval h) μ := by
      rw [hb, Subring.coe_inclusion]
      exact ha_coe
    have hbne : (b : C.functionField) ≠ 0 := by
      rw [hbcoe]
      intro h0
      exact hμne ((transcendental_iff.mp hht) μ h0)
    rw [mem_maximalIdeal_iff_ord_pos C Q b hbne, hbcoe]
    exact hμpos
  intro hbot
  rw [hbot] at hmem
  exact ha_ne (Ideal.mem_bot.mp hmem)

end Work.CurveBasics.Order
