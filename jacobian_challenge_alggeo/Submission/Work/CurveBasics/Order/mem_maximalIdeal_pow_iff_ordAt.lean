import Mathlib
import Submission.Work.CurveBasics.Order.Bridge
import Submission.Work.CurveBasics.Order.ordPosSetup
import Submission.Work.CurveBasics.Place.Valuation
import Submission.Work.CurveBasics.Place.mem_valuationSubring_iff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

namespace Work.CurveBasics.Order

open Work.CurveBasics

/-- In the value group `ℤᵐ⁰`, an element is `< 1` if and only if it is `≤ exp (-1)`. -/
private lemma lt_one_iff_le_exp_neg_one_ord {y : WithZero (Multiplicative ℤ)} :
    y < 1 ↔ y ≤ WithZero.exp (-1) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · conv_lhs => rw [← WithZero.exp_log hy]
    conv_rhs => rw [← WithZero.exp_log hy]
    rw [← WithZero.exp_zero (M := ℤ), WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega

theorem mem_maximalIdeal_pow_iff_ordAt {k : Type*} [Field k] (C : Curve k) (Q : C.Place)
    (a : ↥(Q.valuationSubring)) (ha : (a : C.functionField) ≠ 0) (n : ℕ) :
    a ∈ IsLocalRing.maximalIdeal ↥(Q.valuationSubring) ^ n ↔
      (n : ℤ) ≤ C.ordAt (a : C.functionField) Q := by
  classical
  -- The local ring of `C` at `Q` is a discrete valuation ring.  Take an irreducible element
  -- of it and view it in the function field; its image `π` is a uniformizer at `Q`.
  have hDVR : IsDiscreteValuationRing (C.left.presheaf.stalk Q.point) :=
    Work.CurveBasics.Place.isDiscreteValuationRing Q
  obtain ⟨π', hπ'⟩ := IsDiscreteValuationRing.exists_irreducible (C.left.presheaf.stalk Q.point)
  let u : C.functionField := algebraMap (C.left.presheaf.stalk Q.point) C.functionField π'
  have hvu : Q.valuation u = WithZero.exp (-1) := by
    change (IsDedekindDomain.HeightOneSpectrum.valuation (C.functionField)
      (IsDiscreteValuationRing.maximalIdeal (C.left.presheaf.stalk Q.point))) u = WithZero.exp (-1)
    have h2 : Ring.ordFrac (C.left.presheaf.stalk Q.point) u = WithZero.exp (1 : ℤ) :=
      Ring.ordFrac_irreducible hπ'
    rw [Ring.ordFrac_eq_valuation_inv] at h2
    simpa using congrArg Inv.inv h2
  have hu : u ∈ Q.valuationSubring := by
    change u ∈ Q.valuation.valuationSubring
    rw [Valuation.mem_valuationSubring_iff, hvu]
    exact WithZero.exp_le_one_iff.mpr (by norm_num)
  let π : ↥(Q.valuationSubring) := ⟨u, hu⟩
  have hvuπ : Q.valuation (π : C.functionField) = WithZero.exp (-1) := hvu
  have hcoe : ∀ z : ↥(Q.valuationSubring),
      algebraMap ↥(Q.valuationSubring) C.functionField z = (z : C.functionField) := fun _ => rfl
  -- `π` generates the maximal ideal of the valuation subring
  have hvint : Q.valuation.Integers ↥(Q.valuationSubring) :=
    Valuation.valuationSubring.integers Q.valuation
  have hpi_set : (Ideal.span {(π : ↥(Q.valuationSubring))} : Set ↥(Q.valuationSubring))
      = (IsLocalRing.maximalIdeal ↥(Q.valuationSubring) : Set ↥(Q.valuationSubring)) := by
    rw [Valuation.Integers.coe_span_singleton_eq_setOfPred_le_v_algebraMap (v := Q.valuation)
      hvint (π : ↥(Q.valuationSubring))]
    ext y
    simp only [Set.mem_ofPred_eq, hcoe]
    change Q.valuation (y : C.functionField) ≤ Q.valuation (π : C.functionField) ↔
      y ∈ IsLocalRing.maximalIdeal ↥(Q.valuation.valuationSubring)
    have hmem : y ∈ IsLocalRing.maximalIdeal ↥(Q.valuation.valuationSubring) ↔
        Q.valuation (y : C.functionField) < 1 :=
      Valuation.mem_maximalIdeal_iff (C.functionField) Q.valuation
    rw [hmem, hvuπ]
    exact lt_one_iff_le_exp_neg_one_ord.symm
  have hpi_span : (Ideal.span {(π : ↥(Q.valuationSubring))} : Ideal ↥(Q.valuationSubring))
      = IsLocalRing.maximalIdeal ↥(Q.valuationSubring) :=
    Ideal.ext fun y => (Set.ext_iff.mp hpi_set) y
  -- the value of `π ^ n`
  have hvpim : Q.valuation ((π ^ n : ↥(Q.valuationSubring)) : C.functionField)
      = WithZero.exp (-(n : ℤ)) := by
    rw [show ((π ^ n : ↥(Q.valuationSubring)) : C.functionField)
          = (π : C.functionField) ^ n from by push_cast; ring]
    rw [Valuation.map_pow, hvuπ, ← WithZero.exp_nsmul]
    congr 1
    simp
  -- the set of elements of `𝔪 ^ n`
  have hR : ((IsLocalRing.maximalIdeal ↥(Q.valuationSubring) ^ n : Ideal ↥(Q.valuationSubring))
      : Set ↥(Q.valuationSubring))
      = {y : ↥(Q.valuationSubring) |
          Q.valuation (y : C.functionField) ≤ WithZero.exp (-(n : ℤ))} := by
    rw [show (IsLocalRing.maximalIdeal ↥(Q.valuationSubring)) ^ n
          = Ideal.span {(π ^ n : ↥(Q.valuationSubring))} from by
        rw [← hpi_span, Ideal.span_singleton_pow]]
    rw [Valuation.Integers.coe_span_singleton_eq_setOfPred_le_v_algebraMap (v := Q.valuation)
      hvint (π ^ n : ↥(Q.valuationSubring))]
    ext y
    simp only [Set.mem_ofPred_eq, hcoe]
    rw [hvpim]
  have key : a ∈ IsLocalRing.maximalIdeal ↥(Q.valuationSubring) ^ n ↔
      Q.valuation (a : C.functionField) ≤ WithZero.exp (-(n : ℤ)) :=
    Set.ext_iff.mp hR a
  rw [key]
  -- the value of `a` is `exp (-ord_Q a)`
  have hva : Q.valuation (a : C.functionField)
      = WithZero.exp (-(C.ordAt (a : C.functionField) Q)) := by
    have hne : Q.valuation (a : C.functionField) ≠ 0 :=
      (Valuation.ne_zero_iff Q.valuation).mpr ha
    have hord : (Q.valuation (a : C.functionField)).log = -(C.ordAt (a : C.functionField) Q) := by
      have h1 := Curve.Place.ord_eq_neg_log_valuation C Q (a : C.functionField)
      change C.ordAt (a : C.functionField) Q = -(Q.valuation (a : C.functionField)).log at h1
      linarith
    rw [← WithZero.exp_log hne, hord]
  rw [hva, WithZero.exp_le_exp]
  omega

end Work.CurveBasics.Order
