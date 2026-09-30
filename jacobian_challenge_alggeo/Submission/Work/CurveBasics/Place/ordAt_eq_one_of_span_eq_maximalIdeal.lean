import Mathlib
import Submission.Work.CurveBasics.Order.mem_maximalIdeal_pow_iff_ordAt
import Submission.Work.CurveBasics.Place.mem_valuationSubring_iff
import Submission.Work.CurveBasics.Place.Valuation
import Submission.Work.CurveBasics.Place.ord_uniformizer

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveBasics.Place

open Work.CurveBasics

/-- If a rational function `h` regular at `Q` generates the maximal ideal of the valuation
subring of the function field at `Q`, then it vanishes to order exactly one at `Q`: it is a
uniformizer.

Mathematically: the maximal ideal of `↥Q.valuationSubring` is the ideal of functions of
positive order of vanishing at `Q`, and `ordAt · Q` is a surjective homomorphism onto `ℤ`; a
generator of the maximal ideal therefore has the least positive order of vanishing, namely `1`.

Formally we avoid all of that: `Work.CurveBasics.Order.mem_maximalIdeal_pow_iff_ordAt` gives
`a ∈ 𝔪 ^ n ↔ n ≤ ordAt a Q` for `a ≠ 0`.  Thus `h ∈ 𝔪 = 𝔪 ^ 1` gives `1 ≤ ordAt h Q`, while
`h ∉ 𝔪 ^ 2` (otherwise `𝔪 = span {h} ≤ 𝔪 ^ 2`, so the explicit uniformizer `Q.uniformizer`,
which is in `𝔪` but not in `𝔪 ^ 2`, would lie in `𝔪 ^ 2`) gives `¬ 2 ≤ ordAt h Q`. -/
theorem ordAt_eq_one_of_span_eq_maximalIdeal {k : Type*} [Field k] {C : Work.CurveBasics.Curve k}
    (Q : C.Place) (h : C.functionField) (hh : h ∈ Q.valuationSubring)
    (hspan : Ideal.span ({(⟨h, hh⟩ : ↥Q.valuationSubring)} : Set ↥Q.valuationSubring)
      = IsLocalRing.maximalIdeal ↥Q.valuationSubring) :
    C.ordAt h Q = 1 := by
  classical
  -- An explicit uniformizer of the local ring at `Q`, viewed in the function field.
  have hord_uni : C.ordAt Q.uniformizer Q = 1 := by rw [Curve.ordAt, ord_uniformizer]
  have hne_uni : Q.uniformizer ≠ 0 := by
    intro h0
    rw [h0] at hord_uni
    simp [Curve.ordAt, AlgebraicGeometry.Scheme.ord_zero] at hord_uni
  have hmem_uni : Q.uniformizer ∈ Q.valuationSubring := by
    rw [mem_valuationSubring_iff]
    rw [show AlgebraicGeometry.Scheme.ord Q.uniformizer Q.point = 1 from hord_uni]
    norm_num
  let π : ↥Q.valuationSubring := ⟨Q.uniformizer, hmem_uni⟩
  have hπne : (π : C.functionField) ≠ 0 := hne_uni
  have hπord : C.ordAt (π : C.functionField) Q = 1 := hord_uni
  -- `π` lies in the maximal ideal but not in its square.
  have hπmem : π ∈ IsLocalRing.maximalIdeal ↥Q.valuationSubring := by
    have h := (Work.CurveBasics.Order.mem_maximalIdeal_pow_iff_ordAt C Q π hπne 1).mpr
      (by rw [hπord]; norm_num)
    simpa only [pow_one] using h
  have hπnot : π ∉ IsLocalRing.maximalIdeal ↥Q.valuationSubring ^ 2 := by
    intro hmem
    have h := (Work.CurveBasics.Order.mem_maximalIdeal_pow_iff_ordAt C Q π hπne 2).mp hmem
    rw [hπord] at h
    omega
  -- `h` is nonzero, since otherwise the maximal ideal would be `⊥`.
  have hne : h ≠ 0 := by
    intro h0
    have ha0 : (⟨h, hh⟩ : ↥Q.valuationSubring) = 0 := by
      apply Subtype.ext
      simpa using h0
    have hbot : IsLocalRing.maximalIdeal ↥Q.valuationSubring = ⊥ := by
      rw [← hspan, ha0]
      exact Ideal.span_singleton_eq_bot.mpr rfl
    have hpi : π ∈ (⊥ : Ideal ↥Q.valuationSubring) := by rw [← hbot]; exact hπmem
    rw [Submodule.mem_bot] at hpi
    exact hπne (by simpa using congrArg Subtype.val hpi)
  -- `h` lies in the maximal ideal, so its order of vanishing at `Q` is at least `1`.
  have ha_mem : (⟨h, hh⟩ : ↥Q.valuationSubring) ∈
      IsLocalRing.maximalIdeal ↥Q.valuationSubring := by
    rw [← hspan]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hle1 : (1 : ℤ) ≤ C.ordAt h Q :=
    (Work.CurveBasics.Order.mem_maximalIdeal_pow_iff_ordAt C Q ⟨h, hh⟩ hne 1).mp
      (by simpa only [pow_one] using ha_mem)
  -- and it is not in the square of the maximal ideal, so the order is at most `1`.
  have hlt2 : ¬ (2 : ℤ) ≤ C.ordAt h Q := by
    intro hle
    have hmem2 : (⟨h, hh⟩ : ↥Q.valuationSubring) ∈
        IsLocalRing.maximalIdeal ↥Q.valuationSubring ^ 2 :=
      (Work.CurveBasics.Order.mem_maximalIdeal_pow_iff_ordAt C Q ⟨h, hh⟩ hne 2).mpr hle
    have hle2 : IsLocalRing.maximalIdeal ↥Q.valuationSubring ≤
        IsLocalRing.maximalIdeal ↥Q.valuationSubring ^ 2 := by
      conv_lhs => rw [← hspan]
      exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem2)
    exact hπnot (hle2 hπmem)
  omega

end Work.CurveBasics.Place
