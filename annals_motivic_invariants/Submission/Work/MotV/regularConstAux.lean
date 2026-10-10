/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotV

# Auxiliary lemmas about the order at a rational place

The order of vanishing `ordOfPlace E S hS f` is defined through the additive valuation
`IsDiscreteValuationRing.addVal` of the discrete valuation ring `S ⊆ N(E)`.  The two lemmas here
translate between the additive valuation (resp. the maximal ideal of `S`) and the value of
`ordOfPlace`:

* `ordOfPlace_eq_zero_iff`: for `x ∈ S`, `x ≠ 0`, the order of `x` is zero exactly when `x` is a
  unit of `S`;
* `one_le_ordOfPlace_iff`: equivalently, for `x ∈ S`, `x ≠ 0`, the order of `x` is at least one
  exactly when `x` lies in the maximal ideal of `S`.

They are used in `Submission/Work/MotV/regularConst.lean` to extract the value at the point at
infinity of a function which is regular there.
-/

import Mathlib
import Submission.Work.MotV.H1Data
import Submission.Work.MotV.Machinery
import Submission.Work.MotC2.Classification

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

set_option linter.style.haveILetI false

namespace Work.MotV

noncomputable section

variable {N : Type*} [Field N]

/-- For `x` in a rational place `S`, the order of `x` vanishes exactly when `x` is a unit of `S`.
Indeed, `ordOfPlace` is the additive valuation of the discrete valuation ring `S`, which vanishes
exactly on the units. -/
lemma ordOfPlace_eq_zero_iff {E : WeierstrassCurve N} {S : Subalgebra N (MotC2.Func E)}
    (hS : MotC2.IsRatPlace E S) {x : MotC2.Func E} (hx : x ∈ S) (hx0 : x ≠ 0) :
    ordOfPlace E S hS x = 0 ↔ IsUnit (⟨x, hx⟩ : S) := by
  letI : IsDiscreteValuationRing ↥S := hS.1.choose
  have hunfold : ordOfPlace E S hS x =
      ((WithTop.untopD 0 ((IsDiscreteValuationRing.addVal ↥S) ⟨x, hx⟩) : ℕ) : ℤ) := by
    unfold ordOfPlace
    rw [dite_eq_left hx]
  have htop : (IsDiscreteValuationRing.addVal ↥S) ⟨x, hx⟩ ≠ ⊤ := by
    intro h
    rw [IsDiscreteValuationRing.addVal_eq_top_iff] at h
    exact hx0 (Subtype.ext_iff.mp h)
  have hzero : (WithTop.untopD 0 ((IsDiscreteValuationRing.addVal ↥S) ⟨x, hx⟩) : ℕ) = 0 ↔
      (IsDiscreteValuationRing.addVal ↥S) ⟨x, hx⟩ = 0 := by
    rw [show (WithTop.untopD 0 ((IsDiscreteValuationRing.addVal ↥S) ⟨x, hx⟩) : ℕ) =
        ENat.toNat ((IsDiscreteValuationRing.addVal ↥S) ⟨x, hx⟩) from rfl,
      ENat.toNat_eq_zero]
    constructor
    · rintro (h | h)
      · exact h
      · exact absurd h htop
    · exact Or.inl
  rw [hunfold, Int.natCast_eq_zero, hzero, IsDiscreteValuationRing.addVal_eq_zero_iff]

/-- For `x` in a rational place `S`, the order of `x` is at least one exactly when `x` is a
non-unit of `S`, i.e. when `x` lies in the maximal ideal of `S`. -/
lemma one_le_ordOfPlace_iff {E : WeierstrassCurve N} {S : Subalgebra N (MotC2.Func E)}
    (hS : MotC2.IsRatPlace E S) {x : MotC2.Func E} (hx : x ∈ S) (hx0 : x ≠ 0) :
    1 ≤ ordOfPlace E S hS x ↔ ¬ IsUnit (⟨x, hx⟩ : S) := by
  have h0 := ordOfPlace_eq_zero_iff hS hx hx0
  have hnonneg : (0 : ℤ) ≤ ordOfPlace E S hS x := by
    letI : IsDiscreteValuationRing ↥S := hS.1.choose
    have hunfold : ordOfPlace E S hS x =
        ((WithTop.untopD 0 ((IsDiscreteValuationRing.addVal ↥S) ⟨x, hx⟩) : ℕ) : ℤ) := by
      unfold ordOfPlace
      rw [dite_eq_left hx]
    rw [hunfold]
    exact Int.natCast_nonneg _
  constructor
  · intro h hunit
    have : ordOfPlace E S hS x = 0 := h0.mpr hunit
    omega
  · intro h
    by_contra hcon
    push Not at hcon
    have : ordOfPlace E S hS x = 0 := by omega
    exact h (h0.mp this)

end

end Work.MotV
