/-
# The class map `ℤ[i] → (ℤ[i]/Q)^*` of *FI* §16

The character expansion (16.11)/(17.10) detects the congruence `z₁ ≡ ω z₂ (mod Q)` (`ω` a *rational*
class) by the characters of the Gaussian unit group `G = (ℤ[i]/Q)^*`.  This file provides the two
objects the expansion is phrased with:

* `gaussUnitOf Q z h` — the class of a Gaussian integer `z` with `(gnorm z, Q) = 1` in the
  coordinate model `G = {p : (ZMod Q)² // IsUnit (gaussNorm p)}` of `GaussUnits`;
* `ratWeight Q e p` — the weight `(ω|e)` of (17.9)/(16.13) on the *rational* classes `(r,0)` of
  `G`, extended by `0`.

They are definitions only (plus the immediate algebraic laws of `gaussUnitOf`).
-/
import Mathlib
import Submission.Work.FIArea7.GaussUnits
import Submission.Work.FIArea7.card_charMod4d_eq_card_units
import Submission.Work.FIArea7.FIsymbols

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The reduction `(z.re, z.im)` of a Gaussian integer modulo `Q`, as an element of the coordinate
model of `ℤ[i]/Q`. -/
def gaussCoord (Q : ℕ) (z : GaussianInt) : ZMod Q × ZMod Q := ((z.re : ZMod Q), (z.im : ZMod Q))

/-- The norm of the reduction is the reduction of the norm. -/
lemma gaussNorm_gaussCoord (Q : ℕ) (z : GaussianInt) :
    gaussNorm (gaussCoord Q z) = ((Work.FIPlan.gnorm z : ℕ) : ZMod Q) := by
  simp only [gaussCoord, gaussNorm]
  exact (gnorm_cast Q z).symm

/-- `IsUnit` of the reduction is coprimality of the norm. -/
lemma isUnit_gaussNorm_gaussCoord_iff (Q : ℕ) (z : GaussianInt) :
    IsUnit (gaussNorm (gaussCoord Q z)) ↔ Nat.Coprime (Work.FIPlan.gnorm z) Q := by
  rw [gaussNorm_gaussCoord, ZMod.isUnit_iff_coprime]

/-- **The class map** `ℤ[i] → G = (ℤ[i]/Q)^*` of §16: the reduction `(z.re, z.im)`, for `z` with
`(gnorm z, Q) = 1`. -/
def gaussUnitOf (Q : ℕ) (z : GaussianInt) (h : Nat.Coprime (Work.FIPlan.gnorm z) Q) :
    {p : ZMod Q × ZMod Q // IsUnit (gaussNorm p)} :=
  ⟨gaussCoord Q z, (isUnit_gaussNorm_gaussCoord_iff Q z).mpr h⟩

@[simp] lemma gaussUnitOf_val (Q : ℕ) (z : GaussianInt)
    (h : Nat.Coprime (Work.FIPlan.gnorm z) Q) :
    (gaussUnitOf Q z h).1 = gaussCoord Q z := rfl

/-- The class map is a monoid hom on the units: the product in `G` is `gaussMul`. -/
lemma gaussUnitOf_mul (Q : ℕ) (z w : GaussianInt)
    (hz : Nat.Coprime (Work.FIPlan.gnorm z) Q) (hw : Nat.Coprime (Work.FIPlan.gnorm w) Q) :
    gaussUnitOf Q (z * w) (by rw [gnorm_mul]; exact hz.mul_left hw)
      = gaussUnitOf Q z hz * gaussUnitOf Q w hw := by
  refine Subtype.ext ?_
  show gaussCoord Q (z * w) = gaussMul (gaussCoord Q z) (gaussCoord Q w)
  simp only [gaussCoord, gaussMul, re_mul, im_mul]
  ext <;> push_cast <;> ring

/-- The class map sends `1` to the identity of `G`. -/
lemma gaussUnitOf_one (Q : ℕ) :
    gaussUnitOf Q 1 (by simp [Work.FIPlan.gnorm]) = 1 := by
  refine Subtype.ext ?_
  show gaussCoord Q 1 = (1, 0)
  ext <;> simp [gaussCoord]

/-- Equality of classes is equality of the reductions. -/
lemma gaussUnitOf_eq_iff (Q : ℕ) (z w : GaussianInt)
    (hz : Nat.Coprime (Work.FIPlan.gnorm z) Q) (hw : Nat.Coprime (Work.FIPlan.gnorm w) Q) :
    gaussUnitOf Q z hz = gaussUnitOf Q w hw ↔ gaussCoord Q z = gaussCoord Q w :=
  Subtype.ext_iff

/-- For a *rational* class `ω : ZMod Q`, the class map of the natural representative
`⟨ω.val, 0⟩` is `(ω, 0)` — the rational class of `G`. -/
lemma gaussUnitOf_rat (Q : ℕ) (ω : ZMod Q) [NeZero Q]
    (h : Nat.Coprime (Work.FIPlan.gnorm (⟨((ω.val : ℤ)), 0⟩ : GaussianInt)) Q) :
    gaussUnitOf Q (⟨((ω.val : ℤ)), 0⟩ : GaussianInt) h
      = ⟨(ω, 0), by
          have := h; rw [← isUnit_gaussNorm_gaussCoord_iff Q (⟨((ω.val : ℤ)), 0⟩ : GaussianInt)] at this
          simpa [gaussCoord, gaussNorm] using this⟩ := by
  refine Subtype.ext ?_
  show gaussCoord Q (⟨((ω.val : ℤ)), 0⟩ : GaussianInt) = (ω, 0)
  ext <;> simp [gaussCoord, ZMod.natCast_val, ZMod.cast_id]

/-- **The weight `(ω|e)` of (17.9)/(16.13) on the rational classes of `G`**, extended by `0` off
the rational classes. -/
def ratWeight (Q e : ℕ) (p : {p : ZMod Q × ZMod Q // IsUnit (gaussNorm p)}) : ℂ :=
  if p.1.2 = 0 then (jacobiSym (p.1.1.val : ℤ) e : ℂ) else 0

lemma ratWeight_rat (Q e : ℕ) (ω : ZMod Q) (h : IsUnit (gaussNorm (ω, 0))) :
    ratWeight Q e ⟨(ω, 0), h⟩ = (jacobiSym (ω.val : ℤ) e : ℂ) := by
  simp [ratWeight]

end

end Work.FIArea7
