import Mathlib
import Submission.CDT.RatFuncDeriv
import Submission.Commons.FieldTheory.RatFunc.exists_sympSigma
import Submission.Commons.FieldTheory.RatFunc.ordAtT_def
import Submission.Commons.FieldTheory.RatFunc.ordAtT_mul
import Submission.Commons.FieldTheory.RatFunc.ordAtT_div
import Submission.Commons.FieldTheory.RatFunc.ordAtT_algebraMap
import Submission.Commons.FieldTheory.RatFunc.ordAtT_add_ge
import Submission.Commons.FieldTheory.RatFunc.ordAtT_inv
import Submission.Commons.FieldTheory.RatFunc.ordAtT_pow
import Submission.Commons.FieldTheory.RatFunc.ordAtT_neg
import Submission.Commons.FieldTheory.RatFunc.le_ordAtT_finset_sum
import Submission.Work.C17.seventeen_defs

/-!
# Local expansion data at `x = 0` for the `C17` order-three class lemma

This module fixes the *interface* used by `Work.C17.order3_class_injective`
(and by the auxiliary lemmas proved for it): the local expansion data of a
rational function at the point `x = 0`.

* `Reg f`      : `f` has no pole at `0` (`0 ≤ ordAtT 0 f`).
* `Unit0 f`    : `f` is regular at `0` and does not vanish there (`ordAtT 0 f = 0`).
* `LeadAt f e lam`  : `f = x^e·(lam + O(x))` with `lam ≠ 0` at `x = 0`.
* `Lead2At f e lam mu`: `f = x^e·(lam + mu·x + O(x²))` with `lam ≠ 0` at `x = 0`.
* `sigmaQ`     : the deck involution `x ↦ x/(x-1)` of `ℚ(x)`, as a `ℚ`-algebra automorphism.

Everything is phrased with the order function `Commons.FieldTheory.RatFunc.ordAtT 0`
(order of vanishing at `0`, with value `⊤` for the zero function).
-/

namespace Work.C17

open Commons.FieldTheory.RatFunc

noncomputable section

/-- `f` is regular at `x = 0` (it has no pole there). -/
def Reg (f : RatFunc ℚ) : Prop := (0 : WithTop ℤ) ≤ ordAtT (0 : ℚ) f

/-- `f` is a unit of the local ring at `0`: regular and non-vanishing there. -/
def Unit0 (f : RatFunc ℚ) : Prop := ordAtT (0 : ℚ) f = 0

/-- `f = x^e·(lam + O(x))` at `x = 0`, with `lam ≠ 0`. -/
def LeadAt (f : RatFunc ℚ) (e : ℤ) (lam : ℚ) : Prop :=
  lam ≠ 0 ∧ (1 : WithTop ℤ) ≤ ordAtT (0 : ℚ) (f * xQ ^ (-e) - algebraMap ℚ (RatFunc ℚ) lam)

/-- `f = x^e·(lam + mu·x + O(x²))` at `x = 0`, with `lam ≠ 0`. -/
def Lead2At (f : RatFunc ℚ) (e : ℤ) (lam mu : ℚ) : Prop :=
  lam ≠ 0 ∧ (2 : WithTop ℤ) ≤ ordAtT (0 : ℚ)
    (f * xQ ^ (-e) - algebraMap ℚ (RatFunc ℚ) lam - algebraMap ℚ (RatFunc ℚ) mu * xQ)

/-- The deck involution `x ↦ x/(x-1)` of `ℚ(x)`, as a `ℚ`-algebra automorphism. -/
noncomputable def sigmaQ : RatFunc ℚ ≃ₐ[ℚ] RatFunc ℚ := Classical.choose exists_sympSigma

theorem sigmaQ_invol (f : RatFunc ℚ) : sigmaQ (sigmaQ f) = f :=
  (Classical.choose_spec exists_sympSigma).1 f

theorem sigmaQ_X : sigmaQ xQ = xQ / (xQ - 1) := by
  have h := (Classical.choose_spec exists_sympSigma).2
  simpa [sigmaQ, xQ, RatFunc.algebraMap_X] using h

/-! ## The concrete functions whose local data is needed

These are the `(1,dx)`-coordinates of the classes `cls a b k` (`k = 2, 3`) of the
`P`-branch module, together with the auxiliaries `w2 = v2/rhoQ`, `w3 = v3/rhoQ`
used in the second equation of the `order3_class_injective` argument. -/

/-- First coordinate of `cls a b 2`. -/
noncomputable def u2 (a b : ℚ) : RatFunc ℚ := -(rhoQ * (rhoQ * P0Q a b / P2Q a b))

/-- Second coordinate of `cls a b 2`. -/
noncomputable def v2 (a b : ℚ) : RatFunc ℚ :=
  rhoQ * (Submission.CDT.dRat rhoQ - rhoQ * P1Q a b / P2Q a b)

/-- `v2 / rhoQ`. -/
noncomputable def w2 (a b : ℚ) : RatFunc ℚ :=
  Submission.CDT.dRat rhoQ - rhoQ * P1Q a b / P2Q a b

/-- First coordinate of `cls a b 3`. -/
noncomputable def u3 (a b : ℚ) : RatFunc ℚ :=
  rhoQ * (Submission.CDT.dRat (u2 a b) - v2 a b * P0Q a b / P2Q a b)

/-- Second coordinate of `cls a b 3`. -/
noncomputable def v3 (a b : ℚ) : RatFunc ℚ :=
  rhoQ * (u2 a b + Submission.CDT.dRat (v2 a b) - v2 a b * P1Q a b / P2Q a b)

/-- `v3 / rhoQ`. -/
noncomputable def w3 (a b : ℚ) : RatFunc ℚ :=
  u2 a b + Submission.CDT.dRat (v2 a b) - v2 a b * P1Q a b / P2Q a b

/-- `u2 - sigmaQ u2` (the anti-invariant part of `u2`). -/
noncomputable def Z2 (a b : ℚ) : RatFunc ℚ := u2 a b - sigmaQ (u2 a b)

/-- `u3 - sigmaQ u3`. -/
noncomputable def Z3 (a b : ℚ) : RatFunc ℚ := u3 a b - sigmaQ (u3 a b)

/-- `w2 - sigmaQ w2`. -/
noncomputable def Y2 (a b : ℚ) : RatFunc ℚ := w2 a b - sigmaQ (w2 a b)

/-- `w3 - sigmaQ w3`. -/
noncomputable def Y3 (a b : ℚ) : RatFunc ℚ := w3 a b - sigmaQ (w3 a b)

/-- The determinant of the two-by-two system. -/
noncomputable def Dd (a b : ℚ) : RatFunc ℚ :=
  Z2 a b * Y3 a b - Z3 a b * Y2 a b

end

end Work.C17
