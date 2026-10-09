/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The norm-form (quaternionic) criterion for the Hilbert symbol

Mathematically, the Hilbert symbol `(a,b)_v` is *defined* by the requirement that
`(a,b)_v = 1` if and only if the ternary quadratic form `x² - a y² - b z²` has a nontrivial
zero over the local field `ℚ_v` (equivalently: the quaternion algebra `(a,b)` splits).

For `ℚ_v = ℝ` this is proved here (`hilbertSymbolReal_isotropic_iff`, in the module
`Submission.Work.HilbertSymbol.hilbertSymbolReal_isotropic_iff`; the `Prop` below records it).
For `ℚ_v = ℚ_p` the explicit formula of `Basic.lean` is used instead, because the formula is what
the local computations and the reciprocity law act on; the equivalence with the norm-form
criterion is the classical local theory of quadratic forms and is *not* formalised here.  The
`Prop`-valued definition `HilbertSymbolCriterionAtPrime` records the content of the missing
equivalence precisely.
-/
import Submission.Work.HilbertSymbol.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped Classical

namespace Work.HilbertSymbol

/-- The norm form `x² - a y² - b z²` of the pair `(a,b)` over a field `K`. -/
def normForm (K : Type*) [Field K] (a b : K) : K → K → K → K :=
  fun x y z => x ^ 2 - a * y ^ 2 - b * z ^ 2

/-- The pair `(a,b)` is *isotropic* over `K` if its norm form has a nontrivial zero. -/
def Isotropic (K : Type*) [Field K] (a b : K) : Prop :=
  ∃ x y z : K, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ normForm K a b x y z = 0

@[simp] theorem isotropic_iff (K : Type*) [Field K] (a b : K) :
    Isotropic K a b ↔
      ∃ x y z : K, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ x ^ 2 - a * y ^ 2 - b * z ^ 2 = 0 :=
  Iff.rfl

/-- **The norm-form / quaternionic criterion at a finite place.**  For every prime `p`, the
Hilbert symbol `(a,b)_p` is `1` if and only if the norm form `x² - a y² - b z²` is isotropic
over `ℚ_p` (equivalently: the quaternion algebra `(a,b)` splits over `ℚ_p`).

This is the classical local description of the Hilbert symbol.  It is recorded here as a
`Prop`; it is *not* proved in this development, where `hilbertSymbolAtPrime` is defined by the
explicit valuation/Legendre-symbol formula of `Basic.lean` (see `NOTES.md`). -/
def HilbertSymbolCriterionAtPrime (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ a b : ℚˣ, hilbertSymbolAtPrime p a b = 1 ↔ Isotropic (Padic p) (a : Padic p) (b : Padic p)

/-- **The norm-form criterion at the archimedean place**, recorded as a `Prop`; it is proved as
`hilbertSymbolReal_isotropic_iff`. -/
def HilbertSymbolCriterionReal : Prop :=
  ∀ a b : ℚˣ, hilbertSymbolReal a b = 1 ↔ Isotropic ℝ (a : ℝ) (b : ℝ)

/-- **The local invariant of a quaternion algebra**: `(a,b)_p = -1` exactly when the norm form is
anisotropic.  (A restatement of the criterion, in the `-1` form.) -/
def HilbertSymbolCriterionAtPrimeNegOne (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ a b : ℚˣ, hilbertSymbolAtPrime p a b = -1 ↔ ¬ Isotropic (Padic p) (a : Padic p) (b : Padic p)

end Work.HilbertSymbol
