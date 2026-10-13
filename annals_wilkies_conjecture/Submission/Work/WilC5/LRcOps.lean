/-
  WilC5 — the semantic operations of the language `LRc = (ring ⊕ rexpL)[[ℝ]]`.

  `LRc` has no relation symbols, so the *order* of a model of `TR` is the definable order
  `leEL x y := ∃ z, z * z = y - x` of the ring reduct (this is the same order that
  `Bridge.lean`/`ReductEmb.lean` use for `LEc`).  This module fixes the semantic notation
  (`addEL`, `mulEL`, `negEL`, `zeroEL`, `oneEL`, `subEL`, `isSquareL`, `leEL`) that the
  ordered-field structure of a model of `TR` is stated with.
-/
import Submission.Work.WilC5.ReductEmb

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

section LRcOps

variable {M : Type} [LRc.Structure M]

/-- The ring symbol of `LRc` corresponding to a ring symbol of `Language.ring`. -/
def ringSymL {n : ℕ} (f : Language.ring.Functions n) : LRc.Functions n := Sum.inl (Sum.inl f)

/-- Addition of an `LRc`-structure. -/
def addEL (x y : M) : M := Structure.funMap (ringSymL Ring.addFunc) ![x, y]

/-- Multiplication of an `LRc`-structure. -/
def mulEL (x y : M) : M := Structure.funMap (ringSymL Ring.mulFunc) ![x, y]

/-- Negation of an `LRc`-structure. -/
def negEL (x : M) : M := Structure.funMap (ringSymL Ring.negFunc) ![x]

/-- The zero of an `LRc`-structure. -/
def zeroEL : M := Structure.funMap (ringSymL Ring.zeroFunc) default

/-- The one of an `LRc`-structure. -/
def oneEL : M := Structure.funMap (ringSymL Ring.oneFunc) default

/-- Subtraction in an `LRc`-structure. -/
def subEL (x y : M) : M := addEL x (negEL y)

/-- The (classically chosen) inverse in an `LRc`-structure: the `y` with `x * y = 1`, or `0` if
there is none.  In a model of `TR` this is the field inverse (it is unique when `x ≠ 0`). -/
def invEL (x : M) : M := if h : ∃ y : M, mulEL x y = oneEL then Classical.choose h else zeroEL

/-- The ring formula `∃z, z*z = y`. -/
def isSquareL (y : M) : Prop := ∃ z : M, mulEL z z = y

/-- The definable order `x ≤ y`, i.e. `∃z, z*z = y - x`. -/
def leEL (x y : M) : Prop := isSquareL (subEL y x)

end LRcOps

end Work.WilC5
