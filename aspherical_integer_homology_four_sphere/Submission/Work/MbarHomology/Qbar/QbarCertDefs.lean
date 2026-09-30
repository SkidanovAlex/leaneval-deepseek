/-
# The concrete sparse certificates for `Carriers QbarPD`

This file turns the tables of `Submission.Work.MbarHomology.Qbar.QbarCertData` (the per-face rows
`empRow` of the code `empCode` and the `888` emptiness patterns) into the certificate data used by
the criterion `Carriers_of_sparse`.

For every pair `(f, c)` of `QbarPD` (`f` a face, `c` a constraint) `empCode f c` is either

* `888`: the region `Fset f ∩ {c tight}` is nonempty and is the face
  `empAddIdx f c = qOfCode (qCode (qTight f ∪ {c}))`, whose tight set is `qTight f ∪ {c}`; or
* `p < 888`: the region is empty, certified by the Farkas pattern `p`: the two constraints
  `empC1 f c`, `empC2 f c` lie in `qTight f ∪ {c}`, and `empMuA f c`, `empMuB f c` (the
  coefficients of the two) together with the nonnegative combination `empLamIdx f c`,
  `empLamVal f c` over at most three constraints satisfy the Farkas identities.

All of this is verified exactly (in integers and rationals) by the generator `_w2_gen3.py`.
-/
import Mathlib
import Submission.Work.MbarHomology.Qbar.Basic
import Submission.Work.MbarHomology.Qbar.QbarCertData

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxRecDepth 100000
set_option autoImplicit false

namespace Work.MbarHomology

open Work.ConvexCells

/-- The emptiness pattern attached to a pair (a natural number, meaningful only when `< 888`). -/
def empPat (f : Fin 865) (i : Fin 48) : ℕ := empCode f i

/-- `empSelB f i` is `true` exactly in the emptiness case. -/
def empSelB (f : Fin 865) (i : Fin 48) : Bool := decide (empCode f i < 888)

/-- The face realising `qTight f ∪ {i}` in the nonempty case. -/
def empAddIdx (f : Fin 865) (i : Fin 48) : Fin 865 := qOfCode (qCode (qTight f ∪ {i}))

/-- The first constraint of the pattern of a pair. -/
def empC1 (f : Fin 865) (i : Fin 48) : Fin 48 := certC1 (empPat f i)

/-- The second constraint of the pattern of a pair. -/
def empC2 (f : Fin 865) (i : Fin 48) : Fin 48 := certC2 (empPat f i)

/-- The coefficient of `empC1 f i` in the Farkas combination. -/
def empMuA (f : Fin 865) (i : Fin 48) : ℤ := certMu1 (empPat f i)

/-- The coefficient of `empC2 f i` in the Farkas combination. -/
def empMuB (f : Fin 865) (i : Fin 48) : ℤ := certMu2 (empPat f i)

/-- The constraint of the `t`-th term of the nonnegative side of the Farkas combination, as a
function of the pattern index. -/
def lamIdxOf (p : ℕ) (t : Fin 3) : Fin 48 :=
  if t = 0 then certL1 p else if t = 1 then certL2 p else certL3 p

/-- The coefficient of the `t`-th term of the nonnegative side of the Farkas combination, as a
function of the pattern index. -/
def lamValOf (p : ℕ) (t : Fin 3) : ℤ :=
  if t = 0 then certV1 p else if t = 1 then certV2 p else certV3 p

/-- The constraint of the `t`-th term of the nonnegative side of the Farkas combination. -/
def empLamIdx (f : Fin 865) (i : Fin 48) (t : Fin 3) : Fin 48 := lamIdxOf (empPat f i) t

/-- The coefficient of the `t`-th term of the nonnegative side of the Farkas combination. -/
def empLamVal (f : Fin 865) (i : Fin 48) (t : Fin 3) : ℤ := lamValOf (empPat f i) t

/-- The Farkas coefficient of the constraint `k` for the pair `(f, i)`. -/
def empMu (f : Fin 865) (i : Fin 48) (k : Fin 48) : ℤ :=
  if k = empC1 f i then empMuA f i else if k = empC2 f i then empMuB f i else 0

/-- The Farkas coefficient of the constraint `i` itself. -/
def empMuI (f : Fin 865) (i : Fin 48) : ℤ := empMu f i i

end Work.MbarHomology
