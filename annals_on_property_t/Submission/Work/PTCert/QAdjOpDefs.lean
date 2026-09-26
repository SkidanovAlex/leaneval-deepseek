import Mathlib
import Submission.Work.PTCert.LetterCore

/-!
# The edge bookkeeping behind `QAdjOp`

`QAdjOp r kop mu a b` is defined as a double sum over a *list* `QEdges r` of edges
`(i,j)`, `i < j < r`, with weights `0` on the diagonal, `1` on adjacent pairs and `kop`
on opposite pairs.  The target of the certificate comparison is instead the same sum
written as `∑_{x ∈ Psub r r} … + kop * ∑_{x ∈ Qsub r r} …`.  This file collects the
vocabulary needed to bridge the two pictures.
-/

set_option autoImplicit false

namespace Submission.PTCert

open Submission.RouteB

/-- The list of edges `(i,j)` with `i < j < r`, in the order used by `QAdjOp`:
for each `i` in increasing order, then `j` in increasing order. -/
def QEdges (r : ℕ) : List (ℕ × ℕ) :=
  (List.range r).flatMap (fun i => (List.range r).filterMap
    (fun j => if i < j then some (i, j) else none))

/-- The condition, on a pair `(e,f)` of edges of `QAdjOp`'s list, that `e` and `f` share
a vertex. -/
def shares (e f : ℕ × ℕ) : Prop :=
  e.1 = f.1 ∨ e.1 = f.2 ∨ e.2 = f.1 ∨ e.2 = f.2

instance (e f : ℕ × ℕ) : Decidable (shares e f) :=
  inferInstanceAs (Decidable (e.1 = f.1 ∨ e.1 = f.2 ∨ e.2 = f.1 ∨ e.2 = f.2))

theorem shares_iff (e f : ℕ × ℕ) :
    shares e f ↔ e.1 = f.1 ∨ e.1 = f.2 ∨ e.2 = f.1 ∨ e.2 = f.2 := Iff.rfl

/-- `QAdjOp` is the double sum over the list `QEdges r` (with weight `0` on the diagonal,
`1` on adjacent pairs and `kop` on opposite ones), minus the Laplacian part. -/
theorem QAdjOp_eq_QEdges (r : ℕ) (kop mu : ℚ) (a b : ℕ) :
    QAdjOp r kop mu a b =
      ((QEdges r).map (fun e => ((QEdges r).map (fun f =>
          if e = f then 0 else
            (if e.1 = f.1 ∨ e.1 = f.2 ∨ e.2 = f.1 ∨ e.2 = f.2 then 1 else kop) *
              cEdge r e a * cEdge r f b)).sum)).sum
      - mu * ((if a = 0 then cDelta r b else 0) + (if b = 0 then cDelta r a else 0)) / 2 := by
  rfl

end Submission.PTCert
