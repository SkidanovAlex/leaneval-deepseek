/-
  WilE9 / Sharp / ExFst — the ambient point `Fin.append x y` written at the type `Fin (Npb n m)`.

  `eaEval` evaluates an `EAPoly (Npb n m) r` at a point of `Fin (Npb n m) → ℝ`.  The natural way
  of producing such a point from a base point `x : Fin n → ℝ` and a fibre point
  `y : Fin (qpb n m) → ℝ` is `Fin.append x y`, whose *own* type is `Fin (n + qpb n m) → ℝ`.  The
  two types are equal by definition (`Npb n m = n + qpb n m`), but not *syntactically*, and Lean's
  rewriting tactics match terms only up to reducible unfolding: the `Sum.elim` inside `eaEval` gets
  elaborated with `Fin (Npb n m)` while its argument `Fin.append x y` is typed at
  `Fin (n + qpb n m)`, and simp lemmas such as `Sum.elim_inl` then refuse to fire.

  `appendPt x y` is `Fin.append x y` *typed at* `Fin (Npb n m) → ℝ`; using it makes every term in
  sight syntactically homogeneous, so `simp`/`rw` work.  The coordinate lemmas
  `appendPt_pbX/pbS/pbY/pbW/pbT/pbU` read the named pulled-back coordinates of `appendPt x y` off
  as `x i` (for `pbX`) and `y (fS/fY/fW/fT/fU)`.  They are the only bridge needed to compare
  `eaEval (pbChain c) P (appendPt x y)` with the fibre coordinates of `y`.
-/
import Mathlib
import Submission.Work.WilE9.Sharp.ExDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Work.WilE9.Sharp.ExFst
open WilkiesDesign WilkiesDesign.E
open Work.WilE9.Sharp

/-- The ambient point `(x, y)` of the pulled-back ambient, typed as `Fin (Npb n m) → ℝ`.

It is `Fin.append x y`, whose type `Fin (n + qpb n m) → ℝ` is *definitionally* the right one but
not syntactically equal to it; wrapping it makes all rewrites see a syntactically matching type. -/
def appendPt {n m : ℕ} (x : Fin n → ℝ) (y : Fin (qpb n m) → ℝ) : Fin (Npb n m) → ℝ :=
  Fin.append x y

@[simp] theorem appendPt_pbX {n m : ℕ} (x : Fin n → ℝ) (y : Fin (qpb n m) → ℝ) (i : Fin n) :
    appendPt x y (pbX n m i) = x i := by
  rw [appendPt]
  rw [show pbX n m i = Fin.castAdd (qpb n m) i from Fin.ext rfl, Fin.append_left]

@[simp] theorem appendPt_pbS {n m : ℕ} (x : Fin n → ℝ) (y : Fin (qpb n m) → ℝ) :
    appendPt x y (pbS n m) = y (fS n m) := by
  rw [appendPt, ← natAdd_fS, Fin.append_right]

@[simp] theorem appendPt_pbY {n m : ℕ} (x : Fin n → ℝ) (y : Fin (qpb n m) → ℝ) (i : Fin n) :
    appendPt x y (pbY n m i) = y (fY n m i) := by
  rw [appendPt, ← natAdd_fY, Fin.append_right]

@[simp] theorem appendPt_pbW {n m : ℕ} (x : Fin n → ℝ) (y : Fin (qpb n m) → ℝ) (i : Fin n) :
    appendPt x y (pbW n m i) = y (fW n m i) := by
  rw [appendPt, ← natAdd_fW, Fin.append_right]

@[simp] theorem appendPt_pbT {n m : ℕ} (x : Fin n → ℝ) (y : Fin (qpb n m) → ℝ) :
    appendPt x y (pbT n m) = y (fT n m) := by
  rw [appendPt, ← natAdd_fT, Fin.append_right]

@[simp] theorem appendPt_pbU {n m : ℕ} (x : Fin n → ℝ) (y : Fin (qpb n m) → ℝ) :
    appendPt x y (pbU n m) = y (fU n m) := by
  rw [appendPt, ← natAdd_fU, Fin.append_right]

end Work.WilE9.Sharp.ExFst
