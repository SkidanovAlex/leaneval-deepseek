/-
# `Work.FIArea7.P231.multEps_vocab` — the vocabulary of the `ε`-inner-bound of *FI* §23

This module fixes the objects that the bound `Work.FIArea7.P231.multEps_inner_bound` (the passage
from the `K`-form of Prop. 21.4 to the `ε`-form of §23) is stated and proved with:

* `epsUnit w = w/|w|`, the unit-modulus point of a Gaussian integer;
* `epsRoomA`, `epsRoomB`, `epsGood`, the "room" conditions of *FI* (20.18) under which the
  separated expansion (20.19) of the multiplier sign `ε(w,z)` converges;
* the finite sets `epsLive`, `epsGoodP`, `epsBadP` of pairs `(w,z)` (coprime, live, and good/bad);
* the "strip" sets `epsBadZ`, `epsBadZN` of `z` violating a room condition;
* the summands `epsSummandP`, `epsKeySummand` of the `ε`-form.

Everything is `Classical`-decidable, so that statements mentioning these objects (in particular the
delegated lemmas) elaborate without decidability side conditions.
-/
import Mathlib
import Submission.Work.FIArea7.P231Defs

set_option autoImplicit false

namespace Work.FIArea7.P231

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The unit-modulus point `w/|w|` attached to a Gaussian integer (`0` at `w = 0`). -/
def epsUnit (w : GaussianInt) : ℂ := w.toComplex / (‖w.toComplex‖ : ℂ)

/-- The "room" condition (20.18) in `w` alone: `|Re(wz)| ≥ |w||z|/R`. -/
def epsRoomB (R : ℕ) (w z : GaussianInt) : Prop :=
  ‖w.toComplex‖ * ‖z.toComplex‖ ≤ (R : ℝ) * |(((w * z).re : ℤ) : ℝ)|

/-- The "room" condition (20.18) involving `σ`: `|Re(σ wz)| ≥ |σ||wz|/R`. -/
def epsRoomA (R : ℕ) (σ w z : GaussianInt) : Prop :=
  ‖σ.toComplex‖ * ‖(w * z).toComplex‖ ≤ (R : ℝ) * |(((σ * (w * z)).re : ℤ) : ℝ)|

/-- Both room conditions at once. -/
def epsGood (R : ℕ) (σ w z : GaussianInt) : Prop := epsRoomA R σ w z ∧ epsRoomB R w z

/-- The pairs of the double box that are Gauss-coprime with both coefficients non-zero. -/
def epsLive (Rw Rz : ℤ) (A B : GaussianInt → ℂ) : Finset (GaussianInt × GaussianInt) :=
  ((Work.FIPlan.gBox Rw).product (Work.FIPlan.gBox Rz)).filter
    (fun p => Work.FIPlan.GaussCoprime p.1 p.2 ∧ A p.1 ≠ 0 ∧ B p.2 ≠ 0)

/-- The live pairs that also satisfy both room conditions. -/
def epsGoodP (Rw Rz : ℤ) (σ : GaussianInt) (R : ℕ) (A B : GaussianInt → ℂ) :
    Finset (GaussianInt × GaussianInt) :=
  (epsLive Rw Rz A B).filter (fun p => epsGood R σ p.1 p.2)

/-- The live pairs that violate at least one room condition. -/
def epsBadP (Rw Rz : ℤ) (σ : GaussianInt) (R : ℕ) (A B : GaussianInt → ℂ) :
    Finset (GaussianInt × GaussianInt) :=
  (epsLive Rw Rz A B).filter (fun p => ¬ epsGood R σ p.1 p.2)

/-- The `z` of the box `gBox Rz` with `|z|² ≤ N` violating a room condition for the fixed `w`. -/
def epsBadZ (Rz : ℤ) (N : ℝ) (R : ℕ) (w σ : GaussianInt) : Finset GaussianInt :=
  (Work.FIPlan.gBox Rz).filter (fun z => (Work.FIPlan.gnorm z : ℝ) ≤ N ∧ ¬ epsGood R σ w z)

/-- As `epsBadZ`, but over the box `gBox N'` — the form in which the point count
`card_strip_le` (the hypothesis `hcard`) applies. -/
def epsBadZN (N' : ℕ) (N : ℝ) (R : ℕ) (w σ : GaussianInt) : Finset GaussianInt :=
  (Work.FIPlan.gBox ((N' : ℤ))).filter (fun z => (Work.FIPlan.gnorm z : ℝ) ≤ N ∧ ¬ epsGood R σ w z)

/-- The summand `α_w β_z ε(σ,wz)[wz]` of the `ε`-form. -/
def epsSummandP (σ : GaussianInt) (A B : GaussianInt → ℂ) (p : GaussianInt × GaussianInt) : ℂ :=
  A p.1 * B p.2 *
    ((Work.FIArea7.MultEps σ (p.1 * p.2) : ℂ) * Work.FIArea7.JKSym (p.1 * p.2))

/-- The summand of the double sum, with the coprimality restriction built in. -/
def epsKeySummand (σ : GaussianInt) (A B : GaussianInt → ℂ)
    (p : GaussianInt × GaussianInt) : ℂ :=
  if Work.FIPlan.GaussCoprime p.1 p.2 then epsSummandP σ A B p else 0

end

end Work.FIArea7.P231
