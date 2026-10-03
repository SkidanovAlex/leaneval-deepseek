import Mathlib
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.Gates
import Submission.Work.Pert.RBlock
import Submission.Work.Pert.Basic

/-!
# `Work.Pert.pert2v2.RBlockDefs` — the objects of the two-piece R-block

The `pert2_v2` assembly builds the lifted return map `R̃_f` as the `T`-saturation (`Work.Pert.tSat_glue`)
of two pieces:

* **low piece** (heights `≤ Hband`, where the waist `Qm Ξ ∩ Qp Ξ` of the gate is empty — no
  direct conjugation formula exists): the crux's formula
  `Work.Pert.Rlow f Qp' τ Φp φ m k d` at `k = 0` and `d` the (A.4.2) constant;
* **high piece**: `Work.Pert.retOf`/`retP` at the datum-level gate, where the waist is available.

This file only *names* the objects so that the lemmas about them can be stated and delegated
without dragging the whole assembly along.  See `NOTES_pert2v2_session20.md` for the mathematics,
in particular §3: with the gate-walk hypothesis (GW) the low piece satisfies
`Rlow w = Φ (Tt α ς) + E` (`w = Φ ς + E`), i.e. it preserves the coordinate level and moves the
gate point by the deck translation — which is exactly what makes `φ_f (R̃_f x) = φ_f x` hold.
-/

namespace Work.Pert.pert2v2

open MandelDim Complex Set

noncomputable section

/-- The clause `crux_limit_v3` produces for every point of its compact `K`: the `f`-walk of the
coordinate value stays in `Df`, the `m`-th iterate lands in the `τ`-image of the gate `Qp'`, and one
further return step stays in `Qp'`. -/
def LowClause (f : ℂ → ℂ) (Df : Set ℂ) (F τ φ : ℂ → ℂ) (Qp' : Set ℂ) (m : ℕ) (w : ℂ) : Prop :=
  (∀ j : ℕ, j ≤ m → f^[j] (φ w) ∈ Df) ∧ f^[m] (φ w) ∈ τ '' Qp' ∧
    F (Work.Pert.invOn τ Qp' (f^[m] (φ w))) ∈ Qp'

/-- The gate point of the `m`-th iterate of the coordinate value: `ζ = invOn τ Qp' (f^m (φ w))`. -/
def lowZeta (f : ℂ → ℂ) (τ φ : ℂ → ℂ) (Qp' : Set ℂ) (m : ℕ) (w : ℂ) : ℂ :=
  Work.Pert.invOn τ Qp' (f^[m] (φ w))

/-- The low piece of the lifted return map: the crux formula with `k = 0` and the (A.4.2)
constant `d` (`Φ (Tt α z) = Φp z + d` on `Qp Ξ'`). -/
def RlowPiece (f : ℂ → ℂ) (Qp' : Set ℂ) (τ Φp φ : ℂ → ℂ) (m : ℕ) (d : ℂ) : ℂ → ℂ :=
  Work.Pert.Rlow f Qp' τ Φp φ m 0 d

/-- **The gate walk (GW)**: the gate point `ς ∈ Qm Ξ α` of a low point has its whole `F`-walk (up to
the level `E + m`) inside the *other* gate `Qp Ξ α`.  This is a domain restriction: it is exactly
what makes `Tt α ς` (and hence the return coordinate) well defined at every legal level.  It is
satisfiable on the whole band (translate a band point by an integer so that its gate point has
just crossed into `Qp Ξ α`; the Re-width of `Qp Ξ α` at height `t` is `≈ Re (1/α) ≫ E + m`). -/
def GateWalk (F : ℂ → ℂ) (Ξ : ℝ) (α : ℂ) (ς : ℂ) (E m : ℕ) : Prop :=
  ∀ i : ℕ, i ≤ E + m → F^[i] ς ∈ Work.Pert.Qp Ξ α

end

end Work.Pert.pert2v2
