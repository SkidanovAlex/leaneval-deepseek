/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# Reversing a directed step

`Work.ORDunwoody.even_visits_defs` defines the *directed steps* of a boundary walk: the traversal
of a cell in the forward direction (`fwd`), the traversal of a cell in the backward direction
(`bwd`), or the traversal of a collapsed generator edge (`skip`).

This file records the **reversal** `op` of a directed step, together with the two facts needed to
run the word-level integral `A` backwards: `op` is an involution, and the contribution `stepHit τ`
of a step is invariant under it (the cochain `phi τ` is symmetric, `phi_comm`).
-/
import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.AlphaWord

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody.Dunwoody

open Work.ORDunwoody.Cayley

variable {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
variable {T : GTree G V} {t₀ : V} {P : FinPresentation G}
variable {D : GeoData T t₀ P}

/-- **The reversal of a directed step of a boundary walk**: forward and backward traversals of a
cell are interchanged, and a collapsed generator edge is traversed the other way. -/
def op : DStep D → DStep D
  | DStep.fwd e => DStep.bwd e
  | DStep.bwd e => DStep.fwd e
  | DStep.skip u w => DStep.skip w u

@[simp] theorem op_fwd (e : Cell D) : op (DStep.fwd e) = DStep.bwd e := rfl

@[simp] theorem op_bwd (e : Cell D) : op (DStep.bwd e) = DStep.fwd e := rfl

@[simp] theorem op_skip (u w : BaseV D) : op (DStep.skip u w) = DStep.skip w u := rfl

/-- `op` is an involution. -/
@[simp] theorem op_op (s : DStep D) : op (op s) = s := by
  cases s <;> rfl

/-- **`stepHit τ` is invariant under reversal of a step.**  A forward step contributes the value of
`phi τ` on the half-cell `(inr e.mid, inl e.tgt)`, the reverse step the value on the half-cell
`(inl e.tgt, inr e.mid)`, and the two are equal because `phi τ` is symmetric. -/
@[simp] theorem stepHit_op (τ : Track D) (s : DStep D) : stepHit τ (op s) = stepHit τ s := by
  cases s with
  | fwd e => simp [stepHit, phi_comm]
  | bwd e => simp [stepHit, phi_comm]
  | skip u w => simp [stepHit]

/-- Reversing a list under `op` twice returns the list. -/
theorem map_op_map_op (L : List (DStep D)) : (L.map op).map op = L := by
  induction L with
  | nil => rfl
  | cons s L ih => simp [ih]

end Work.ORDunwoody.Dunwoody
