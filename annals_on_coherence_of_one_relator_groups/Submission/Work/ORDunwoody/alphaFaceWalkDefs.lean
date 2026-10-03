/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The contribution of a directed step of a boundary walk to `alpha τ`

`Dunwoody/Alpha.lean` defines the counting cochain `phi τ` on the edges of the 1-skeleton of
`Λ''` and its integral `alpha τ` over a walk.  `Work.ORDunwoody.even_visits_defs` defines the
*directed steps* `DStep` of a boundary walk: the traversal of a cell of `Λ'` in the forward
direction (`fwd`) or the backward direction (`bwd`), or the traversal of a collapsed generator
edge (`skip`).

A boundary walk of a face is the concatenation of the vertex lists `DStep.verts` of its steps,
preceded by the initial old vertex (`faceAux_eq_flatMap_verts`, `faceWalk_eq`).  Consequently its
integral `alpha τ` is the sum of the values of `phi τ` on the *non-zero half-cells* of the steps:
the cochain `phi τ` is zero on every half-cell except the ones joining a pattern point `m` of the
track `τ` to the *target* end `m.tgt` of its cell.  Thus

* a forward step `fwd e` (the traversal `e.src → e.mid → e.tgt`) contributes the value on its
  second half `phi τ (inr e.mid) (inl e.tgt)` (its first half is zero);
* a backward step `bwd e` (the traversal `e.tgt → e.mid → e.src`) contributes the value on its
  first half `phi τ (inl e.tgt) (inr e.mid)` (its second half is zero);
* a collapsed step `skip u w` has no pattern point and contributes `0`.

That is the value recorded by `stepHit` below.  By `phi_mid_tgt` and `phi_tgt_mid` this value is
`[m ∈ τ]`, `m` being the pattern point of the step; the evaluation is in
`Work.ORDunwoody.sum_stepHit`, together with the statement that the whole integral `alpha τ` of a
boundary walk is (in `ZMod 2`) the number of the visits of the walk lying in `τ`.

Nothing here uses the simple connectivity of `Λ''`.
-/
import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.Alpha
import Submission.Work.ORDunwoody.even_visits_defs

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody.Dunwoody

open Work.ORDunwoody.Cayley

variable {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
variable {T : GTree G V} {t₀ : V} {P : FinPresentation G}
variable {D : GeoData T t₀ P}

/-- **The contribution of a directed step to `alpha τ`**: the value of the cochain `phi τ` on the
non-zero half-cell of the cell of the step.  A forward step contributes the value on its second
half `(inr e.mid, inl e.tgt)`, a backward step the value on its first half `(inl e.tgt, inr e.mid)`
(the two are equal by `phi_comm`); a collapsed generator edge contributes `0`. -/
noncomputable def stepHit (τ : Track D) : DStep D → ZMod 2
  | DStep.fwd e => phi τ (Sum.inr e.mid) (Sum.inl e.tgt)
  | DStep.bwd e => phi τ (Sum.inl e.tgt) (Sum.inr e.mid)
  | DStep.skip _ _ => 0

@[simp] theorem stepHit_fwd (τ : Track D) (e : Cell D) :
    stepHit τ (DStep.fwd e) = phi τ (Sum.inr e.mid) (Sum.inl e.tgt) := rfl

@[simp] theorem stepHit_bwd (τ : Track D) (e : Cell D) :
    stepHit τ (DStep.bwd e) = phi τ (Sum.inl e.tgt) (Sum.inr e.mid) := rfl

@[simp] theorem stepHit_skip (τ : Track D) (u w : BaseV D) :
    stepHit τ (DStep.skip u w) = 0 := rfl

end Work.ORDunwoody.Dunwoody
