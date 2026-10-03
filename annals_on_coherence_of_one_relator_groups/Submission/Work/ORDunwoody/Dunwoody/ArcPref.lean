/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The arc prefix of a walk in `Λ''`

`DESIGN_N13.md` §10.4 reduces the `RegionRel`-invariance of `alpha τ` to two facts about the
boundary walk `l = faceWalk D c w` of a face:

* an old vertex `u` occurring in `l` whose *arc index* is `i` (the number of pattern points before
  it) is reached by a path whose `alpha τ` is `Σ_{t < i} [V_t ∈ τ]`, `V_t` the visits of `l`;
* for a chord `(p,q)` of the visits, `Σ_{p ≤ t ≤ q} [V_t ∈ τ] = 0` (this is nestedness, §10.1).

This file provides the *data* for the first statement: `arcPrefAux` walks along the list keeping

* the last vertex seen (to add the cochain value `phi τ prev v` of the current step),
* the number `k` of pattern points seen so far (the arc index),
* the accumulated `alpha τ` `a` of the walk read so far,

and records, at every *old* vertex `u`, the triple `(u, k, a)`.  `arcPref l` starts this process at
the beginning of `l`; `visitSum τ l k` is the sum of `[m ∈ τ]` over the first `k` pattern points
of `l`, so the intended statement is `(u, k, a) ∈ arcPref τ l → a = visitSum τ l k`.
-/
import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.Alpha
import Submission.Work.ORDunwoody.faceVisits_eq_faceAux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

namespace Work.ORDunwoody.Dunwoody

open Work.ORDunwoody.Cayley

attribute [local instance] Classical.propDecidable

variable {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
variable {T : GTree G V} {t₀ : V} {P : FinPresentation G}
variable {D : GeoData T t₀ P}

/-- Walking along a list of vertices, keeping the previous vertex, the number of pattern points
seen and the accumulated `alpha τ`; every *old* vertex encountered is recorded with its arc index
and with the accumulated value. -/
noncomputable def arcPrefAux (τ : Track D) : Option (Vertex D) → List (Vertex D) → ℕ → ZMod 2 →
    List (BaseV D × ℕ × ZMod 2)
  | _, [], _, _ => []
  | prev, v :: rest, k, a =>
      let a' : ZMod 2 := a + (match prev with | none => 0 | some p => phi τ p v)
      match v with
      | Sum.inl u => (u, k, a') :: arcPrefAux τ (some v) rest k a'
      | Sum.inr _ => arcPrefAux τ (some v) rest (k + 1) a'

@[simp] theorem arcPrefAux_nil (τ : Track D) (prev : Option (Vertex D)) (k : ℕ) (a : ZMod 2) :
    arcPrefAux τ prev [] k a = [] := rfl

@[simp] theorem arcPrefAux_cons_inl (τ : Track D) (prev : Option (Vertex D)) (u : BaseV D)
    (rest : List (Vertex D)) (k : ℕ) (a : ZMod 2) :
    arcPrefAux τ prev (Sum.inl u :: rest) k a =
      (u, k, a + (match prev with | none => 0 | some p => phi τ p (Sum.inl u))) ::
        arcPrefAux τ (some (Sum.inl u)) rest k
          (a + (match prev with | none => 0 | some p => phi τ p (Sum.inl u))) := rfl

@[simp] theorem arcPrefAux_cons_inr (τ : Track D) (prev : Option (Vertex D)) (m : MidV D)
    (rest : List (Vertex D)) (k : ℕ) (a : ZMod 2) :
    arcPrefAux τ prev (Sum.inr m :: rest) k a =
      arcPrefAux τ (some (Sum.inr m)) rest (k + 1)
        (a + (match prev with | none => 0 | some p => phi τ p (Sum.inr m))) := rfl

/-- The old vertices of a walk, with their arc index and the accumulated `alpha τ`. -/
noncomputable def arcPref (τ : Track D) (l : List (Vertex D)) : List (BaseV D × ℕ × ZMod 2) :=
  arcPrefAux τ none l 0 0

@[simp] theorem arcPref_nil (τ : Track D) : arcPref τ ([] : List (Vertex D)) = [] := rfl

/-- The sum of the contributions `[m ∈ τ]` of the first `k` pattern points of a list. -/
noncomputable def visitSum (τ : Track D) (l : List (Vertex D)) (k : ℕ) : ZMod 2 :=
  ((l.filterMap Vertex.midOf).take k).map (fun m => if trackOf m = τ then 1 else 0) |>.sum

@[simp] theorem visitSum_zero (τ : Track D) (l : List (Vertex D)) : visitSum τ l 0 = 0 := rfl

/-- The sum of the contributions `[m ∈ τ]` of the first `k` pattern points of a list of *pattern
points*. -/
noncomputable def midSum (τ : Track D) (vs : List (MidV D)) (k : ℕ) : ZMod 2 :=
  ((vs.take k).map (fun m => if trackOf m = τ then 1 else 0)).sum

@[simp] theorem midSum_zero (τ : Track D) (vs : List (MidV D)) : midSum τ vs 0 = 0 := rfl

/-- `visitSum` is `midSum` of the pattern points of the walk. -/
@[simp] theorem visitSum_eq_midSum (τ : Track D) (l : List (Vertex D)) (k : ℕ) :
    visitSum τ l k = midSum τ (l.filterMap Vertex.midOf) k := rfl

/-- The visits of the boundary walk of a face are the visits of `Pattern.lean`. -/
theorem filterMap_midOf_faceWalk (c : G) (w : List (Fin P.n × Bool)) :
    (faceWalk D c w).filterMap Vertex.midOf = faceVisits D c w := by
  rw [faceVisits_eq_faceAux, faceWalk_eq]
  rfl

end Work.ORDunwoody.Dunwoody
