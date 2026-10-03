import Mathlib
import Submission.Work.ORDunwoody.alphaFaceWalkDefs

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

namespace Work.ORDunwoody

open Work.ORDunwoody.Dunwoody

/-!
# `alpha τ` over a chain of directed steps

`Dunwoody/Alpha.lean` defines the integral `alpha τ [v₀, …, vₙ] = Σ_{i<n} phi τ vᵢ vᵢ₊₁` of the
counting cochain `phi τ` of a track over a walk of the 1-skeleton of `Λ''`, and
`Work.ORDunwoody.alphaFaceWalkDefs` records the contribution `stepHit τ s` of a *directed step*
`s` (`DStep D`) — the non-zero half-cell of the cell traversed by `s`.

The present file proves the computation of the integral over the walk obtained by concatenating
the vertex lists `DStep.verts` of a **chain** of directed steps: it is the sum of the
contributions `stepHit τ` of the steps, plus the integral over what follows the chain.  This is
the input `Work.ORDunwoody.alpha_steps` of the computation of `alpha τ` over the boundary walk of
a face (`alpha_faceWalk.lean`).

The argument is an induction on the list of steps; the single step is the observation `alpha_step`
that a forward step `fwd e` traverses the cell `e.src → e.mid → e.tgt`, so that by `alpha_cell` it
contributes `phi τ (inr e.mid) (inl e.tgt) = stepHit τ (fwd e)` — and likewise for a backward
step, whose contribution is `phi τ (inl e.tgt) (inr e.mid)` — while a collapsed step `skip u w`
moves along a plain edge, on which `phi τ` vanishes.
-/

/-- Membership in `List.head?`, in the form used by `List.IsChain.rel_head?`. -/
theorem mem_head?_iff {α : Type*} {l : List α} {a : α} : a ∈ l.head? ↔ l.head? = some a := by
  cases l <;> simp

/-- **The contribution of a single directed step to `alpha τ`.**  The traversal `s.src → s.verts`
of a step, followed by `rest`, contributes exactly `stepHit τ s`:

    alpha τ (inl s.src :: (s.verts ++ rest)) = stepHit τ s + alpha τ (inl s.tgt :: rest) .

For a forward step this is `alpha_cell` (`phi τ` is zero on the source half of a cell), for a
backward step `alpha_cell_rev` (zero on the target half), and for a collapsed step it is the
vanishing of `phi τ` on the plain edges. -/
theorem alpha_step {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} (τ : Track D) (s : DStep D)
    (rest : List (Vertex D)) :
    alpha τ (Sum.inl s.src :: (s.verts ++ rest)) =
      stepHit τ s + alpha τ (Sum.inl s.tgt :: rest) := by
  cases s with
  | fwd e =>
      simp only [DStep.verts_fwd, DStep.src_fwd, DStep.tgt_fwd, stepHit_fwd, List.cons_append,
        List.nil_append]
      change alpha τ
          (Sum.inl (MidV.src e.mid) :: Sum.inr e.mid :: Sum.inl (MidV.tgt e.mid) :: rest) =
        phi τ (Sum.inr e.mid) (Sum.inl (MidV.tgt e.mid)) +
          alpha τ (Sum.inl (MidV.tgt e.mid) :: rest)
      rw [alpha_cell, phi_mid_tgt]
  | bwd e =>
      simp only [DStep.verts_bwd, DStep.src_bwd, DStep.tgt_bwd, stepHit_bwd, List.cons_append,
        List.nil_append]
      change alpha τ
          (Sum.inl (MidV.tgt e.mid) :: Sum.inr e.mid :: Sum.inl (MidV.src e.mid) :: rest) =
        phi τ (Sum.inl (MidV.tgt e.mid)) (Sum.inr e.mid) +
          alpha τ (Sum.inl (MidV.src e.mid) :: rest)
      rw [alpha_cell_rev, phi_tgt_mid]
  | skip u w => simp

/-- **The integral over a chain of directed steps.**  If the list `l` of directed steps is a chain
(`DStep.tgt s = DStep.src s'` for consecutive steps) whose first step starts at `a`, then the
integral of `phi τ` over the walk obtained by concatenating the vertex lists of the steps, followed
by `rest`, is the sum of the contributions of the steps plus the integral over `rest` from the
point reached by the chain:

    alpha τ (inl a :: (l.flatMap DStep.verts ++ rest))
      = (l.map (stepHit τ)).sum + alpha τ (inl (last step of l).tgt :: rest) .

The vertex reached by the chain is recorded as the `foldl` of `DStep.tgt` over `l`, which is what
makes the induction terminate (the fold of a step list from `a` ends at the target of its last
step, see `foldl_tgt_of_getLast`). -/
theorem alpha_flatMap_verts {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} (τ : Track D) :
    ∀ (l : List (DStep D)) (a : BaseV D) (rest : List (Vertex D)),
      l.IsChain (fun s s' => DStep.tgt s = DStep.src s') →
      (∀ s, l.head? = some s → DStep.src s = a) →
      alpha τ (Sum.inl a :: (l.flatMap DStep.verts ++ rest)) =
        (l.map (stepHit τ)).sum +
          alpha τ (Sum.inl (l.foldl (fun _ s => DStep.tgt s) a) :: rest) := by
  intro l
  induction l with
  | nil =>
      intro a rest _ _
      simp
  | cons s l' ih =>
      intro a rest hchain hhead
      have hsrc : DStep.src s = a := hhead s (by simp)
      have hchain' : l'.IsChain (fun s s' => DStep.tgt s = DStep.src s') := hchain.tail
      -- the chain hands the start of the remainder to the induction hypothesis
      have hhead' : ∀ t, l'.head? = some t → DStep.src t = DStep.tgt s := by
        intro t ht
        exact (hchain.rel_head? (mem_head?_iff.mpr ht)).symm
      have hstep : alpha τ (Sum.inl a :: ((s :: l').flatMap DStep.verts ++ rest)) =
          stepHit τ s +
            alpha τ (Sum.inl (DStep.tgt s) :: (l'.flatMap DStep.verts ++ rest)) := by
        rw [List.flatMap_cons, List.append_assoc, ← hsrc]
        exact alpha_step τ s (l'.flatMap DStep.verts ++ rest)
      rw [hstep, ih (DStep.tgt s) rest hchain' hhead', List.map_cons, List.sum_cons]
      simp only [List.foldl_cons]
      abel

/-- **The point reached by a chain of steps.**  Folding `DStep.tgt` over a nonempty list of steps
gives the target of its last step (the accumulator is discarded); for the empty list it is the
starting point. -/
theorem foldl_tgt_of_getLast {G : Type u} [Group G] {V : Type u} [MulAction G V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} (l : List (DStep D)) (a u₁ : BaseV D)
    (hlast : ∀ s, l.getLast? = some s → DStep.tgt s = u₁)
    (hnil : l = [] → a = u₁) :
    l.foldl (fun _ s => DStep.tgt s) a = u₁ := by
  induction l generalizing a with
  | nil => simpa using hnil rfl
  | cons s l' ih =>
      have hlast' : ∀ t, l'.getLast? = some t → DStep.tgt t = u₁ := by
        intro t ht
        exact hlast t (by rw [List.getLast?_cons, ht]; rfl)
      have hnil' : l' = [] → DStep.tgt s = u₁ := by
        intro h
        subst h
        exact hlast s (by simp)
      rw [List.foldl_cons]
      exact ih (DStep.tgt s) hlast' hnil'

/-- **The integral over a chain of directed steps is the sum of the contributions of the steps.**
The walk that runs through the vertex lists `DStep.verts` of a chain `l` of directed steps from
`u₀` to `u₁`, followed by `rest`, has integral the sum of the values `stepHit τ` of its steps plus
the integral over `rest` from `u₁`. -/
theorem alpha_steps {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} (τ : Work.ORDunwoody.Dunwoody.Track D)
    (l : List (Work.ORDunwoody.Dunwoody.DStep D))
    (u₀ u₁ : Work.ORDunwoody.Dunwoody.BaseV D)
    (rest : List (Work.ORDunwoody.Dunwoody.Vertex D))
    (hhead : ∀ s, l.head? = some s → Work.ORDunwoody.Dunwoody.DStep.src s = u₀)
    (hlast : ∀ s, l.getLast? = some s → Work.ORDunwoody.Dunwoody.DStep.tgt s = u₁)
    (hchain : l.IsChain (fun s s' => Work.ORDunwoody.Dunwoody.DStep.tgt s =
      Work.ORDunwoody.Dunwoody.DStep.src s'))
    (hnil : l = [] → u₀ = u₁) :
    Work.ORDunwoody.Dunwoody.alpha τ
        (Sum.inl u₀ :: (l.flatMap Work.ORDunwoody.Dunwoody.DStep.verts ++ rest)) =
      (l.map (Work.ORDunwoody.Dunwoody.stepHit τ)).sum +
        Work.ORDunwoody.Dunwoody.alpha τ (Sum.inl u₁ :: rest) := by
  have key := alpha_flatMap_verts τ l u₀ rest hchain hhead
  have hfold : l.foldl (fun _ s => DStep.tgt s) u₀ = u₁ :=
    foldl_tgt_of_getLast l u₀ u₁ hlast hnil
  rw [hfold] at key
  exact key

end Work.ORDunwoody
