/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The directed steps of a positive letter form a chain

`Work.ORDunwoody.Dunwoody.posSteps D a j` is the list of directed steps of the boundary walk of
`Λ''` while it traverses the positive generator edge `(j,true)` based at the group element `a`
(`Submission/Work/ORDunwoody/even_visits_defs.lean`).  Either the generator edge is collapsed
(`L (j,true) = 0`), in which case the walk consists of the single step
`skip (a,∗) (a * genE (j,true), ∗)` visiting no pattern point, or it consists of the
`L (j,true)` cells of the geodesic, traversed forwards:

    posSteps D a j = (finRange (L (j,true))).map (fun k => fwd ⟨a, j, k⟩).

The present file records the four elementary facts about that list which the computation of
`alpha τ` on the boundary walk of a face needs (`Work.ORDunwoody.alpha_faceWalk`):

* its first step starts at the current base point `(a, ∗)`;
* its last step ends at the next base point `(a * genE (j,true), ∗)`;
* consecutive steps form a chain (`DStep.tgt s = DStep.src s'`);
* the list is nonempty.

All four are immediate from the shape of `posSteps`: the head of `finRange n` is `0`, its last
entry is `n - 1`, consecutive entries of `finRange n` are `k` and `k + 1`, and the source of
`fwd ⟨a,j,k⟩` is `pos a j k` while its target is `pos a j (k+1)`.
-/
import Mathlib
import Submission.Work.ORDunwoody.even_visits_defs

set_option autoImplicit false

namespace Work.ORDunwoody

universe u

open Work.ORDunwoody.Dunwoody
open Work.ORDunwoody.Cayley

/-! ## Two elementary facts about `List.finRange` -/

/-- The list `(List.finRange n).map f` is a chain for `R` as soon as `R` relates the values of `f`
at consecutive natural indices. -/
theorem chain_map_finRange {α : Type u} (R : α → α → Prop) (n : ℕ) (f : (k : Fin n) → α)
    (h : ∀ (k : ℕ) (hk : k + 1 < n), R (f ⟨k, Nat.lt_of_succ_lt hk⟩) (f ⟨k + 1, hk⟩)) :
    ((List.finRange n).map f).IsChain R := by
  rw [List.isChain_iff_getElem]
  intro i hi
  rw [List.length_map, List.length_finRange] at hi
  rw [List.getElem_map, List.getElem_finRange]
  simpa using h i hi

/-- The first entry of `List.finRange n` is `0` and its last entry is `n - 1` (for `n ≠ 0`). -/
theorem finRange_head_getLast {n : ℕ} (hn : 0 < n) :
    (List.finRange n).head? = some ⟨0, hn⟩ ∧
    (List.finRange n).getLast? = some ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩ := by
  constructor
  · cases n with
    | zero => omega
    | succ m => rw [List.finRange_succ, List.head?_cons]; rfl
  · cases n with
    | zero => omega
    | succ m => rw [List.finRange_succ_last, List.getLast?_append, List.getLast?_singleton]
                rfl

/-! ## The four facts about `posSteps` -/

/-- **The directed steps of the traversal of the positive generator edge `(j,true)` based at `a`**:
the walk starts at `(a, ∗)`, ends at `(a * genE (j,true), ∗)`, is a chain of directed steps, and is
nonempty. -/
theorem posSteps_facts {G : Type u} [Group G] {V : Type u} [MulAction G V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} (a : G) (j : Fin P.n) :
    (∀ s, (Work.ORDunwoody.Dunwoody.posSteps D a j).head? = some s →
        Work.ORDunwoody.Dunwoody.DStep.src s = (a, Sum.inl ())) ∧
    (∀ s, (Work.ORDunwoody.Dunwoody.posSteps D a j).getLast? = some s →
        Work.ORDunwoody.Dunwoody.DStep.tgt s =
          (a * Work.ORDunwoody.Cayley.CayV.genE P (j, true), Sum.inl ())) ∧
    (Work.ORDunwoody.Dunwoody.posSteps D a j).IsChain
      (fun s s' => Work.ORDunwoody.Dunwoody.DStep.tgt s =
        Work.ORDunwoody.Dunwoody.DStep.src s') ∧
    Work.ORDunwoody.Dunwoody.posSteps D a j ≠ [] := by
  by_cases h0 : D.L (j, true) = 0
  · -- the generator edge is collapsed: one step, from `(a,∗)` to `(a * genE, ∗)`, visiting
    -- no pattern point
    have hp : posSteps D a j = [DStep.skip ((a, Sum.inl ()) : BaseV D)
        ((a * CayV.genE P (j, true), Sum.inl ()) : BaseV D)] := by
      rw [posSteps, dif_pos h0]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s hs
      rw [hp, List.head?_cons] at hs
      simp only [Option.some.injEq] at hs
      subst hs; rfl
    · intro s hs
      rw [hp, List.getLast?_singleton] at hs
      simp only [Option.some.injEq] at hs
      subst hs; rfl
    · rw [hp]; exact List.IsChain.singleton _
    · rw [hp]; exact List.cons_ne_nil _ _
  · -- the generator edge is a genuine geodesic: one forward step per cell
    have hn : 0 < D.L (j, true) := Nat.pos_of_ne_zero h0
    have hp : posSteps D a j = (List.finRange (D.L (j, true))).map
        (fun k : Fin (D.L (j, true)) => DStep.fwd (⟨a, j, k⟩ : Cell D)) := by
      rw [posSteps, dif_neg h0]
    have hhead : (posSteps D a j).head? = some (DStep.fwd (⟨a, j, ⟨0, hn⟩⟩ : Cell D)) := by
      rw [hp, List.head?_map, (finRange_head_getLast hn).1]
      rfl
    have hlast : (posSteps D a j).getLast? =
        some (DStep.fwd
          (⟨a, j, ⟨D.L (j, true) - 1, Nat.sub_lt hn Nat.zero_lt_one⟩⟩ : Cell D)) := by
      rw [hp, List.getLast?_map, (finRange_head_getLast hn).2]
      rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s hs
      rw [hhead] at hs
      simp only [Option.some.injEq] at hs
      subst hs; rfl
    · intro s hs
      rw [hlast] at hs
      simp only [Option.some.injEq] at hs
      subst hs
      exact pos_succ_of_not_lt D a j (i := D.L (j, true) - 1) (by omega)
    · rw [hp]
      refine chain_map_finRange (fun s s' => DStep.tgt s = DStep.src s')
        (D.L (j, true)) (fun k : Fin (D.L (j, true)) => DStep.fwd (⟨a, j, k⟩ : Cell D)) ?_
      intro k hk
      rfl
    · intro hnil
      rw [hnil, List.head?_nil] at hhead
      simp at hhead

end Work.ORDunwoody
