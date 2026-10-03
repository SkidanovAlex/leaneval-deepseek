import Mathlib
import Submission.Work.OROneRel.exists_treeGauge

/-!
# An edge-set-parameterised exploration of the window graph

This file contains *definitions* (and the elementary lemmas about them), so that the lemmas about
them may be delegated to other files.

The exploration of `Submission/Work/OROneRel/exists_treeGauge.lean` builds the tree-path gauge of a
window `[lo,hi]` by a breadth-first search of the level graph, where every level is reached along an
edge of the full window `winE c lo hi`.  Here the same search is run with an **arbitrary allowed edge
set** `E` (which in applications is a window with some edges, and possibly all edges incident with
some level, deleted) and from an **arbitrary seed state** `σ₀` (so that the search can be resumed
after an extra prescribed step).

* `lvInc c i e` -- the level `i` is an endpoint of the edge `e`;
* `winErem c lo hi F` -- the window edges outside `F`;
* `xExists c E g x` -- some witness reaches the level `x` from a level assigned by `g` along an
  edge of `E`;
* `xstep c E g` -- one round of the search: every level not yet assigned and reachable in one step is
  assigned the word of that step;
* `xstate c E σ₀ n` -- the state after `n` rounds;
* `stGauge σ` -- the gauge of a state, with `1` at the levels the state does not assign;
* `lastEdge? c L` -- the edge of the level graph traversed by the last letter of `L`, read from the
  level `0`;
* `XInv c E σ` -- the structural invariant of the search: the words are reduced and have the level of
  their level, their decorated edges and the edges of their last letters lie in `E`, they are closed
  under their running levels, and they are *nested*: every prefix of an assigned word is the word
  assigned to the prefix's level.

The invariant is what makes the "trivial loop class" and the "non-trivial loop class" halves of
`Work.OROneRel.exists_gauge_excl` work: nestedness makes the last letter of every assigned word
traverse an edge of trivial loop class, and (with the uniqueness of reduced forms) it forces a window
edge of trivial loop class to be the last letter's edge of an assigned word, hence an edge of `E`.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-! ## Incident levels and restricted edge sets -/

/-- A level `i` is an endpoint of the edge `e` of the level graph. -/
def lvInc (c : α → ℤ) (i : ℤ) (e : α × ℤ) : Prop := e.2 = i ∨ e.2 + c e.1 = i

/-- The target level of a witness is an endpoint of the edge it traverses. -/
theorem lvInc_tgt_edge (c : α → ℤ) (p : Bwit α) : lvInc c (Bwit.tgt c p) (Bwit.edge c p) := by
  obtain ⟨lv, gen, dir, word⟩ := p
  cases dir <;> simp [lvInc, Bwit.tgt, Bwit.edge]

/-- The source level of a witness is an endpoint of the edge it traverses. -/
theorem lvInc_src_edge (c : α → ℤ) (p : Bwit α) : lvInc c p.lv (Bwit.edge c p) := by
  obtain ⟨lv, gen, dir, word⟩ := p
  cases dir <;> simp [lvInc, Bwit.edge]

/-- The target level of a decorated letter is an endpoint of its edge. -/
theorem lvInc_coverTgt (c : α → ℤ) (p : (α × ℤ) × Bool) : lvInc c (coverTgt c p) (coverEdge p) := by
  obtain ⟨⟨a, i⟩, b⟩ := p
  cases b <;> simp [lvInc, coverTgt, coverEdge]

/-- The source level of a decorated letter is an endpoint of its edge. -/
theorem lvInc_coverSrc (c : α → ℤ) (p : (α × ℤ) × Bool) : lvInc c (coverSrc c p) (coverEdge p) := by
  obtain ⟨⟨a, i⟩, b⟩ := p
  cases b <;> simp [lvInc, coverSrc, coverEdge]

/-- **The allowed edges**: the window edges outside `F`. -/
def winErem (c : α → ℤ) (lo hi : ℤ) (F : Set (α × ℤ)) : Set (α × ℤ) :=
  {e | e ∈ winE c lo hi ∧ e ∉ F}

@[simp] theorem mem_winErem {c : α → ℤ} {lo hi : ℤ} {F : Set (α × ℤ)} {e : α × ℤ} :
    e ∈ winErem c lo hi F ↔ e ∈ winE c lo hi ∧ e ∉ F := Iff.rfl

theorem winErem_subset (c : α → ℤ) (lo hi : ℤ) (F : Set (α × ℤ)) :
    winErem c lo hi F ⊆ winE c lo hi := fun _ he => he.1

theorem winErem_anti {c : α → ℤ} {lo hi : ℤ} {F G : Set (α × ℤ)} (h : F ⊆ G) :
    winErem c lo hi G ⊆ winErem c lo hi F := fun _ he => ⟨he.1, fun hc => he.2 (h hc)⟩

/-! ## The last edge of a word -/

/-- **The edge of the last letter of a word**, read from the level `0`: for a nonempty word `L` whose
last letter is `p`, it is `(p.1, if p.2 then lsig c L.dropLast else lsig c L.dropLast - c p.1)`, the
edge of the level graph traversed by that letter (whose source level is `lsig c L.dropLast`). -/
noncomputable def lastEdge? (c : α → ℤ) (L : List (α × Bool)) : Option (α × ℤ) :=
  L.getLast?.map (fun p => (p.1, if p.2 then lsig c L.dropLast else lsig c L.dropLast - c p.1))

theorem lastEdge?_append (c : α → ℤ) (L : List (α × Bool)) (p : α × Bool) :
    lastEdge? c (L ++ [p]) = some (p.1, if p.2 then lsig c L else lsig c L - c p.1) := by
  simp [lastEdge?, List.getLast?_append]

/-! ## The exploration -/

/-- **A witness of one round of the search**: a level `p.lv` carrying the word `p.word` is joined to
the level `x` by the edge `Bwit.edge c p`, which lies in `E`. -/
def xExists (c : α → ℤ) (E : Set (α × ℤ)) (g : ℤ → Option (List (α × Bool))) (x : ℤ) : Prop :=
  ∃ p : Bwit α, Bwit.edge c p ∈ E ∧ g p.lv = some p.word ∧ x = Bwit.tgt c p

theorem xExists_mono {c : α → ℤ} {E E' : Set (α × ℤ)} (h : E ⊆ E')
    {g : ℤ → Option (List (α × Bool))} {x : ℤ} (hx : xExists c E g x) : xExists c E' g x :=
  let ⟨p, hp, hg, hx⟩ := hx; ⟨p, h hp, hg, hx⟩

/-- **One round of the search**: the assigned levels keep their word, and every level not assigned
that is reached in one step from an assigned level along an edge of `E` is assigned the word of that
step. -/
noncomputable def xstep (c : α → ℤ) (E : Set (α × ℤ)) (g : ℤ → Option (List (α × Bool))) (x : ℤ) :
    Option (List (α × Bool)) := by
  classical
  exact
    if g x = none then
      (if h : xExists c E g x then some (Bwit.newWord (Classical.choose h)) else none)
    else g x

/-- **The state of the search after `n` rounds.** -/
noncomputable def xstate (c : α → ℤ) (E : Set (α × ℤ))
    (σ₀ : ℤ → Option (List (α × Bool))) (n : ℕ) : ℤ → Option (List (α × Bool)) :=
  (xstep c E)^[n] σ₀

/-- **The gauge of a state**: the word of its assigned levels, and `1` at the others. -/
noncomputable def stGauge (σ : ℤ → Option (List (α × Bool))) : ℤ → FreeGroup α :=
  fun i => FreeGroup.mk ((σ i).getD [])

theorem xstep_of_some {c : α → ℤ} {E : Set (α × ℤ)} {g : ℤ → Option (List (α × Bool))} {x : ℤ}
    {v : List (α × Bool)} (h : g x = some v) : xstep c E g x = some v := by
  classical
  unfold xstep
  rw [if_neg (by simp [h])]
  exact h

theorem xstep_eq_some_of_exists {c : α → ℤ} {E : Set (α × ℤ)}
    {g : ℤ → Option (List (α × Bool))} {x : ℤ} (hx : g x = none)
    (h : xExists c E g x) :
    xstep c E g x = some (Bwit.newWord (Classical.choose h)) := by
  classical
  unfold xstep
  rw [if_pos hx]
  simp only [dif_pos h]

theorem xstep_eq_none_of_not {c : α → ℤ} {E : Set (α × ℤ)}
    {g : ℤ → Option (List (α × Bool))} {x : ℤ} (hx : g x = none) (h : ¬ xExists c E g x) :
    xstep c E g x = none := by
  classical
  unfold xstep
  rw [if_pos hx]
  simp only [dif_neg h]

/-- A step of the search never forgets an assigned level. -/
theorem xstep_ne_none_of_wit {c : α → ℤ} {E : Set (α × ℤ)}
    {g : ℤ → Option (List (α × Bool))} {p : Bwit α} (hE : Bwit.edge c p ∈ E)
    (hg : g p.lv = some p.word) : xstep c E g (Bwit.tgt c p) ≠ none := by
  classical
  by_cases hx : g (Bwit.tgt c p) = none
  · exact ne_of_eq_of_ne (xstep_eq_some_of_exists hx ⟨p, hE, hg, rfl⟩) (by simp)
  · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hx
    exact ne_of_eq_of_ne (xstep_of_some hv) (by simp)

theorem xstate_zero (c : α → ℤ) (E : Set (α × ℤ)) (σ₀ : ℤ → Option (List (α × Bool))) :
    xstate c E σ₀ 0 = σ₀ := rfl

/-- **The weight of a prefix is a running level**: the prefixes of a word realise the running levels
of its walk. -/
theorem lsig_take_mem_running (c : α → ℤ) (i : ℤ) (L : List (α × Bool)) (k : ℕ)
    (hk : k ≤ L.length) : i + lsig c (L.take k) ∈ running c i L := by
  induction L generalizing i k with
  | nil =>
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst hk0
    rw [List.take_zero, show lsig c ([] : List (α × Bool)) = 0 from rfl, add_zero,
      show running c i ([] : List (α × Bool)) = [i] from rfl]
    exact List.mem_singleton_self _
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    rw [running_cons']
    match k with
    | 0 =>
      rw [List.take_zero, show lsig c ([] : List (α × Bool)) = 0 from rfl, add_zero]
      exact List.mem_cons_self ..
    | (k + 1) =>
      refine List.mem_cons_of_mem _ ?_
      rw [List.take_succ_cons,
        show lsig c ((a, b) :: L.take k) = linc c (a, b) + lsig c (L.take k) from rfl,
        show i + (linc c (a, b) + lsig c (L.take k)) = (i + linc c (a, b)) + lsig c (L.take k)
          from by ring]
      exact ih (i + linc c (a, b)) k (by rw [List.length_cons] at hk; omega)

theorem stGauge_of_some {σ : ℤ → Option (List (α × Bool))} {i : ℤ} {L : List (α × Bool)}
    (h : σ i = some L) : Work.OROneRel.stGauge σ i = FreeGroup.mk L := by
  simp [stGauge, h]

theorem xstate_succ (c : α → ℤ) (E : Set (α × ℤ)) (σ₀ : ℤ → Option (List (α × Bool))) (n : ℕ) :
    xstate c E σ₀ (n + 1) = xstep c E (xstate c E σ₀ n) := by
  show (xstep c E)^[n + 1] σ₀ = xstep c E ((xstep c E)^[n] σ₀)
  exact Function.iterate_succ_apply' (xstep c E) n σ₀

theorem xstate_succ_of_some {c : α → ℤ} {E : Set (α × ℤ)}
    {σ₀ : ℤ → Option (List (α × Bool))} {n : ℕ} {x : ℤ} {v : List (α × Bool)}
    (h : xstate c E σ₀ n x = some v) : xstate c E σ₀ (n + 1) x = some v := by
  rw [xstate_succ]
  exact xstep_of_some h

theorem xstate_mono {c : α → ℤ} {E : Set (α × ℤ)} {σ₀ : ℤ → Option (List (α × Bool))}
    {n m : ℕ} (hnm : n ≤ m) {x : ℤ} {v : List (α × Bool)}
    (h : xstate c E σ₀ n x = some v) : xstate c E σ₀ m x = some v := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact xstate_succ_of_some ih

/-- **The closure property of a fixed point of the search**: at a fixed point, a level reached by an
edge of `E` from an assigned level is assigned. -/
theorem xstep_fixed_closed {c : α → ℤ} {E : Set (α × ℤ)}
    {σ : ℤ → Option (List (α × Bool))} (hfix : xstep c E σ = σ) {p : Bwit α}
    (hE : Bwit.edge c p ∈ E) (hσ : σ p.lv = some p.word) : σ (Bwit.tgt c p) ≠ none := by
  classical
  intro hnone
  have hx : xExists c E σ (Bwit.tgt c p) := ⟨p, hE, hσ, rfl⟩
  have h1 : xstep c E σ (Bwit.tgt c p) = some (Bwit.newWord (Classical.choose hx)) :=
    xstep_eq_some_of_exists hnone hx
  rw [hfix, hnone] at h1
  exact absurd h1 (by simp)

/-- **A level all of whose incident edges are deleted is never assigned** (unless it was already
assigned in the seed). -/
theorem xstate_blocked {c : α → ℤ} {E : Set (α × ℤ)} {σ₀ : ℤ → Option (List (α × Bool))}
    {bl : ℤ} (h0 : σ₀ bl = none) (hE : ∀ e ∈ E, ¬ lvInc c bl e) (n : ℕ) :
    xstate c E σ₀ n bl = none := by
  classical
  induction n with
  | zero => rw [xstate_zero]; exact h0
  | succ k ih =>
    rw [xstate_succ]
    refine xstep_eq_none_of_not ih ?_
    rintro ⟨p, hpE, -, hpx⟩
    exact hE (Bwit.edge c p) hpE (hpx ▸ lvInc_tgt_edge c p)

/-! ## The levels of a word whose traversals avoid a deleted edge set -/

/-- **No traversal of a word whose edges avoid the edges incident with `bl` arrives at `bl`.** -/
theorem linc_ne_of_decor_avoid (c : α → ℤ) (bl : ℤ) {E : Set (α × ℤ)}
    (hE : ∀ e ∈ E, ¬ lvInc c bl e) (i : ℤ) (p : α × Bool) (L : List (α × Bool))
    (hL : ∀ q ∈ decor c i (p :: L), coverEdge q ∈ E) : i + linc c p ≠ bl := by
  obtain ⟨a, b⟩ := p
  have hmem : ((a, if b then i else i - c a), b) ∈ decor c i ((a, b) :: L) := by
    cases b
    · rw [show decor c i ((a, false) :: L) = ((a, i - c a), false) :: decor c (i - c a) L from rfl]
      exact List.mem_cons_self ..
    · rw [show decor c i ((a, true) :: L) = ((a, i), true) :: decor c (i + c a) L from rfl]
      exact List.mem_cons_self ..
  have htm : coverTgt c ((a, if b then i else i - c a), b) = i + linc c (a, b) := by
    cases b <;> simp [coverTgt, linc] <;> ring
  intro hc
  have h1 : lvInc c (i + linc c (a, b)) (coverEdge ((a, if b then i else i - c a), b)) :=
    htm ▸ lvInc_coverTgt c _
  rw [hc] at h1
  exact hE _ (hL _ hmem) h1

/-- **The levels of a walk whose traversals all avoid the edges incident with `bl` avoid `bl`.** -/
theorem running_ne_of_decor_avoid (c : α → ℤ) (bl : ℤ) {E : Set (α × ℤ)}
    (hE : ∀ e ∈ E, ¬ lvInc c bl e) (i : ℤ) (hi : i ≠ bl) (L : List (α × Bool))
    (hL : ∀ q ∈ decor c i L, coverEdge q ∈ E) : ∀ l ∈ running c i L, l ≠ bl := by
  induction L generalizing i with
  | nil =>
    intro l hl
    rw [show running c i ([] : List (α × Bool)) = [i] from rfl, List.mem_singleton] at hl
    exact hl ▸ hi
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    intro l hl
    rw [running_cons'] at hl
    rcases List.mem_cons.mp hl with rfl | hl
    · exact hi
    · have hL' : ∀ q ∈ decor c (i + linc c (a, b)) L, coverEdge q ∈ E := by
        intro q hq
        cases b
        · exact hL q (by
            rw [show decor c i ((a, false) :: L) = ((a, i - c a), false) :: decor c (i - c a) L
              from rfl]
            exact List.mem_cons_of_mem _ hq)
        · exact hL q (by
            rw [show decor c i ((a, true) :: L) = ((a, i), true) :: decor c (i + c a) L
              from rfl]
            exact List.mem_cons_of_mem _ hq)
      exact ih (i + linc c (a, b)) (linc_ne_of_decor_avoid c bl hE i (a, b) L hL) hL' l hl

/-! ## The invariant of the search -/

/-- **The structural invariant of the search.**

1. every assigned word is reduced and has the level of its level;
2. the decorated edges of an assigned word are edges of `E`;
3. the running levels of an assigned word are assigned;
4. the assigned words are *nested*: every prefix of an assigned word is the word assigned to the
   prefix's level;
5. the edge traversed by the last letter of a nonempty assigned word is an edge of `E`. -/
def XInv (c : α → ℤ) (E : Set (α × ℤ)) (σ : ℤ → Option (List (α × Bool))) : Prop :=
  (∀ i L, σ i = some L → lsig c L = i ∧ FreeGroup.IsReduced L) ∧
  (∀ i L, σ i = some L → ∀ q ∈ decor c 0 L, coverEdge q ∈ E) ∧
  (∀ i L, σ i = some L → ∀ l ∈ running c 0 L, σ l ≠ none) ∧
  (∀ i L, σ i = some L → ∀ k, k ≤ L.length → σ (lsig c (L.take k)) = some (L.take k)) ∧
  (∀ i L, σ i = some L → ∀ e, lastEdge? c L = some e → e ∈ E)

theorem XInv.mono {c : α → ℤ} {E E' : Set (α × ℤ)} (hEE : E ⊆ E')
    {σ : ℤ → Option (List (α × Bool))} (h : XInv c E σ) : XInv c E' σ :=
  ⟨h.1, fun i L hi => fun q hq => hEE (h.2.1 i L hi q hq),
    h.2.2.1, h.2.2.2.1, fun i L hi => fun e he => hEE (h.2.2.2.2 i L hi e he)⟩

/-- The invariant holds for the empty state. -/
theorem XInv_zero (c : α → ℤ) (E : Set (α × ℤ)) :
    XInv c E (fun _ => (none : Option (List (α × Bool)))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro i L h <;> simp at h

/-- **The invariant holds for the seed state of the search**: the empty word at the level `0`. -/
theorem XInv_seed (c : α → ℤ) (E : Set (α × ℤ)) :
    XInv c E (fun x => if x = 0 then some ([] : List (α × Bool)) else none) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i L h
    by_cases hi : i = 0
    · simp only [if_pos hi] at h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨by rw [show lsig c ([] : List (α × Bool)) = 0 from rfl]; exact hi.symm,
        FreeGroup.IsReduced.nil⟩
    · simp only [if_neg hi] at h
      exact absurd h (by simp)
  · intro i L h
    by_cases hi : i = 0
    · simp only [if_pos hi] at h
      simp only [Option.some.injEq] at h
      subst h
      intro q hq
      rw [show decor c 0 ([] : List (α × Bool)) = ([] : List ((α × ℤ) × Bool)) from rfl] at hq
      exact absurd hq (by simp)
    · simp only [if_neg hi] at h
      exact absurd h (by simp)
  · intro i L h
    by_cases hi : i = 0
    · simp only [if_pos hi] at h
      simp only [Option.some.injEq] at h
      subst h
      intro l hl
      rw [show running c 0 ([] : List (α × Bool)) = [0] from rfl, List.mem_singleton] at hl
      subst hl
      simp
    · simp only [if_neg hi] at h
      exact absurd h (by simp)
  · intro i L h
    by_cases hi : i = 0
    · simp only [if_pos hi] at h
      simp only [Option.some.injEq] at h
      subst h
      intro k hk
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst hk0
      simp [lsig]
    · simp only [if_neg hi] at h
      exact absurd h (by simp)
  · intro i L h
    by_cases hi : i = 0
    · simp only [if_pos hi] at h
      simp only [Option.some.injEq] at h
      subst h
      intro e he
      rw [show lastEdge? c ([] : List (α × Bool)) = none from rfl] at he
      exact absurd he (by simp)
    · simp only [if_neg hi] at h
      exact absurd h (by simp)

end Work.OROneRel
