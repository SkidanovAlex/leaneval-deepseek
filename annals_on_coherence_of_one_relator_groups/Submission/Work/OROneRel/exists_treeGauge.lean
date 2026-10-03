import Mathlib
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.gauge_walk_defs

/-!
# Existence of the tree-path gauge of a window

Given a weight `c : α → ℤ` and a level window `[lo,hi]`, suppose every level `i` of the window is
reachable from the level `0` by a walk whose traversed edges all lie in the window
(`hreach`).  Then there is a *gauge* `Wt : ℤ → FreeGroup α` (a word of level `i` assigned to every
level `i`), with `Wt 0 = 1`, such that for every level `i` of the window the traversals of
`wordOf (Wt i)` are edges of *trivial loop class* (`winTree`) — i.e. `Wt` is the tree-path gauge of a
spanning tree of the window graph.

## The construction

The proof runs a breadth-first exploration of the level graph (restricted to the window edges) from
the level `0`: `bstate c lo hi n` is the state of the exploration after `n` rounds, i.e. a partial
assignment of reduced words to levels.  The state is a fixed point after finitely many rounds (the
assigned levels always lie in the bounded set `bSet c lo hi`), and all reachable levels are assigned
at the fixed point; the gauge is the fixed point evaluated at the number of rounds `NW c lo hi`.

The invariant maintained by the exploration (`Inv`) says that every assigned word is reduced, has the
weight of its level, traverses only window edges, is built from previously assigned levels, and that
the *discovering* edges have trivial loop class — which is what makes them the tree of the gauge.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-! ## 1. List plumbing for the walk of a word -/

theorem lsig_nil' (c : α → ℤ) : lsig c ([] : List (α × Bool)) = 0 := rfl

theorem lsig_append' (c : α → ℤ) (L₁ L₂ : List (α × Bool)) :
    lsig c (L₁ ++ L₂) = lsig c L₁ + lsig c L₂ := by
  simp [lsig, List.map_append, List.sum_append]

theorem lsig_cons' (c : α → ℤ) (p : α × Bool) (L : List (α × Bool)) :
    lsig c (p :: L) = linc c p + lsig c L := by
  obtain ⟨a, b⟩ := p
  cases b <;> simp [lsig, linc, List.sum_cons]

theorem lsig_singleton' (c : α → ℤ) (p : α × Bool) : lsig c [p] = linc c p := by
  rw [lsig_cons', lsig_nil', add_zero]

theorem running_cons' (c : α → ℤ) (i : ℤ) (p : α × Bool) (L : List (α × Bool)) :
    running c i (p :: L) = i :: running c (i + linc c p) L := by
  obtain ⟨a, b⟩ := p
  cases b
  · show i :: running c (i - c a) L = i :: running c (i + -c a) L
    rfl
  · rfl

theorem running_nil' (c : α → ℤ) (i : ℤ) : running c i ([] : List (α × Bool)) = [i] := rfl

theorem running_singleton' (c : α → ℤ) (i : ℤ) (p : α × Bool) :
    running c i [p] = [i, i + linc c p] := by
  rw [running_cons', running_nil']

theorem lsig_mem_running (c : α → ℤ) (i : ℤ) (L : List (α × Bool)) :
    i + lsig c L ∈ running c i L := by
  induction L generalizing i with
  | nil => rw [lsig_nil', add_zero, running_nil']; exact List.mem_singleton.mpr rfl
  | cons p L ih =>
    rw [running_cons', lsig_cons']
    refine List.mem_cons_of_mem _ ?_
    rw [show i + (linc c p + lsig c L) = (i + linc c p) + lsig c L from by ring]
    exact ih (i + linc c p)

theorem running_append' (c : α → ℤ) (i : ℤ) (L₁ L₂ : List (α × Bool)) :
    running c i (L₁ ++ L₂) = running c i L₁ ++ (running c (i + lsig c L₁) L₂).tail := by
  induction L₁ generalizing i with
  | nil =>
    rw [List.nil_append, lsig_nil', add_zero, running_nil', List.singleton_append,
      running_eq_cons_tail]
  | cons p L₁ ih =>
    obtain ⟨a, b⟩ := p
    have hlv : (i + linc c (a, b)) + lsig c L₁ = i + (linc c (a, b) + lsig c L₁) := by ring
    rw [List.cons_append, running_cons', ih (i + linc c (a, b)), lsig_cons', running_cons',
      hlv, List.cons_append]

theorem running_snoc (c : α → ℤ) (i : ℤ) (L : List (α × Bool)) (p : α × Bool) :
    running c i (L ++ [p]) = running c i L ++ [i + lsig c (L ++ [p])] := by
  rw [running_append', running_singleton', lsig_append', lsig_singleton', List.tail_cons]
  rw [show (i + lsig c L) + linc c p = i + (lsig c L + linc c p) from by ring]

theorem lsig_dropLast_mem_running (c : α → ℤ) {L : List (α × Bool)} (h : L ≠ []) :
    lsig c L.dropLast ∈ running c 0 L := by
  rw [← List.dropLast_append_getLast h, running_snoc]
  refine List.mem_append_left _ ?_
  simpa using lsig_mem_running c 0 L.dropLast

theorem lsig_eq_lsig_dropLast_add (c : α → ℤ) {L : List (α × Bool)} (h : L ≠ []) :
    lsig c L = lsig c L.dropLast + linc c (L.getLast h) := by
  conv_lhs => rw [← List.dropLast_append_getLast h]
  rw [lsig_append', lsig_singleton']

/-! ## 2. Decorations -/

theorem decor_cons' (c : α → ℤ) (i : ℤ) (p : α × Bool) (L : List (α × Bool)) :
    decor c i (p :: L) =
      ((p.1, if p.2 then i else i - c p.1), p.2) :: decor c (i + linc c p) L := by
  obtain ⟨a, b⟩ := p
  cases b
  · show ((a, i - c a), false) :: decor c (i - c a) L =
        ((a, i - c a), false) :: decor c (i + linc c (a, false)) L
    rw [show linc c (a, false) = -c a from rfl, show i + -c a = i - c a from by ring]
  · rfl

theorem decor_singleton' (c : α → ℤ) (i : ℤ) (p : α × Bool) :
    decor c i [p] = [((p.1, if p.2 then i else i - c p.1), p.2)] := by
  rw [decor_cons', decor]

theorem decor_append' (c : α → ℤ) (i : ℤ) (L₁ L₂ : List (α × Bool)) :
    decor c i (L₁ ++ L₂) = decor c i L₁ ++ decor c (i + lsig c L₁) L₂ := by
  induction L₁ generalizing i with
  | nil => rw [List.nil_append, lsig_nil', add_zero, decor, List.nil_append]
  | cons p L₁ ih =>
    rw [List.cons_append, decor_cons', decor_cons', ih (i + linc c p), lsig_cons',
      show (i + linc c p) + lsig c L₁ = i + (linc c p + lsig c L₁) from by ring,
      List.cons_append]

/-! ## 3. Reduced words -/

theorem FreeGroup.IsReduced.append_singleton' {L : List (α × Bool)} {p : α × Bool}
    (hL : FreeGroup.IsReduced L)
    (hj : ∀ q ∈ L.getLast?, ¬ (q.1 = p.1 ∧ q.2 = !p.2)) :
    FreeGroup.IsReduced (L ++ [p]) := by
  show List.IsChain _ (L ++ [p])
  refine List.IsChain.append hL FreeGroup.IsReduced.singleton ?_
  intro x hx y hy hxy
  simp only [List.head?_singleton, Option.mem_some_iff] at hy
  subst hy
  by_contra hc
  exact hj x hx ⟨hxy, Bool.eq_not_iff.mpr hc⟩

theorem wordOf_mk_of_isReduced {L : List (α × Bool)} (h : FreeGroup.IsReduced L) :
    wordOf (FreeGroup.mk L) = L := by
  classical
  show @FreeGroup.toWord α (Classical.decEq α) (FreeGroup.mk L) = L
  rw [FreeGroup.toWord_mk]
  exact FreeGroup.IsReduced.reduce_eq h

/-! ## 4. Free-group list identities -/

theorem mk_append_true (L : List (α × Bool)) (a : α) :
    FreeGroup.mk (L ++ [(a, true)]) = FreeGroup.mk L * FreeGroup.of a := by
  rw [FreeGroup.of, FreeGroup.mul_mk]

theorem mk_singleton_false (a : α) :
    FreeGroup.mk [(a, false)] = (FreeGroup.of a)⁻¹ := by
  rw [FreeGroup.of, FreeGroup.inv_mk]
  rfl

theorem mk_append_false (L : List (α × Bool)) (a : α) :
    FreeGroup.mk (L ++ [(a, false)]) = FreeGroup.mk L * (FreeGroup.of a)⁻¹ := by
  rw [← mk_singleton_false, FreeGroup.mul_mk]

/-! ## 5. The exploration step -/

/-- A witness for one round of the exploration: the level `lv` carrying the reduced word `word`, a
generator `gen` and a direction `dir`; the round leaves the level `lv` along the traversal of the
window edge `edge` and arrives at the level `tgt`. -/
structure Bwit (α : Type u) where
  lv : ℤ
  gen : α
  dir : Bool
  word : List (α × Bool)

namespace Bwit

variable (c : α → ℤ)

/-- The (undirected) window edge traversed by the step. -/
def edge (p : Bwit α) : α × ℤ := (p.gen, if p.dir then p.lv else p.lv - c p.gen)

/-- The level reached by the step. -/
def tgt (p : Bwit α) : ℤ := if p.dir then p.lv + c p.gen else p.lv - c p.gen

/-- The word carried by the level reached by the step. -/
def newWord (p : Bwit α) : List (α × Bool) := p.word ++ [(p.gen, p.dir)]

/-- The decorated letter of the step. -/
def dec (p : Bwit α) : (α × ℤ) × Bool :=
  ((p.gen, if p.dir then p.lv else p.lv - c p.gen), p.dir)

theorem coverEdge_dec (p : Bwit α) : coverEdge (dec c p) = edge c p := rfl

theorem coverSrc_dec (p : Bwit α) : coverSrc c (dec c p) = p.lv := by
  obtain ⟨lv, gen, dir, word⟩ := p
  cases dir
  · simp only [dec, coverSrc, edge, Bool.false_eq_true, if_false]
    ring
  · simp only [dec, coverSrc, if_true]

theorem coverTgt_dec (p : Bwit α) : coverTgt c (dec c p) = tgt c p := by
  obtain ⟨lv, gen, dir, word⟩ := p
  cases dir <;> rfl

/-- If the last letter of the word of a witness is the inverse of the letter of its step, then the
target level of the step is a level of the walk of that word. -/
theorem tgt_mem_running_of_last (p : Bwit α) (hlv : lsig c p.word = p.lv)
    (hlast : p.word.getLast? = some (p.gen, !p.dir)) : tgt c p ∈ running c 0 p.word := by
  obtain ⟨lv, gen, dir, word⟩ := p
  have hne : word ≠ [] := by
    intro hh; rw [hh] at hlast; simp at hlast
  have hlast' : word.getLast hne = (gen, !dir) := by
    rw [List.getLast?_eq_getLast hne] at hlast
    exact Option.some.inj hlast
  have hlt : lsig c word.dropLast = tgt c ⟨lv, gen, dir, word⟩ := by
    have h := lsig_eq_lsig_dropLast_add c hne
    rw [hlast', hlv] at h
    cases dir
    · simp only [Bool.not_false, linc, tgt, Bool.false_eq_true, if_false, if_true,
        reduceIte] at h ⊢
      omega
    · simp only [Bool.not_true, linc, tgt, Bool.false_eq_true, if_false, if_true,
        reduceIte] at h ⊢
      omega
  rw [← hlt]
  exact lsig_dropLast_mem_running c hne

theorem newWord_lsig (p : Bwit α) (hW : lsig c p.word = p.lv) :
    lsig c (newWord p) = tgt c p := by
  obtain ⟨lv, gen, dir, word⟩ := p
  simp only [newWord, tgt] at hW ⊢
  rw [lsig_append', lsig_singleton', hW]
  cases dir <;> simp only [Bool.false_eq_true, if_false, if_true, linc] <;> ring_nf

theorem newWord_red (p : Bwit α) (hred : FreeGroup.IsReduced p.word)
    (hj : ∀ q, p.word.getLast? = some q → ¬ (q.1 = p.gen ∧ q.2 = !p.dir)) :
    FreeGroup.IsReduced (newWord p) := by
  obtain ⟨lv, gen, dir, word⟩ := p
  refine FreeGroup.IsReduced.append_singleton' hred ?_
  intro q hq
  exact hj q (Option.mem_def.mp hq)

theorem newWord_decor (p : Bwit α) (hW : lsig c p.word = p.lv) :
    decor c 0 (newWord p) = decor c 0 p.word ++ [dec c p] := by
  obtain ⟨lv, gen, dir, word⟩ := p
  simp only [newWord, dec] at hW ⊢
  rw [decor_append', hW, zero_add, decor_singleton']

theorem newWord_running (p : Bwit α) (hW : lsig c p.word = p.lv) :
    running c 0 (newWord p) = running c 0 p.word ++ [tgt c p] := by
  obtain ⟨lv, gen, dir, word⟩ := p
  simp only [newWord, tgt] at hW ⊢
  have key : lv + linc c (gen, dir) = (if dir then lv + c gen else lv - c gen) := by
    cases dir <;> simp only [Bool.false_eq_true, if_false, if_true, linc] <;> ring_nf
  rw [running_snoc, zero_add, lsig_append', lsig_singleton', hW, key]

theorem newWord_class {Wt : ℤ → FreeGroup α} (p : Bwit α)
    (hz : Wt p.lv = FreeGroup.mk p.word)
    (hx : Wt (tgt c p) = FreeGroup.mk (newWord p)) :
    coverClassAt Wt c (edge c p) = 1 := by
  obtain ⟨lv, gen, dir, word⟩ := p
  simp only [edge, tgt, newWord] at hz hx ⊢
  rw [coverClassAt, gaugeMap_of]
  cases dir
  · simp only [Bool.false_eq_true, if_false] at hz hx ⊢
    rw [show (lv - c gen) + c gen = lv from by ring, hz, hx, mk_append_false]
    group
  · simp only [if_true] at hz hx ⊢
    rw [hz, hx, mk_append_true]
    group

/-- The step of the level `coverSrc q` along the traversal `q` has the edge `coverEdge q`. -/
theorem edge_mk_coverSrc (q : (α × ℤ) × Bool) (v : List (α × Bool)) :
    edge c ⟨coverSrc c q, q.1.1, q.2, v⟩ = coverEdge q := by
  obtain ⟨⟨a, i⟩, b⟩ := q
  cases b
  · simp only [edge, coverSrc, coverEdge, Bool.false_eq_true, if_false]
    ring
  · rfl

/-- The step of the level `coverSrc q` along the traversal `q` arrives at `coverTgt q`. -/
theorem tgt_mk_coverSrc (q : (α × ℤ) × Bool) (v : List (α × Bool)) :
    tgt c ⟨coverSrc c q, q.1.1, q.2, v⟩ = coverTgt c q := by
  obtain ⟨⟨a, i⟩, b⟩ := q
  cases b
  · simp only [tgt, coverSrc, coverTgt, Bool.false_eq_true, if_false]
    ring
  · rfl

end Bwit

/-! ## 5. Free-group list identities -/

/-! ## 6. The exploration -/

/-- The existence predicate for one round of the exploration: some assigned level is joined to `x`
by a window edge. -/
def bExists (c : α → ℤ) (lo hi : ℤ) (g : ℤ → Option (List (α × Bool))) (x : ℤ) : Prop :=
  ∃ p : Bwit α, Bwit.edge c p ∈ winE c lo hi ∧ g p.lv = some p.word ∧ x = Bwit.tgt c p

/-- One round of the exploration: assigned levels keep their word, and a level not yet assigned
that is reached by a window edge from an assigned level is assigned the word of the step. -/
noncomputable def bstep (c : α → ℤ) (lo hi : ℤ) (g : ℤ → Option (List (α × Bool))) (x : ℤ) :
    Option (List (α × Bool)) := by
  classical
  exact if g x = none then
    (if h : bExists c lo hi g x then some (Bwit.newWord (Classical.choose h)) else none)
  else g x

/-- The state of the exploration after `n` rounds. -/
noncomputable def bstate (c : α → ℤ) (lo hi : ℤ) (n : ℕ) : ℤ → Option (List (α × Bool)) :=
  (bstep c lo hi)^[n] (fun x => if x = 0 then some [] else none)

theorem bstate_zero (c : α → ℤ) (lo hi : ℤ) :
    bstate c lo hi 0 = fun x => if x = 0 then some [] else none := rfl

theorem bstate_succ (c : α → ℤ) (lo hi : ℤ) (n : ℕ) (x : ℤ) :
    bstate c lo hi (n + 1) x = bstep c lo hi (bstate c lo hi n) x :=
  congrFun (Function.iterate_succ_apply' (bstep c lo hi) n
    (fun x => if x = 0 then some [] else none)) x

theorem bstep_of_some {c : α → ℤ} {lo hi : ℤ} {g : ℤ → Option (List (α × Bool))} {x : ℤ}
    {v : List (α × Bool)} (h : g x = some v) : bstep c lo hi g x = some v := by
  classical
  unfold bstep
  rw [h]
  simp

theorem bstep_eq_some_of_exists {c : α → ℤ} {lo hi : ℤ} {g : ℤ → Option (List (α × Bool))}
    {x : ℤ} (hx : g x = none) (h : bExists c lo hi g x) :
    bstep c lo hi g x = some (Bwit.newWord (Classical.choose h)) := by
  classical
  unfold bstep
  rw [hx]
  simp only [if_true]
  rw [dif_pos h]

theorem bstep_eq_none_of_not {c : α → ℤ} {lo hi : ℤ} {g : ℤ → Option (List (α × Bool))}
    {x : ℤ} (hx : g x = none) (h : ¬ bExists c lo hi g x) : bstep c lo hi g x = none := by
  classical
  unfold bstep
  rw [hx]
  simp only [if_true]
  rw [dif_neg h]

theorem bstep_ne_none_of_wit {c : α → ℤ} {lo hi : ℤ} {g : ℤ → Option (List (α × Bool))}
    {p : Bwit α} (hE : Bwit.edge c p ∈ winE c lo hi) (hW : g p.lv = some p.word) :
    bstep c lo hi g (Bwit.tgt c p) ≠ none := by
  classical
  by_cases hx : g (Bwit.tgt c p) = none
  · exact ne_of_eq_of_ne (bstep_eq_some_of_exists hx ⟨p, hE, hW, rfl⟩) (by simp)
  · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hx
    exact ne_of_eq_of_ne (bstep_of_some hv) (by simp)

theorem bstate_succ_of_some {c : α → ℤ} {lo hi : ℤ} {n : ℕ} {x : ℤ} {v : List (α × Bool)}
    (h : bstate c lo hi n x = some v) : bstate c lo hi (n + 1) x = some v := by
  rw [bstate_succ]
  exact bstep_of_some h

theorem bstate_mono {c : α → ℤ} {lo hi : ℤ} {n m : ℕ} (hnm : n ≤ m) {x : ℤ}
    {v : List (α × Bool)} (h : bstate c lo hi n x = some v) :
    bstate c lo hi m x = some v := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact bstate_succ_of_some ih

/-! ## 7. The bounded level set -/

variable [Fintype α] [DecidableEq α]

noncomputable def lvBound (c : α → ℤ) : ℕ :=
  (Finset.univ : Finset α).sup (fun a => (c a).natAbs)

theorem natAbs_le_lvBound (c : α → ℤ) (a : α) : (c a).natAbs ≤ lvBound c := by
  rw [lvBound]
  exact Finset.le_sup (s := (Finset.univ : Finset α)) (f := fun a => (c a).natAbs)
    (Finset.mem_univ a)

theorem abs_le_lvBound (c : α → ℤ) (a : α) :
    -(((lvBound c : ℕ)) : ℤ) ≤ c a ∧ c a ≤ ((lvBound c : ℕ) : ℤ) := by
  have h := natAbs_le_lvBound c a
  have h' : (((c a).natAbs : ℕ) : ℤ) ≤ ((lvBound c : ℕ) : ℤ) := by exact_mod_cast h
  have h1 : c a ≤ (((c a).natAbs : ℕ) : ℤ) := Int.le_natAbs
  have h2 : -(((c a).natAbs : ℕ) : ℤ) ≤ c a := by
    have h3 := Int.le_natAbs (a := -c a)
    rw [Int.natAbs_neg] at h3
    linarith
  constructor <;> linarith

noncomputable def bSet (c : α → ℤ) (lo hi : ℤ) : Finset ℤ :=
  insert 0 (Finset.Icc (lo - ((lvBound c : ℕ) : ℤ)) (hi + ((lvBound c : ℕ) : ℤ)))

noncomputable def NW (c : α → ℤ) (lo hi : ℤ) : ℕ := (bSet c lo hi).card + 1

theorem bSet_card_eq (c : α → ℤ) (lo hi : ℤ) : (bSet c lo hi).card + 1 = NW c lo hi := rfl

noncomputable def bA (c : α → ℤ) (lo hi : ℤ) (n : ℕ) : Finset ℤ :=
  (bSet c lo hi).filter (fun x => bstate c lo hi n x ≠ none)

theorem mem_bA {c : α → ℤ} {lo hi : ℤ} {n : ℕ} {x : ℤ} :
    x ∈ bA c lo hi n ↔ x ∈ bSet c lo hi ∧ bstate c lo hi n x ≠ none := by
  rw [bA, Finset.mem_filter]

theorem bA_subset (c : α → ℤ) (lo hi : ℤ) (n : ℕ) : bA c lo hi n ⊆ bSet c lo hi :=
  fun _ hx => (mem_bA.mp hx).1

/-- **The target level of a window-edge step stays in the bounded set.** -/
theorem Bwit.tgt_mem_bSet {c : α → ℤ} {lo hi : ℤ} {p : Bwit α}
    (hE : Bwit.edge c p ∈ winE c lo hi) : Bwit.tgt c p ∈ bSet c lo hi := by
  obtain ⟨lv, gen, dir, word⟩ := p
  obtain ⟨hD1, hD2⟩ := abs_le_lvBound c gen
  cases dir
  · simp only [Bwit.edge, Bwit.tgt, bSet, Finset.mem_insert, Finset.mem_Icc, winE,
      Set.mem_setOf_eq, Bool.false_eq_true, if_false] at hE ⊢
    right
    constructor <;> omega
  · simp only [Bwit.edge, Bwit.tgt, bSet, Finset.mem_insert, Finset.mem_Icc, winE,
      Set.mem_setOf_eq, if_true] at hE ⊢
    right
    constructor <;> omega

theorem bstate_mem_bSet (c : α → ℤ) (lo hi : ℤ) (m : ℕ) {x : ℤ}
    (h : bstate c lo hi m x ≠ none) : x ∈ bSet c lo hi := by
  classical
  induction m with
  | zero =>
    rw [bstate_zero] at h
    have hx0 : x = 0 := by
      by_contra hx
      exact h (by simp [hx])
    rw [hx0]
    exact Finset.mem_insert_self 0 _
  | succ k ih =>
    rw [bstate_succ] at h
    by_cases hk : bstate c lo hi k x = none
    · have hB : bExists c lo hi (bstate c lo hi k) x := by
        by_contra hB
        rw [bstep_eq_none_of_not hk hB] at h
        exact h rfl
      obtain ⟨hE, -, hT⟩ := Classical.choose_spec hB
      rw [hT]
      exact Bwit.tgt_mem_bSet hE
    · exact ih hk

theorem bA_zero (c : α → ℤ) (lo hi : ℤ) : bA c lo hi 0 = {0} := by
  classical
  ext x
  rw [mem_bA, Finset.mem_singleton]
  constructor
  · rintro ⟨-, hx⟩
    by_contra hne
    exact hx (by rw [bstate_zero]; simp [hne])
  · rintro rfl
    exact ⟨Finset.mem_insert_self 0 _, by rw [bstate_zero]; simp⟩

theorem bA_mono (c : α → ℤ) (lo hi : ℤ) (n : ℕ) : bA c lo hi n ⊆ bA c lo hi (n + 1) := by
  classical
  intro x hx
  rw [mem_bA] at hx ⊢
  refine ⟨hx.1, ?_⟩
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hx.2
  rw [bstate_succ_of_some hv]
  simp

/-- If the assigned sets of two consecutive rounds agree, the states agree. -/
theorem bstate_eq_of_bA_eq {c : α → ℤ} {lo hi : ℤ} {n : ℕ}
    (h : bA c lo hi (n + 1) = bA c lo hi n) :
    bstate c lo hi (n + 1) = bstate c lo hi n := by
  classical
  funext x
  by_cases hx : bstate c lo hi n x = none
  · rw [hx]
    by_contra hcon
    have hmem : x ∈ bA c lo hi (n + 1) := by
      rw [mem_bA]
      exact ⟨bstate_mem_bSet c lo hi (n + 1) hcon, hcon⟩
    rw [h, mem_bA] at hmem
    exact hmem.2 hx
  · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hx
    rw [bstate_succ_of_some hv, hv]

/-- The exploration stabilises: there is a round after which the state does not change. -/
theorem exists_stable (c : α → ℤ) (lo hi : ℤ) :
    ∃ n, n + 1 ≤ NW c lo hi ∧ bA c lo hi (n + 1) = bA c lo hi n := by
  classical
  by_contra hcon
  push_neg at hcon
  have hcard : ∀ m, m ≤ NW c lo hi → 1 + m ≤ (bA c lo hi m).card := by
    intro m hm
    induction m with
    | zero => rw [bA_zero]; simp
    | succ k ih =>
      have hk : k ≤ NW c lo hi := by omega
      have hkn : k + 1 ≤ NW c lo hi := by omega
      have hsub := bA_mono c lo hi k
      have hne : bA c lo hi k ≠ bA c lo hi (k + 1) := fun he => hcon k hkn he.symm
      have hlt : (bA c lo hi k).card < (bA c lo hi (k + 1)).card :=
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
      have := ih hk
      omega
  have h1 := hcard (NW c lo hi) le_rfl
  have h2 : (bA c lo hi (NW c lo hi)).card ≤ (bSet c lo hi).card :=
    Finset.card_le_card (bA_subset c lo hi _)
  have h3 := bSet_card_eq c lo hi
  omega

theorem bstate_stable (c : α → ℤ) (lo hi : ℤ) :
    ∃ n, n + 1 ≤ NW c lo hi ∧ bstate c lo hi (n + 1) = bstate c lo hi n := by
  obtain ⟨n, hn, hA⟩ := exists_stable c lo hi
  exact ⟨n, hn, bstate_eq_of_bA_eq hA⟩

theorem bstate_const {c : α → ℤ} {lo hi : ℤ} {n : ℕ}
    (heq : bstate c lo hi (n + 1) = bstate c lo hi n) :
    ∀ m, n ≤ m → bstate c lo hi m = bstate c lo hi n := by
  intro m hm
  refine Nat.le_induction rfl ?_ m hm
  intro k _ ih
  rw [funext (fun x => bstate_succ c lo hi k x), ih,
    funext (fun x => (bstate_succ c lo hi n x).symm)]
  exact heq

/-- The state after `NW c lo hi` rounds is a fixed point of the exploration step. -/
theorem bstep_fixed (c : α → ℤ) (lo hi : ℤ) :
    bstep c lo hi (bstate c lo hi (NW c lo hi)) = bstate c lo hi (NW c lo hi) := by
  obtain ⟨n, _, heq⟩ := bstate_stable c lo hi
  have hNW : bstate c lo hi (NW c lo hi) = bstate c lo hi n :=
    bstate_const heq (NW c lo hi) (by omega)
  rw [hNW, funext (fun x => (bstate_succ c lo hi n x).symm)]
  exact heq

/-! ## 8. The gauge -/

/-- The gauge produced by the exploration: the level `i` carries the word the fixed point assigns to
it (the empty word if it is not assigned). -/
noncomputable def treeGauge (c : α → ℤ) (lo hi : ℤ) : ℤ → FreeGroup α :=
  fun x => FreeGroup.mk ((bstate c lo hi (NW c lo hi) x).getD [])

theorem treeGauge_of {c : α → ℤ} {lo hi : ℤ} {n : ℕ} {i : ℤ} {L : List (α × Bool)}
    (h : bstate c lo hi n i = some L) (hn : n ≤ NW c lo hi) :
    treeGauge c lo hi i = FreeGroup.mk L := by
  have hm := bstate_mono hn h
  simp [treeGauge, hm]

/-- The invariant maintained by the exploration. -/
def Inv (c : α → ℤ) (lo hi : ℤ) (Wt : ℤ → FreeGroup α) (n : ℕ) : Prop :=
  bstate c lo hi n 0 = some [] ∧
  ∀ i L, bstate c lo hi n i = some L →
    lsig c L = i ∧ FreeGroup.IsReduced L ∧
    (∀ q ∈ decor c 0 L, coverEdge q ∈ winE c lo hi) ∧
    (∀ l ∈ running c 0 L, bstate c lo hi n l ≠ none) ∧
    (∀ q ∈ decor c 0 L, coverClassAt Wt c (coverEdge q) = 1)

theorem Inv_zero (c : α → ℤ) (lo hi : ℤ) (Wt : ℤ → FreeGroup α) : Inv c lo hi Wt 0 := by
  classical
  refine ⟨?_, ?_⟩
  · rw [bstate_zero]; simp
  · intro i L h
    have h0 : i = 0 ∧ L = [] := by
      by_cases hi : i = 0
      · subst hi; simpa [bstate_zero] using h
      · rw [bstate_zero] at h; simp [hi] at h
    obtain ⟨rfl, rfl⟩ := h0
    refine ⟨lsig_nil' c, FreeGroup.IsReduced.nil, ?_, ?_, ?_⟩
    · intro q hq; simp [decor] at hq
    · intro l hl; rw [running_nil'] at hl; rw [List.mem_singleton] at hl; subst hl
      rw [bstate_zero]; simp
    · intro q hq; simp [decor] at hq

/-- The components of the invariant for the word produced by a discovering step. -/
theorem Inv_newWord {c : α → ℤ} {lo hi : ℤ} {n : ℕ} {p : Bwit α} {x : ℤ}
    (hn : n + 1 ≤ NW c lo hi) (hInv : Inv c lo hi (treeGauge c lo hi) n)
    (hT : x = Bwit.tgt c p)
    (hE : Bwit.edge c p ∈ winE c lo hi) (hW : bstate c lo hi n p.lv = some p.word)
    (hnew : bstate c lo hi n x = none)
    (hstep : bstate c lo hi (n + 1) x = some (Bwit.newWord p)) :
    lsig c (Bwit.newWord p) = x ∧ FreeGroup.IsReduced (Bwit.newWord p) ∧
      (∀ q ∈ decor c 0 (Bwit.newWord p), coverEdge q ∈ winE c lo hi) ∧
      (∀ l ∈ running c 0 (Bwit.newWord p), bstate c lo hi (n + 1) l ≠ none) ∧
      (∀ q ∈ decor c 0 (Bwit.newWord p),
        coverClassAt (treeGauge c lo hi) c (coverEdge q) = 1) := by
  classical
  subst hT
  have hrest := hInv.2
  obtain ⟨ihlsig, ihred, ihE, ihRun, ihcl⟩ := hrest p.lv p.word hW
  have hlast : ∀ q, p.word.getLast? = some q → ¬ (q.1 = p.gen ∧ q.2 = !p.dir) := by
    intro q hq hcon
    rw [show q = (p.gen, !p.dir) from by
      cases q; simp only [Prod.mk.injEq]; exact ⟨hcon.1, hcon.2⟩] at hq
    have hmem := Bwit.tgt_mem_running_of_last (c := c) p ihlsig hq
    exact ihRun (Bwit.tgt c p) hmem hnew
  refine ⟨Bwit.newWord_lsig c p ihlsig, Bwit.newWord_red p ihred hlast, ?_, ?_, ?_⟩
  · intro q hq
    rw [Bwit.newWord_decor c p ihlsig] at hq
    rcases List.mem_append.mp hq with hq | hq
    · exact ihE q hq
    · rw [List.mem_singleton] at hq
      rw [hq, Bwit.coverEdge_dec c p]
      exact hE
  · intro l hl
    rw [Bwit.newWord_running c p ihlsig] at hl
    rcases List.mem_append.mp hl with hl | hl
    · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (ihRun l hl)
      rw [bstate_succ_of_some hv]; simp
    · rw [List.mem_singleton] at hl
      rw [hl, hstep]; simp
  · intro q hq
    rw [Bwit.newWord_decor c p ihlsig] at hq
    rcases List.mem_append.mp hq with hq | hq
    · exact ihcl q hq
    · rw [List.mem_singleton] at hq
      rw [hq, Bwit.coverEdge_dec c p]
      exact Bwit.newWord_class c p
        (treeGauge_of hW (by omega)) (treeGauge_of hstep hn)

theorem Inv_succ {c : α → ℤ} {lo hi : ℤ} {n : ℕ} (hn : n + 1 ≤ NW c lo hi)
    (hInv : Inv c lo hi (treeGauge c lo hi) n) :
    Inv c lo hi (treeGauge c lo hi) (n + 1) := by
  classical
  have h0 := hInv.1
  have hrest := hInv.2
  refine ⟨?_, ?_⟩
  · rw [bstate_succ]
    exact bstep_of_some h0
  · intro x Lx hx
    by_cases hgx : bstate c lo hi n x = none
    · have hB : bExists c lo hi (bstate c lo hi n) x := by
        by_contra hB
        rw [bstate_succ, bstep_eq_none_of_not hgx hB] at hx
        exact absurd hx (by simp)
      obtain ⟨hE, hW, hT⟩ := Classical.choose_spec hB
      have hLx : Lx = Bwit.newWord (Classical.choose hB) := by
        rw [bstate_succ, bstep_eq_some_of_exists hgx hB] at hx
        exact (Option.some.inj hx).symm
      rw [hLx]
      exact Inv_newWord hn hInv hT hE hW hgx
        (by rw [bstate_succ]; exact bstep_eq_some_of_exists hgx hB)
    · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hgx
      have hLx : Lx = v := by
        rw [bstate_succ_of_some hv] at hx
        exact (Option.some.inj hx).symm
      obtain ⟨ihlsig, ihred, ihE, ihRun, ihcl⟩ := hrest x v hv
      rw [hLx]
      exact ⟨ihlsig, ihred, ihE, fun l hl => by
          obtain ⟨v', hv'⟩ := Option.ne_none_iff_exists'.mp (ihRun l hl)
          rw [bstate_succ_of_some hv']; simp, ihcl⟩

theorem Inv_all (c : α → ℤ) (lo hi : ℤ) :
    ∀ n, n ≤ NW c lo hi → Inv c lo hi (treeGauge c lo hi) n := by
  intro n
  induction n with
  | zero => intro _; exact Inv_zero c lo hi _
  | succ m ih => intro hm; exact Inv_succ hm (ih (by omega))

/-! ## 9. Coverage -/

/-- At the fixed point, the assigned set is closed under window edges. -/
theorem bstate_closed (c : α → ℤ) (lo hi : ℤ) {q : (α × ℤ) × Bool}
    (hq : coverEdge q ∈ winE c lo hi)
    (hv : bstate c lo hi (NW c lo hi) (coverSrc c q) ≠ none) :
    bstate c lo hi (NW c lo hi) (coverTgt c q) ≠ none := by
  obtain ⟨v, hv'⟩ := Option.ne_none_iff_exists'.mp hv
  have h1 : Bwit.edge c ⟨coverSrc c q, q.1.1, q.2, v⟩ ∈ winE c lo hi := by
    rw [Bwit.edge_mk_coverSrc]; exact hq
  have h3 := bstep_ne_none_of_wit (c := c) (lo := lo) (hi := hi)
    (g := bstate c lo hi (NW c lo hi)) h1 hv'
  rw [bstep_fixed c lo hi, Bwit.tgt_mk_coverSrc] at h3
  exact h3

theorem reach_of_closed (c : α → ℤ) (lo hi : ℤ) (L : List (α × Bool)) (i₀ : ℤ)
    (hL : ∀ q ∈ decor c i₀ L, coverEdge q ∈ winE c lo hi)
    (h0 : bstate c lo hi (NW c lo hi) i₀ ≠ none) :
    ∀ l ∈ running c i₀ L, bstate c lo hi (NW c lo hi) l ≠ none := by
  classical
  induction L generalizing i₀ with
  | nil =>
    intro l hl
    rw [running_nil'] at hl
    rw [List.mem_singleton] at hl
    subst hl
    exact h0
  | cons p L ih =>
    intro l hl
    rw [running_cons'] at hl
    rcases List.mem_cons.mp hl with rfl | hl'
    · exact h0
    · have hstep : bstate c lo hi (NW c lo hi) (i₀ + linc c p) ≠ none := by
        have hq : ((p.1, if p.2 then i₀ else i₀ - c p.1), p.2) ∈ decor c i₀ (p :: L) := by
          rw [decor_cons']; exact List.mem_cons_self ..
        have he : coverEdge ((p.1, if p.2 then i₀ else i₀ - c p.1), p.2) ∈ winE c lo hi :=
          hL _ hq
        have hs : coverSrc c ((p.1, if p.2 then i₀ else i₀ - c p.1), p.2) = i₀ := by
          cases hp : p.2 <;> simp only [coverSrc, hp, Bool.false_eq_true, if_false, if_true]
          ring
        have ht : coverTgt c ((p.1, if p.2 then i₀ else i₀ - c p.1), p.2) = i₀ + linc c p := by
          cases hp : p.2 <;> simp only [coverTgt, linc, hp, Bool.false_eq_true, if_false,
            if_true]
          ring
        have := bstate_closed c lo hi he (by rw [hs]; exact h0)
        rwa [ht] at this
      exact ih (i₀ + linc c p) (fun q hq => hL q (by
        rw [decor_cons']; exact List.mem_cons_of_mem _ hq)) hstep l hl'

/-- Every level of the window is assigned at the fixed point. -/
theorem assigned_of_window (c : α → ℤ) (lo hi : ℤ)
    (hreach : ∀ i : ℤ, lo ≤ i → i ≤ hi → ∃ w : FreeGroup α,
      cohom c w = Multiplicative.ofAdd i ∧
      ∀ q ∈ decor c 0 (wordOf w), coverEdge q ∈ winE c lo hi)
    {i : ℤ} (hi1 : lo ≤ i) (hi2 : i ≤ hi) : bstate c lo hi (NW c lo hi) i ≠ none := by
  classical
  obtain ⟨w, hw, hwin⟩ := hreach i hi1 hi2
  have hlsig : lsig c (wordOf w) = i := by
    have h1 : cohom c (FreeGroup.mk (wordOf w)) =
        Multiplicative.ofAdd (lsig c (wordOf w)) := cohom_mk c (wordOf w)
    rw [mk_wordOf] at h1
    exact Multiplicative.ofAdd.injective (h1.symm.trans hw)
  have hmem : i ∈ running c 0 (wordOf w) := by
    have := lsig_mem_running c 0 (wordOf w)
    rwa [zero_add, hlsig] at this
  refine reach_of_closed c lo hi (wordOf w) 0 hwin ?_ i hmem
  rw [(Inv_all c lo hi (NW c lo hi) le_rfl).1]
  simp

theorem exists_treeGauge {α : Type*} [Fintype α] [DecidableEq α] (c : α → ℤ) (lo hi : ℤ)
    (hreach : ∀ i : ℤ, lo ≤ i → i ≤ hi → ∃ w : FreeGroup α,
      Work.OROneRel.cohom c w = Multiplicative.ofAdd i ∧
      ∀ q ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf w),
        Work.OROneRel.coverEdge q ∈ Work.OROneRel.winE c lo hi) :
    ∃ Wt : ℤ → FreeGroup α, Wt 0 = 1 ∧
      (∀ i : ℤ, lo ≤ i → i ≤ hi →
        Work.OROneRel.cohom c (Wt i) = Multiplicative.ofAdd i) ∧
      (∀ i : ℤ, lo ≤ i → i ≤ hi →
        ∀ q ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf (Wt i)),
          Work.OROneRel.coverEdge q ∈ Work.OROneRel.winTree Wt c lo hi) := by
  classical
  refine ⟨treeGauge c lo hi, ?_, ?_, ?_⟩
  · have h := (Inv_all c lo hi (NW c lo hi) le_rfl).1
    simp only [treeGauge, h, Option.getD_some]
    exact FreeGroup.one_eq_mk.symm
  · intro i hi1 hi2
    have hass := assigned_of_window c lo hi hreach hi1 hi2
    obtain ⟨L, hL⟩ := Option.ne_none_iff_exists'.mp hass
    have hinv := (Inv_all c lo hi (NW c lo hi) le_rfl).2 i L hL
    rw [treeGauge_of hL le_rfl, cohom_mk, hinv.1]
  · intro i hi1 hi2 q hq
    have hass := assigned_of_window c lo hi hreach hi1 hi2
    obtain ⟨L, hL⟩ := Option.ne_none_iff_exists'.mp hass
    have hinv := (Inv_all c lo hi (NW c lo hi) le_rfl).2 i L hL
    obtain ⟨hlsig, hred, hE, -, hcl⟩ := hinv
    rw [treeGauge_of hL le_rfl, wordOf_mk_of_isReduced hred] at hq
    exact mem_winTree.mpr ⟨hE q hq, hcl q hq⟩

end Work.OROneRel
