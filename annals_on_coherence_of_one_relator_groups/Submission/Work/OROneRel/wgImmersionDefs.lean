/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# The `ℤ`-cover walk as a graph immersion: the toolkit

Fix `vs : List ℤ` (the levels of a walk, of length `n + 1`) and `lbl : List (FreeGroup α)` (its labels,
of length `n`).  The data of the walk is a *labelled graph* `X`: its vertices are the levels `ℤ`, and
its `j`-th edge (`j < n`) runs from the level `vs_j` to the level `vs_{j+1}` and carries the label
`lbl_j`.  The *first-arrival gauge* `walkGauge vs lbl` (`gauge_walk_defs`) is the spanning tree of `X`
obtained by keeping the edges that arrive at a new level.

This file sets up the vocabulary in which the immersion theorem
`Work.OROneRel.walkGauge_stepWord_injective_immersion` is proved.

* A *traversal* of an edge is a pair `p : ℕ × Bool`; `p.2 = true` means the edge `p.1` is traversed
  from `wgSig p.1` to `wgTau p.1`, and `p.2 = false` from `wgTau p.1` to `wgSig p.1`.  `wgFlip`
  reverses a traversal.
* `wgPath vs u γ v` says that the list `γ` of traversals is a walk in `X` from the level `u` to the
  level `v`.
* `wgWord vs lbl γ` is the image in `FreeGroup α` of that walk, i.e. the product of the labels of
  its traversals: it lands in the target free group.
* `wgT vs lbl` indexes the non-tree edges (`j < n` with `wgTree vs j` false).  `wgMu vs lbl γ` is the
  image of the walk in the free group on the non-tree edges, the tree edges being sent to `1`: it
  lands in the fundamental group of the domain graph.

The two maps `wgWord` and `wgMu` are the two sides of the immersion theorem: `wgWord` is the map
whose injectivity is wanted, and `wgMu` is the retraction that detects non-triviality of a walk.
-/
import Mathlib
import Submission.Work.OROneRel.gauge_levels_bound

namespace Work.OROneRel

universe u

variable {α : Type u}

attribute [local instance] Classical.propDecidable

/-! ## Signed letters -/

/-- The element of `FreeGroup α` carried by a signed generator: `(a, true) ↦ of a` and
`(a, false) ↦ (of a)⁻¹`. -/
def sletter (a : α) (b : Bool) : FreeGroup α := if b then FreeGroup.of a else (FreeGroup.of a)⁻¹

@[simp] theorem sletter_true (a : α) : sletter a true = FreeGroup.of a := rfl

@[simp] theorem sletter_false (a : α) : sletter a false = (FreeGroup.of a)⁻¹ := rfl

@[simp] theorem sletter_swap (a : α) (b : Bool) : sletter a (!b) = (sletter a b)⁻¹ := by
  cases b <;> simp

/-- A generator of a free group is not the inverse of itself: a free group has no element of order
two. -/
theorem of_ne_inv_self (a : α) : FreeGroup.of a ≠ (FreeGroup.of a)⁻¹ := by
  classical
  intro h
  have hw : ([(a, true)] : List (α × Bool)) = [(a, false)] := by
    simpa [FreeGroup.toWord_inv, FreeGroup.invRev] using congrArg FreeGroup.toWord h
  simp at hw

/-! ## The step data of the walk -/

/-- The source level of the `j`-th step of the walk. -/
def wgSig (vs : List ℤ) (j : ℕ) : ℤ := vs.getD j 0

/-- The target level of the `j`-th step of the walk. -/
def wgTau (vs : List ℤ) (j : ℕ) : ℤ := vs.getD (j + 1) 0

/-- The label of the `j`-th step of the walk. -/
def wgLbl (lbl : List (FreeGroup α)) (j : ℕ) : FreeGroup α := lbl.getD j 1

/-- The `j`-th step is a *first-arrival* (tree) step: its target level is not among `vs_0, …, vs_j`,
so the first-arrival gauge crosses it. -/
def wgTree (vs : List ℤ) (j : ℕ) : Prop := wgTau vs j ∉ vs.take (j + 1)

/-- The `j`-th step of the walk, as a `WalkStep`. -/
noncomputable def wgStep (vs : List ℤ) (lbl : List (FreeGroup α)) (j : ℕ) : WalkStep α :=
  (mkSteps vs lbl).getD j (defaultStep α)

/-! ## The domain graph: walks, labels, and the fundamental group of the domain -/

/-- Reading a traversal at its tail.  A traversal `(j, true)` starts at the level `vs_j`, and
`(j, false)` at the level `vs_{j+1}`. -/
def wgTail (vs : List ℤ) (p : ℕ × Bool) : ℤ :=
  if p.2 then vs.getD p.1 0 else vs.getD (p.1 + 1) 0

/-- Reading a traversal at its head. -/
def wgHead (vs : List ℤ) (p : ℕ × Bool) : ℤ :=
  if p.2 then vs.getD (p.1 + 1) 0 else vs.getD p.1 0

/-- The reverse traversal of an edge. -/
def wgFlip (p : ℕ × Bool) : ℕ × Bool := (p.1, !p.2)

/-- The reverse of a walk. -/
def wgRev (γ : List (ℕ × Bool)) : List (ℕ × Bool) := γ.reverse.map wgFlip

/-- The label carried by a traversal. -/
def wgLblP (lbl : List (FreeGroup α)) (p : ℕ × Bool) : FreeGroup α :=
  if p.2 then wgLbl lbl p.1 else (wgLbl lbl p.1)⁻¹

/-- `wgPath vs u γ v` asserts that `γ` is a walk in the domain graph from the level `u` to the level
`v`. -/
def wgPath (vs : List ℤ) : ℤ → List (ℕ × Bool) → ℤ → Prop
  | u, [], v => u = v
  | u, p :: ps, v => u = wgTail vs p ∧ wgPath vs (wgHead vs p) ps v

/-- The image of a walk in the target free group: the product of the labels of its traversals. -/
def wgWord (vs : List ℤ) (lbl : List (FreeGroup α)) (γ : List (ℕ × Bool)) : FreeGroup α :=
  (γ.map (wgLblP lbl)).prod

/-- The non-tree edges of the walk graph.  These index the free group that is the fundamental group
of the domain. -/
def wgT (vs : List ℤ) (lbl : List (FreeGroup α)) : Type :=
  {j : ℕ // j < lbl.length ∧ ¬ wgTree vs j}

/-- A tree edge is sent to `1`, a non-tree edge `j` to the corresponding free generator. -/
noncomputable def wgMuGen (vs : List ℤ) (lbl : List (FreeGroup α)) (j : ℕ) :
    FreeGroup (wgT vs lbl) :=
  if h : j < lbl.length ∧ ¬ wgTree vs j then FreeGroup.of ⟨j, h⟩ else 1

/-- The image of a walk in the free group on the non-tree edges. -/
noncomputable def wgMu (vs : List ℤ) (lbl : List (FreeGroup α)) (γ : List (ℕ × Bool)) :
    FreeGroup (wgT vs lbl) :=
  (γ.map fun p => if p.2 then wgMuGen vs lbl p.1 else (wgMuGen vs lbl p.1)⁻¹).prod

/-- The state of the first-arrival machine after `k` steps. -/
noncomputable def wgState (vs : List ℤ) (lbl : List (FreeGroup α)) (k : ℕ) :
    ℤ → Option (FreeGroup α) :=
  runSteps (initState (vs.headD 0)) ((mkSteps vs lbl).take k)

/-! ## The first-arrival tree, as a path -/

/-- The tree path reaching the level `v` after `k` steps of the machine, as a list of traversals.
The level `v` is reached along the edges that discovered new levels on the way; the definition below
reproduces the state machine `runSteps` of the first-arrival gauge at the level of paths. -/
noncomputable def wgTpAux (vs : List ℤ) : ℕ → ℤ → List (ℕ × Bool)
  | 0, _ => []
  | k + 1, v =>
    if wgTree vs k ∧ wgTau vs k = v then wgTpAux vs k (wgSig vs k) ++ [(k, true)]
    else wgTpAux vs k v

/-- The tree path from the base level `vs.headD 0` to the level `v`. -/
noncomputable def wgTp (vs : List ℤ) (lbl : List (FreeGroup α)) (v : ℤ) : List (ℕ × Bool) :=
  wgTpAux vs lbl.length v

/-- The loop of the `j`-th edge of the walk: down the tree to its source, across the edge, and back
up the tree from its target. -/
noncomputable def wgLoop (vs : List ℤ) (lbl : List (FreeGroup α)) (j : ℕ) : List (ℕ × Bool) :=
  wgTp vs lbl (wgSig vs j) ++ [(j, true)] ++ wgRev (wgTp vs lbl (wgTau vs j))

/-! ## Easy structural lemmas -/

@[simp] theorem wgPath_nil {vs : List ℤ} {u v : ℤ} :
    wgPath vs u ([] : List (ℕ × Bool)) v ↔ u = v := Iff.rfl

theorem wgPath_cons {vs : List ℤ} {u v : ℤ} {p : ℕ × Bool} {ps : List (ℕ × Bool)} :
    wgPath vs u (p :: ps) v ↔ u = wgTail vs p ∧ wgPath vs (wgHead vs p) ps v := Iff.rfl

@[simp] theorem wgFlip_flip (p : ℕ × Bool) : wgFlip (wgFlip p) = p := by
  cases p with
  | mk j b => cases b <;> rfl

@[simp] theorem wgTail_flip (vs : List ℤ) (p : ℕ × Bool) :
    wgTail vs (wgFlip p) = wgHead vs p := by
  cases p with
  | mk j b => cases b <;> rfl

@[simp] theorem wgHead_flip (vs : List ℤ) (p : ℕ × Bool) :
    wgHead vs (wgFlip p) = wgTail vs p := by
  cases p with
  | mk j b => cases b <;> rfl

@[simp] theorem wgLblP_flip (lbl : List (FreeGroup α)) (p : ℕ × Bool) :
    wgLblP lbl (wgFlip p) = (wgLblP lbl p)⁻¹ := by
  cases p with
  | mk j b => cases b <;> simp [wgFlip, wgLblP]

/-- A walk can be split at any point. -/
theorem wgPath_append {vs : List ℤ} {u v : ℤ} {γ δ : List (ℕ × Bool)} :
    wgPath vs u (γ ++ δ) v ↔ ∃ w, wgPath vs u γ w ∧ wgPath vs w δ v := by
  induction γ generalizing u with
  | nil => simp [wgPath]
  | cons p ps ih => simp only [List.cons_append, wgPath_cons, ih]; tauto

/-- Consecutive traversals of a walk are contiguous. -/
theorem wgPath_adjacent {vs : List ℤ} {u v : ℤ} {γ δ : List (ℕ × Bool)} {p q : ℕ × Bool}
    (h : wgPath vs u (γ ++ p :: q :: δ) v) : wgHead vs p = wgTail vs q := by
  induction γ generalizing u with
  | nil => simpa [wgPath_cons] using h.2.1
  | cons r rs ih => exact ih h.2

/-- The reverse of a walk is a walk. -/
theorem wgPath_rev {vs : List ℤ} {u v : ℤ} {γ : List (ℕ × Bool)} (h : wgPath vs u γ v) :
    wgPath vs v (wgRev γ) u := by
  induction γ generalizing u v with
  | nil => simpa [wgPath, wgRev] using h.symm
  | cons p ps ih =>
    obtain ⟨h1, h2⟩ := wgPath_cons.mp h
    have hsplit : wgRev (p :: ps) = wgRev ps ++ [wgFlip p] := by simp [wgRev]
    rw [hsplit, wgPath_append]
    refine ⟨wgHead vs p, ih h2, ?_⟩
    rw [wgPath_cons]
    exact ⟨by simp, by simpa [wgPath] using h1.symm⟩

/-- Cancelling a backtrack (`p` followed by its reverse) in a walk leaves a walk. -/
theorem wgPath_cancel_backtrack {vs : List ℤ} {u v : ℤ} {γ δ : List (ℕ × Bool)} {p : ℕ × Bool}
    (h : wgPath vs u (γ ++ p :: wgFlip p :: δ) v) : wgPath vs u (γ ++ δ) v := by
  induction γ generalizing u with
  | nil =>
    obtain ⟨h1, h2⟩ := h
    obtain ⟨-, h3⟩ := wgPath_cons.mp h2
    subst h1
    simpa [wgPath_cons] using h3
  | cons r rs ih => exact wgPath_cons.mpr ⟨h.1, ih h.2⟩

/-- Two consecutive traversals of a walk that are mutually inverse exhibit a backtrack. -/
theorem exists_backtrack_of_getElem_flip {γ : List (ℕ × Bool)} {i : ℕ} (hi : i + 1 < γ.length)
    (h : γ[i + 1] = wgFlip γ[i]) :
    ∃ (γ₁ : List (ℕ × Bool)) (p : ℕ × Bool) (γ₂ : List (ℕ × Bool)),
      γ = γ₁ ++ p :: wgFlip p :: γ₂ := by
  refine ⟨γ.take i, γ[i], γ.drop (i + 2), ?_⟩
  conv_lhs => rw [← List.take_append_drop i γ]
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega), h]

/-- A walk that has a backtrack can be split at it. -/
theorem wgPath_exists_backtrack {vs : List ℤ} {u v : ℤ} {γ : List (ℕ × Bool)}
    (h : wgPath vs u γ v) {i : ℕ} (hi : i + 1 < γ.length)
    (hbt : γ[i + 1] = wgFlip γ[i]) :
    ∃ (γ₁ : List (ℕ × Bool)) (p : ℕ × Bool) (γ₂ : List (ℕ × Bool)),
      γ = γ₁ ++ p :: wgFlip p :: γ₂ :=
  exists_backtrack_of_getElem_flip hi hbt

@[simp] theorem wgWord_nil (vs : List ℤ) (lbl : List (FreeGroup α)) :
    wgWord vs lbl ([] : List (ℕ × Bool)) = 1 := rfl

@[simp] theorem wgWord_singleton (vs : List ℤ) (lbl : List (FreeGroup α)) (p : ℕ × Bool) :
    wgWord vs lbl [p] = wgLblP lbl p := by
  simp [wgWord]

theorem wgWord_append (vs : List ℤ) (lbl : List (FreeGroup α)) (γ δ : List (ℕ × Bool)) :
    wgWord vs lbl (γ ++ δ) = wgWord vs lbl γ * wgWord vs lbl δ := by
  simp [wgWord, List.map_append, List.prod_append]

@[simp] theorem wgRev_nil : (wgRev ([] : List (ℕ × Bool))) = [] := rfl

theorem wgRev_append (γ δ : List (ℕ × Bool)) :
    wgRev (γ ++ δ) = wgRev δ ++ wgRev γ := by
  simp [wgRev]

/-- The image of a reversed walk is the inverse word. -/
theorem wgWord_rev (vs : List ℤ) (lbl : List (FreeGroup α)) (γ : List (ℕ × Bool)) :
    wgWord vs lbl (wgRev γ) = (wgWord vs lbl γ)⁻¹ := by
  induction γ with
  | nil => simp
  | cons p ps ih =>
    have hsplit : wgRev (p :: ps) = wgRev ps ++ [wgFlip p] := by simp [wgRev]
    rw [hsplit, wgWord_append, ih, wgWord_singleton, wgLblP_flip,
      show (p :: ps : List (ℕ × Bool)) = [p] ++ ps from rfl, wgWord_append, wgWord_singleton]
    group

/-- Cancelling a backtrack in a walk does not change its image in the target free group. -/
theorem wgWord_cancel_backtrack (vs : List ℤ) (lbl : List (FreeGroup α))
    (γ δ : List (ℕ × Bool)) (p : ℕ × Bool) :
    wgWord vs lbl (γ ++ p :: wgFlip p :: δ) = wgWord vs lbl (γ ++ δ) := by
  simp only [wgWord, List.map_append, List.map_cons, List.prod_append, List.prod_cons]
  rw [wgLblP_flip lbl p]
  group

@[simp] theorem wgMu_nil (vs : List ℤ) (lbl : List (FreeGroup α)) :
    wgMu vs lbl ([] : List (ℕ × Bool)) = 1 := rfl

@[simp] theorem wgMu_singleton (vs : List ℤ) (lbl : List (FreeGroup α)) (p : ℕ × Bool) :
    wgMu vs lbl [p] = if p.2 then wgMuGen vs lbl p.1 else (wgMuGen vs lbl p.1)⁻¹ := by
  simp [wgMu]

theorem wgMu_append (vs : List ℤ) (lbl : List (FreeGroup α)) (γ δ : List (ℕ × Bool)) :
    wgMu vs lbl (γ ++ δ) = wgMu vs lbl γ * wgMu vs lbl δ := by
  simp [wgMu, List.map_append, List.prod_append]

/-- The image of a reversed walk is the inverse word. -/
theorem wgMu_rev (vs : List ℤ) (lbl : List (FreeGroup α)) (γ : List (ℕ × Bool)) :
    wgMu vs lbl (wgRev γ) = (wgMu vs lbl γ)⁻¹ := by
  have key : ∀ p : ℕ × Bool,
      (if (wgFlip p).2 then wgMuGen vs lbl (wgFlip p).1
        else (wgMuGen vs lbl (wgFlip p).1)⁻¹) =
      (if p.2 then wgMuGen vs lbl p.1 else (wgMuGen vs lbl p.1)⁻¹)⁻¹ := by
    intro p
    cases p with
    | mk j b => cases b <;> simp [wgFlip]
  induction γ with
  | nil => simp
  | cons p ps ih =>
    have hsplit : wgRev (p :: ps) = wgRev ps ++ [wgFlip p] := by simp [wgRev]
    rw [hsplit, wgMu_append, ih, wgMu_singleton, key,
      show (p :: ps : List (ℕ × Bool)) = [p] ++ ps from rfl, wgMu_append, wgMu_singleton]
    group

/-- Cancelling a backtrack in a walk does not change its image in the fundamental group of the
domain. -/
theorem wgMu_cancel_backtrack (vs : List ℤ) (lbl : List (FreeGroup α))
    (γ δ : List (ℕ × Bool)) (p : ℕ × Bool) :
    wgMu vs lbl (γ ++ p :: wgFlip p :: δ) = wgMu vs lbl (γ ++ δ) := by
  have hpair : wgMu vs lbl [p, wgFlip p] = 1 := by
    have hcancel : (if p.2 then wgMuGen vs lbl p.1 else (wgMuGen vs lbl p.1)⁻¹) *
        (if (wgFlip p).2 then wgMuGen vs lbl (wgFlip p).1
          else (wgMuGen vs lbl (wgFlip p).1)⁻¹) = 1 := by
      cases p with
      | mk j b => cases b <;> simp [wgFlip]
    simpa [wgMu] using hcancel
  rw [show p :: wgFlip p :: δ = [p, wgFlip p] ++ δ from rfl, ← List.append_assoc, wgMu_append,
    wgMu_append, wgMu_append, hpair]
  simp


end Work.OROneRel
