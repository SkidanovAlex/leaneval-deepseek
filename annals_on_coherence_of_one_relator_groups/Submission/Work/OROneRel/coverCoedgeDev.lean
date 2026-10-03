/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# The development map of the coedge basis: definitions and elementary algebra

Definitions used by the proof of `Work.OROneRel.coverCoedge_injective`, together with the elementary
algebra of the development `devAux` of `Submission/Work/OROneRel/coverCoedgeDefs`.

`coverCoedgeDefs` defines the development `devAux W c u i L` by the *level-indexed* step
`devStep W c u i a b`: reading the letter `(a,b)` at running level `i` contributes the symbol of the
edge `(a, i)` (for `b = true`) or `(a, i - c a)` (for `b = false`), or `1` if that edge is not in
`coverBetaEdge W c u`.

For the inductive study of `devAux` it is convenient to index the step by the *edge* itself rather
than by the level: `devEdge W c u e b` is the symbol of the traversal of the edge `e` in the
direction `b`, or `1` if `e` is not in `coverBetaEdge W c u`.  The two agree
(`devStep_eq_devEdge`), and `devEdge` has the two formal properties the argument needs: the two
directions of one edge cancel (`devEdge_mul_inv`), and `devEdge` only depends on the edge
(`devEdge_congr`).

The rest of the file records the algebra of `devAux` that the proofs of `devAux_edgeWord`,
`devAux_expand` and the final argument use:

* multiplicativity over concatenation, `devAux_append`;
* invariance under the cancellation of an adjacent inverse pair, `devAux_head_cancel_true/false`,
  hence under reduction (`devAux_red`), hence `devAux` is a function of the represented element of
  the free group (`devAux_eq_of_mk_eq`, `devFun`);
* the behaviour on the reversed word, `devAux_invRev`;
* the basic `lsig` (weight) computations, all obtained from `cohom_mk`;
* the identification of the walk of `u` (`walkLv`, `walkLbl`) with the walk of the decorated word
  `decor c 0 (wordOf u)`.
-/
import Mathlib
import Submission.Work.OROneRel.coverCoedgeDefs
import Submission.Work.OROneRel.cohom_mk
import Submission.Work.OROneRel.wgLoop_facts

namespace Work.OROneRel

universe u

variable {α : Type u}

/-! ## The edge-indexed development symbol -/

/-- The predicate that indexes the coedge basis: the edge `e` is traversed by the walk of `u` and
its loop class is non-trivial. -/
abbrev coverDevPred (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (e : α × ℤ) : Prop :=
  (∃ p ∈ decor c 0 (wordOf u), coverEdge p = e) ∧ coverClassAt W c e ≠ 1

/-- The symbol contributed by the traversal of the edge `e` in the direction `b`: the symbol of `e`
for `b = true`, its inverse for `b = false`, and `1` if `e` is not in `coverBetaEdge W c u`. -/
noncomputable def devEdge (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (e : α × ℤ)
    (b : Bool) : FreeGroup (coverBetaEdge W c u) := by
  classical
  exact if h : coverDevPred W c u e then
    (bif b then FreeGroup.of (⟨e, h⟩ : coverBetaEdge W c u)
      else (FreeGroup.of (⟨e, h⟩ : coverBetaEdge W c u))⁻¹) else 1

/-- The `devStep` of the definitions is `devEdge` at the traversed edge. -/
theorem devStep_eq_devEdge (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (i : ℤ) (a : α)
    (b : Bool) :
    devStep W c u i a b = devEdge W c u (a, if b then i else i - c a) b := rfl

theorem devStep_eq_devEdge_true (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (i : ℤ)
    (a : α) : devStep W c u i a true = devEdge W c u (a, i) true := rfl

theorem devStep_eq_devEdge_false (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (i : ℤ)
    (a : α) : devStep W c u i a false = devEdge W c u (a, i - c a) false := rfl

theorem devEdge_true_of_pred (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (e : α × ℤ)
    (h : coverDevPred W c u e) :
    devEdge W c u e true = FreeGroup.of (⟨e, h⟩ : coverBetaEdge W c u) := by
  unfold devEdge
  rw [dif_pos h]
  simp only [cond_true]
  rfl

theorem devEdge_false_of_pred (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (e : α × ℤ)
    (h : coverDevPred W c u e) :
    devEdge W c u e false = (FreeGroup.of (⟨e, h⟩ : coverBetaEdge W c u))⁻¹ := by
  unfold devEdge
  rw [dif_pos h]
  simp only [cond_false]
  rfl

theorem devEdge_true_of_not (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (e : α × ℤ)
    (h : ¬ coverDevPred W c u e) : devEdge W c u e true = 1 := by
  unfold devEdge
  rw [dif_neg h]

theorem devEdge_false_of_not (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (e : α × ℤ)
    (h : ¬ coverDevPred W c u e) : devEdge W c u e false = 1 := by
  unfold devEdge
  rw [dif_neg h]

/-- The two directions of one edge cancel. -/
theorem devEdge_mul_inv (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (e : α × ℤ) :
    devEdge W c u e true * devEdge W c u e false = 1 := by
  classical
  by_cases h : coverDevPred W c u e
  · rw [devEdge_true_of_pred W c u e h, devEdge_false_of_pred W c u e h]
    exact mul_inv_cancel _
  · rw [devEdge_true_of_not W c u e h, devEdge_false_of_not W c u e h, mul_one]

/-- The same cancellation in the other order. -/
theorem devEdge_inv_mul (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (e : α × ℤ) :
    devEdge W c u e false * devEdge W c u e true = 1 :=
  (mul_eq_one_comm).mpr (devEdge_mul_inv W c u e)

/-- The second direction is the inverse of the first. -/
theorem devEdge_false_eq_inv (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (e : α × ℤ) :
    devEdge W c u e false = (devEdge W c u e true)⁻¹ :=
  eq_inv_of_mul_eq_one_left (devEdge_inv_mul W c u e)

/-- The first direction is the inverse of the second. -/
theorem devEdge_true_eq_inv (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (e : α × ℤ) :
    devEdge W c u e true = (devEdge W c u e false)⁻¹ := by
  rw [devEdge_false_eq_inv, inv_inv]

/-- The symbol of a traversal depends only on the edge. -/
theorem devEdge_congr {W : ℤ → FreeGroup α} {c : α → ℤ} {u : FreeGroup α} {e e' : α × ℤ}
    (h : e = e') (b : Bool) : devEdge W c u e b = devEdge W c u e' b := by
  subst h; rfl

/-- The cancellation of an adjacent inverse pair, in the positive direction, at the level
indexing of `devStep`. -/
theorem devStep_mul (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (i : ℤ) (a : α) :
    devStep W c u i a true * devStep W c u (i + c a) a false = 1 := by
  rw [devStep_eq_devEdge_true, devStep_eq_devEdge_false,
    show (a, i + c a - c a) = (a, i) by rw [show i + c a - c a = i by ring]]
  exact devEdge_mul_inv W c u (a, i)

/-- The cancellation of an adjacent inverse pair, in the negative direction. -/
theorem devStep_inv_mul (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (i : ℤ) (a : α) :
    devStep W c u i a false * devStep W c u (i - c a) a true = 1 := by
  rw [devStep_eq_devEdge_false, devStep_eq_devEdge_true]
  exact devEdge_inv_mul W c u (a, i - c a)

/-! ## The weight `lsig` -/

theorem lsig_nil (c : α → ℤ) : lsig c ([] : List (α × Bool)) = 0 := rfl

theorem lsig_cons (c : α → ℤ) (a : α) (b : Bool) (L : List (α × Bool)) :
    lsig c ((a, b) :: L) = (if b then c a else -c a) + lsig c L := by
  simp [lsig]

theorem lsig_cons_true (c : α → ℤ) (a : α) (L : List (α × Bool)) :
    lsig c ((a, true) :: L) = c a + lsig c L := by
  simp [lsig]

theorem lsig_cons_false (c : α → ℤ) (a : α) (L : List (α × Bool)) :
    lsig c ((a, false) :: L) = -c a + lsig c L := by
  simp [lsig]

theorem lsig_singleton_true (c : α → ℤ) (a : α) : lsig c [(a, true)] = c a := by
  simp [lsig]

theorem lsig_singleton_false (c : α → ℤ) (a : α) : lsig c [(a, false)] = -c a := by
  simp [lsig]

theorem lsig_append (c : α → ℤ) (L₁ L₂ : List (α × Bool)) :
    lsig c (L₁ ++ L₂) = lsig c L₁ + lsig c L₂ := by
  simp [lsig, List.map_append, List.sum_append]

/-- The weight only depends on the element of the free group. -/
theorem lsig_eq_of_mk_eq (c : α → ℤ) {L₁ L₂ : List (α × Bool)}
    (h : FreeGroup.mk L₁ = FreeGroup.mk L₂) : lsig c L₁ = lsig c L₂ := by
  have h₁ := cohom_mk c L₁
  have h₂ := cohom_mk c L₂
  rw [h] at h₁
  exact Multiplicative.ofAdd.injective (h₁.symm.trans h₂)

theorem lsig_invRev (c : α → ℤ) (L : List (α × Bool)) :
    lsig c (FreeGroup.invRev L) = -lsig c L := by
  induction L with
  | nil => simp [lsig]
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    rw [FreeGroup.invRev_cons, show FreeGroup.invRev [(a, b)] = [(a, !b)] from rfl,
      lsig_append, ih]
    cases b
    · rw [show ([(a, !false)] : List (α × Bool)) = [(a, true)] by simp, lsig_cons_true, lsig_nil,
        lsig_cons_false]
      ring
    · rw [show ([(a, !true)] : List (α × Bool)) = [(a, false)] by simp, lsig_cons_false, lsig_nil,
        lsig_cons_true]
      ring

/-- The weight of the reduced word of an element is the cohomological weight of the element. -/
theorem lsig_wordOf (c : α → ℤ) (v : FreeGroup α) :
    lsig c (wordOf v) = (cohom c v).toAdd := by
  have h := cohom_mk c (wordOf v)
  rw [mk_wordOf] at h
  have h' := congrArg Multiplicative.toAdd h
  simpa using h'.symm

theorem wordOf_inv (v : FreeGroup α) : wordOf v⁻¹ = FreeGroup.invRev (wordOf v) := by
  classical
  simp [wordOf, FreeGroup.toWord_inv]

theorem lsig_wordOf_inv (c : α → ℤ) (v : FreeGroup α) :
    lsig c (wordOf v⁻¹) = -lsig c (wordOf v) := by
  rw [wordOf_inv, lsig_invRev]

theorem lsig_step_not (c : α → ℤ) (L₃ L₄ : List (α × Bool)) (x : α) (b : Bool) :
    lsig c (L₃ ++ (x, b) :: (x, !b) :: L₄) = lsig c (L₃ ++ L₄) := by
  rw [lsig_append, lsig_append,
    show lsig c ((x, b) :: (x, !b) :: L₄) = lsig c L₄ from by
      cases b
      · simp only [Bool.not_false, lsig_cons_false, lsig_cons_true]
        ring
      · simp only [Bool.not_true, lsig_cons_true, lsig_cons_false]
        ring]

theorem lsig_step (c : α → ℤ) {L₁ L₂ : List (α × Bool)} (h : FreeGroup.Red.Step L₁ L₂) :
    lsig c L₁ = lsig c L₂ := by
  cases h
  exact lsig_step_not c _ _ _ _

/-! ## The development of a word -/

theorem devAux_nil (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (i : ℤ) :
    devAux W c u i ([] : List (α × Bool)) = 1 := rfl

theorem devAux_cons_true (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (i : ℤ) (a : α)
    (L : List (α × Bool)) :
    devAux W c u i ((a, true) :: L) = devStep W c u i a true * devAux W c u (i + c a) L := rfl

theorem devAux_cons_false (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (i : ℤ) (a : α)
    (L : List (α × Bool)) :
    devAux W c u i ((a, false) :: L) = devStep W c u i a false * devAux W c u (i - c a) L := rfl

theorem devAux_singleton_true (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (i : ℤ)
    (a : α) : devAux W c u i [(a, true)] = devEdge W c u (a, i) true := by
  rw [devAux_cons_true, devAux_nil, mul_one, devStep_eq_devEdge_true]

theorem devAux_singleton_false (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (i : ℤ)
    (a : α) : devAux W c u i [(a, false)] = devEdge W c u (a, i - c a) false := by
  rw [devAux_cons_false, devAux_nil, mul_one, devStep_eq_devEdge_false]

theorem devAux_congr (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) {i i' : ℤ}
    (h : i = i') (L : List (α × Bool)) : devAux W c u i L = devAux W c u i' L := by
  subst h; rfl

/-- **The development is multiplicative over concatenation.**  Reading `L₁ ++ L₂` from level `i` is
the same as reading `L₁` from `i` and then `L₂` from the level `i + lsig c L₁` reached by `L₁`. -/
theorem devAux_append (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (i : ℤ)
    (L₁ L₂ : List (α × Bool)) :
    devAux W c u i (L₁ ++ L₂) =
      devAux W c u i L₁ * devAux W c u (i + lsig c L₁) L₂ := by
  induction L₁ generalizing i with
  | nil => simp [devAux_nil, lsig_nil]
  | cons p L₁ ih =>
    obtain ⟨a, b⟩ := p
    cases b
    · rw [List.cons_append, devAux_cons_false, ih (i - c a), lsig_cons_false, devAux_cons_false,
        mul_assoc, show (i - c a) + lsig c L₁ = i + (-c a + lsig c L₁) by ring]
    · rw [List.cons_append, devAux_cons_true, ih (i + c a), lsig_cons_true, devAux_cons_true,
        mul_assoc, add_assoc]

/-- **The development is invariant under the cancellation of an adjacent inverse pair.** -/
theorem devAux_head_cancel_true (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (j : ℤ) (a : α)
    (L : List (α × Bool)) :
    devAux W c u j ((a, true) :: (a, false) :: L) = devAux W c u j L := by
  rw [devAux_cons_true, devAux_cons_false, show (j + c a) - c a = j by ring, ← mul_assoc,
    devStep_mul W c u j a, one_mul]

theorem devAux_head_cancel_false (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (j : ℤ)
    (a : α) (L : List (α × Bool)) :
    devAux W c u j ((a, false) :: (a, true) :: L) = devAux W c u j L := by
  rw [devAux_cons_false, devAux_cons_true, show (j - c a) + c a = j by ring, ← mul_assoc,
    devStep_inv_mul W c u j a, one_mul]

theorem devAux_step_not (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (i : ℤ)
    (L₃ L₄ : List (α × Bool)) (x : α) (b : Bool) :
    devAux W c u i (L₃ ++ (x, b) :: (x, !b) :: L₄) = devAux W c u i (L₃ ++ L₄) := by
  cases b
  · simp only [Bool.not_false]
    rw [devAux_append, devAux_append]
    exact congrArg (fun z => devAux W c u i L₃ * z)
      (devAux_head_cancel_false W c u (i + lsig c L₃) x L₄)
  · simp only [Bool.not_true]
    rw [devAux_append, devAux_append]
    exact congrArg (fun z => devAux W c u i L₃ * z)
      (devAux_head_cancel_true W c u (i + lsig c L₃) x L₄)

theorem devAux_step (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (i : ℤ)
    {L₁ L₂ : List (α × Bool)} (h : FreeGroup.Red.Step L₁ L₂) :
    devAux W c u i L₁ = devAux W c u i L₂ := by
  cases h
  exact devAux_step_not W c u i _ _ _ _

/-- The development, as a function of the element of the free group.  (It is not a homomorphism:
the level at which the remainder of the word is read depends on the word already read.) -/
noncomputable def devFun (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (i : ℤ) :
    FreeGroup α → FreeGroup (coverBetaEdge W c u) :=
  Quot.lift (devAux W c u i) fun _L₁ _L₂ h => devAux_step W c u i h

theorem devFun_mk (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (i : ℤ)
    (L : List (α × Bool)) : devFun W c u i (FreeGroup.mk L) = devAux W c u i L := rfl

/-- Words representing the same element of the free group have the same development. -/
theorem devAux_eq_of_mk_eq (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (i : ℤ)
    {L₁ L₂ : List (α × Bool)} (h : FreeGroup.mk L₁ = FreeGroup.mk L₂) :
    devAux W c u i L₁ = devAux W c u i L₂ := by
  rw [← devFun_mk W c u i L₁, h, devFun_mk W c u i L₂]

/-- The development of the reduced word of an element. -/
theorem devAux_wordOf (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (i : ℤ)
    (v : FreeGroup α) : devAux W c u i (wordOf v) = devFun W c u i v := by
  conv_rhs => rw [← mk_wordOf v]
  rw [devFun_mk]

theorem mk_nil {β : Type u} : FreeGroup.mk ([] : List (β × Bool)) = 1 := rfl

/-- A word representing the trivial element has trivial development. -/
theorem devAux_eq_one_of_mk_eq_one (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (i : ℤ)
    {L : List (α × Bool)} (h : FreeGroup.mk L = 1) : devAux W c u i L = 1 := by
  rw [devAux_eq_of_mk_eq W c u i (L₂ := ([] : List (α × Bool)))
    (by rw [mk_nil]; exact h), devAux_nil]

/-- **The development of a reversed word is the inverse development**, read from the level reached
by the word. -/
theorem devAux_invRev (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (i : ℤ)
    (L : List (α × Bool)) :
    devAux W c u (i + lsig c L) (FreeGroup.invRev L) = (devAux W c u i L)⁻¹ := by
  induction L generalizing i with
  | nil => simp [devAux_nil, lsig_nil]
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    rw [FreeGroup.invRev_cons, show FreeGroup.invRev [(a, b)] = [(a, !b)] from rfl, devAux_append]
    cases b
    · -- the letter is `(a, false)`: the reversed word starts with `(a, true)`
      simp only [Bool.not_false]
      rw [lsig_cons_false, show i + (-c a + lsig c L) = (i + -c a) + lsig c L by ring,
        ih (i + -c a), lsig_invRev, devAux_singleton_true,
        show (i + -c a) + lsig c L + -lsig c L = i + -c a by ring,
        show (i : ℤ) + -c a = i - c a by ring, devEdge_true_eq_inv, devAux_cons_false,
        devStep_eq_devEdge_false, mul_inv_rev]
    · -- the letter is `(a, true)`: the reversed word starts with `(a, false)`
      simp only [Bool.not_true]
      rw [lsig_cons_true, show i + (c a + lsig c L) = (i + c a) + lsig c L by ring,
        ih (i + c a), lsig_invRev, devAux_singleton_false,
        show (i + c a) + lsig c L + -lsig c L = i + c a by ring,
        show (a, i + c a - c a) = (a, i) by rw [show i + c a - c a = i by ring],
        devEdge_false_eq_inv, devAux_cons_true, devStep_eq_devEdge_true, mul_inv_rev]

/-! ## Elementary `mk` computations -/

theorem mk_append {β : Type u} (L₁ L₂ : List (β × Bool)) :
    FreeGroup.mk (L₁ ++ L₂) = FreeGroup.mk L₁ * FreeGroup.mk L₂ :=
  (FreeGroup.mul_mk (L₁ := L₁) (L₂ := L₂)).symm

theorem mk_singleton_true {β : Type u} (a : β) :
    FreeGroup.mk [(a, true)] = FreeGroup.of a := rfl

theorem mk_singleton_false {β : Type u} (a : β) :
    FreeGroup.mk [(a, false)] = (FreeGroup.of a)⁻¹ := by
  have h : ([(a, false)] : List (β × Bool)) = FreeGroup.invRev [(a, true)] := by
    simp [FreeGroup.invRev]
  rw [h, ← FreeGroup.inv_mk]
  rfl

theorem mk_cons_true {β : Type u} (a : β) (L : List (β × Bool)) :
    FreeGroup.mk ((a, true) :: L) = FreeGroup.of a * FreeGroup.mk L := by
  rw [show ((a, true) :: L : List (β × Bool)) = [(a, true)] ++ L from rfl, mk_append,
    mk_singleton_true]

theorem mk_cons_false {β : Type u} (a : β) (L : List (β × Bool)) :
    FreeGroup.mk ((a, false) :: L) = (FreeGroup.of a)⁻¹ * FreeGroup.mk L := by
  rw [show ((a, false) :: L : List (β × Bool)) = [(a, false)] ++ L from rfl, mk_append,
    mk_singleton_false]

theorem mk_invRev {β : Type u} (L : List (β × Bool)) :
    FreeGroup.mk (FreeGroup.invRev L) = (FreeGroup.mk L)⁻¹ :=
  (FreeGroup.inv_mk (L := L)).symm

theorem mk_flatten_map {β : Type u} (f : β → List (α × Bool)) (l : List β) :
    FreeGroup.mk (l.map f).flatten = (l.map fun x => FreeGroup.mk (f x)).prod := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    rw [List.map_cons, List.flatten_cons, mk_append, ih, List.map_cons, List.prod_cons]

/-- The word of a list product, as a product of signed generators. -/
theorem mk_eq_prod_map_signed {β : Type u} (L : List (β × Bool)) :
    FreeGroup.mk L =
      (L.map fun p => if p.2 then FreeGroup.of p.1 else (FreeGroup.of p.1)⁻¹).prod := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    cases b
    · rw [mk_cons_false, ih, List.map_cons, List.prod_cons]
      rfl
    · rw [mk_cons_true, ih, List.map_cons, List.prod_cons]
      rfl

/-- The development of the concatenation of a mapped list of words of weight `0`. -/
theorem devAux_map_flatten_of_lsig_eq_zero (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α)
    {β : Type u} (l : List β) (f : β → List (α × Bool))
    (h : ∀ x ∈ l.map f, lsig c x = 0) (i : ℤ) :
    devAux W c u i (l.map f).flatten = (l.map fun x => devAux W c u i (f x)).prod := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    have hx : lsig c (f x) = 0 := h (f x) (by simp)
    have ht : ∀ y ∈ t.map f, lsig c y = 0 := fun y hy => h y (by simp [hy])
    rw [List.map_cons, List.flatten_cons, devAux_append, hx, add_zero, ih ht,
      List.map_cons, List.prod_cons]

/-- The development of a concatenation of words of weight `0`, all read from the same level. -/
theorem devAux_flatten_of_lsig_eq_zero (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α)
    (l : List (List (α × Bool))) (h : ∀ x ∈ l, lsig c x = 0) (i : ℤ) :
    devAux W c u i l.flatten = (l.map fun x => devAux W c u i x).prod := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    have hx : lsig c x = 0 := h x (List.mem_cons_self ..)
    have ht : ∀ y ∈ t, lsig c y = 0 := fun y hy => h y (List.mem_cons_of_mem x hy)
    rw [List.flatten_cons, devAux_append, hx, add_zero, ih ht, List.map_cons, List.prod_cons]

/-! ## The walk of `u` and the first-arrival gauge -/

theorem running_cons (c : α → ℤ) (i : ℤ) (p : α × Bool) (M : List (α × Bool)) :
    running c i (p :: M) = i :: running c (i + linc c p) M := by
  obtain ⟨a, b⟩ := p
  cases b <;> rfl

theorem lv_eq_running (c : α → ℤ) (i : ℤ) (M : List (α × Bool)) :
    lv c i M = running c i M := by
  induction M generalizing i with
  | nil => simp [lv, running]
  | cons p M ih => rw [lv_cons, running_cons, ih (i + linc c p)]

theorem running_getD_zero (c : α → ℤ) (X : ℤ) (M : List (α × Bool)) (d : ℤ) :
    (running c X M).getD 0 d = X := by
  cases M with
  | nil => simp [running]
  | cons p M => rw [running_cons]; simp

/-- The level recurrence of the walk: the `(k+1)`-st level is the `k`-th level plus the weight of
the `k`-th letter.  (The default value of `getD` is irrelevant, both indices being in range.) -/
theorem running_getD_succ (c : α → ℤ) (i : ℤ) (M : List (α × Bool)) (k : ℕ) (d : ℤ)
    (hk : k < M.length) :
    (running c i M).getD (k + 1) d = (running c i M).getD k d + linc c (M[k]'hk) := by
  induction M generalizing i k with
  | nil => simp at hk
  | cons p M ih =>
    obtain ⟨a, b⟩ := p
    cases k with
    | zero =>
      rw [running_cons, List.getD_cons_succ, List.getD_cons_zero, running_getD_zero]
      cases b <;> simp [linc]
    | succ k =>
      rw [running_cons, List.getD_cons_succ, List.getElem_cons_succ]
      exact ih (i + linc c (a, b)) k (by simpa using hk)

theorem walkLv_eq_running (c : α → ℤ) (u : FreeGroup α) :
    walkLv c u = running c 0 (wordOf u) := lv_eq_running c 0 (wordOf u)

theorem walkLv_headD (c : α → ℤ) (u : FreeGroup α) : (walkLv c u).headD 0 = 0 := by
  rw [walkLv_eq_running]; exact running_headD_zero c 0 (wordOf u)

theorem lab_cons_true (M : List (α × Bool)) (a : α) :
    lab ((a, true) :: M) = FreeGroup.of a :: lab M := rfl

theorem lab_cons_false (M : List (α × Bool)) (a : α) :
    lab ((a, false) :: M) = (FreeGroup.of a)⁻¹ :: lab M := rfl

theorem lab_eq_map_coverLetter (c : α → ℤ) (i : ℤ) (M : List (α × Bool)) :
    lab M = (decor c i M).map coverLetter := by
  induction M generalizing i with
  | nil => rfl
  | cons p M ih =>
    obtain ⟨a, b⟩ := p
    cases b
    · rw [show decor c i ((a, false) :: M) = ((a, i - c a), false) :: decor c (i - c a) M from rfl,
        List.map_cons, lab_cons_false, ih (i - c a)]
      rfl
    · rw [show decor c i ((a, true) :: M) = ((a, i), true) :: decor c (i + c a) M from rfl,
        List.map_cons, lab_cons_true, ih (i + c a)]
      rfl

theorem walkLbl_eq_map_coverLetter (c : α → ℤ) (u : FreeGroup α) :
    walkLbl u = (decor c 0 (wordOf u)).map coverLetter := lab_eq_map_coverLetter c 0 (wordOf u)

theorem walkLbl_length (u : FreeGroup α) : (walkLbl u).length = (wordOf u).length := by
  simp [walkLbl, lab_length]

theorem walkLv_length (c : α → ℤ) (u : FreeGroup α) :
    (walkLv c u).length = (wordOf u).length + 1 := by
  rw [walkLv_eq_running, running_length]

theorem walkGauge_hlen (c : α → ℤ) (u : FreeGroup α) :
    (walkLv c u).length = (walkLbl u).length + 1 := by
  rw [walkLv_length, walkLbl_length]

theorem uGauge_def (c : α → ℤ) (u : FreeGroup α) :
    uGauge c u = walkGauge (walkLv c u) (walkLbl u) := rfl

/-- The state machine of the first-arrival gauge, run to the end. -/
theorem uGauge_getD (c : α → ℤ) (u : FreeGroup α) (v : ℤ) :
    uGauge c u v = (runSteps (initState ((walkLv c u).headD 0)) (mkSteps (walkLv c u) (walkLbl u))
        v).getD 1 := rfl

end Work.OROneRel
