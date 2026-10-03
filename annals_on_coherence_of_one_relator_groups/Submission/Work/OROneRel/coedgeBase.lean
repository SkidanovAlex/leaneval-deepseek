/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# The development map of the coedge basis (self-contained copy)

This module contains, in the namespace `Work.OROneRel.CoedgeBase`, a self-contained copy of the
definitions and elementary algebra of the development `devAux` of
`Submission.Work.OROneRel.coverCoedgeDefs`, together with the walk data of `u`.  It is deliberately
independent of `Submission.Work.OROneRel.coverCoedgeDev`, so that the proof of
`Work.OROneRel.coedge_injective` rests only on stable definitions.

* `devEdge W c u e b` is the symbol of the traversal of the edge `e` in the direction `b`, or `1` if
  `e` is not in `coverBetaEdge W c u`; `devStep_eq_devEdge` identifies it with `devStep`;
* `devAux` is multiplicative over concatenation (`devAux_append`), invariant under the cancellation
  of an adjacent inverse pair (`devAux_head_cancel`) hence under `FreeGroup.Red` (`devAux_red`) and
  under passing to the represented element (`devAux_eq_of_mk_eq`), and its behaviour on the reversed
  word is `devAux_invRev`;
* `devEl W c u i g` is the development of the *element* `g` from the level `i`;
* `walkState c u k v` is the first-arrival state of the walk of `u`.
-/
import Mathlib
import Submission.Work.OROneRel.coverCoedgeDefs
import Submission.Work.OROneRel.cohom_mk
import Submission.Work.OROneRel.wgImmersionDefs
import Submission.Work.OROneRel.wgLoop_facts

namespace Work.OROneRel

universe u

variable {α : Type u}

namespace CoedgeBase

/-! ## The edge-indexed development symbol -/

/-- The predicate that indexes the coedge basis: the edge `e` is traversed by the walk of `u` and
its loop class is non-trivial. -/
abbrev coverDevPred (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (e : α × ℤ) : Prop :=
  (∃ p ∈ decor c 0 (wordOf u), coverEdge p = e) ∧ coverClassAt W c e ≠ 1

/-- The symbol contributed by the traversal of the edge `e` in the direction `b`. -/
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

/-- The weight of a word is the cohomological weight of its class. -/
theorem lsig_toAdd (c : α → ℤ) (L : List (α × Bool)) :
    lsig c L = (cohom c (FreeGroup.mk L)).toAdd := by
  rw [cohom_mk c L]
  rfl

theorem lsig_invRev (c : α → ℤ) (L : List (α × Bool)) :
    lsig c (FreeGroup.invRev L) = -lsig c L := by
  rw [lsig_toAdd c (FreeGroup.invRev L), (FreeGroup.inv_mk (L := L)).symm, map_inv,
    lsig_toAdd c L]
  simp

theorem lsig_wordOf_inv (c : α → ℤ) (v : FreeGroup α) :
    lsig c (wordOf v⁻¹) = -lsig c (wordOf v) := by
  have h : wordOf v⁻¹ = FreeGroup.invRev (wordOf v) := by
    classical
    simp [wordOf, FreeGroup.toWord_inv]
  rw [h, lsig_invRev]

/-- The weight of the reduced word of an element is the cohomological weight of the element. -/
theorem lsig_wordOf (c : α → ℤ) (v : FreeGroup α) :
    lsig c (wordOf v) = (cohom c v).toAdd := by
  rw [lsig_toAdd, mk_wordOf]

theorem lsig_eq_of_red {L₁ L₂ : List (α × Bool)} (c : α → ℤ) (h : FreeGroup.Red L₁ L₂) :
    lsig c L₁ = lsig c L₂ :=
  lsig_eq_of_mk_eq c (FreeGroup.Red.exact.mpr ⟨L₂, h, FreeGroup.Red.refl⟩)

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

/-- **The development is multiplicative over concatenation.** -/
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
        mul_assoc, show (i + c a) + lsig c L₁ = i + (c a + lsig c L₁) by ring]

/-- **The development is invariant under the cancellation of an adjacent inverse pair.** -/
theorem devAux_head_cancel (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (j : ℤ) (a : α)
    (b : Bool) (L : List (α × Bool)) :
    devAux W c u j ((a, b) :: (a, !b) :: L) = devAux W c u j L := by
  cases b
  · show devAux W c u j ((a, false) :: (a, true) :: L) = devAux W c u j L
    rw [devAux_cons_false, devAux_cons_true, ← mul_assoc, devStep_inv_mul W c u j a, one_mul]
    exact devAux_congr W c u (by ring) L
  · show devAux W c u j ((a, true) :: (a, false) :: L) = devAux W c u j L
    rw [devAux_cons_true, devAux_cons_false, ← mul_assoc, devStep_mul W c u j a, one_mul]
    exact devAux_congr W c u (by ring) L

theorem devAux_step (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (i : ℤ)
    {L₁ L₂ : List (α × Bool)} (h : FreeGroup.Red.Step L₁ L₂) :
    devAux W c u i L₁ = devAux W c u i L₂ := by
  cases h with
  | not => rw [devAux_append, devAux_append, devAux_head_cancel]

/-- **The development descends to the free group.**  The function on `List (α × Bool)` given by
`devAux` is invariant under `FreeGroup.Red.Step`, hence induces a function on `FreeGroup α`. -/
noncomputable def devElem (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (i : ℤ) :
    FreeGroup α → FreeGroup (coverBetaEdge W c u) :=
  Quot.lift (devAux W c u i) (fun _ _ h => devAux_step W c u i h)

theorem devElem_mk (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (i : ℤ)
    (L : List (α × Bool)) : devElem W c u i (FreeGroup.mk L) = devAux W c u i L := rfl

/-- Words representing the same element of the free group have the same development. -/
theorem devAux_eq_of_mk_eq (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (i : ℤ)
    {L₁ L₂ : List (α × Bool)} (h : FreeGroup.mk L₁ = FreeGroup.mk L₂) :
    devAux W c u i L₁ = devAux W c u i L₂ := by
  have h1 : devElem W c u i (FreeGroup.mk L₁) = devElem W c u i (FreeGroup.mk L₂) := by rw [h]
  rwa [devElem_mk, devElem_mk] at h1

/-- **The development is invariant under free reduction.** -/
theorem devAux_red (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (i : ℤ)
    {L₁ L₂ : List (α × Bool)} (h : FreeGroup.Red L₁ L₂) :
    devAux W c u i L₁ = devAux W c u i L₂ :=
  devAux_eq_of_mk_eq W c u i (FreeGroup.Red.exact.mpr ⟨L₂, h, FreeGroup.Red.refl⟩)

/-- A word representing the trivial element has trivial development. -/
theorem devAux_eq_one_of_mk_eq_one (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (i : ℤ)
    {L : List (α × Bool)} (h : FreeGroup.mk L = 1) : devAux W c u i L = 1 := by
  have h' : FreeGroup.mk L = FreeGroup.mk ([] : List (α × Bool)) :=
    h.trans FreeGroup.one_eq_mk.symm
  rw [devAux_eq_of_mk_eq W c u i h', devAux_nil]

/-- **The development of a reversed word is the inverse development**, read from the level reached
by the word. -/
theorem devAux_invRev (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (i : ℤ)
    (L : List (α × Bool)) :
    devAux W c u (i + lsig c L) (FreeGroup.invRev L) = (devAux W c u i L)⁻¹ := by
  have h : devAux W c u i (L ++ FreeGroup.invRev L) = 1 := by
    refine devAux_eq_one_of_mk_eq_one W c u i ?_
    rw [← FreeGroup.mul_mk, ← FreeGroup.inv_mk, mul_inv_cancel]
  rw [devAux_append] at h
  exact eq_inv_of_mul_eq_one_right h

/-! ## The walk of `u` and the first-arrival gauge -/

theorem lv_eq_running (c : α → ℤ) (i : ℤ) (M : List (α × Bool)) :
    lv c i M = running c i M := by
  induction M generalizing i with
  | nil => simp [lv, running]
  | cons p M ih =>
    obtain ⟨a, b⟩ := p
    cases b
    · rw [lv_cons, show i + linc c (a, false) = i - c a by simp [linc, sub_eq_add_neg]]
      change i :: lv c (i - c a) M = i :: running c (i - c a) M
      rw [ih (i - c a)]
    · rw [lv_cons, show i + linc c (a, true) = i + c a by simp [linc]]
      change i :: lv c (i + c a) M = i :: running c (i + c a) M
      rw [ih (i + c a)]

theorem lab_eq_map_coverLetter (c : α → ℤ) (i : ℤ) (M : List (α × Bool)) :
    lab M = (decor c i M).map coverLetter := by
  induction M generalizing i with
  | nil => simp [lab, decor]
  | cons p M ih =>
    obtain ⟨a, b⟩ := p
    cases b
    · show ((FreeGroup.of a)⁻¹) :: lab M =
        ((FreeGroup.of a)⁻¹) :: (decor c (i - c a) M).map coverLetter
      rw [ih (i - c a)]
    · show FreeGroup.of a :: lab M =
        FreeGroup.of a :: (decor c (i + c a) M).map coverLetter
      rw [ih (i + c a)]

theorem walkLv_eq_running (c : α → ℤ) (u : FreeGroup α) :
    walkLv c u = running c 0 (wordOf u) := lv_eq_running c 0 (wordOf u)

theorem walkLv_headD (c : α → ℤ) (u : FreeGroup α) : (walkLv c u).headD 0 = 0 := by
  rw [walkLv_eq_running, running_headD_zero]

theorem walkLbl_length (u : FreeGroup α) : (walkLbl u).length = (wordOf u).length := by
  simp [walkLbl, lab_length]

theorem walkLv_length (c : α → ℤ) (u : FreeGroup α) :
    (walkLv c u).length = (wordOf u).length + 1 := by
  rw [walkLv_eq_running, running_length]

theorem walkGauge_hlen (c : α → ℤ) (u : FreeGroup α) :
    (walkLv c u).length = (walkLbl u).length + 1 := by
  rw [walkLv_length, walkLbl_length]

theorem walkLbl_eq_map_coverLetter (c : α → ℤ) (u : FreeGroup α) :
    walkLbl u = (decor c 0 (wordOf u)).map coverLetter := lab_eq_map_coverLetter c 0 (wordOf u)

theorem uGauge_def (c : α → ℤ) (u : FreeGroup α) :
    uGauge c u = walkGauge (walkLv c u) (walkLbl u) := rfl

/-- The state machine of the first-arrival gauge, run to the end. -/
theorem uGauge_getD (c : α → ℤ) (u : FreeGroup α) (v : ℤ) :
    uGauge c u v = (runSteps (initState ((walkLv c u).headD 0)) (mkSteps (walkLv c u) (walkLbl u))
        v).getD 1 := by
  rw [uGauge_def, walkGauge]

/-! ## The development of an element, and the walk state -/

/-- **The development of an element.**  The development of `g : FreeGroup α` from the level `i`. -/
noncomputable def devEl (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (i : ℤ)
    (g : FreeGroup α) : FreeGroup (coverBetaEdge W c u) :=
  devAux W c u i (wordOf g)

/-- Unfolding of `devEl`. -/
theorem devEl_def (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (i : ℤ)
    (g : FreeGroup α) :
    devEl W c u i g = devAux W c u i (wordOf g) := rfl

/-- **The first-arrival state of the walk of `u` after `k` steps.** -/
noncomputable def walkState (c : α → ℤ) (u : FreeGroup α) (k : ℕ) (v : ℤ) :
    Option (FreeGroup α) :=
  wgState (walkLv c u) (walkLbl u) k v

/-- Unfolding of `walkState`. -/
theorem walkState_def (c : α → ℤ) (u : FreeGroup α) (k : ℕ) (v : ℤ) :
    walkState c u k v = wgState (walkLv c u) (walkLbl u) k v := rfl

/-- The state of the first-arrival machine after all the steps is the first-arrival gauge. -/
theorem walkState_full (c : α → ℤ) (u : FreeGroup α) (v : ℤ) :
    (walkState c u (walkLbl u).length v).getD 1 = uGauge c u v := by
  rw [walkState_def, uGauge_def]
  exact wglE_wgState_eq_walkGauge (walkLv c u) (walkLbl u) (walkGauge_hlen c u) v

end CoedgeBase

end Work.OROneRel
