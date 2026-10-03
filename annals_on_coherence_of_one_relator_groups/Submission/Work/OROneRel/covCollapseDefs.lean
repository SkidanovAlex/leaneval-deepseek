/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# The collapse of the level graph along the tree of trivial loop classes

Let `c : α → ℤ` be a weight and `W : ℤ → FreeGroup α` a gauge.  The `ℤ`-cover `Y` of the
one-relator complex has vertices the levels `ℤ` and one edge `e = (x,i) : i → i + c x` for every
generator `x` and level `i`; its loop class is `coverClassAt W c e = W i * x * (W (i + c x))⁻¹`.

Write `T = {e | coverClassAt W c e = 1}` for the *tree* (the edges of trivial loop class) and
`X = α × ℤ \ T` for its complement; `covX W c` is `X` as a type.  This file sets up the
*development* of a word along the levels: reading a word in `α`-letters from a level, a traversal
contributes the symbol of its edge, or `1` if the edge has trivial loop class.  It is the exact
analogue of the development `devAux` of `Submission/Work/OROneRel/coverCoedgeDefs.lean`, with the
predicate "traversed by the walk of `u`" replaced by "of non-trivial loop class"; that replacement is
what makes the development a *function* of the whole free group `F (α × ℤ)` and yields the identity

  `covCollapse W c y = covDevFun W c 0 (gaugeMap W c y)`

(`Work.OROneRel.covCollapse_eq_covDevFun_gaugeMap`), i.e. the collapse of `F (α × ℤ)` onto the
non-tree edges is computed by the development of the gauge image.  Together with
`Work.OROneRel.mul_tau_inv_mem` this gives `ker (gaugeMap W c) ⊆ ⟪T⟫`.

The file contains definitions and the elementary algebra of the development (`covDevSym`,
`covDevAux`, `covDevFun`, and the collapse/tree maps `covCollapse`, `covTau`, `covIota`).
-/
import Mathlib
import Submission.Work.OROneRel.GaugeDefs
import Submission.Work.OROneRel.coverCoedgeDev

namespace Work.OROneRel

universe u

variable {α : Type u}

/-! ## The alphabet of the collapse -/

/-- **The alphabet of the collapse**: the edges of the level graph of *non-trivial* loop class, i.e.
the complement of the tree `T = {e | coverClassAt W c e = 1}`. -/
abbrev covX (W : ℤ → FreeGroup α) (c : α → ℤ) : Type u :=
  {e : α × ℤ // coverClassAt W c e ≠ 1}

/-- The symbol contributed by the traversal of the edge `e` in the direction `b`: the symbol of the
edge (or its inverse) when the loop class of `e` is non-trivial, and `1` when it is trivial. -/
noncomputable def covDevSym (W : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ) (b : Bool) :
    FreeGroup (covX W c) := by
  classical
  exact if h : coverClassAt W c e ≠ 1 then
    (bif b then FreeGroup.of (⟨e, h⟩ : covX W c) else (FreeGroup.of (⟨e, h⟩ : covX W c))⁻¹)
  else 1

theorem covDevSym_true_of_ne (W : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ)
    (h : coverClassAt W c e ≠ 1) :
    covDevSym W c e true = FreeGroup.of (⟨e, h⟩ : covX W c) := by
  unfold covDevSym
  rw [dif_pos h]
  simp only [cond_true]

theorem covDevSym_false_of_ne (W : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ)
    (h : coverClassAt W c e ≠ 1) :
    covDevSym W c e false = (FreeGroup.of (⟨e, h⟩ : covX W c))⁻¹ := by
  unfold covDevSym
  rw [dif_pos h]
  simp only [cond_false]

theorem covDevSym_true_of_eq (W : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ)
    (h : coverClassAt W c e = 1) : covDevSym W c e true = 1 := by
  unfold covDevSym
  rw [dif_neg (by intro h'; exact h' h)]

theorem covDevSym_false_of_eq (W : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ)
    (h : coverClassAt W c e = 1) : covDevSym W c e false = 1 := by
  unfold covDevSym
  rw [dif_neg (by intro h'; exact h' h)]

/-- The two directions of one edge cancel. -/
theorem covDevSym_mul_inv (W : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ) :
    covDevSym W c e true * covDevSym W c e false = 1 := by
  classical
  by_cases h : coverClassAt W c e ≠ 1
  · rw [covDevSym_true_of_ne W c e h, covDevSym_false_of_ne W c e h]
    exact mul_inv_cancel _
  · rw [covDevSym_true_of_eq W c e (not_not.mp h), covDevSym_false_of_eq W c e (not_not.mp h),
      mul_one]

/-- The same cancellation in the other order. -/
theorem covDevSym_inv_mul (W : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ) :
    covDevSym W c e false * covDevSym W c e true = 1 :=
  (mul_eq_one_comm).mpr (covDevSym_mul_inv W c e)

/-- The second direction is the inverse of the first. -/
theorem covDevSym_false_eq_inv (W : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ) :
    covDevSym W c e false = (covDevSym W c e true)⁻¹ :=
  eq_inv_of_mul_eq_one_left (covDevSym_inv_mul W c e)

/-- The first direction is the inverse of the second. -/
theorem covDevSym_true_eq_inv (W : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ) :
    covDevSym W c e true = (covDevSym W c e false)⁻¹ := by
  rw [covDevSym_false_eq_inv, inv_inv]

/-- The symbol of a traversal depends only on the edge. -/
theorem covDevSym_congr {W : ℤ → FreeGroup α} {c : α → ℤ} {e e' : α × ℤ} (h : e = e') (b : Bool) :
    covDevSym W c e b = covDevSym W c e' b := by
  subst h; rfl

/-! ## The development of a word read from a level -/

/-- **The development of a word from a level.**  The word `L` is read starting at level `i`; every
traversal contributes the symbol of its edge (with the sign of the traversal), or `1` if that edge
has trivial loop class. -/
noncomputable def covDevAux (W : ℤ → FreeGroup α) (c : α → ℤ) :
    ℤ → List (α × Bool) → FreeGroup (covX W c)
  | _, [] => 1
  | i, (a, true) :: L => covDevSym W c (a, i) true * covDevAux W c (i + c a) L
  | i, (a, false) :: L => covDevSym W c (a, i - c a) false * covDevAux W c (i - c a) L

theorem covDevAux_nil (W : ℤ → FreeGroup α) (c : α → ℤ) (i : ℤ) :
    covDevAux W c i ([] : List (α × Bool)) = 1 := rfl

theorem covDevAux_cons_true (W : ℤ → FreeGroup α) (c : α → ℤ) (i : ℤ) (a : α)
    (L : List (α × Bool)) :
    covDevAux W c i ((a, true) :: L) = covDevSym W c (a, i) true * covDevAux W c (i + c a) L :=
  rfl

theorem covDevAux_cons_false (W : ℤ → FreeGroup α) (c : α → ℤ) (i : ℤ) (a : α)
    (L : List (α × Bool)) :
    covDevAux W c i ((a, false) :: L) =
      covDevSym W c (a, i - c a) false * covDevAux W c (i - c a) L :=
  rfl

theorem covDevAux_singleton_true (W : ℤ → FreeGroup α) (c : α → ℤ) (i : ℤ) (a : α) :
    covDevAux W c i [(a, true)] = covDevSym W c (a, i) true := by
  rw [covDevAux_cons_true, covDevAux_nil, mul_one]

theorem covDevAux_singleton_false (W : ℤ → FreeGroup α) (c : α → ℤ) (i : ℤ) (a : α) :
    covDevAux W c i [(a, false)] = covDevSym W c (a, i - c a) false := by
  rw [covDevAux_cons_false, covDevAux_nil, mul_one]

theorem covDevAux_congr (W : ℤ → FreeGroup α) (c : α → ℤ) {i i' : ℤ} (h : i = i')
    (L : List (α × Bool)) : covDevAux W c i L = covDevAux W c i' L := by
  subst h; rfl

/-- **The development is multiplicative over concatenation.**  Reading `L₁ ++ L₂` from level `i` is
the same as reading `L₁` from `i` and then `L₂` from the level `i + lsig c L₁` reached by `L₁`. -/
theorem covDevAux_append (W : ℤ → FreeGroup α) (c : α → ℤ) (i : ℤ) (L₁ L₂ : List (α × Bool)) :
    covDevAux W c i (L₁ ++ L₂) =
      covDevAux W c i L₁ * covDevAux W c (i + lsig c L₁) L₂ := by
  induction L₁ generalizing i with
  | nil => simp [covDevAux_nil, lsig_nil]
  | cons p L₁ ih =>
    obtain ⟨a, b⟩ := p
    cases b
    · rw [List.cons_append, covDevAux_cons_false, ih (i - c a), lsig_cons_false,
        covDevAux_cons_false, mul_assoc,
        show (i - c a) + lsig c L₁ = i + (-c a + lsig c L₁) by ring]
    · rw [List.cons_append, covDevAux_cons_true, ih (i + c a), lsig_cons_true,
        covDevAux_cons_true, mul_assoc, add_assoc]

/-- **The development is invariant under the cancellation of an adjacent inverse pair.** -/
theorem covDevAux_head_cancel_true (W : ℤ → FreeGroup α) (c : α → ℤ) (j : ℤ) (a : α)
    (L : List (α × Bool)) :
    covDevAux W c j ((a, true) :: (a, false) :: L) = covDevAux W c j L := by
  rw [covDevAux_cons_true, covDevAux_cons_false, show (j + c a) - c a = j by ring, ← mul_assoc,
    covDevSym_mul_inv W c (a, j), one_mul]

theorem covDevAux_head_cancel_false (W : ℤ → FreeGroup α) (c : α → ℤ) (j : ℤ) (a : α)
    (L : List (α × Bool)) :
    covDevAux W c j ((a, false) :: (a, true) :: L) = covDevAux W c j L := by
  rw [covDevAux_cons_false, covDevAux_cons_true, show (j - c a) + c a = j by ring, ← mul_assoc,
    covDevSym_inv_mul W c (a, j - c a), one_mul]

theorem covDevAux_step_not (W : ℤ → FreeGroup α) (c : α → ℤ) (i : ℤ) (L₃ L₄ : List (α × Bool))
    (x : α) (b : Bool) :
    covDevAux W c i (L₃ ++ (x, b) :: (x, !b) :: L₄) = covDevAux W c i (L₃ ++ L₄) := by
  cases b
  · simp only [Bool.not_false]
    rw [covDevAux_append, covDevAux_append]
    exact congrArg (fun z => covDevAux W c i L₃ * z)
      (covDevAux_head_cancel_false W c (i + lsig c L₃) x L₄)
  · simp only [Bool.not_true]
    rw [covDevAux_append, covDevAux_append]
    exact congrArg (fun z => covDevAux W c i L₃ * z)
      (covDevAux_head_cancel_true W c (i + lsig c L₃) x L₄)

theorem covDevAux_step (W : ℤ → FreeGroup α) (c : α → ℤ) (i : ℤ) {L₁ L₂ : List (α × Bool)}
    (h : FreeGroup.Red.Step L₁ L₂) : covDevAux W c i L₁ = covDevAux W c i L₂ := by
  cases h
  exact covDevAux_step_not W c i _ _ _ _

/-! ## The development as a function of the represented element -/

/-- The development, as a function of the element of the free group.  (It is not a homomorphism: the
level at which the remainder of the word is read depends on the word already read.) -/
noncomputable def covDevFun (W : ℤ → FreeGroup α) (c : α → ℤ) (i : ℤ) :
    FreeGroup α → FreeGroup (covX W c) :=
  Quot.lift (covDevAux W c i) fun _L₁ _L₂ h => covDevAux_step W c i h

theorem covDevFun_mk (W : ℤ → FreeGroup α) (c : α → ℤ) (i : ℤ) (L : List (α × Bool)) :
    covDevFun W c i (FreeGroup.mk L) = covDevAux W c i L := rfl

/-- Words representing the same element of the free group have the same development. -/
theorem covDevAux_eq_of_mk_eq (W : ℤ → FreeGroup α) (c : α → ℤ) (i : ℤ) {L₁ L₂ : List (α × Bool)}
    (h : FreeGroup.mk L₁ = FreeGroup.mk L₂) : covDevAux W c i L₁ = covDevAux W c i L₂ := by
  rw [← covDevFun_mk W c i L₁, h, covDevFun_mk W c i L₂]

/-- The development of the reduced word of an element. -/
theorem covDevAux_wordOf (W : ℤ → FreeGroup α) (c : α → ℤ) (i : ℤ) (v : FreeGroup α) :
    covDevAux W c i (wordOf v) = covDevFun W c i v := by
  conv_rhs => rw [← mk_wordOf v]
  rw [covDevFun_mk]

/-- A word representing the trivial element has trivial development. -/
theorem covDevAux_eq_one_of_mk_eq_one (W : ℤ → FreeGroup α) (c : α → ℤ) (i : ℤ)
    {L : List (α × Bool)} (h : FreeGroup.mk L = 1) : covDevAux W c i L = 1 := by
  rw [covDevAux_eq_of_mk_eq W c i (L₂ := ([] : List (α × Bool)))
    (by rw [mk_nil]; exact h), covDevAux_nil]

/-! ## The collapse, the tree and the inclusion of the non-tree edges -/

/-- **The collapse of `F (α × ℤ)` onto the non-tree edges**: every edge of trivial loop class is
killed, and the edges of non-trivial loop class are kept. -/
noncomputable def covCollapse (W : ℤ → FreeGroup α) (c : α → ℤ) :
    FreeGroup (α × ℤ) →* FreeGroup (covX W c) :=
  FreeGroup.lift fun e => covDevSym W c e true

@[simp] theorem covCollapse_of (W : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ) :
    covCollapse W c (FreeGroup.of e) = covDevSym W c e true :=
  FreeGroup.lift_apply_of

/-- **The retraction onto the non-tree edges**, inside `F (α × ℤ)`: every edge of trivial loop class
is killed.  Its kernel is the normal closure of the tree. -/
noncomputable def covTau (W : ℤ → FreeGroup α) (c : α → ℤ) :
    FreeGroup (α × ℤ) →* FreeGroup (α × ℤ) := by
  classical
  exact FreeGroup.lift fun e => if h : coverClassAt W c e = 1 then 1 else FreeGroup.of e

theorem covTau_of_eq (W : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ)
    (h : coverClassAt W c e = 1) : covTau W c (FreeGroup.of e) = 1 := by
  classical
  rw [covTau, FreeGroup.lift_apply_of, dif_pos h]

theorem covTau_of_ne (W : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ)
    (h : coverClassAt W c e ≠ 1) : covTau W c (FreeGroup.of e) = FreeGroup.of e := by
  classical
  rw [covTau, FreeGroup.lift_apply_of, dif_neg h]

/-- The inclusion of the non-tree edges into `F (α × ℤ)`. -/
noncomputable def covIota (W : ℤ → FreeGroup α) (c : α → ℤ) :
    FreeGroup (covX W c) →* FreeGroup (α × ℤ) :=
  FreeGroup.lift fun e => FreeGroup.of e.1

@[simp] theorem covIota_of (W : ℤ → FreeGroup α) (c : α → ℤ) (e : covX W c) :
    covIota W c (FreeGroup.of e) = FreeGroup.of e.1 :=
  FreeGroup.lift_apply_of

/-- `covTau` is the conjugate of the collapse by the inclusion of the non-tree edges. -/
theorem covIota_covCollapse (W : ℤ → FreeGroup α) (c : α → ℤ) (y : FreeGroup (α × ℤ)) :
    covIota W c (covCollapse W c y) = covTau W c y := by
  classical
  induction y using FreeGroup.induction_on with
  | one => simp
  | of e =>
    by_cases h : coverClassAt W c e = 1
    · rw [covCollapse_of, covTau_of_eq W c e h, covDevSym_true_of_eq W c e h, map_one]
    · rw [covCollapse_of, covTau_of_ne W c e h,
        covDevSym_true_of_ne W c e (by simpa using h), covIota_of]
  | inv_of e ih =>
    simp only [map_inv, ih]
  | mul x y hx hy => simp [hx, hy]

end Work.OROneRel
