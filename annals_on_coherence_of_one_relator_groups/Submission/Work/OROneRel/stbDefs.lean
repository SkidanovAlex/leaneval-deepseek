/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# The Schreier development of the tree transversal

This file sets up the vocabulary of the proof of `Work.OROneRel.schreier_tree_basis`.

Fix a weight `c : α → ℤ` and a family `t : ℤ → FreeGroup α` ("the tree transversal"): `t k` is a
word of weight `k` (`cohom c (t k) = ofAdd k`), `t 0 = 1`, and – the hypothesis `htree` of the
target theorem – the prefixes of `t k` are again transversals: if `P` is the prefix of `toWord (t k)`
of weight `j` then `t j = mk P`.

The Schreier graph of `cohom c` has vertices the levels `ℤ` and, for each generator `x : α`, one
oriented edge `(x,i) : i → i + c x`; the *edge* `e = (x,i)` is in the spanning tree given by `t`
iff `t i * x = t (i + c x)`.  The kernel of `cohom c` is free on the *non-tree edges*, i.e. on

  `stbBeta t c = {e : α × ℤ // stbLoop t c e ≠ 1}`,  `stbLoop t c (x,i) = t i * x * (t (i + c x))⁻¹`,

and `stbToClasses t c : FreeGroup (stbBeta t c) →* FreeGroup α` is the map sending `e` to its loop
class.  The theorem `schreier_tree_basis` says that `stbToClasses` is an isomorphism onto
`ker (cohom c)`.

## The development `stbDev`

The proof of injectivity is the classical "development" argument: reading a word of `F α` from level
`0` and recording, for every traversed edge, the symbol of that edge with the sign of the traversal
(and nothing if the edge is a tree edge) is a *function of the represented element of `F α`*
(`stbDev_eq_of_mk_eq`), it maps the loop word of a non-tree edge to its symbol, and hence kills a
word only if that word is trivial.

`stbEdge t c e b` is the symbol of the traversal of the edge `e` in the direction `b`, and `stbDev`
is the corresponding recursion on lists of letters.  This file proves the elementary algebra of
`stbEdge`/`stbDev` (needed by `Submission/Work/OROneRel/stbExpandDev.lean` and by the main file);
the parts that use the tree hypothesis are elsewhere.
-/
import Mathlib
import Submission.Work.OROneRel.MagnusGenDefs
import Submission.Work.OROneRel.cohom_mk

namespace Work.OROneRel

universe u

variable {α : Type u}

/-! ## The index set and the class map -/

/-- The loop class of the edge `e = (x,i)` of the `ℤ`-cover under the transversal `t`:
`t i * x * (t (i + c x))⁻¹`. -/
abbrev stbLoop (t : ℤ → FreeGroup α) (c : α → ℤ) (p : α × ℤ) : FreeGroup α :=
  t p.2 * FreeGroup.of p.1 * (t (p.2 + c p.1))⁻¹

/-- **The Schreier index set**: the edges of the `ℤ`-cover of non-trivial loop class, i.e. the
non-tree edges of the tree transversal `t`. -/
abbrev stbBeta (t : ℤ → FreeGroup α) (c : α → ℤ) : Type u :=
  {p : α × ℤ // stbLoop t c p ≠ 1}

/-- The Schreier index set carries a decidable equality (chosen classically), so that words in it can
be reduced.  This is the only `DecidableEq` instance for `stbBeta t c`, so that all uses agree. -/
noncomputable instance stbBetaDecidableEq (t : ℤ → FreeGroup α) (c : α → ℤ) :
    DecidableEq (stbBeta t c) :=
  Classical.decEq _
/-- The loop class of the edge `e` is trivial exactly when the edge is a tree edge, i.e. when
`t` already continues along `e`: `t i * x = t (i + c x)`. -/
theorem stbLoop_eq_one_iff (t : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ) :
    stbLoop t c e = 1 ↔ t e.2 * FreeGroup.of e.1 = t (e.2 + c e.1) := by
  rw [stbLoop, mul_inv_eq_one]

theorem stbLoop_ne_one_iff (t : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ) :
    stbLoop t c e ≠ 1 ↔ t e.2 * FreeGroup.of e.1 ≠ t (e.2 + c e.1) :=
  not_congr (stbLoop_eq_one_iff t c e)

/-- The class map `F (stbBeta t c) →* F α` sending an edge to its loop class. -/
noncomputable def stbToClasses (t : ℤ → FreeGroup α) (c : α → ℤ) :
    FreeGroup (stbBeta t c) →* FreeGroup α :=
  FreeGroup.lift fun p => stbLoop t c p.1

@[simp] theorem stbToClasses_of (t : ℤ → FreeGroup α) (c : α → ℤ) (p : stbBeta t c) :
    stbToClasses t c (FreeGroup.of p) = stbLoop t c p.1 :=
  FreeGroup.lift_apply_of

/-! ## The symbol of a traversal -/

/-- The symbol contributed by the traversal of the edge `e` in the direction `b`: the symbol of `e`
for `b = true`, its inverse for `b = false`, and `1` if `e` is a tree edge. -/
noncomputable def stbEdge (t : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ) (b : Bool) :
    FreeGroup (stbBeta t c) := by
  classical
  exact if h : stbLoop t c e ≠ 1 then
    (bif b then FreeGroup.of (⟨e, h⟩ : stbBeta t c)
      else (FreeGroup.of (⟨e, h⟩ : stbBeta t c))⁻¹) else 1

theorem stbEdge_true_of_ne (t : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ)
    (h : stbLoop t c e ≠ 1) :
    stbEdge t c e true = FreeGroup.of (⟨e, h⟩ : stbBeta t c) := by
  unfold stbEdge
  rw [dif_pos h]
  simp only [cond_true]

theorem stbEdge_false_of_ne (t : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ)
    (h : stbLoop t c e ≠ 1) :
    stbEdge t c e false = (FreeGroup.of (⟨e, h⟩ : stbBeta t c))⁻¹ := by
  unfold stbEdge
  rw [dif_pos h]
  simp only [cond_false]

theorem stbEdge_true_of_eq_one (t : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ)
    (h : stbLoop t c e = 1) : stbEdge t c e true = 1 := by
  unfold stbEdge
  rw [dif_neg (fun hh => hh h)]

theorem stbEdge_false_of_eq_one (t : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ)
    (h : stbLoop t c e = 1) : stbEdge t c e false = 1 := by
  unfold stbEdge
  rw [dif_neg (fun hh => hh h)]

/-- The two directions of one edge cancel. -/
theorem stbEdge_mul_inv (t : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ) :
    stbEdge t c e true * stbEdge t c e false = 1 := by
  classical
  by_cases h : stbLoop t c e ≠ 1
  · rw [stbEdge_true_of_ne t c e h, stbEdge_false_of_ne t c e h]
    exact mul_inv_cancel _
  · rw [stbEdge_true_of_eq_one t c e (not_not.mp h), stbEdge_false_of_eq_one t c e (not_not.mp h),
      mul_one]

/-- The same cancellation in the other order. -/
theorem stbEdge_inv_mul (t : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ) :
    stbEdge t c e false * stbEdge t c e true = 1 :=
  mul_eq_one_comm.mpr (stbEdge_mul_inv t c e)

/-- The second direction is the inverse of the first. -/
theorem stbEdge_false_eq_inv (t : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ) :
    stbEdge t c e false = (stbEdge t c e true)⁻¹ :=
  eq_inv_of_mul_eq_one_left (stbEdge_inv_mul t c e)

/-- The first direction is the inverse of the second. -/
theorem stbEdge_true_eq_inv (t : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ) :
    stbEdge t c e true = (stbEdge t c e false)⁻¹ := by
  rw [stbEdge_false_eq_inv, inv_inv]

/-- The symbol of a traversal depends only on the edge. -/
theorem stbEdge_congr {t : ℤ → FreeGroup α} {c : α → ℤ} {e e' : α × ℤ} (h : e = e') (b : Bool) :
    stbEdge t c e b = stbEdge t c e' b := by
  subst h; rfl

/-! ## The development -/

/-- **The development of a word from a level.**  The word `L` is read starting at the level `i`;
each letter `(a,b)` read at the running level `j` traverses the edge `(a,j)` (for `b = true`) or
`(a, j - c a)` (for `b = false`) and contributes the corresponding symbol, or `1` if that edge is a
tree edge. -/
noncomputable def stbDev (t : ℤ → FreeGroup α) (c : α → ℤ) :
    ℤ → List (α × Bool) → FreeGroup (stbBeta t c)
  | _, [] => 1
  | i, (a, true) :: L => stbEdge t c (a, i) true * stbDev t c (i + c a) L
  | i, (a, false) :: L => stbEdge t c (a, i - c a) false * stbDev t c (i - c a) L

@[simp] theorem stbDev_nil (t : ℤ → FreeGroup α) (c : α → ℤ) (i : ℤ) :
    stbDev t c i ([] : List (α × Bool)) = 1 := rfl

theorem stbDev_cons_true (t : ℤ → FreeGroup α) (c : α → ℤ) (i : ℤ) (a : α)
    (L : List (α × Bool)) :
    stbDev t c i ((a, true) :: L) = stbEdge t c (a, i) true * stbDev t c (i + c a) L := rfl

theorem stbDev_cons_false (t : ℤ → FreeGroup α) (c : α → ℤ) (i : ℤ) (a : α)
    (L : List (α × Bool)) :
    stbDev t c i ((a, false) :: L) = stbEdge t c (a, i - c a) false * stbDev t c (i - c a) L := rfl

theorem stbDev_singleton_true (t : ℤ → FreeGroup α) (c : α → ℤ) (i : ℤ) (a : α) :
    stbDev t c i [(a, true)] = stbEdge t c (a, i) true := by
  rw [stbDev_cons_true, stbDev_nil, mul_one]

theorem stbDev_singleton_false (t : ℤ → FreeGroup α) (c : α → ℤ) (i : ℤ) (a : α) :
    stbDev t c i [(a, false)] = stbEdge t c (a, i - c a) false := by
  rw [stbDev_cons_false, stbDev_nil, mul_one]

theorem stbDev_congr (t : ℤ → FreeGroup α) (c : α → ℤ) {i i' : ℤ} (h : i = i')
    (L : List (α × Bool)) : stbDev t c i L = stbDev t c i' L := by
  subst h; rfl

/-! ## The weight `lsig` -/

theorem stb_lsig_nil (c : α → ℤ) : lsig c ([] : List (α × Bool)) = 0 := rfl

theorem stb_lsig_cons_true (c : α → ℤ) (a : α) (L : List (α × Bool)) :
    lsig c ((a, true) :: L) = c a + lsig c L := rfl

theorem stb_lsig_cons_false (c : α → ℤ) (a : α) (L : List (α × Bool)) :
    lsig c ((a, false) :: L) = -c a + lsig c L := rfl

theorem stb_lsig_singleton_true (c : α → ℤ) (a : α) : lsig c [(a, true)] = c a := by
  simp [lsig]

theorem stb_lsig_singleton_false (c : α → ℤ) (a : α) : lsig c [(a, false)] = -c a := by
  simp [lsig]

theorem stb_lsig_append (c : α → ℤ) (L₁ L₂ : List (α × Bool)) :
    lsig c (L₁ ++ L₂) = lsig c L₁ + lsig c L₂ := by
  simp [lsig, List.map_append, List.sum_append]

theorem stb_lsig_invRev (c : α → ℤ) (L : List (α × Bool)) :
    lsig c (FreeGroup.invRev L) = -lsig c L := by
  induction L with
  | nil => simp [lsig]
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    rw [FreeGroup.invRev_cons, show FreeGroup.invRev [(a, b)] = [(a, !b)] from rfl,
      stb_lsig_append, ih]
    cases b
    · rw [show ([(a, !false)] : List (α × Bool)) = [(a, true)] by simp, stb_lsig_cons_true,
        stb_lsig_nil, stb_lsig_cons_false]
      ring
    · rw [show ([(a, !true)] : List (α × Bool)) = [(a, false)] by simp, stb_lsig_cons_false,
        stb_lsig_nil, stb_lsig_cons_true]
      ring

/-- The weight of the reduced word of an element is the cohomological weight of the element. -/
theorem stb_lsig_toWord [DecidableEq α] (c : α → ℤ) (v : FreeGroup α) :
    lsig c (FreeGroup.toWord v) = (cohom c v).toAdd := by
  have h := cohom_mk c (FreeGroup.toWord v)
  rw [FreeGroup.mk_toWord] at h
  exact (congrArg Multiplicative.toAdd h).symm

/-! ## The algebra of the development -/

/-- **The development is multiplicative over concatenation.** -/
theorem stbDev_append (t : ℤ → FreeGroup α) (c : α → ℤ) (i : ℤ)
    (L₁ L₂ : List (α × Bool)) :
    stbDev t c i (L₁ ++ L₂) = stbDev t c i L₁ * stbDev t c (i + lsig c L₁) L₂ := by
  induction L₁ generalizing i with
  | nil => simp [stbDev_nil, stb_lsig_nil]
  | cons p L₁ ih =>
    obtain ⟨a, b⟩ := p
    cases b
    · rw [List.cons_append, stbDev_cons_false, ih (i - c a), stb_lsig_cons_false, stbDev_cons_false,
        mul_assoc, show (i - c a) + lsig c L₁ = i + (-c a + lsig c L₁) by ring]
    · rw [List.cons_append, stbDev_cons_true, ih (i + c a), stb_lsig_cons_true, stbDev_cons_true,
        mul_assoc, add_assoc]

/-- **The development is invariant under the cancellation of an adjacent inverse pair.** -/
theorem stbDev_head_cancel_true (t : ℤ → FreeGroup α) (c : α → ℤ) (j : ℤ) (a : α)
    (L : List (α × Bool)) :
    stbDev t c j ((a, true) :: (a, false) :: L) = stbDev t c j L := by
  rw [stbDev_cons_true, stbDev_cons_false,
    show (a, j + c a - c a) = (a, j) by rw [show j + c a - c a = j by ring],
    show j + c a - c a = j by ring, ← mul_assoc, stbEdge_mul_inv, one_mul]

theorem stbDev_head_cancel_false (t : ℤ → FreeGroup α) (c : α → ℤ) (j : ℤ) (a : α)
    (L : List (α × Bool)) :
    stbDev t c j ((a, false) :: (a, true) :: L) = stbDev t c j L := by
  rw [stbDev_cons_false, stbDev_cons_true, show j - c a + c a = j by ring, ← mul_assoc,
    stbEdge_inv_mul, one_mul]

theorem stbDev_step_not (t : ℤ → FreeGroup α) (c : α → ℤ) (i : ℤ)
    (L₃ L₄ : List (α × Bool)) (x : α) (b : Bool) :
    stbDev t c i (L₃ ++ (x, b) :: (x, !b) :: L₄) = stbDev t c i (L₃ ++ L₄) := by
  cases b
  · simp only [Bool.not_false]
    rw [stbDev_append, stbDev_append]
    exact congrArg (fun z => stbDev t c i L₃ * z)
      (stbDev_head_cancel_false t c (i + lsig c L₃) x L₄)
  · simp only [Bool.not_true]
    rw [stbDev_append, stbDev_append]
    exact congrArg (fun z => stbDev t c i L₃ * z)
      (stbDev_head_cancel_true t c (i + lsig c L₃) x L₄)

theorem stbDev_step (t : ℤ → FreeGroup α) (c : α → ℤ) (i : ℤ)
    {L₁ L₂ : List (α × Bool)} (h : FreeGroup.Red.Step L₁ L₂) :
    stbDev t c i L₁ = stbDev t c i L₂ := by
  cases h
  exact stbDev_step_not t c i _ _ _ _

/-- The development, as a function of the element of the free group.  (It is not a homomorphism:
the level at which the remainder of the word is read depends on the word already read.) -/
noncomputable def stbDevFun (t : ℤ → FreeGroup α) (c : α → ℤ) (i : ℤ) :
    FreeGroup α → FreeGroup (stbBeta t c) :=
  Quot.lift (stbDev t c i) fun _L₁ _L₂ h => stbDev_step t c i h

theorem stbDevFun_mk (t : ℤ → FreeGroup α) (c : α → ℤ) (i : ℤ) (L : List (α × Bool)) :
    stbDevFun t c i (FreeGroup.mk L) = stbDev t c i L := rfl

/-- **The development is a function of the represented element of the free group.** -/
theorem stbDev_eq_of_mk_eq (t : ℤ → FreeGroup α) (c : α → ℤ) (i : ℤ)
    {L₁ L₂ : List (α × Bool)} (h : FreeGroup.mk L₁ = FreeGroup.mk L₂) :
    stbDev t c i L₁ = stbDev t c i L₂ := by
  rw [← stbDevFun_mk t c i L₁, h, stbDevFun_mk t c i L₂]

/-- A word representing the trivial element has trivial development. -/
theorem stbDev_eq_one_of_mk_eq_one (t : ℤ → FreeGroup α) (c : α → ℤ) (i : ℤ)
    {L : List (α × Bool)} (h : FreeGroup.mk L = 1) : stbDev t c i L = 1 := by
  rw [stbDev_eq_of_mk_eq t c i (L₂ := ([] : List (α × Bool))) (by rw [h]; rfl),
    stbDev_nil]

/-- **The development of a reversed word is the inverse development**, read from the level reached
by the word. -/
theorem stbDev_invRev (t : ℤ → FreeGroup α) (c : α → ℤ) (i : ℤ) (L : List (α × Bool)) :
    stbDev t c (i + lsig c L) (FreeGroup.invRev L) = (stbDev t c i L)⁻¹ := by
  induction L generalizing i with
  | nil => simp [stbDev_nil]
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    rw [FreeGroup.invRev_cons, show FreeGroup.invRev [(a, b)] = [(a, !b)] from rfl, stbDev_append]
    cases b
    · simp only [Bool.not_false]
      have h1 : i + lsig c ((a, false) :: L) = (i + -c a) + lsig c L := by
        rw [stb_lsig_cons_false]; ring
      have h2 : (i + -c a + lsig c L) + lsig c (FreeGroup.invRev L) = i - c a := by
        rw [stb_lsig_invRev]; ring
      rw [h1, h2, ih (i + -c a), show i + -c a = i - c a by ring,
        stbDev_singleton_true, stbEdge_true_eq_inv, stbDev_cons_false, mul_inv_rev]
    · simp only [Bool.not_true]
      have h1 : i + lsig c ((a, true) :: L) = (i + c a) + lsig c L := by
        rw [stb_lsig_cons_true]; ring
      have h2 : (i + c a + lsig c L) + lsig c (FreeGroup.invRev L) = i + c a := by
        rw [stb_lsig_invRev]; ring
      rw [h1, h2, ih (i + c a), stbDev_singleton_false,
        show (a, i + c a - c a) = (a, i) by rw [show i + c a - c a = i by ring],
        stbEdge_false_eq_inv, stbDev_cons_true, mul_inv_rev]

/-! ## The loop word of an edge and the expansion of a word in the basis -/

/-- The loop word of the edge `e = (x,i)` based at level `0`:
`toWord (t i) ++ [(x,true)] ++ (toWord (t (i + c x)))⁻¹`.  Read from level `0` it traverses the
tree path from `0` to `i`, then the edge, then the tree path back to `0`. -/
noncomputable def stbEdgeWord (t : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ) :
    List (α × Bool) := by
  classical
  exact FreeGroup.toWord (t e.2) ++ [(e.1, true)] ++
    FreeGroup.invRev (FreeGroup.toWord (t (e.2 + c e.1)))

/-- The signed loop word of the edge `e` (`b = false` gives the inverse word). -/
noncomputable def stbEdgeWordSigned (t : ℤ → FreeGroup α) (c : α → ℤ)
    (e : α × ℤ) (b : Bool) : List (α × Bool) :=
  bif b then stbEdgeWord t c e else FreeGroup.invRev (stbEdgeWord t c e)

/-- **The expansion of a word in the Schreier basis**: the word obtained by replacing each letter
`(e,b)` by the loop word of the corresponding traversal of the edge `e`. -/
noncomputable def stbExpand (t : ℤ → FreeGroup α) (c : α → ℤ)
    (w : FreeGroup (stbBeta t c)) : List (α × Bool) :=
  ((FreeGroup.toWord w).map (fun p => stbEdgeWordSigned t c p.1.1 p.2)).flatten

/-! ## `mk` plumbing -/

theorem stb_mk_append {β : Type*} (L₁ L₂ : List (β × Bool)) :
    FreeGroup.mk (L₁ ++ L₂) = FreeGroup.mk L₁ * FreeGroup.mk L₂ :=
  (FreeGroup.mul_mk (L₁ := L₁) (L₂ := L₂)).symm

theorem stb_mk_singleton_true {β : Type*} (a : β) :
    FreeGroup.mk [(a, true)] = FreeGroup.of a := rfl

theorem stb_mk_invRev {β : Type*} (L : List (β × Bool)) :
    FreeGroup.mk (FreeGroup.invRev L) = (FreeGroup.mk L)⁻¹ :=
  (FreeGroup.inv_mk (L := L)).symm

theorem stb_mk_singleton_false {β : Type*} (a : β) :
    FreeGroup.mk [(a, false)] = (FreeGroup.of a)⁻¹ := by
  have h : ([(a, false)] : List (β × Bool)) = FreeGroup.invRev [(a, true)] := by
    simp [FreeGroup.invRev]
  rw [h, stb_mk_invRev]
  rfl

/-- The word of a list product, as a product of signed generators. -/
theorem stb_mk_eq_prod_map_signed {β : Type*} (L : List (β × Bool)) :
    FreeGroup.mk L =
      (L.map fun p => if p.2 then FreeGroup.of p.1 else (FreeGroup.of p.1)⁻¹).prod := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    rw [show ((a, b) :: L : List (β × Bool)) = [(a, b)] ++ L from rfl, stb_mk_append, ih,
      List.map_append, List.prod_append]
    cases b <;> simp [stb_mk_singleton_true, stb_mk_singleton_false]

theorem stb_mk_flatten_map {β : Type*} (f : β → List (α × Bool)) (l : List β) :
    FreeGroup.mk (l.map f).flatten = (l.map fun x => FreeGroup.mk (f x)).prod := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    rw [List.map_cons, List.flatten_cons, stb_mk_append, ih, List.map_cons, List.prod_cons]

/-- The development of the concatenation of a mapped list of words of weight `0`. -/
theorem stb_dev_map_flatten_of_lsig_eq_zero (t : ℤ → FreeGroup α) (c : α → ℤ)
    {β : Type*} (l : List β) (f : β → List (α × Bool))
    (h : ∀ x ∈ l.map f, lsig c x = 0) (i : ℤ) :
    stbDev t c i (l.map f).flatten = (l.map fun x => stbDev t c i (f x)).prod := by
  induction l with
  | nil => rfl
  | cons x tl ih =>
    have hx : lsig c (f x) = 0 := h (f x) (by simp)
    have ht : ∀ y ∈ tl.map f, lsig c y = 0 := fun y hy => h y (by simp [hy])
    rw [List.map_cons, List.flatten_cons, stbDev_append, hx, add_zero, ih ht, List.map_cons,
      List.prod_cons]

end Work.OROneRel
