import Mathlib
import Submission.Work.OROneRel.substDefs
import Submission.Work.OROneRel.FreiheitssatzDefs
import Submission.Work.OROneRel.HNNStep
import Submission.Work.OROneRel.rewriteAux_append
import Submission.Work.OROneRel.rewrite_length_lt

/-!
# Plumbing for the decorated transport of the Magnus substitution

Vocabulary for `Work.OROneRel.magRew_subst_localisation`.

For the Magnus substitution `ψ = subst t x p q` (`t ↦ t ^ p`, `x ↦ x * t ^ (-q)`, all other
generators fixed) and a word `L`, the substituted word `M := substList t x p q L` is the
concatenation of the blocks `blkLetter t x p q c` of the letters `c` of `L` (`substDefs`).

This file fixes the *exponent bookkeeping* of those blocks:

* `blkSigma t x p q c` is the exponent sum in `t` of the whole block of `c`;
* `blkPre t x p q c` (resp. `blkPost t x p q c`) is the exponent sum in `t` of the part of that block
  *before* (resp. *after*) its unique letter different from `t` (so that for `c.1 ≠ t` one has
  `blkSigma = blkPre + blkPost`);

and the elementary consequences for the Magnus rewriting `rewrite`:

* `rewriteAux t acc (blkLetter …)` is *empty* if `c.1 = t` and the single decorated letter
  `((c.1, acc + blkPre), c.2)` otherwise (`rewriteAux_blkLetter_of_eq/_of_ne`);
* hence the rewriting of a block word is computed letter by letter
  (`rewriteAux_substList_cons`), with the head (`head_rewriteAux_substList`) and last
  (`getLast_rewriteAux_substList`) letter read off from the first/last letter different from `t`.

It also contains the *expansion* `expAux` of a decorated word (the inverse operation to the Magnus
rewriting: the `t`-frame is put back), together with the structure lemmas used by the cyclic
reduction of the substituted relator.
-/

namespace Work.OROneRel

universe u

variable {β : Type u}

variable {t x : β} {p q : ℤ}

/-! ### The block exponent bookkeeping -/

/-- The exponent sum in `t` of the block of a letter `c`. -/
noncomputable def blkSigma (t x : β) (p q : ℤ) (c : β × Bool) : ℤ := by
  classical
  exact
    if c.1 = t then (if c.2 then p else -p)
    else if c.1 = x then (if c.2 then -q else q)
    else 0

/-- The exponent sum in `t` of the part of the block of `c` preceding its letter different from `t`
(`0` when there is none). -/
noncomputable def blkPre (t x : β) (p q : ℤ) (c : β × Bool) : ℤ := by
  classical
  exact
    if c.1 = t then 0
    else if c.1 = x then (if c.2 then 0 else q)
    else 0

/-- The exponent sum in `t` of the part of the block of `c` following its letter different from `t`
(`0` when there is none). -/
noncomputable def blkPost (t x : β) (p q : ℤ) (c : β × Bool) : ℤ := by
  classical
  exact
    if c.1 = t then 0
    else if c.1 = x then (if c.2 then -q else 0)
    else 0

theorem blkSigma_of_eq {c : β × Bool} (h : c.1 = t) :
    blkSigma t x p q c = (if c.2 then p else -p) := by
  rw [blkSigma]; simp only [if_pos h]

theorem blkSigma_of_ne_of_eq {c : β × Bool} (h : c.1 ≠ t) (h2 : c.1 = x) :
    blkSigma t x p q c = (if c.2 then -q else q) := by
  rw [blkSigma]; simp only [if_neg h, if_pos h2]

theorem blkSigma_of_ne_of_ne {c : β × Bool} (h : c.1 ≠ t) (h2 : c.1 ≠ x) :
    blkSigma t x p q c = 0 := by
  rw [blkSigma]; simp only [if_neg h, if_neg h2]

theorem blkPre_of_eq {c : β × Bool} (h : c.1 = t) : blkPre t x p q c = 0 := by
  rw [blkPre]; simp only [if_pos h]

theorem blkPre_of_ne_of_eq {c : β × Bool} (h : c.1 ≠ t) (h2 : c.1 = x) :
    blkPre t x p q c = (if c.2 then 0 else q) := by
  rw [blkPre]; simp only [if_neg h, if_pos h2]

theorem blkPre_of_ne_of_ne {c : β × Bool} (h : c.1 ≠ t) (h2 : c.1 ≠ x) :
    blkPre t x p q c = 0 := by
  rw [blkPre]; simp only [if_neg h, if_neg h2]

theorem blkPost_of_eq {c : β × Bool} (h : c.1 = t) : blkPost t x p q c = 0 := by
  rw [blkPost]; simp only [if_pos h]

theorem blkPost_of_ne_of_eq {c : β × Bool} (h : c.1 ≠ t) (h2 : c.1 = x) :
    blkPost t x p q c = (if c.2 then -q else 0) := by
  rw [blkPost]; simp only [if_neg h, if_pos h2]

theorem blkPost_of_ne_of_ne {c : β × Bool} (h : c.1 ≠ t) (h2 : c.1 ≠ x) :
    blkPost t x p q c = 0 := by
  rw [blkPost]; simp only [if_neg h, if_neg h2]

/-- For a letter different from `t` the block exponent splits into the parts before and after the
single letter of the block different from `t`. -/
theorem blkSigma_eq_pre_add_post {c : β × Bool} (h : c.1 ≠ t) :
    blkSigma t x p q c = blkPre t x p q c + blkPost t x p q c := by
  by_cases h2 : c.1 = x
  · rw [blkSigma_of_ne_of_eq h h2, blkPre_of_ne_of_eq h h2, blkPost_of_ne_of_eq h h2]
    cases c.2 <;> simp
  · rw [blkSigma_of_ne_of_ne h h2, blkPre_of_ne_of_ne h h2, blkPost_of_ne_of_ne h h2]
    simp

/-! ### Elementary word lemmas for the blocks -/

/-! ### Computation rules for the blocks themselves -/

theorem blkLetter_of_eq {c : β × Bool} (h : c.1 = t) :
    blkLetter t x p q c = runLetters t (if c.2 then p else -p) := by
  rw [blkLetter]; simp only [if_pos h]

theorem blkLetter_of_ne_of_eq {c : β × Bool} (h : c.1 ≠ t) (h2 : c.1 = x) :
    blkLetter t x p q c =
      (if c.2 then [c] ++ runLetters t (-q) else runLetters t q ++ [c]) := by
  rw [blkLetter]; simp only [if_neg h, if_pos h2]

theorem blkLetter_of_ne_of_ne {c : β × Bool} (h : c.1 ≠ t) (h2 : c.1 ≠ x) :
    blkLetter t x p q c = [c] := by
  rw [blkLetter]; simp only [if_neg h, if_neg h2]

theorem substList_append (L₁ L₂ : List (β × Bool)) :
    substList t x p q (L₁ ++ L₂) = substList t x p q L₁ ++ substList t x p q L₂ := by
  rw [substList, substList, substList, List.map_append, List.flatten_append]

theorem substList_cons (c : β × Bool) (L : List (β × Bool)) :
    substList t x p q (c :: L) = blkLetter t x p q c ++ substList t x p q L := by
  rw [substList, substList, List.map_cons, List.flatten_cons]

theorem substList_nil : substList t x p q ([] : List (β × Bool)) = [] := by
  rw [substList]; simp

/-- `substList` commutes with flattening a replicated list. -/
theorem substList_flatten_replicate (L : List (β × Bool)) (k : ℕ) :
    substList t x p q ((List.replicate k L).flatten) =
      (List.replicate k (substList t x p q L)).flatten := by
  induction k with
  | zero => simp [substList]
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, substList_append, ih, List.replicate_succ,
      List.flatten_cons]

theorem sigmaList_append (L₁ L₂ : List (β × Bool)) :
    sigmaList t (L₁ ++ L₂) = sigmaList t L₁ + sigmaList t L₂ := by
  simp [sigmaList, List.map_append]

/-- The letters of a signed run of `t` are exactly the letters `t` with the sign of the run. -/
theorem runLetters_mem {n : ℤ} {c : β × Bool} (h : c ∈ runLetters t n) :
    c = (t, decide (0 < n)) := by
  rw [runLetters, List.mem_replicate] at h
  exact h.2

theorem runLetters_eq_nil_iff {n : ℤ} : (runLetters t n).length = 0 ↔ n = 0 := by
  rw [runLetters, List.length_replicate, Int.natAbs_eq_zero]

theorem sigmaList_runLetters (n : ℤ) : sigmaList t (runLetters t n) = n := by
  have key : ∀ (k : ℕ) (b : Bool),
      sigmaList t (List.replicate k ((t : β), b)) = (if b then (k : ℤ) else -(k : ℤ)) := by
    intro k b
    rw [sigmaList, List.map_replicate, List.sum_replicate]
    cases b <;> simp [letterSign, nsmul_eq_mul]
  rw [runLetters, key]
  split_ifs with h
  · rw [Int.natAbs_of_nonneg (le_of_lt (of_decide_eq_true h))]
  · rw [Int.ofNat_natAbs_of_nonpos (not_lt.mp (mt decide_eq_true h))]
    ring

theorem rewriteAux_runLetters (acc n : ℤ) : rewriteAux t acc (runLetters t n) = [] := by
  have key : ∀ (k : ℕ), ∀ (b : Bool) (acc : ℤ),
      rewriteAux t acc (List.replicate k ((t : β), b)) = [] := by
    intro k
    induction k with
    | zero => intro b acc; rw [List.replicate_zero, rewriteAux.eq_1]
    | succ k ih =>
      intro b acc
      rw [List.replicate_succ, rewriteAux.eq_2, dif_pos (rfl : (t : β) = t)]
      exact ih b (acc + (if b then (1 : ℤ) else -1))
  rw [runLetters]
  exact key n.natAbs (decide (0 < n)) acc

/-- The Magnus rewriting of a single letter different from `t`. -/
theorem rewriteAux_singleton_of_ne {c : β × Bool} (h : c.1 ≠ t) (acc : ℤ) :
    rewriteAux t acc [c] = [((⟨c.1, h⟩, acc), c.2)] := by
  rw [rewriteAux.eq_2, dif_neg (show ¬(c).1 = t from h), rewriteAux.eq_1]

theorem sigmaList_singleton_of_ne {c : β × Bool} (h : c.1 ≠ t) : sigmaList t [c] = 0 := by
  rw [sigmaList]
  simp [letterSign, h]

/-! ### The rewriting of the blocks -/

theorem sigmaList_blkLetter (c : β × Bool) :
    sigmaList t (blkLetter t x p q c) = blkSigma t x p q c := by
  by_cases h : c.1 = t
  · rw [blkLetter_of_eq h, blkSigma_of_eq h]
    cases hb : c.2 <;> simp [hb, sigmaList_runLetters]
  · by_cases h2 : c.1 = x
    · rw [blkLetter_of_ne_of_eq h h2, blkSigma_of_ne_of_eq h h2]
      cases c.2
      · simp only [Bool.false_eq_true, reduceIte]
        rw [sigmaList_append, sigmaList_runLetters, sigmaList_singleton_of_ne h, add_zero]
      · simp only [reduceIte]
        rw [sigmaList_append, sigmaList_singleton_of_ne h, sigmaList_runLetters, zero_add]
    · rw [blkLetter_of_ne_of_ne h h2, blkSigma_of_ne_of_ne h h2]
      exact sigmaList_singleton_of_ne h

theorem rewriteAux_blkLetter_of_eq {c : β × Bool} (h : c.1 = t) (acc : ℤ) :
    rewriteAux t acc (blkLetter t x p q c) = [] := by
  rw [blkLetter_of_eq h]
  exact rewriteAux_runLetters acc _

theorem rewriteAux_blkLetter_of_ne {c : β × Bool} (h : c.1 ≠ t) (acc : ℤ) :
    rewriteAux t acc (blkLetter t x p q c) =
      [((⟨c.1, h⟩, acc + blkPre t x p q c), c.2)] := by
  by_cases h2 : c.1 = x
  · rw [blkLetter_of_ne_of_eq h h2, blkPre_of_ne_of_eq h h2]
    by_cases hb : c.2 = true
    · rw [if_pos hb, if_pos hb]
      rw [rewriteAux_append, rewriteAux_singleton_of_ne h, sigmaList_singleton_of_ne h,
        rewriteAux_runLetters, List.append_nil, add_zero]
    · rw [if_neg hb, if_neg hb]
      rw [rewriteAux_append, rewriteAux_runLetters, List.nil_append, sigmaList_runLetters,
        rewriteAux_singleton_of_ne h]
  · rw [blkLetter_of_ne_of_ne h h2, blkPre_of_ne_of_ne h h2,
      rewriteAux_singleton_of_ne h, add_zero]

/-- The rewriting of a block word, one block at a time. -/
theorem rewriteAux_substList_cons (c : β × Bool) (L : List (β × Bool)) (acc : ℤ) :
    rewriteAux t acc (substList t x p q (c :: L)) =
      rewriteAux t acc (blkLetter t x p q c) ++
        rewriteAux t (acc + blkSigma t x p q c) (substList t x p q L) := by
  rw [substList_cons, rewriteAux_append, sigmaList_blkLetter]

theorem sigmaList_substList (L : List (β × Bool)) :
    sigmaList t (substList t x p q L) = (L.map (blkSigma t x p q)).sum := by
  induction L with
  | nil => simp [substList, sigmaList]
  | cons c L ih => rw [substList_cons, sigmaList_append, sigmaList_blkLetter, ih]; simp

/-- Every letter of `substList` of a list of letters `t` lies in the corresponding run, so the
Magnus rewriting of that block word is empty. -/
theorem rewriteAux_substList_of_all_t {L : List (β × Bool)} (hL : ∀ c ∈ L, c.1 = t) :
    ∀ acc : ℤ, rewriteAux t acc (substList t x p q L) = [] := by
  induction L with
  | nil => intro acc; rw [substList_nil, rewriteAux.eq_1]
  | cons c L ih =>
    intro acc
    rw [substList_cons, rewriteAux_append, rewriteAux_blkLetter_of_eq (hL c (by simp)),
      List.nil_append]
    exact ih (fun d hd => hL d (by simp [hd])) _

/-! ### The accumulated block exponent -/

/-- The decoration of the first letter different from `t` of a block word `substList L`: the sum of
the block exponents of the letters of `L` preceding it, added to the initial value. -/
noncomputable def accSum (t x : β) (p q : ℤ) (acc : ℤ) (L : List (β × Bool)) : ℤ :=
  (L.map (blkSigma t x p q)).foldl (fun a b => a + b) acc

theorem accSum_nil (acc : ℤ) : accSum t x p q acc ([] : List (β × Bool)) = acc := rfl

theorem accSum_cons (c : β × Bool) (L : List (β × Bool)) (acc : ℤ) :
    accSum t x p q acc (c :: L) = accSum t x p q (acc + blkSigma t x p q c) L := by
  rw [accSum, accSum, List.map_cons, List.foldl_cons]

theorem accSum_eq (L : List (β × Bool)) (acc : ℤ) :
    accSum t x p q acc L = acc + (L.map (blkSigma t x p q)).sum := by
  induction L generalizing acc with
  | nil => simp [accSum, List.map_nil]
  | cons c L ih =>
    rw [accSum_cons, ih (acc + blkSigma t x p q c), List.map_cons, List.sum_cons, Int.add_assoc]

/-- The head of the Magnus rewriting of a block word: the first letter of `L` different from `t`,
with its decoration. -/
theorem head_rewriteAux_substList {Mid : List (β × Bool)} {v : β × Bool}
    (hMid : ∀ m ∈ Mid, m.1 = t) (hv : v.1 ≠ t) :
    ∀ (acc : ℤ) (Q : List (β × Bool)),
      rewriteAux t acc (substList t x p q (Mid ++ v :: Q)) =
        ((⟨v.1, hv⟩, accSum t x p q acc Mid + blkPre t x p q v), v.2) ::
          rewriteAux t (accSum t x p q acc Mid + blkSigma t x p q v) (substList t x p q Q) := by
  induction Mid with
  | nil =>
    intro acc Q
    rw [List.nil_append, substList_cons, rewriteAux_append, rewriteAux_blkLetter_of_ne hv,
      sigmaList_blkLetter, accSum_nil, List.singleton_append]
  | cons m Mid ih =>
    intro acc Q
    rw [List.cons_append, substList_cons, rewriteAux_append,
      rewriteAux_blkLetter_of_eq (hMid m (by simp)), List.nil_append, sigmaList_blkLetter,
      accSum_cons]
    exact ih (fun d hd => hMid d (by simp [hd])) (acc + blkSigma t x p q m) Q

/-- The last letter of the Magnus rewriting of a block word: the last letter of `L` different from
`t`, with its decoration. -/
theorem getLast_rewriteAux_substList {Mid : List (β × Bool)} {u : β × Bool}
    (hMid : ∀ m ∈ Mid, m.1 = t) (hu : u.1 ≠ t) (acc : ℤ) (P : List (β × Bool)) :
    (rewriteAux t acc (substList t x p q (P ++ u :: Mid))).getLast? =
      some ((⟨u.1, hu⟩, accSum t x p q acc P + blkPre t x p q u), u.2) := by
  have h1 : substList t x p q (P ++ u :: Mid)
      = substList t x p q P ++ (blkLetter t x p q u ++ substList t x p q Mid) := by
    rw [substList_append, substList_cons]
  have hred : rewriteAux t (acc + sigmaList t (substList t x p q P))
      (blkLetter t x p q u ++ substList t x p q Mid)
      = [((⟨u.1, hu⟩, acc + sigmaList t (substList t x p q P) + blkPre t x p q u), u.2)] := by
    rw [rewriteAux_append, rewriteAux_blkLetter_of_ne hu,
      rewriteAux_substList_of_all_t hMid, List.append_nil]
  rw [h1, rewriteAux_append, hred, List.getLast?_append_cons]
  rw [accSum_eq, sigmaList_substList]
  simp

end Work.OROneRel
