import Submission.Work.NielsenAlign
import Mathlib.Data.List.Chain

open Commons.GroupTheory.FreeGroup
set_option autoImplicit false

/-!
# Cancellation pairing of a word under free reduction (foundation for the
general-`k` aggregate / "T1")

When a word `W` is freely reduced, its letters split into **survivors** (the
letters of `reduce W`, in order) and **cancelled letters**, each cancelled
letter being paired with the letter that annihilates it.  This module
constructs that pairing by recursion **mirroring `FreeGroup.reduce` exactly**
(`reduce (l :: t)` prepends `l` to `reduce t`, cancelling if `l` is the
letter-inverse of the head of `reduce t` — the head of the reduced tail is
its *first survivor*):

* `survivorPos W` — the positions (inside `W`) of the letters of
  `reduce W`, in left-to-right order;
* `cancelledPairs W` — the pairs `(i, j)` of cancelled positions, `i < j`.

Since the definitions follow the recursion of `reduce`, every structural fact
is a clean induction on `W`.  Proved in this file (first primitives of the
planarity theory; kernel-checked, axioms `[propext, Classical.choice,
Quot.sound]`):

1. `reduce_cons_nil` / `reduce_cons_cancel` / `reduce_cons_nocancel`: the
   explicit step lemmas of `reduce` on a cons (via the `letterInv` ↔
   componentwise condition bridge `fst_letterInv` / `snd_letterInv` /
   `letterInv_of_cond`);
2. `survivorPos_length` : `(survivorPos W).length = (reduce W).length`, so
   `survivorPos_eq_nil_iff` : `survivorPos W = [] ↔ reduce W = []`;
3. `survivorPos_lt_length` : survivor positions lie inside `W`;
4. `cancelledPairs_cons_nil` / `cancelledPairs_cons_cancel` /
   `cancelledPairs_cons_nocancel`: step lemmas of the pairs recursion;
5. `pair_lt` / `pair_lt_length` : a cancelled pair has increasing positions
   (`i < j`) strictly inside `W` (`j < W.length`);
6. `survivorPos_sorted` : the survivor positions of `W` are strictly
   increasing (`List.IsChain (· < ·) (survivorPos W)`; helpers
   `isChain_map_add`, `isChain_head_lt`), so the first survivor position is
   the minimum;
7. `survivor_not_inside_pair` : no survivor position of `W` lies strictly
   between the endpoints of a cancelled pair — every position strictly
   inside a pair is cancelled (the engine for the no-crossing/interval
   joint induction; the `cons_cancel` case uses head-minimality via
   `isChain_head_lt`, `cons_nocancel` and the shifted-tail cases use the
   induction hypothesis).

8. `position_covered` : every position of `W` is either a survivor or
   occurs in a cancelled pair (coverage);
9. `survivor_not_pair` : a survivor is never an endpoint of a cancelled
   pair;
10. `pairs_no_cross` : no two cancelled pairs cross (given pairs `(i,j)`,
    `(k,l)` with `i < k`, not `(k < j ∧ j < l)`); uses
    `survivor_not_inside_pair` to rule out the new-pair-vs-shifted-pair
    case;
11. `pair_interval_complete` : every position strictly inside a cancelled
    pair is cancelled with its partner strictly inside too (uses coverage
    `position_covered` and head-minimality for the region below the first
    survivor).

Together items 6–11 form the completed planarity layer: survivor positions
sorted, no survivor inside a pair, coverage, no crossings, interval
completeness.  These are exactly the facts the general-`k` aggregate lemma
(T1, `NielsenReductionBlueprint.lean`) consumes.

12. `survivorPos_letter` : the letter of `W` at a survivor position equals
    the corresponding letter of `reduce W` (`(survivorPos W)[k]? = some p`
    ⟹ `W[p]? = (reduce W)[k]?`; helper `cons_get_succ`);
13. `pair_letters_inv` : the letters at the endpoints of a cancelled pair
    are letter-inverses (`letterInv (W[i]) = W[j]` for a pair `(i,j)`;
    new-pair case via the cancel condition `letterInv a = hd` and
    `survivorPos_letter` at index 0).

14. `survivorPos_length_add` : `2·|cancelledPairs W| + |survivorPos W| =
    |W|` — every letter is either a survivor or one of the two endpoints of a
    cancelled pair (counting companion of `position_covered`).

15. factor-segment seeds: `seg_take_isReduced` / `seg_drop_isReduced` /
    `segment_isReduced` (prefixes, suffixes and contiguous segments `[lo, hi)`
    of a reduced word are reduced) and `isReduced_reduce_ne_of_ne_nil` (a
    nonempty reduced word does not reduce to the empty word);
16. `pair_eq_of_share` (**partner uniqueness**): two cancelled pairs that
    share a position are the same pair (helper `share_shift_down`); used by
    the span induction below.

17. `mk_single_letter_inv`: `mk [letterInv l] = (mk [l])⁻¹` in the free
    group (the last small piece for the span induction);
18. `drop_take_decomp`: a segment `[a, c)` splits at any cut point `b`
    (`a ≤ b ≤ c ≤ W.length`) into its two consecutive pieces — the
    `drop`/`take` decomposition used by the span induction.

19. `interval_fully_cancelled_reduce_empty` (**the span induction**): a
    closed interval `[i, j]` of `W` whose positions are all paired within
    itself forces its segment to reduce to the empty word.  Peels the pair
    of the left endpoint `i` (partner `y`, via `pair_eq_of_share`), splits
    at `y` with `drop_take_decomp`, inherits coverage on the two inner
    intervals (`left_cover` via `pair_interval_complete`; `right_cover` via
    `pairs_no_cross` + `pair_eq_of_share`), recurses by the span, and closes
    at the `mk`-level (`pair_letters_inv` + `mk_single_letter_inv`,
    `reduce.sound`).  Helpers: `seg_take_one_cons`, `seg_drop_head_get?`,
    `seg_mk_drop_single`, `red_to_one`, `red_of_mk_one`, `left_cover`,
    `right_cover`.

20. `pair_not_in_reduced_factor` (**the factor-segment corollary**): a
    cancelled pair of a concatenation `A ++ F ++ B` never has both endpoints
    inside the reduced factor `F` (helper `factor_segment_eq` identifies the
    `F`-block segment with the corresponding segment of `F`; the span
    induction makes it reduce to `[]`, contradicting reducedness via
    `segment_isReduced` + `isReduced_reduce_ne_of_ne_nil`).  This is the
    bridge from single-word pairing to factor concatenations.

Open next: the **general-`k` aggregate lemma T1** (a tuple of reduced words
with reduced product of length ≤ 1 has a factor fully absorbed by its ≤ 2
neighbours) — `NielsenReductionBlueprint.lean` item T1; the pairing layer of
`CancelPair.lean` (items 1–20) is complete.
-/

namespace Submission.Nielsen

/-- Shift a position by one. -/
abbrev shiftPos (p : ℕ) : ℕ := p + 1

/-- Shift both endpoints of a pair by one. -/
abbrev shiftPair (ab : ℕ × ℕ) : ℕ × ℕ := (ab.1 + 1, ab.2 + 1)

/-- The positions of the letters that survive the reduction of `W`, in
left-to-right order. -/
def survivorPos {α : Type*} [DecidableEq α] : List (α × Bool) → List ℕ
  | [] => []
  | l :: t =>
      match FreeGroup.reduce t with
      | [] => [0]
      | hd :: tl => if letterInv l = hd then (survivorPos t).tail.map shiftPos
                    else 0 :: (survivorPos t).map shiftPos

/-- The cancelled pairs `(i, j)` of positions of `W`. -/
def cancelledPairs {α : Type*} [DecidableEq α] : List (α × Bool) → List (ℕ × ℕ)
  | [] => []
  | l :: t =>
      let pr := (cancelledPairs t).map shiftPair
      match FreeGroup.reduce t, survivorPos t with
      | hd :: tl, p :: ptl => if letterInv l = hd then (0, p + 1) :: pr else pr
      | _, _ => pr

lemma fst_letterInv {α : Type*} {l hd : α × Bool} (h : letterInv l = hd) : l.1 = hd.1 := by
  have hf := congrArg Prod.fst h
  calc l.1 = (letterInv l).1 := rfl
  _ = hd.1 := hf

lemma snd_letterInv {α : Type*} {l hd : α × Bool} (h : letterInv l = hd) : l.2 = !hd.2 := by
  have hs := congrArg Prod.snd h
  simp [letterInv] at hs
  exact hs

lemma letterInv_of_cond {α : Type*} {l hd : α × Bool}
    (h1 : l.1 = hd.1) (h2 : l.2 = !hd.2) : letterInv l = hd := by
  apply Prod.ext
  · calc (letterInv l).1 = l.1 := rfl
    _ = hd.1 := h1
  · calc (letterInv l).2 = !l.2 := rfl
    _ = !(!hd.2) := by rw [h2]
    _ = hd.2 := by cases hd.2 <;> simp

lemma reduce_cons_nil {α : Type*} [DecidableEq α] {l : α × Bool} {t : List (α × Bool)}
    (hr : FreeGroup.reduce t = []) : FreeGroup.reduce (l :: t) = [l] := by
  rw [FreeGroup.reduce.cons, hr]

lemma reduce_cons_cancel {α : Type*} [DecidableEq α] {l hd : α × Bool} {t tl : List (α × Bool)}
    (hr : FreeGroup.reduce t = hd :: tl) (hc : letterInv l = hd) :
    FreeGroup.reduce (l :: t) = tl := by
  rw [FreeGroup.reduce.cons, hr]
  have hcond : l.1 = hd.1 ∧ l.2 = !hd.2 := ⟨fst_letterInv hc, snd_letterInv hc⟩
  dsimp
  rw [if_pos hcond]

lemma reduce_cons_nocancel {α : Type*} [DecidableEq α] {l hd : α × Bool} {t tl : List (α × Bool)}
    (hr : FreeGroup.reduce t = hd :: tl) (hc : letterInv l ≠ hd) :
    FreeGroup.reduce (l :: t) = l :: hd :: tl := by
  rw [FreeGroup.reduce.cons, hr]
  have hcond : ¬ (l.1 = hd.1 ∧ l.2 = !hd.2) := by
    intro hc'
    apply hc
    exact letterInv_of_cond hc'.1 hc'.2
  dsimp
  rw [if_neg hcond]

lemma survivorPos_cons_nil {α : Type*} [DecidableEq α] {l : α × Bool} {t : List (α × Bool)}
    (hr : FreeGroup.reduce t = []) : survivorPos (l :: t) = [0] := by
  simp [survivorPos, hr]

lemma survivorPos_cons_cancel {α : Type*} [DecidableEq α] {l hd : α × Bool} {t tl : List (α × Bool)}
    (hr : FreeGroup.reduce t = hd :: tl) (hc : letterInv l = hd) :
    survivorPos (l :: t) = (survivorPos t).tail.map shiftPos := by
  simp [survivorPos, hr, hc]

lemma survivorPos_cons_nocancel {α : Type*} [DecidableEq α] {l hd : α × Bool} {t tl : List (α × Bool)}
    (hr : FreeGroup.reduce t = hd :: tl) (hc : letterInv l ≠ hd) :
    survivorPos (l :: t) = 0 :: (survivorPos t).map shiftPos := by
  simp [survivorPos, hr, hc]

lemma survivorPos_length {α : Type*} [DecidableEq α] (W : List (α × Bool)) :
    (survivorPos W).length = (FreeGroup.reduce W).length := by
  induction W with
  | nil => rfl
  | cons l t ih =>
      cases hr : FreeGroup.reduce t with
      | nil =>
          rw [survivorPos_cons_nil hr, reduce_cons_nil hr]
          simp
      | cons hd tl =>
          by_cases hc : letterInv l = hd
          · rw [survivorPos_cons_cancel hr hc, reduce_cons_cancel hr hc]
            rw [List.length_map, List.length_tail, ih, hr]
            simp
          · rw [survivorPos_cons_nocancel hr hc, reduce_cons_nocancel hr hc]
            simp [ih, hr]

lemma survivorPos_eq_nil_iff {α : Type*} [DecidableEq α] (W : List (α × Bool)) :
    survivorPos W = [] ↔ FreeGroup.reduce W = [] := by
  constructor
  · intro h
    apply List.eq_nil_iff_length_eq_zero.mpr
    rw [← survivorPos_length, h]
    simp
  · intro h
    apply List.length_eq_zero_iff.mp
    rw [survivorPos_length, h]
    simp

lemma survivorPos_lt_length {α : Type*} [DecidableEq α] (W : List (α × Bool))
    {p : ℕ} (hp : p ∈ survivorPos W) : p < W.length := by
  induction W generalizing p with
  | nil => simp [survivorPos] at hp
  | cons l t ih =>
      cases hr : FreeGroup.reduce t with
      | nil =>
          rw [survivorPos_cons_nil hr] at hp
          simp at hp
          subst p
          simp
      | cons hd tl =>
          by_cases hc : letterInv l = hd
          · rw [survivorPos_cons_cancel hr hc] at hp
            rw [List.mem_map] at hp
            rcases hp with ⟨q, hq, hp⟩
            have hp' : q + 1 = p := by simpa [shiftPos] using hp
            subst p
            have hq' : q < t.length := ih (List.mem_of_mem_tail hq)
            rw [List.length_cons]
            omega
          · rw [survivorPos_cons_nocancel hr hc] at hp
            rw [List.mem_cons] at hp
            rcases hp with hp | hp
            · subst p
              simp
            · rw [List.mem_map] at hp
              rcases hp with ⟨q, hq, hp⟩
              have hp' : q + 1 = p := by simpa [shiftPos] using hp
              subst p
              have hq' : q < t.length := ih hq
              rw [List.length_cons]
              omega


/-! ## Cancelled pairs: step lemmas, order and bounds -/

lemma cancelledPairs_cons_nil {α : Type*} [DecidableEq α] {l : α × Bool} {t : List (α × Bool)}
    (hr : FreeGroup.reduce t = []) : cancelledPairs (l :: t) = (cancelledPairs t).map shiftPair := by
  simp [cancelledPairs, hr]

lemma cancelledPairs_cons_cancel {α : Type*} [DecidableEq α] {l hd : α × Bool} {t rest : List (α × Bool)}
    {p : ℕ} {ptl : List ℕ} (hr : FreeGroup.reduce t = hd :: rest) (hsp : survivorPos t = p :: ptl)
    (hc : letterInv l = hd) :
    cancelledPairs (l :: t) = (0, p + 1) :: (cancelledPairs t).map shiftPair := by
  simp [cancelledPairs, hr, hsp, hc]

lemma cancelledPairs_cons_nocancel {α : Type*} [DecidableEq α] {l hd : α × Bool} {t rest : List (α × Bool)}
    {p : ℕ} {ptl : List ℕ} (hr : FreeGroup.reduce t = hd :: rest) (hsp : survivorPos t = p :: ptl)
    (hc : letterInv l ≠ hd) :
    cancelledPairs (l :: t) = (cancelledPairs t).map shiftPair := by
  simp [cancelledPairs, hr, hsp, hc]

/-- A pair of the shifted tail pairs is a shifted tail pair. -/
lemma mem_shiftPair (ps : List (ℕ × ℕ)) {i j : ℕ}
    (h : (i, j) ∈ ps.map shiftPair) :
    ∃ i' j' : ℕ, (i', j') ∈ ps ∧ i = i' + 1 ∧ j = j' + 1 := by
  rw [List.mem_map] at h
  rcases h with ⟨ab, hab, heq⟩
  rcases ab with ⟨i', j'⟩
  refine ⟨i', j', hab, ?_, ?_⟩
  · have hf := congrArg Prod.fst heq
    simpa [shiftPair] using hf.symm
  · have hs := congrArg Prod.snd heq
    simpa [shiftPair] using hs.symm

/-- The endpoints of a cancelled pair are ordered: `i < j`. -/
lemma pair_lt {α : Type*} [DecidableEq α] (W : List (α × Bool)) {i j : ℕ}
    (hp : (i, j) ∈ cancelledPairs W) : i < j := by
  induction W generalizing i j with
  | nil => simp [cancelledPairs] at hp
  | cons l t ih =>
      cases hr : FreeGroup.reduce t with
      | nil =>
          rw [cancelledPairs_cons_nil hr] at hp
          rcases mem_shiftPair (cancelledPairs t) hp with ⟨i', j', hp', hi, hj⟩
          subst i
          subst j
          have hlt := ih hp'
          omega
      | cons hd tl =>
          cases hsp : survivorPos t with
          | nil =>
              have hz : FreeGroup.reduce t = [] := (survivorPos_eq_nil_iff t).mp hsp
              rw [hz] at hr
              simp at hr
          | cons p ptl =>
              by_cases hc : letterInv l = hd
              · rw [cancelledPairs_cons_cancel hr hsp hc] at hp
                rw [List.mem_cons] at hp
                rcases hp with hp | hp
                · have hi : i = 0 := congrArg Prod.fst hp
                  have hj : j = p + 1 := congrArg Prod.snd hp
                  subst i
                  subst j
                  omega
                · rcases mem_shiftPair (cancelledPairs t) hp with ⟨i', j', hp', hi, hj⟩
                  subst i
                  subst j
                  have hlt := ih hp'
                  omega
              · rw [cancelledPairs_cons_nocancel hr hsp hc] at hp
                rcases mem_shiftPair (cancelledPairs t) hp with ⟨i', j', hp', hi, hj⟩
                subst i
                subst j
                have hlt := ih hp'
                omega

/-- The right endpoint of a cancelled pair lies strictly inside `W`. -/
lemma pair_lt_length {α : Type*} [DecidableEq α] (W : List (α × Bool)) {i j : ℕ}
    (hp : (i, j) ∈ cancelledPairs W) : j < W.length := by
  induction W generalizing i j with
  | nil => simp [cancelledPairs] at hp
  | cons l t ih =>
      cases hr : FreeGroup.reduce t with
      | nil =>
          rw [cancelledPairs_cons_nil hr] at hp
          rcases mem_shiftPair (cancelledPairs t) hp with ⟨i', j', hp', hi, hj⟩
          subst j
          have hj' : j' < t.length := ih hp'
          rw [List.length_cons]
          omega
      | cons hd tl =>
          cases hsp : survivorPos t with
          | nil =>
              have hz : FreeGroup.reduce t = [] := (survivorPos_eq_nil_iff t).mp hsp
              rw [hz] at hr
              simp at hr
          | cons p ptl =>
              by_cases hc : letterInv l = hd
              · rw [cancelledPairs_cons_cancel hr hsp hc] at hp
                rw [List.mem_cons] at hp
                rcases hp with hp | hp
                · have hj : j = p + 1 := congrArg Prod.snd hp
                  subst j
                  have hp_mem : p ∈ survivorPos t := by
                    rw [hsp]
                    simp
                  have hlt := survivorPos_lt_length t hp_mem
                  rw [List.length_cons]
                  omega
                · rcases mem_shiftPair (cancelledPairs t) hp with ⟨i', j', hp', hi, hj⟩
                  subst j
                  have hj' : j' < t.length := ih hp'
                  rw [List.length_cons]
                  omega
              · rw [cancelledPairs_cons_nocancel hr hsp hc] at hp
                rcases mem_shiftPair (cancelledPairs t) hp with ⟨i', j', hp', hi, hj⟩
                subst j
                have hj' : j' < t.length := ih hp'
                rw [List.length_cons]
                omega

/-! ## Survivor positions are strictly increasing -/

/-- Adding one to every entry preserves strict increasingness of a chain. -/
lemma isChain_map_add {l : List ℕ} (h : List.IsChain (· < ·) l) :
    List.IsChain (· < ·) (l.map (fun a => a + 1)) := by
  cases l with
  | nil => simpa
  | cons a rest =>
      cases rest with
      | nil => simpa
      | cons b rest' =>
          have hrel : a < b := List.IsChain.rel_head h
          have htail : List.IsChain (· < ·) (b :: rest') := List.IsChain.tail h
          have ihrest : List.IsChain (· < ·) ((b :: rest').map (fun x => x + 1)) :=
            isChain_map_add htail
          change List.IsChain (· < ·) ((a + 1) :: (b + 1) :: (rest'.map (fun x => x + 1)))
          apply List.IsChain.cons_cons
          · omega
          · exact ihrest

/-- The survivor positions of `W` are strictly increasing; in particular the
first survivor position (if any) is the smallest one. -/
lemma survivorPos_sorted {α : Type*} [DecidableEq α] (W : List (α × Bool)) :
    List.IsChain (· < ·) (survivorPos W) := by
  induction W with
  | nil => exact List.IsChain.nil
  | cons l t ih =>
      cases hr : FreeGroup.reduce t with
      | nil =>
          rw [survivorPos_cons_nil hr]
          exact List.IsChain.singleton 0
      | cons hd tl =>
          by_cases hc : letterInv l = hd
          · rw [survivorPos_cons_cancel hr hc]
            simpa [shiftPos] using isChain_map_add (List.IsChain.tail ih)
          · rw [survivorPos_cons_nocancel hr hc]
            apply List.IsChain.cons
            · simpa [shiftPos] using isChain_map_add ih
            · intro y hy'
              rw [List.head?_map] at hy'
              cases hhead : (survivorPos t).head? with
              | none => simp [hhead] at hy'
              | some z =>
                  simp [hhead, shiftPos] at hy'
                  omega

/-! ## No survivor strictly inside a cancelled pair -/

/-- In a strictly increasing chain, the head is smaller than every other
member. -/
lemma isChain_head_lt {a : ℕ} {l : List ℕ} (h : List.IsChain (· < ·) (a :: l))
    {b : ℕ} (hb : b ∈ l) : a < b := by
  induction l generalizing a with
  | nil => simp at hb
  | cons c rest ih =>
      have hac : a < c := List.IsChain.rel_head h
      have htail : List.IsChain (· < ·) (c :: rest) := List.IsChain.tail h
      cases hb with
      | head as => exact hac
      | tail b' hbr => exact lt_trans hac (ih (a := c) htail hbr)

/-- No survivor position of `W` lies strictly between the endpoints of a
cancelled pair of `W`: every position strictly inside a pair is cancelled. -/
lemma survivor_not_inside_pair {α : Type*} [DecidableEq α] (W : List (α × Bool))
    {i j p : ℕ} (hp : (i, j) ∈ cancelledPairs W) (hsur : p ∈ survivorPos W) :
    ¬ (i < p ∧ p < j) := by
  induction W generalizing i j p with
  | nil => simp [cancelledPairs] at hp
  | cons l t ih =>
      cases hr : FreeGroup.reduce t with
      | nil =>
          rw [survivorPos_cons_nil hr] at hsur
          simp at hsur
          subst p
          intro hipj
          rcases hipj with ⟨hip, hpj⟩
          omega
      | cons hd tl =>
          cases hsp : survivorPos t with
          | nil =>
              have hz : FreeGroup.reduce t = [] := (survivorPos_eq_nil_iff t).mp hsp
              rw [hz] at hr
              simp at hr
          | cons r ptl =>
              by_cases hc : letterInv l = hd
              · rw [cancelledPairs_cons_cancel hr hsp hc] at hp
                rw [List.mem_cons] at hp
                rcases hp with hp | hp
                · have hi : i = 0 := congrArg Prod.fst hp
                  have hj : j = r + 1 := congrArg Prod.snd hp
                  subst i
                  subst j
                  rw [survivorPos_cons_cancel hr hc, hsp] at hsur
                  rw [List.mem_map] at hsur
                  rcases hsur with ⟨q, hq, hp_eq⟩
                  have hqsp : q ∈ survivorPos t := by
                    rw [hsp]
                    exact List.mem_cons_of_mem r hq
                  have hpeq : q + 1 = p := by simpa [shiftPos] using hp_eq
                  subst p
                  have hsorted := survivorPos_sorted t
                  have hrq : r < q := isChain_head_lt (by simpa [hsp] using hsorted) hq
                  intro hipj
                  rcases hipj with ⟨hip, hpj⟩
                  omega
                · rcases mem_shiftPair (cancelledPairs t) hp with ⟨i', j', hp', hi, hj⟩
                  subst i
                  subst j
                  rw [survivorPos_cons_cancel hr hc, hsp] at hsur
                  rw [List.mem_map] at hsur
                  rcases hsur with ⟨q, hq, hp_eq⟩
                  have hqsp : q ∈ survivorPos t := by
                    rw [hsp]
                    exact List.mem_cons_of_mem r hq
                  have hpeq : q + 1 = p := by simpa [shiftPos] using hp_eq
                  subst p
                  intro hipj
                  rcases hipj with ⟨hip, hpj⟩
                  apply ih (i := i') (j := j') (p := q) hp' hqsp
                  constructor <;> omega
              · rw [cancelledPairs_cons_nocancel hr hsp hc] at hp
                rcases mem_shiftPair (cancelledPairs t) hp with ⟨i', j', hp', hi, hj⟩
                subst i
                subst j
                rw [survivorPos_cons_nocancel hr hc] at hsur
                rw [List.mem_cons] at hsur
                rcases hsur with hsur | hsur
                · subst p
                  intro hipj
                  rcases hipj with ⟨hip, hpj⟩
                  omega
                · rw [List.mem_map] at hsur
                  rcases hsur with ⟨q, hq, hp_eq⟩
                  have hpeq : q + 1 = p := by simpa [shiftPos] using hp_eq
                  subst p
                  intro hipj
                  rcases hipj with ⟨hip, hpj⟩
                  apply ih (i := i') (j := j') (p := q) hp' hq
                  constructor <;> omega

/-! ## Coverage: every position is a survivor or cancelled -/

/-- Shifting a survivor membership gives membership in the shifted list. -/
lemma mem_shiftPos {t : List ℕ} {q : ℕ} (hq : q ∈ t) : q + 1 ∈ t.map shiftPos := by
  exact List.mem_map.mpr ⟨q, hq, rfl⟩

/-- Shifting a pair membership gives membership in the shifted pairs. -/
lemma mem_shiftPair_mem {t : List (ℕ × ℕ)} {a b : ℕ} (h : (a, b) ∈ t) :
    (a + 1, b + 1) ∈ t.map shiftPair := by
  exact List.mem_map.mpr ⟨(a, b), h, rfl⟩

/-- Every position of `W` is either a survivor or occurs in a cancelled pair
(as a left or a right endpoint). -/
lemma position_covered {α : Type*} [DecidableEq α] (W : List (α × Bool)) :
    ∀ x : ℕ, x < W.length →
      x ∈ survivorPos W ∨ (∃ j : ℕ, (x, j) ∈ cancelledPairs W) ∨
        (∃ i : ℕ, (i, x) ∈ cancelledPairs W) := by
  induction W with
  | nil => intro x hx
           simp at hx
  | cons l t ih =>
      intro x hx
      cases hr : FreeGroup.reduce t with
      | nil =>
          cases x with
          | zero =>
              left
              rw [survivorPos_cons_nil hr]
              simp
          | succ x' =>
              have hx' : x' < t.length := by
                rw [List.length_cons] at hx
                omega
              rcases ih x' hx' with hsur | hpair
              · exfalso
                have hz : survivorPos t = [] := (survivorPos_eq_nil_iff t).mpr hr
                rw [hz] at hsur
                simpa using hsur
              · rcases hpair with hpair | hpair
                · rcases hpair with ⟨j', hp⟩
                  right
                  left
                  refine ⟨j' + 1, ?_⟩
                  rw [cancelledPairs_cons_nil hr]
                  exact mem_shiftPair_mem hp
                · rcases hpair with ⟨i', hp⟩
                  right
                  right
                  refine ⟨i' + 1, ?_⟩
                  rw [cancelledPairs_cons_nil hr]
                  exact mem_shiftPair_mem hp
      | cons hd tl =>
          cases hsp : survivorPos t with
          | nil =>
              exfalso
              have hz : FreeGroup.reduce t = [] := (survivorPos_eq_nil_iff t).mp hsp
              rw [hz] at hr
              simp at hr
          | cons r ptl =>
              by_cases hc : letterInv l = hd
              · cases x with
                | zero =>
                    right
                    left
                    refine ⟨r + 1, ?_⟩
                    rw [cancelledPairs_cons_cancel hr hsp hc]
                    simp
                | succ x' =>
                    have hx' : x' < t.length := by
                      rw [List.length_cons] at hx
                      omega
                    rcases ih x' hx' with hsur | hpair
                    · rw [hsp] at hsur
                      cases hsur with
                      | head as =>
                          right
                          right
                          refine ⟨0, ?_⟩
                          rw [cancelledPairs_cons_cancel hr hsp hc]
                          simp
                      | tail b hm =>
                          left
                          rw [survivorPos_cons_cancel hr hc]
                          have htail_eq : ptl = (survivorPos t).tail := by
                            rw [hsp]
                            simp
                          have hqt : x' ∈ (survivorPos t).tail := by
                            rw [← htail_eq]
                            exact hm
                          exact mem_shiftPos hqt
                    · rcases hpair with hpair | hpair
                      · rcases hpair with ⟨j', hp⟩
                        right
                        left
                        refine ⟨j' + 1, ?_⟩
                        rw [cancelledPairs_cons_cancel hr hsp hc]
                        rw [List.mem_cons]
                        right
                        exact mem_shiftPair_mem hp
                      · rcases hpair with ⟨i', hp⟩
                        right
                        right
                        refine ⟨i' + 1, ?_⟩
                        rw [cancelledPairs_cons_cancel hr hsp hc]
                        rw [List.mem_cons]
                        right
                        exact mem_shiftPair_mem hp
              · cases x with
                | zero =>
                    left
                    rw [survivorPos_cons_nocancel hr hc]
                    simp
                | succ x' =>
                    have hx' : x' < t.length := by
                      rw [List.length_cons] at hx
                      omega
                    rcases ih x' hx' with hsur | hpair
                    · left
                      rw [survivorPos_cons_nocancel hr hc]
                      exact List.mem_cons_of_mem 0 (mem_shiftPos hsur)
                    · rcases hpair with hpair | hpair
                      · rcases hpair with ⟨j', hp⟩
                        right
                        left
                        refine ⟨j' + 1, ?_⟩
                        rw [cancelledPairs_cons_nocancel hr hsp hc]
                        exact mem_shiftPair_mem hp
                      · rcases hpair with ⟨i', hp⟩
                        right
                        right
                        refine ⟨i' + 1, ?_⟩
                        rw [cancelledPairs_cons_nocancel hr hsp hc]
                        exact mem_shiftPair_mem hp

/-! ## A survivor is never a pair endpoint; pairs do not cross; interval completeness -/

/-- A survivor position is never an endpoint of a cancelled pair. -/
lemma survivor_not_pair {α : Type*} [DecidableEq α] (W : List (α × Bool)) {i j p : ℕ}
    (hp : (i, j) ∈ cancelledPairs W) (hsur : p ∈ survivorPos W) : i ≠ p ∧ j ≠ p := by
  induction W generalizing i j p with
  | nil => simp [cancelledPairs] at hp
  | cons a t ih =>
      cases hr : FreeGroup.reduce t with
      | nil =>
          rw [cancelledPairs_cons_nil hr] at hp
          rw [survivorPos_cons_nil hr] at hsur
          simp at hsur
          subst p
          rcases mem_shiftPair (cancelledPairs t) hp with ⟨i', j', hp', hi, hj⟩
          constructor <;> omega
      | cons hd tl =>
          cases hsp : survivorPos t with
          | nil =>
              have hz : FreeGroup.reduce t = [] := (survivorPos_eq_nil_iff t).mp hsp
              rw [hz] at hr
              simp at hr
          | cons r ptl =>
              by_cases hc : letterInv a = hd
              · rw [cancelledPairs_cons_cancel hr hsp hc] at hp
                rw [List.mem_cons] at hp
                rcases hp with hp | hp
                · have hi : i = 0 := congrArg Prod.fst hp
                  have hj : j = r + 1 := congrArg Prod.snd hp
                  subst i
                  subst j
                  rw [survivorPos_cons_cancel hr hc, hsp] at hsur
                  rw [List.mem_map] at hsur
                  rcases hsur with ⟨q, hq, hp_eq⟩
                  have hpeq : q + 1 = p := by simpa [shiftPos] using hp_eq
                  subst p
                  constructor
                  · omega
                  · have hchain : List.IsChain (· < ·) (r :: ptl) := by
                      simpa [hsp] using survivorPos_sorted t
                    have hq' : q ∈ ptl := by simpa using hq
                    have hrq : r < q := isChain_head_lt (a := r) (l := ptl) hchain (b := q) hq'
                    omega
                · rcases mem_shiftPair (cancelledPairs t) hp with ⟨i', j', hp', hi, hj⟩
                  subst i
                  subst j
                  rw [survivorPos_cons_cancel hr hc, hsp] at hsur
                  rw [List.mem_map] at hsur
                  rcases hsur with ⟨q, hq, hp_eq⟩
                  have hq' : q ∈ ptl := by simpa using hq
                  have hqsp : q ∈ survivorPos t := by
                    rw [hsp]
                    exact List.mem_cons_of_mem r hq'
                  have hpeq : q + 1 = p := by simpa [shiftPos] using hp_eq
                  subst p
                  have hbad := ih hp' hqsp
                  constructor <;> omega
              · rw [cancelledPairs_cons_nocancel hr hsp hc] at hp
                rcases mem_shiftPair (cancelledPairs t) hp with ⟨i', j', hp', hi, hj⟩
                subst i
                subst j
                rw [survivorPos_cons_nocancel hr hc] at hsur
                rw [List.mem_cons] at hsur
                rcases hsur with hsur | hsur
                · subst p
                  constructor <;> omega
                · rw [List.mem_map] at hsur
                  rcases hsur with ⟨q, hq, hp_eq⟩
                  have hpeq : q + 1 = p := by simpa [shiftPos] using hp_eq
                  subst p
                  have hbad := ih hp' hq
                  constructor <;> omega

/-- No two cancelled pairs cross: if `i < k`, the pair `(i,j)` does not have
`k` strictly inside it while ending before `l`. -/
lemma pairs_no_cross {α : Type*} [DecidableEq α] (W : List (α × Bool)) {i j k l : ℕ}
    (hp : (i, j) ∈ cancelledPairs W) (hk : (k, l) ∈ cancelledPairs W) (hik : i < k) :
    ¬ (k < j ∧ j < l) := by
  intro hc'
  induction W generalizing i j k l with
  | nil => simp [cancelledPairs] at hp
  | cons a t ih =>
      cases hr : FreeGroup.reduce t with
      | nil =>
          rw [cancelledPairs_cons_nil hr] at hp hk
          rcases mem_shiftPair (cancelledPairs t) hp with ⟨i', j', hp', hi, hj⟩
          rcases mem_shiftPair (cancelledPairs t) hk with ⟨k', l', hk', hik', hkl'⟩
          subst i
          subst j
          subst k
          subst l
          have hik' : i' < k' := by omega
          have hnc := ih hp' hk' hik'
          apply hnc
          constructor <;> omega
      | cons hd tl =>
          cases hsp : survivorPos t with
          | nil =>
              have hz : FreeGroup.reduce t = [] := (survivorPos_eq_nil_iff t).mp hsp
              rw [hz] at hr
              simp at hr
          | cons r ptl =>
              by_cases hc : letterInv a = hd
              · rw [cancelledPairs_cons_cancel hr hsp hc] at hp hk
                rw [List.mem_cons] at hp
                rw [List.mem_cons] at hk
                rcases hp with hp | hp
                · rcases hk with hk | hk
                  · have hi : i = 0 := congrArg Prod.fst hp
                    have hk0 : k = 0 := congrArg Prod.fst hk
                    subst i
                    subst k
                    omega
                  · have hi : i = 0 := congrArg Prod.fst hp
                    have hj : j = r + 1 := congrArg Prod.snd hp
                    subst i
                    subst j
                    rcases mem_shiftPair (cancelledPairs t) hk with ⟨k', l', hk', hik', hkl'⟩
                    subst k
                    subst l
                    have hsur_r : r ∈ survivorPos t := by
                      rw [hsp]
                      simp
                    have hbad := survivor_not_inside_pair t hk' hsur_r
                    apply hbad
                    constructor <;> omega
                · rcases hk with hk | hk
                  · have hk0 : k = 0 := congrArg Prod.fst hk
                    subst k
                    rcases mem_shiftPair (cancelledPairs t) hp with ⟨i', j', hp', hi, hj⟩
                    omega
                  · rcases mem_shiftPair (cancelledPairs t) hp with ⟨i', j', hp', hi, hj⟩
                    rcases mem_shiftPair (cancelledPairs t) hk with ⟨k', l', hk', hik', hkl'⟩
                    subst i
                    subst j
                    subst k
                    subst l
                    have hik' : i' < k' := by omega
                    have hnc := ih hp' hk' hik'
                    apply hnc
                    constructor <;> omega
              · rw [cancelledPairs_cons_nocancel hr hsp hc] at hp hk
                rcases mem_shiftPair (cancelledPairs t) hp with ⟨i', j', hp', hi, hj⟩
                rcases mem_shiftPair (cancelledPairs t) hk with ⟨k', l', hk', hik', hkl'⟩
                subst i
                subst j
                subst k
                subst l
                have hik' : i' < k' := by omega
                have hnc := ih hp' hk' hik'
                apply hnc
                constructor <;> omega

/-- Every position strictly inside a cancelled pair is itself cancelled, with
its partner strictly inside the pair as well. -/
lemma pair_interval_complete {α : Type*} [DecidableEq α] (W : List (α × Bool)) {i j : ℕ}
    (hp : (i, j) ∈ cancelledPairs W) : ∀ x : ℕ, i < x → x < j →
      ∃ y : ℕ, i < y ∧ y < j ∧ ((x, y) ∈ cancelledPairs W ∨ (y, x) ∈ cancelledPairs W) := by
  induction W generalizing i j with
  | nil => simp [cancelledPairs] at hp
  | cons a t ih =>
      intro x hix hxj
      cases hr : FreeGroup.reduce t with
      | nil =>
          rw [cancelledPairs_cons_nil hr] at hp
          rcases mem_shiftPair (cancelledPairs t) hp with ⟨i', j', hp', hi, hj⟩
          subst i
          subst j
          cases x with
          | zero => omega
          | succ x' =>
              have hx'i : i' < x' := by omega
              have hx'j : x' < j' := by omega
              have hrec := ih hp' x' hx'i hx'j
              rcases hrec with ⟨y', hy'i, hy'j, hy'pair⟩
              refine ⟨y' + 1, ?_, ?_, ?_⟩
              · omega
              · omega
              · rcases hy'pair with hy'pair | hy'pair
                · left
                  rw [cancelledPairs_cons_nil hr]
                  exact mem_shiftPair_mem hy'pair
                · right
                  rw [cancelledPairs_cons_nil hr]
                  exact mem_shiftPair_mem hy'pair
      | cons hd tl =>
          cases hsp : survivorPos t with
          | nil =>
              have hz : FreeGroup.reduce t = [] := (survivorPos_eq_nil_iff t).mp hsp
              rw [hz] at hr
              simp at hr
          | cons r ptl =>
              by_cases hc : letterInv a = hd
              · rw [cancelledPairs_cons_cancel hr hsp hc] at hp
                rw [List.mem_cons] at hp
                rcases hp with hp | hp
                · have hi : i = 0 := congrArg Prod.fst hp
                  have hj : j = r + 1 := congrArg Prod.snd hp
                  subst i
                  subst j
                  cases x with
                  | zero => omega
                  | succ x' =>
                      have hxr : x' < r := by omega
                      have hr_mem : r ∈ survivorPos t := by
                        rw [hsp]
                        simp
                      have hrlt := survivorPos_lt_length t hr_mem
                      have hxr2 : x' < t.length := by omega
                      have hcov := position_covered t x' hxr2
                      rcases hcov with hsur' | hpair'
                      · exfalso
                        rw [hsp] at hsur'
                        cases hsur' with
                        | head as => omega
                        | tail b hm =>
                            have hchain : List.IsChain (· < ·) (r :: ptl) := by
                              simpa [hsp] using survivorPos_sorted t
                            have hrx : r < x' := isChain_head_lt (a := r) (l := ptl) hchain (b := x') hm
                            omega
                      · rcases hpair' with hpair' | hpair'
                        · rcases hpair' with ⟨j', hpj'⟩
                          have hj'le : j' < r := by
                            by_cases hlt : j' < r
                            · exact hlt
                            · have hge : r ≤ j' := le_of_not_gt hlt
                              have hne : j' ≠ r := by
                                intro hEq
                                have hnp := survivor_not_pair t hpj' hr_mem
                                exact hnp.2 hEq
                              have hgt : r < j' := lt_of_le_of_ne hge (fun h => hne h.symm)
                              exfalso
                              have hbad := survivor_not_inside_pair t hpj' hr_mem
                              apply hbad
                              constructor <;> omega
                          refine ⟨j' + 1, ?_, ?_, ?_⟩
                          · omega
                          · omega
                          · left
                            rw [cancelledPairs_cons_cancel hr hsp hc]
                            rw [List.mem_cons]
                            right
                            exact mem_shiftPair_mem hpj'
                        · rcases hpair' with ⟨i', hpi'⟩
                          have hi'r : i' < r := by
                            have hlt := pair_lt t hpi'
                            omega
                          refine ⟨i' + 1, ?_, ?_, ?_⟩
                          · omega
                          · omega
                          · right
                            rw [cancelledPairs_cons_cancel hr hsp hc]
                            rw [List.mem_cons]
                            right
                            exact mem_shiftPair_mem hpi'
                · rcases mem_shiftPair (cancelledPairs t) hp with ⟨i', j', hp', hi, hj⟩
                  subst i
                  subst j
                  cases x with
                  | zero => omega
                  | succ x' =>
                      have hx'i : i' < x' := by omega
                      have hx'j : x' < j' := by omega
                      have hrec := ih hp' x' hx'i hx'j
                      rcases hrec with ⟨y', hy'i, hy'j, hy'pair⟩
                      refine ⟨y' + 1, ?_, ?_, ?_⟩
                      · omega
                      · omega
                      · rcases hy'pair with hy'pair | hy'pair
                        · left
                          rw [cancelledPairs_cons_cancel hr hsp hc]
                          rw [List.mem_cons]
                          right
                          exact mem_shiftPair_mem hy'pair
                        · right
                          rw [cancelledPairs_cons_cancel hr hsp hc]
                          rw [List.mem_cons]
                          right
                          exact mem_shiftPair_mem hy'pair
              · rw [cancelledPairs_cons_nocancel hr hsp hc] at hp
                rcases mem_shiftPair (cancelledPairs t) hp with ⟨i', j', hp', hi, hj⟩
                subst i
                subst j
                cases x with
                | zero => omega
                | succ x' =>
                    have hx'i : i' < x' := by omega
                    have hx'j : x' < j' := by omega
                    have hrec := ih hp' x' hx'i hx'j
                    rcases hrec with ⟨y', hy'i, hy'j, hy'pair⟩
                    refine ⟨y' + 1, ?_, ?_, ?_⟩
                    · omega
                    · omega
                    · rcases hy'pair with hy'pair | hy'pair
                      · left
                        rw [cancelledPairs_cons_nocancel hr hsp hc]
                        exact mem_shiftPair_mem hy'pair
                      · right
                        rw [cancelledPairs_cons_nocancel hr hsp hc]
                        exact mem_shiftPair_mem hy'pair

/-! ## Letter content: the survivors' letters equal `reduce`; pair endpoints
are letter-inverses -/

/-- The letter of `W` at a survivor position is the corresponding letter of
`reduce W` (positions of survivors are indexed in the same order). -/
lemma survivorPos_letter {α : Type*} [DecidableEq α] (W : List (α × Bool)) :
    ∀ k p : ℕ, (survivorPos W)[k]? = some p → W[p]? = (FreeGroup.reduce W)[k]? := by
  induction W with
  | nil => intro k p hp
           simp [survivorPos] at hp
  | cons a t ih =>
      intro k p hp
      cases hr : FreeGroup.reduce t with
      | nil =>
          rw [survivorPos_cons_nil hr] at hp
          cases k with
          | zero =>
              have hp0' : 0 = p := by simpa using hp
              have hp0 : p = 0 := hp0'.symm
              subst p
              rw [reduce_cons_nil hr]
              simp
          | succ k' =>
              simp at hp
      | cons hd tl =>
          cases hsp : survivorPos t with
          | nil =>
              have hz : FreeGroup.reduce t = [] := (survivorPos_eq_nil_iff t).mp hsp
              rw [hz] at hr
              simp at hr
          | cons q qs =>
              by_cases hc : letterInv a = hd
              · rw [survivorPos_cons_cancel hr hc] at hp
                simp [hsp] at hp
                rcases hp with ⟨u, hqu, hp_eq⟩
                have hp' : u + 1 = p := by simpa [shiftPos] using hp_eq
                subst p
                have hih := ih (k + 1) u (by
                  simpa [hsp])
                rw [reduce_cons_cancel hr hc]
                have hget : (a :: t)[u + 1]? = t[u]? := by
                  induction u with
                  | zero => rfl
                  | succ u ih' => simpa using ih'
                rw [hget]
                have hih' : t[u]? = (FreeGroup.reduce t)[k + 1]? := hih
                rw [hih']
                rw [hr]
                induction k with
                | zero => rfl
                | succ k ihk => simpa using ihk
              · rw [survivorPos_cons_nocancel hr hc] at hp
                cases k with
                | zero =>
                    have hp0' : 0 = p := by simpa using hp
                    have hp0 : p = 0 := hp0'.symm
                    subst p
                    rw [reduce_cons_nocancel hr hc]
                    simp
                | succ k' =>
                    have hshift : (0 :: (survivorPos t).map shiftPos)[k' + 1]? =
                        ((survivorPos t).map shiftPos)[k']? := by
                      induction k' with
                      | zero => rfl
                      | succ k ihk => simpa using ihk
                    rw [hshift] at hp
                    simp at hp
                    rcases hp with ⟨u, hqu, hp_eq⟩
                    have hp' : u + 1 = p := by simpa [shiftPos] using hp_eq
                    subst p
                    have hih := ih k' u hqu
                    rw [reduce_cons_nocancel hr hc]
                    have hget : (a :: t)[u + 1]? = t[u]? := by
                      induction u with
                      | zero => rfl
                      | succ u ih' => simpa using ih'
                    rw [hget]
                    rw [hih]
                    rw [hr]
                    rfl

/-- Positional lookup skips the head of a cons. -/
lemma cons_get_succ {α : Type*} (a : α) (t : List α) (n : ℕ) :
    (a :: t)[n + 1]? = t[n]? := by
  induction n with
  | zero => rfl
  | succ n ih => simpa using ih

/-- The letters at the endpoints of a cancelled pair are letter-inverses:
`letterInv (W[i]) = W[j]` for a pair `(i, j)`. -/
lemma pair_letters_inv {α : Type*} [DecidableEq α] (W : List (α × Bool)) {i j : ℕ}
    (hp : (i, j) ∈ cancelledPairs W) :
    ∀ x y : α × Bool, W[i]? = some x → W[j]? = some y → letterInv x = y := by
  induction W generalizing i j with
  | nil => simp [cancelledPairs] at hp
  | cons a t ih =>
      intro x y hix hjy
      cases hr : FreeGroup.reduce t with
      | nil =>
          rw [cancelledPairs_cons_nil hr] at hp
          rcases mem_shiftPair (cancelledPairs t) hp with ⟨i', j', hp', hi, hj⟩
          subst i
          subst j
          have hix' : t[i']? = some x := by
            rw [cons_get_succ a t i'] at hix
            exact hix
          have hjy' : t[j']? = some y := by
            rw [cons_get_succ a t j'] at hjy
            exact hjy
          exact ih hp' x y hix' hjy'
      | cons hd tl =>
          cases hsp : survivorPos t with
          | nil =>
              have hz : FreeGroup.reduce t = [] := (survivorPos_eq_nil_iff t).mp hsp
              rw [hz] at hr
              simp at hr
          | cons r ptl =>
              by_cases hc : letterInv a = hd
              · rw [cancelledPairs_cons_cancel hr hsp hc] at hp
                rw [List.mem_cons] at hp
                rcases hp with hp | hp
                · have hi : i = 0 := congrArg Prod.fst hp
                  have hj : j = r + 1 := congrArg Prod.snd hp
                  subst i
                  subst j
                  have hx' : a = x := by simpa using hix
                  have hx : x = a := hx'.symm
                  subst x
                  have hjy_t : t[r]? = some y := by
                    rw [cons_get_succ a t r] at hjy
                    exact hjy
                  have hsp2 : (survivorPos t)[0]? = some r := by simpa [hsp]
                  have hl := survivorPos_letter t 0 r hsp2
                  rw [hl] at hjy_t
                  rw [hr] at hjy_t
                  have hyeq : y = hd := by simpa using hjy_t.symm
                  subst y
                  exact hc
                · rcases mem_shiftPair (cancelledPairs t) hp with ⟨i', j', hp', hi, hj⟩
                  subst i
                  subst j
                  have hix' : t[i']? = some x := by
                    rw [cons_get_succ a t i'] at hix
                    exact hix
                  have hjy' : t[j']? = some y := by
                    rw [cons_get_succ a t j'] at hjy
                    exact hjy
                  exact ih hp' x y hix' hjy'
              · rw [cancelledPairs_cons_nocancel hr hsp hc] at hp
                rcases mem_shiftPair (cancelledPairs t) hp with ⟨i', j', hp', hi, hj⟩
                subst i
                subst j
                have hix' : t[i']? = some x := by
                  rw [cons_get_succ a t i'] at hix
                  exact hix
                have hjy' : t[j']? = some y := by
                  rw [cons_get_succ a t j'] at hjy
                  exact hjy
                exact ih hp' x y hix' hjy'

/-! ## Counting: twice the pairs plus the survivors equals the length -/

/-- `2 · |cancelledPairs W| + |survivorPos W| = |W|`: every letter is either a
survivor or one of the two endpoints of a cancelled pair. -/
lemma survivorPos_length_add {α : Type*} [DecidableEq α] (W : List (α × Bool)) :
    2 * (cancelledPairs W).length + (survivorPos W).length = W.length := by
  induction W with
  | nil => simp [cancelledPairs, survivorPos]
  | cons l t ih =>
      cases hr : FreeGroup.reduce t with
      | nil =>
          rw [cancelledPairs_cons_nil hr, survivorPos_cons_nil hr]
          have hz : survivorPos t = [] := (survivorPos_eq_nil_iff t).mpr hr
          rw [hz] at ih
          simp [List.length_map]
          simp at ih
          omega
      | cons hd tl =>
          cases hsp : survivorPos t with
          | nil =>
              have hz : FreeGroup.reduce t = [] := (survivorPos_eq_nil_iff t).mp hsp
              rw [hz] at hr
              simp at hr
          | cons r ptl =>
              by_cases hc : letterInv l = hd
              · rw [cancelledPairs_cons_cancel hr hsp hc, survivorPos_cons_cancel hr hc]
                simp [List.length_map, List.length_cons]
                rw [hsp]
                simp
                have ih' : 2 * (cancelledPairs t).length + (ptl.length + 1) = t.length := by
                  rw [hsp] at ih
                  simpa using ih
                omega
              · rw [cancelledPairs_cons_nocancel hr hsp hc, survivorPos_cons_nocancel hr hc]
                simp [List.length_map, List.length_cons]
                omega

/-! ## Factor-segment analysis: segments of reduced words are reduced -/

/-- A prefix of a reduced word is reduced. -/
lemma seg_take_isReduced {α : Type*} (L : List (α × Bool)) (k : ℕ)
    (hL : FreeGroup.IsReduced L) : FreeGroup.IsReduced (L.take k) := by
  simpa [FreeGroup.IsReduced] using List.IsChain.take hL k

/-- A suffix of a reduced word is reduced. -/
lemma seg_drop_isReduced {α : Type*} (L : List (α × Bool)) (k : ℕ)
    (hL : FreeGroup.IsReduced L) : FreeGroup.IsReduced (L.drop k) := by
  simpa [FreeGroup.IsReduced] using List.IsChain.drop hL k

/-- Any contiguous segment `[lo, hi)` of a reduced word is reduced. -/
lemma segment_isReduced {α : Type*} (L : List (α × Bool)) (lo hi : ℕ)
    (hL : FreeGroup.IsReduced L) : FreeGroup.IsReduced (L.drop lo |>.take (hi - lo)) := by
  exact seg_take_isReduced (L.drop lo) (hi - lo) (seg_drop_isReduced L lo hL)

/-- A reduced word is empty iff its reduction is empty, so a nonempty reduced
word does not reduce to the empty word. -/
lemma isReduced_reduce_ne_of_ne_nil {α : Type*} [DecidableEq α] (L : List (α × Bool))
    (hL : FreeGroup.IsReduced L) (hne : L ≠ []) : FreeGroup.reduce L ≠ [] := by
  intro hz
  have hself := FreeGroup.IsReduced.reduce_eq hL
  rw [hself] at hz
  exact hne hz

/-! ## Partner uniqueness -/

/-- Sharing an endpoint descends through a simultaneous shift by one. -/
lemma share_shift_down {i j k l i' j' k' l' : ℕ}
    (hi : i = i' + 1) (hj : j = j' + 1) (hk : k = k' + 1) (hl : l = l' + 1)
    (hs : i = k ∨ i = l ∨ j = k ∨ j = l) :
    i' = k' ∨ i' = l' ∨ j' = k' ∨ j' = l' := by
  rcases hs with hs | hs | hs | hs
  · left
    omega
  · right
    left
    omega
  · right
    right
    left
    omega
  · right
    right
    right
    omega

/-- Two cancelled pairs that share a position are the same pair. -/
lemma pair_eq_of_share {α : Type*} [DecidableEq α] (W : List (α × Bool)) {i j k l : ℕ}
    (hp : (i, j) ∈ cancelledPairs W) (hk : (k, l) ∈ cancelledPairs W)
    (hshare : i = k ∨ i = l ∨ j = k ∨ j = l) : (i, j) = (k, l) := by
  induction W generalizing i j k l with
  | nil => simp [cancelledPairs] at hp
  | cons a t ih =>
      cases hr : FreeGroup.reduce t with
      | nil =>
          rw [cancelledPairs_cons_nil hr] at hp hk
          rcases mem_shiftPair (cancelledPairs t) hp with ⟨i', j', hp', hi, hj⟩
          rcases mem_shiftPair (cancelledPairs t) hk with ⟨k', l', hk', hik, hil⟩
          have hs' : i' = k' ∨ i' = l' ∨ j' = k' ∨ j' = l' :=
            share_shift_down hi hj hik hil hshare
          have heq := ih hp' hk' hs'
          have hik' : i' = k' := congrArg Prod.fst heq
          have hjl' : j' = l' := congrArg Prod.snd heq
          have hik1 : i = k := by omega
          have hjl1 : j = l := by omega
          rw [hik1, hjl1]
      | cons hd tl =>
          cases hsp : survivorPos t with
          | nil =>
              have hz : FreeGroup.reduce t = [] := (survivorPos_eq_nil_iff t).mp hsp
              rw [hz] at hr
              simp at hr
          | cons r ptl =>
              by_cases hc : letterInv a = hd
              · rw [cancelledPairs_cons_cancel hr hsp hc] at hp hk
                rw [List.mem_cons] at hp
                rw [List.mem_cons] at hk
                rcases hp with hp | hp
                · rcases hk with hk | hk
                  · rw [← hp] at hk
                    exact hk.symm
                  · have hi : i = 0 := congrArg Prod.fst hp
                    have hj : j = r + 1 := congrArg Prod.snd hp
                    rcases mem_shiftPair (cancelledPairs t) hk with ⟨k', l', hk', hik, hil⟩
                    have hr_mem : r ∈ survivorPos t := by
                      rw [hsp]
                      simp
                    rcases hshare with hs | hs | hs | hs
                    · omega
                    · omega
                    · have hEq : k' = r := by omega
                      have hne := (survivor_not_pair t hk' hr_mem).1
                      omega
                    · have hEq : l' = r := by omega
                      have hne := (survivor_not_pair t hk' hr_mem).2
                      omega
                · rcases hk with hk | hk
                  · have hk0 : k = 0 := congrArg Prod.fst hk
                    have hl0 : l = r + 1 := congrArg Prod.snd hk
                    rcases mem_shiftPair (cancelledPairs t) hp with ⟨i', j', hp', hi, hj⟩
                    have hr_mem : r ∈ survivorPos t := by
                      rw [hsp]
                      simp
                    rcases hshare with hs | hs | hs | hs
                    · omega
                    · have hEq : i' = r := by omega
                      have hne := (survivor_not_pair t hp' hr_mem).1
                      omega
                    · omega
                    · have hEq : j' = r := by omega
                      have hne := (survivor_not_pair t hp' hr_mem).2
                      omega
                  · rcases mem_shiftPair (cancelledPairs t) hp with ⟨i', j', hp', hi, hj⟩
                    rcases mem_shiftPair (cancelledPairs t) hk with ⟨k', l', hk', hik, hil⟩
                    have hs' : i' = k' ∨ i' = l' ∨ j' = k' ∨ j' = l' :=
                      share_shift_down hi hj hik hil hshare
                    have heq := ih hp' hk' hs'
                    have hik' : i' = k' := congrArg Prod.fst heq
                    have hjl' : j' = l' := congrArg Prod.snd heq
                    have hik1 : i = k := by omega
                    have hjl1 : j = l := by omega
                    rw [hik1, hjl1]
              · rw [cancelledPairs_cons_nocancel hr hsp hc] at hp hk
                rcases mem_shiftPair (cancelledPairs t) hp with ⟨i', j', hp', hi, hj⟩
                rcases mem_shiftPair (cancelledPairs t) hk with ⟨k', l', hk', hik, hil⟩
                have hs' : i' = k' ∨ i' = l' ∨ j' = k' ∨ j' = l' :=
                  share_shift_down hi hj hik hil hshare
                have heq := ih hp' hk' hs'
                have hik' : i' = k' := congrArg Prod.fst heq
                have hjl' : j' = l' := congrArg Prod.snd heq
                have hik1 : i = k := by omega
                have hjl1 : j = l := by omega
                rw [hik1, hjl1]

/-! ## The single-letter `mk`-inverse fact -/

/-- In the free group, a single letter is the inverse of the group element
of its letter-inverse: `mk [letterInv l] = (mk [l])⁻¹`. -/
lemma mk_single_letter_inv {α : Type*} [DecidableEq α] (l : α × Bool) :
    FreeGroup.mk ([letterInv l] : List (α × Bool)) = (FreeGroup.mk [l])⁻¹ := by
  cases l with | mk a b =>
  cases b with
  | true =>
      have h1 : FreeGroup.mk ([(a, true)] : List (α × Bool)) = FreeGroup.of a := by
        rw [← FreeGroup.toWord_of (a := a), FreeGroup.mk_toWord]
      have hw : ((FreeGroup.of a)⁻¹).toWord = [(a, false)] := by
        rw [FreeGroup.toWord_inv, FreeGroup.toWord_of]
        rfl
      have h2 : FreeGroup.mk ([(a, false)] : List (α × Bool)) = (FreeGroup.of a)⁻¹ := by
        rw [← hw, FreeGroup.mk_toWord]
      simp [letterInv, h1, h2]
  | false =>
      have h1 : FreeGroup.mk ([(a, true)] : List (α × Bool)) = FreeGroup.of a := by
        rw [← FreeGroup.toWord_of (a := a), FreeGroup.mk_toWord]
      have hw : ((FreeGroup.of a)⁻¹).toWord = [(a, false)] := by
        rw [FreeGroup.toWord_inv, FreeGroup.toWord_of]
        rfl
      have h2 : FreeGroup.mk ([(a, false)] : List (α × Bool)) = (FreeGroup.of a)⁻¹ := by
        rw [← hw, FreeGroup.mk_toWord]
      change FreeGroup.mk ([(a, true)] : List (α × Bool)) =
        (FreeGroup.mk ([(a, false)] : List (α × Bool)))⁻¹
      rw [h1, h2]
      simp

/-! ## Segment decomposition at cut points -/

/-- A segment `[a, c)` of a list splits at any cut point `b` with
`a ≤ b ≤ c` (within the list): the `drop`/`take` decomposition. -/
lemma drop_take_decomp {α : Type*} (W : List α) (a b c : ℕ)
    (hab : a ≤ b) (hbc : b ≤ c) (hc : c ≤ W.length) :
    List.take (c - a) (List.drop a W) =
      List.take (b - a) (List.drop a W) ++ List.take (c - b) (List.drop b W) := by
  have hlen_da : b - a ≤ (List.drop a W).length := by
    rw [List.length_drop]
    omega
  have hA : (List.take (b - a) (List.drop a W)).length = b - a := by
    rw [List.length_take, min_eq_left hlen_da]
  have hlenA_le : (List.take (b - a) (List.drop a W)).length ≤ c - a := by
    rw [List.length_take]
    have hmin := min_le_left (b - a) (List.drop a W).length
    have hba : b - a ≤ c - a := by omega
    omega
  have hW : List.drop a W = List.take (b - a) (List.drop a W) ++ List.drop b W := by
    have hd := (List.take_append_drop (b - a) (List.drop a W)).symm
    have hdrop : List.drop (b - a) (List.drop a W) = List.drop b W := by
      rw [List.drop_drop]
      congr 1
      omega
    calc
      List.drop a W = List.take (b - a) (List.drop a W) ++ List.drop (b - a) (List.drop a W) := hd
      _ = List.take (b - a) (List.drop a W) ++ List.drop b W := by rw [hdrop]
  calc
    List.take (c - a) (List.drop a W)
        = List.take (c - a) (List.take (b - a) (List.drop a W) ++ List.drop b W) := by
          nth_rw 1 [hW]
    _ = List.take (c - a) (List.take (b - a) (List.drop a W)) ++
          List.take ((c - a) - (List.take (b - a) (List.drop a W)).length) (List.drop b W) := by
          rw [List.take_append]
    _ = List.take (b - a) (List.drop a W) ++
          List.take ((c - a) - (b - a)) (List.drop b W) := by
          rw [List.take_of_length_le hlenA_le, hA]
    _ = List.take (b - a) (List.drop a W) ++ List.take (c - b) (List.drop b W) := by
          apply congrArg (fun x : List α =>
            List.take (b - a) (List.drop a W) ++ x)
          apply congrArg (fun n : ℕ => List.take n (List.drop b W))
          omega

/-- take 1 of a nonempty list is the singleton of its head. -/
lemma seg_take_one_cons {α : Type*} (x : α) (l : List α) : List.take 1 (x :: l) = [x] := rfl

/-- head of a drop, as getElem. -/
lemma seg_drop_head_get? {α : Type*} (W : List α) (i : ℕ) (x : α) (rest : List α)
    (h : List.drop i W = x :: rest) : W[i]? = some x := by
  induction i generalizing W with
  | zero =>
      have hW : W = x :: rest := by simpa using h
      rw [hW]
      rfl
  | succ i ih =>
      cases W with
      | nil => simp at h
      | cons a t =>
          -- drop (i+1) (a::t) = drop i t: h : drop i t = x :: rest: ih t i?
          have h' : List.drop i t = x :: rest := by simpa using h
          -- W[i+1]? = t[i]?
          have hget : (a :: t)[i + 1]? = t[i]? := by
            induction i with
            | zero => rfl
            | succ i ih => simpa using ih
          rw [hget]
          exact ih t h'

/-- mk of a single-letter list via head of drop. -/
lemma seg_mk_drop_single {α : Type*} [DecidableEq α] (W : List (α × Bool)) (i : ℕ)
    (x : α × Bool) (rest : List (α × Bool)) (h : List.drop i W = x :: rest) :
    FreeGroup.mk (List.take 1 (List.drop i W)) = FreeGroup.mk [x] := by
  rw [h, seg_take_one_cons]


/-- The interior of a pair inherits "covered within" on the left part. -/
lemma left_cover {α : Type*} [DecidableEq α] (W : List (α × Bool)) {i y : ℕ}
    (hp : (i, y) ∈ cancelledPairs W) :
    ∀ x : ℕ, i + 1 ≤ x → x ≤ y - 1 →
      ∃ z : ℕ, i + 1 ≤ z ∧ z ≤ y - 1 ∧
        ((x, z) ∈ cancelledPairs W ∨ (z, x) ∈ cancelledPairs W) := by
  intro x hxi hxj
  have hix : i < x := by omega
  have hxy : x < y := by
    have hlt := pair_lt W hp  -- i < y
    omega
  rcases pair_interval_complete W hp x hix hxy with ⟨z, hiz, hzy, hpair⟩
  refine ⟨z, ?_, ?_, hpair⟩
  · omega
  · omega

/-- The part right of a pair's partner inherits coverage (partners cannot
land at or left of `y`, by no-crossing and partner uniqueness). -/
lemma right_cover {α : Type*} [DecidableEq α] (W : List (α × Bool)) {i y j : ℕ}
    (hp : (i, y) ∈ cancelledPairs W) (hyj : y ≤ j)
    {x : ℕ} (hxi : y + 1 ≤ x) (hxj : x ≤ j)
    (hcovx : ∃ z : ℕ, i ≤ z ∧ z ≤ j ∧
      ((x, z) ∈ cancelledPairs W ∨ (z, x) ∈ cancelledPairs W)) :
    ∃ z : ℕ, y + 1 ≤ z ∧ z ≤ j ∧
      ((x, z) ∈ cancelledPairs W ∨ (z, x) ∈ cancelledPairs W) := by
  rcases hcovx with ⟨z, hzi, hzj, hzp⟩
  have hzgt : y + 1 ≤ z := by
    by_contra hle
    have hzley : z ≤ y := by omega
    rcases hzp with hzp | hzp
    · have hxltz := pair_lt W hzp   -- x < z
      omega
    · have hzltx := pair_lt W hzp   -- z < x
      by_cases hzeq_i : z = i
      · have hsh := pair_eq_of_share W hp hzp (Or.inl hzeq_i.symm)
        have hy_eq_x : y = x := congrArg Prod.snd hsh
        omega
      · by_cases hzeq_y : z = y
        · have hsh := pair_eq_of_share W hp hzp (Or.inr (Or.inr (Or.inl hzeq_y.symm)))
          have hi_eq_z : i = z := congrArg Prod.fst hsh
          have hlt := pair_lt W hp
          omega
        · have hiz : i < z := by omega
          have hzlt_y : z < y := by omega
          have hnc := pairs_no_cross W hp hzp hiz
          exact hnc ⟨hzlt_y, by omega⟩
  refine ⟨z, hzgt, hzj, hzp⟩

/-- `reduce L = []` implies `mk L = 1`. -/
lemma red_to_one {α : Type*} [DecidableEq α] (L : List (α × Bool))
    (h : FreeGroup.reduce L = []) : FreeGroup.mk L = 1 := by
  have hs := (FreeGroup.reduce.self (L := L)).symm  -- mk L = mk (reduce L)
  rw [hs, h]
  rfl

/-- `mk L = 1` implies `reduce L = []`. -/
lemma red_of_mk_one {α : Type*} [DecidableEq α] (L : List (α × Bool))
    (h : FreeGroup.mk L = 1) : FreeGroup.reduce L = [] := by
  have hs := FreeGroup.reduce.sound (L₁ := L) (L₂ := [])
  have hmk : FreeGroup.mk L = FreeGroup.mk [] := by
    exact h
  exact hs hmk

/-- Every position of the closed interval `[i, j]` pairing within itself
forces the segment to reduce to the empty word. -/
theorem interval_fully_cancelled_reduce_empty {α : Type*} [DecidableEq α]
    (W : List (α × Bool)) : ∀ i j : ℕ, i ≤ j → j < W.length →
    (∀ x : ℕ, i ≤ x → x ≤ j →
      ∃ y : ℕ, i ≤ y ∧ y ≤ j ∧
        ((x, y) ∈ cancelledPairs W ∨ (y, x) ∈ cancelledPairs W)) →
    FreeGroup.reduce (List.take (j - i + 1) (List.drop i W)) = [] := by
  have hmain : ∀ n i j : ℕ, j - i = n → i ≤ j → j < W.length →
      (∀ x : ℕ, i ≤ x → x ≤ j →
        ∃ y : ℕ, i ≤ y ∧ y ≤ j ∧
          ((x, y) ∈ cancelledPairs W ∨ (y, x) ∈ cancelledPairs W)) →
      FreeGroup.reduce (List.take (j - i + 1) (List.drop i W)) = [] := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro i j hn hij hj hcov
        have hcovi := hcov i (by omega) (by omega)
        rcases hcovi with ⟨y, hyi, hyj, hyp⟩
        have hyp' : (i, y) ∈ cancelledPairs W := by
          rcases hyp with hyp | hyp
          · exact hyp
          · exfalso
            have hlt := pair_lt W hyp
            omega
        have hiy : i < y := pair_lt W hyp'
        have hiyW : i < W.length := by omega
        have hyW : y < W.length := by omega
        -- decompose the segment S into four parts
        let A1 := List.take 1 (List.drop i W)
        let A2 := List.take (y - i - 1) (List.drop (i + 1) W)
        let B1 := List.take 1 (List.drop y W)
        let B2 := List.take (j - y) (List.drop (y + 1) W)
        have hS : List.take (j - i + 1) (List.drop i W) = A1 ++ A2 ++ B1 ++ B2 := by
          have hdec1 := drop_take_decomp W i y (j + 1) (by omega) (by omega) (by omega)
          have hdec2 := drop_take_decomp W i (i + 1) y (by omega) (by omega) (by omega)
          have hdec3 := drop_take_decomp W y (y + 1) (j + 1) (by omega) (by omega) (by omega)
          have hA : List.take (y - i) (List.drop i W) = A1 ++ A2 := by
            unfold A1 A2
            have h0 : (i + 1) - i = 1 := by omega
            have h1 : y - (i + 1) = y - i - 1 := by omega
            rw [h0, h1] at hdec2
            exact hdec2
          have hB : List.take ((j + 1) - y) (List.drop y W) = B1 ++ B2 := by
            unfold B1 B2
            have h0 : (y + 1) - y = 1 := by omega
            have h1 : (j + 1) - (y + 1) = j - y := by omega
            rw [h0, h1] at hdec3
            exact hdec3
          calc
            List.take (j - i + 1) (List.drop i W)
                = List.take ((j + 1) - i) (List.drop i W) := by congr 1; omega
            _ = List.take (y - i) (List.drop i W) ++ List.take ((j + 1) - y) (List.drop y W) := hdec1
            _ = (A1 ++ A2) ++ (B1 ++ B2) := by rw [hA, hB]
            _ = A1 ++ A2 ++ B1 ++ B2 := by simp [List.append_assoc]
        -- interior reductions
        have hA2red : FreeGroup.reduce A2 = [] := by
          unfold A2
          by_cases hLe : y = i + 1
          · subst y
            simp
          · have hspan : (y - 1) - (i + 1) < n := by omega
            have hcovL : ∀ x : ℕ, i + 1 ≤ x → x ≤ y - 1 →
                ∃ z : ℕ, i + 1 ≤ z ∧ z ≤ y - 1 ∧
                  ((x, z) ∈ cancelledPairs W ∨ (z, x) ∈ cancelledPairs W) := left_cover W hyp'
            have hlen : (y - 1) - (i + 1) + 1 = y - i - 1 := by omega
            have hiL : i + 1 ≤ y - 1 := by omega
            have hjL : y - 1 < W.length := by omega
            have hred := ih ((y - 1) - (i + 1)) hspan (i + 1) (y - 1) rfl hiL hjL hcovL
            rw [hlen] at hred
            exact hred
        have hB2red : FreeGroup.reduce B2 = [] := by
          unfold B2
          by_cases hLe : j = y
          · subst j
            simp
          · have hspan : j - (y + 1) < n := by omega
            have hcovR : ∀ x : ℕ, y + 1 ≤ x → x ≤ j →
                ∃ z : ℕ, y + 1 ≤ z ∧ z ≤ j ∧
                  ((x, z) ∈ cancelledPairs W ∨ (z, x) ∈ cancelledPairs W) := by
              intro x hx1 hx2
              exact right_cover W hyp' hyj hx1 hx2 (hcov x (by omega) hx2)
            have hlen : j - (y + 1) + 1 = j - y := by omega
            have hiR : y + 1 ≤ j := by omega
            have hred := ih (j - (y + 1)) hspan (y + 1) j rfl hiR hj hcovR
            rw [hlen] at hred
            exact hred
        -- mk-level telescoping
        have hmkA1 : FreeGroup.mk A1 = FreeGroup.mk (List.take 1 (List.drop i W)) := by rfl
        -- letter facts
        have hdrop_i : List.drop i W ≠ [] := by
          intro hz
          have hl : (List.drop i W).length = 0 := by simp [hz]
          rw [List.length_drop] at hl
          omega
        have hhead_i : ∃ x rest, List.drop i W = x :: rest := List.exists_cons_of_ne_nil hdrop_i
        rcases hhead_i with ⟨xi, resti, hd_i⟩
        have hdrop_y : List.drop y W ≠ [] := by
          intro hz
          have hl : (List.drop y W).length = 0 := by simp [hz]
          rw [List.length_drop] at hl
          omega
        rcases (List.exists_cons_of_ne_nil hdrop_y) with ⟨xy, resty, hd_y⟩
        have hA1_single : A1 = [xi] := by
          unfold A1
          rw [hd_i]
          rfl
        have hB1_single : B1 = [xy] := by
          unfold B1
          rw [hd_y]
          rfl
        have hmkA1' : FreeGroup.mk A1 = FreeGroup.mk [xi] := by rw [hA1_single]
        have hmkB1' : FreeGroup.mk B1 = FreeGroup.mk [xy] := by rw [hB1_single]
        have hget_i : W[i]? = some xi := seg_drop_head_get? W i xi resti hd_i
        have hget_y : W[y]? = some xy := seg_drop_head_get? W y xy resty hd_y
        have hinv : letterInv xi = xy := pair_letters_inv W hyp' xi xy hget_i hget_y
        have hxi_inv : FreeGroup.mk [xi] * FreeGroup.mk [xy] = 1 := by
          have hm : FreeGroup.mk [xy] = (FreeGroup.mk [xi])⁻¹ := by
            calc FreeGroup.mk [xy] = FreeGroup.mk [letterInv xi] := by rw [← hinv]
            _ = (FreeGroup.mk [xi])⁻¹ := mk_single_letter_inv xi
          rw [hm]
          exact mul_inv_cancel (FreeGroup.mk [xi])
        have hmkA2 : FreeGroup.mk A2 = 1 := by
          exact red_to_one A2 hA2red
        have hmkB2 : FreeGroup.mk B2 = 1 := by
          exact red_to_one B2 hB2red
        have hmkS : FreeGroup.mk (List.take (j - i + 1) (List.drop i W)) = 1 := by
          rw [hS]
          rw [← FreeGroup.mul_mk]
          rw [← FreeGroup.mul_mk]
          rw [← FreeGroup.mul_mk]
          rw [hmkA1', hmkA2, hmkB1', hmkB2]
          simp [hxi_inv]
        exact red_of_mk_one (List.take (j - i + 1) (List.drop i W)) hmkS
  intro i j hij hj hcov
  exact hmain (j - i) i j rfl hij hj hcov
/-- The `F`-block segment of `A ++ F ++ B` equals the corresponding segment
of `F`. -/
lemma factor_segment_eq {α : Type*} (A F B : List α) {i j : ℕ}
    (hij : i ≤ j) (hge : A.length ≤ i) (hlt : j < A.length + F.length) :
    List.take (j - i + 1) (List.drop i (A ++ F ++ B)) =
      List.take (j - i + 1) (List.drop (i - A.length) F) := by
  have hle_drop : j - i + 1 ≤ (List.drop (i - A.length) F).length := by
    rw [List.length_drop]
    omega
  have hle_idrop : i - A.length ≤ F.length := by omega
  have hdi : List.drop i (A ++ F ++ B) =
      List.drop (i - A.length) (List.drop A.length (A ++ F ++ B)) := by
    rw [List.drop_drop]
    congr 1
    omega
  have hd : List.drop A.length (A ++ F ++ B) = F ++ B := by
    have hw : A ++ F ++ B = A ++ (F ++ B) := by rw [List.append_assoc]
    rw [hw]
    rw [List.drop_append_of_le_length (by rfl)]
    rw [List.drop_length]
    simp
  have hd2 : List.drop (i - A.length) (F ++ B) =
      List.drop (i - A.length) F ++ B := by
    exact List.drop_append_of_le_length hle_idrop
  calc
    List.take (j - i + 1) (List.drop i (A ++ F ++ B))
        = List.take (j - i + 1)
            (List.drop (i - A.length) (List.drop A.length (A ++ F ++ B))) := by rw [hdi]
    _ = List.take (j - i + 1) (List.drop (i - A.length) (F ++ B)) := by rw [hd]
    _ = List.take (j - i + 1) (List.drop (i - A.length) F) := by
          rw [hd2]
          rw [List.take_append_of_le_length hle_drop]

/-- A cancelled pair of a concatenation never has both endpoints inside a
reduced factor. -/
theorem pair_not_in_reduced_factor {α : Type*} [DecidableEq α]
    (A F B : List (α × Bool)) (hF : FreeGroup.IsReduced F) {i j : ℕ}
    (hp : (i, j) ∈ cancelledPairs (A ++ F ++ B))
    (hge : A.length ≤ i) (hlt : j < A.length + F.length) : False := by
  have hij : i ≤ j := le_of_lt (pair_lt (A ++ F ++ B) hp)
  have hjW : j < (A ++ F ++ B).length := by
    rw [List.length_append, List.length_append]
    omega
  have hcov : ∀ x : ℕ, i ≤ x → x ≤ j → ∃ y : ℕ, i ≤ y ∧ y ≤ j ∧
      ((x, y) ∈ cancelledPairs (A ++ F ++ B) ∨
        (y, x) ∈ cancelledPairs (A ++ F ++ B)) := by
    intro x hxi hxj
    by_cases hxi_eq : x = i
    · subst x
      refine ⟨j, hij, le_rfl, ?_⟩
      left
      exact hp
    · by_cases hxj_eq : x = j
      · subst x
        refine ⟨i, le_rfl, hij, ?_⟩
        right
        exact hp
      · have hix : i < x := by omega
        have hxj2 : x < j := by omega
        rcases pair_interval_complete (A ++ F ++ B) hp x hix hxj2 with ⟨y, hiy, hyj, hp2⟩
        refine ⟨y, ?_, ?_, hp2⟩
        · omega
        · omega
  have hred := interval_fully_cancelled_reduce_empty (A ++ F ++ B) i j hij hjW hcov
  have heq := factor_segment_eq A F B hij hge hlt
  have hredF : FreeGroup.reduce
      (List.take (j - i + 1) (List.drop (i - A.length) F)) = [] := by
    rwa [heq] at hred
  let S := List.take (j - i + 1) (List.drop (i - A.length) F)
  have hSred : FreeGroup.IsReduced S := by
    unfold S
    exact seg_take_isReduced (List.drop (i - A.length) F) (j - i + 1)
      (seg_drop_isReduced F (i - A.length) hF)
  have hSn : S ≠ [] := by
    intro hz
    have hz' : List.take (j - i + 1) (List.drop (i - A.length) F) = [] := by simpa [S] using hz
    have hcases := (List.take_eq_nil_iff).mp hz'
    rcases hcases with hzero | hdropnil
    · omega
    · have hlen0 : (List.drop (i - A.length) F).length = 0 := by
        have := congrArg List.length hdropnil
        simpa using this
      rw [List.length_drop] at hlen0
      omega
  exact isReduced_reduce_ne_of_ne_nil S hSred hSn hredF
