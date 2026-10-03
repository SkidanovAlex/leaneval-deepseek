/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# Blocks and run decomposition for the Nielsen substitution `t ↦ t ^ p`

This file sets up the combinatorics of the substitution `t ↦ t ^ p` (all other letters fixed) at the
level of words, which is what the lemma `Work.OROneRel.not_isProperPower_subst` rests on.

* `blk t p c` is the *block* substituted for a single letter `c = (a, b)`: the word of `|p|` copies
  of `t` (with the sign flipped when `p < 0`) if `a = t`, and the single letter `c` otherwise.
* `blkT t p L` is the concatenation of the blocks of the letters of `L`.  For a reduced word `L` this
  is the reduced word of the image of `mk L` under `powSubst t p` (see `powSubst_toWord`).
* `unblk t p X` is the "inverse" of `blkT t p` on a run of `t`-letters: it divides the number of
  `t`-letters by `|p|` and shifts the sign back.
* `parseT t L` splits a word into the list of its non-`t` letters, each paired with the maximal run
  of `t`-letters following it.  It is designed for words that start with a letter different from `t`
  (`StartsNonT t L`), for which `assembleT (parseT t L) = L`.

The point of the run decomposition is that `blkT t p` multiplies the length of every `t`-run by `|p|`
and only shifts its sign, so a block-substituted word which is a `k`-th power forces the original
word to be a `k`-th power (`Work.OROneRel.exists_replicate_flatten_of_blkT_eq_flatten`).
-/
import Mathlib

namespace Work.OROneRel

universe u

variable {β : Type u}

/-- The sign of a `t`-letter after the substitution `t ↦ t ^ p`: unchanged for `p > 0`, flipped for
`p < 0`. -/
def signShift (p : ℤ) (b : Bool) : Bool := if p < 0 then !b else b

@[simp] theorem signShift_signShift (p : ℤ) (b : Bool) : signShift p (signShift p b) = b := by
  unfold signShift
  split_ifs <;> simp_all

theorem signShift_pos {p : ℤ} (hp : 0 < p) (b : Bool) : signShift p b = b := by
  unfold signShift
  rw [if_neg (by omega)]

theorem signShift_neg {p : ℤ} (hp : p < 0) (b : Bool) : signShift p b = !b := by
  unfold signShift
  rw [if_pos hp]

/-- The block substituted for a single letter `c = (a, b)`: `|p|` copies of `t` (sign shifted if
`p < 0`) when `a = t`, and the single letter `c` otherwise. -/
def blk [DecidableEq β] (t : β) (p : ℤ) (c : β × Bool) : List (β × Bool) :=
  if c.1 = t then List.replicate p.natAbs (t, signShift p c.2) else [c]

/-- The word obtained from `L` by substituting every letter by its block. -/
def blkT [DecidableEq β] (t : β) (p : ℤ) (L : List (β × Bool)) : List (β × Bool) :=
  (L.map (blk t p)).flatten

/-- The inverse of `blkT t p` on a run of `t`-letters: a run of `N` `t`-letters is the image of
`N / |p|` `t`-letters with the sign shifted back. -/
def unblk (t : β) (p : ℤ) (X : List (β × Bool)) : List (β × Bool) :=
  List.replicate (X.length / p.natAbs) (t, signShift p ((X.head?.map (fun c => c.2)).getD false))

/-- `L` starts with a letter different from `t` (or is empty). -/
def StartsNonT (t : β) (L : List (β × Bool)) : Prop :=
  ∀ (c : β × Bool) (rest : List (β × Bool)), L = c :: rest → c.1 ≠ t

/-- The Boolean test "`c` is a `t`-letter". -/
def isT [DecidableEq β] (t : β) (c : β × Bool) : Bool := decide (c.1 = t)

@[simp] theorem isT_eq_true_iff [DecidableEq β] {t : β} {c : β × Bool} :
    isT t c = true ↔ c.1 = t := by
  simp [isT]

@[simp] theorem isT_eq_false_iff [DecidableEq β] {t : β} {c : β × Bool} :
    isT t c = false ↔ c.1 ≠ t := by
  simp [isT]

/-- The run decomposition of a word with respect to the letter `t`: the list of its non-`t` letters,
each paired with the maximal run of `t`-letters that follows it.  Leading `t`-letters are dropped, so
the decomposition is faithful exactly on words starting with a non-`t` letter. -/
def parseT [DecidableEq β] (t : β) : List (β × Bool) → List ((β × Bool) × List (β × Bool)) := fun L =>
  match L with
  | [] => []
  | c :: rest =>
    if c.1 = t then parseT t rest
    else (c, rest.takeWhile (isT t)) :: parseT t (rest.dropWhile (isT t))
termination_by L => L.length
decreasing_by
  · exact Nat.lt_succ_self _
  · exact Nat.lt_succ_of_le (List.length_dropWhile_le _ _)

/-- The word assembled from a run decomposition. -/
def assembleT (P : List ((β × Bool) × List (β × Bool))) : List (β × Bool) :=
  (P.map (fun q => q.1 :: q.2)).flatten

@[simp] theorem parseT_nil [DecidableEq β] (t : β) : parseT t ([] : List (β × Bool)) = [] := by
  rw [parseT]

theorem parseT_cons_of_eq [DecidableEq β] {t : β} {c : β × Bool} {rest : List (β × Bool)}
    (h : c.1 = t) : parseT t (c :: rest) = parseT t rest := by
  rw [parseT]
  simp only [h, if_pos]

theorem parseT_cons_of_ne [DecidableEq β] {t : β} {c : β × Bool} {rest : List (β × Bool)}
    (h : c.1 ≠ t) :
    parseT t (c :: rest) = (c, rest.takeWhile (isT t)) :: parseT t (rest.dropWhile (isT t)) := by
  rw [parseT]
  simp only [h, if_neg, not_false_iff]

@[simp] theorem assembleT_nil : assembleT ([] : List ((β × Bool) × List (β × Bool))) = [] := rfl

theorem assembleT_cons (c : β × Bool) (R : List (β × Bool))
    (P : List ((β × Bool) × List (β × Bool))) :
    assembleT ((c, R) :: P) = c :: (R ++ assembleT P) := by
  simp [assembleT]

/-! ### `StartsNonT` -/

theorem StartsNonT.nil (t : β) : StartsNonT t [] := by
  intro c rest h; exact absurd h (by simp)

theorem StartsNonT.cons {t : β} {c : β × Bool} {rest : List (β × Bool)} (h : c.1 ≠ t) :
    StartsNonT t (c :: rest) := by
  intro c' rest' h'
  injection h' with h1 _
  rw [← h1]; exact h

theorem startsNonT_iff {t : β} {L : List (β × Bool)} :
    StartsNonT t L ↔ L = [] ∨ ∃ (c : β × Bool) (rest : List (β × Bool)), L = c :: rest ∧ c.1 ≠ t := by
  constructor
  · intro h
    cases L with
    | nil => exact Or.inl rfl
    | cons c rest => exact Or.inr ⟨c, rest, rfl, h c rest rfl⟩
  · rintro (rfl | ⟨c, rest, rfl, hc⟩)
    · exact StartsNonT.nil t
    · exact StartsNonT.cons hc

theorem startsNonT_dropWhile [DecidableEq β] (t : β) (L : List (β × Bool)) :
    StartsNonT t (L.dropWhile (isT t)) := by
  induction L with
  | nil => exact StartsNonT.nil t
  | cons c rest ih =>
    by_cases h : c.1 = t
    · rw [List.dropWhile_cons_of_pos (p := isT t) (a := c) (l := rest) (by simp [isT, h])]
      exact ih
    · rw [List.dropWhile_cons_of_neg (p := isT t) (a := c) (l := rest) (by simp [isT, h])]
      exact StartsNonT.cons h

theorem startsNonT_takeWhile_all [DecidableEq β] (t : β) (L : List (β × Bool)) :
    ∀ c ∈ L.takeWhile (isT t), c.1 = t := by
  induction L with
  | nil => simp
  | cons d rest ih =>
    by_cases h : d.1 = t
    · rw [List.takeWhile_cons_of_pos (p := isT t) (a := d) (l := rest) (by simp [isT, h])]
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact h
      · exact ih c hc
    · rw [List.takeWhile_cons_of_neg (p := isT t) (a := d) (l := rest) (by simp [isT, h])]
      simp

/-! ### Elementary computations with `blk` and `blkT` -/

theorem blk_of_eq [DecidableEq β] {t : β} {p : ℤ} {c : β × Bool} (h : c.1 = t) :
    blk t p c = List.replicate p.natAbs (t, signShift p c.2) := by
  rw [blk]; simp only [h, if_pos]

theorem blk_of_ne [DecidableEq β] {t : β} {p : ℤ} {c : β × Bool} (h : c.1 ≠ t) :
    blk t p c = [c] := by
  rw [blk]; simp only [h, if_neg, not_false_iff]

theorem blk_ne_nil [DecidableEq β] {t : β} {p : ℤ} (hp : p ≠ 0) (c : β × Bool) :
    blk t p c ≠ [] := by
  by_cases h : c.1 = t
  · rw [blk_of_eq h, List.ne_nil_iff_length_pos, List.length_replicate]
    exact Int.natAbs_pos.mpr hp
  · rw [blk_of_ne h]; simp

theorem fst_mem_blk [DecidableEq β] {t : β} (p : ℤ) {c d : β × Bool} (hd : d ∈ blk t p c) :
    d.1 = c.1 ∨ d.1 = t := by
  by_cases h : c.1 = t
  · rw [blk_of_eq h] at hd
    exact Or.inr (by simp [List.eq_of_mem_replicate hd])
  · rw [blk_of_ne h, List.mem_singleton] at hd
    exact Or.inl (by rw [hd])

theorem blkT_cons [DecidableEq β] {t : β} (p : ℤ) (c : β × Bool) (L : List (β × Bool)) :
    blkT t p (c :: L) = blk t p c ++ blkT t p L := by
  simp [blkT]

theorem blkT_append [DecidableEq β] {t : β} (p : ℤ) (L M : List (β × Bool)) :
    blkT t p (L ++ M) = blkT t p L ++ blkT t p M := by
  simp [blkT, List.map_append, List.flatten_append]

theorem blkT_eq_nil_iff [DecidableEq β] {t : β} {p : ℤ} (hp : p ≠ 0) (L : List (β × Bool)) :
    blkT t p L = [] ↔ L = [] := by
  constructor
  · intro h
    cases L with
    | nil => rfl
    | cons c rest =>
      rw [blkT_cons, List.append_eq_nil_iff] at h
      exact absurd h.1 (blk_ne_nil hp c)
  · rintro rfl; simp [blkT]

theorem blkT_fst_of_all_fst_eq [DecidableEq β] {t : β} (p : ℤ) {L : List (β × Bool)}
    (hL : ∀ c ∈ L, c.1 = t) : ∀ c ∈ blkT t p L, c.1 = t := by
  intro c hc
  rw [blkT, List.mem_flatten] at hc
  obtain ⟨Y, hY, hcY⟩ := hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hY
  rcases fst_mem_blk p hcY with h | h
  · rw [h]; exact hL d hd
  · exact h

theorem startsNonT_blkT [DecidableEq β] {t : β} {p : ℤ} {L : List (β × Bool)}
    (hL : StartsNonT t L) : StartsNonT t (blkT t p L) := by
  intro c rest h
  cases L with
  | nil => simp [blkT] at h
  | cons d L' =>
    have hd : d.1 ≠ t := hL d L' rfl
    rw [blkT_cons, blk_of_ne hd] at h
    simp only [List.singleton_append, List.cons.injEq] at h
    rw [← h.1]; exact hd

/-! ### Runs of `t`-letters -/

/-- A *run* of `t`-letters: the empty word, or `n` copies of the letter `(t, b)`. -/
def IsTRun (t : β) (X : List (β × Bool)) : Prop :=
  X = [] ∨ ∃ (n : ℕ) (b : Bool), X = List.replicate n (t, b)

theorem IsTRun.nil (t : β) : IsTRun t [] := Or.inl rfl

theorem IsTRun.of_replicate (t : β) (n : ℕ) (b : Bool) : IsTRun t (List.replicate n (t, b)) :=
  Or.inr ⟨n, b, rfl⟩

theorem IsTRun.fst {t : β} {X : List (β × Bool)} (h : IsTRun t X) {c : β × Bool} (hc : c ∈ X) :
    c.1 = t := by
  rcases h with rfl | ⟨n, b, rfl⟩
  · simp at hc
  · rw [List.eq_of_mem_replicate hc]

/-! ### `unblk` -/

theorem flatten_replicate_replicate {σ : Type*} (n m : ℕ) (a : σ) :
    (List.replicate n (List.replicate m a)).flatten = List.replicate (n * m) a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, ih, ← List.replicate_add, Nat.add_comm, Nat.succ_mul]

theorem blkT_replicate_t [DecidableEq β] {t : β} (p : ℤ) (n : ℕ) (b : Bool) :
    blkT t p (List.replicate n (t, b)) = List.replicate (n * p.natAbs) (t, signShift p b) := by
  rw [blkT, List.map_replicate, blk_of_eq (t := t) (p := p) (c := (t, b)) rfl,
    flatten_replicate_replicate]

theorem unblk_blkT_of_isTRun {t : β} [DecidableEq β] {p : ℤ} (hp : p ≠ 0)
    {X : List (β × Bool)} (hX : IsTRun t X) : unblk t p (blkT t p X) = X := by
  rcases hX with rfl | ⟨n, b, rfl⟩
  · simp [blkT, unblk]
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [blkT, unblk]
    have hpos : 0 < n * p.natAbs := Nat.mul_pos hn (Int.natAbs_pos.mpr hp)
    have hlen : (blkT t p (List.replicate n (t, b))).length = n * p.natAbs := by
      rw [blkT_replicate_t, List.length_replicate]
    have hhead : (blkT t p (List.replicate n (t, b))).head? = some (t, signShift p b) := by
      rw [blkT_replicate_t, List.head?_replicate, if_neg (Nat.ne_of_gt hpos)]
    rw [unblk, hlen, hhead]
    simp [Nat.mul_div_right, Int.natAbs_pos.mpr hp]

/-! ### Powers of words -/

theorem map_flatten_replicate {σ τ : Type*} (f : σ → τ) (k : ℕ) (X : List σ) :
    ((List.replicate k X).flatten).map f = (List.replicate k (X.map f)).flatten := by
  rw [List.map_flatten, List.map_replicate]

theorem flatten_flatten_replicate {σ : Type*} (k : ℕ) (Y : List (List σ)) :
    ((List.replicate k Y).flatten).flatten = (List.replicate k Y.flatten).flatten := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, List.flatten_append, ih, ← List.flatten_cons,
      ← List.replicate_succ]

theorem assembleT_flatten_replicate (k : ℕ) (P : List ((β × Bool) × List (β × Bool))) :
    assembleT ((List.replicate k P).flatten) = (List.replicate k (assembleT P)).flatten := by
  unfold assembleT
  rw [map_flatten_replicate]
  exact flatten_flatten_replicate k _

end Work.OROneRel
