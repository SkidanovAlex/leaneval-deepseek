import Submission.Work.NielsenAlign
import Submission.Work.NielsenCore
import Mathlib.Data.List.Infix

open FreeGroup
open Commons.GroupTheory.FreeGroup
set_option autoImplicit false

/-!
# The peeling lemma of Nielsen 1918 (F₂ pair reduction): skeleton

Target theorems (machine-validated; see `NielsenReductionBlueprint.lean`).
Ambient group `F₂ := FreeGroup (Fin 2)`.  For reduced words `u v` write
`|x| := FreeGroup.norm x`; a word is *cyclically reduced* when its first
letter is not the letter-inverse of its last letter (`CyclicallyReduced`);
`(u, v)` is *primitive* when `Subgroup.closure ({u, v}) = ⊤`.

    peel_shorter_prefix_suffix (hu : u ≠ 1) (hv : v ≠ 1)
        (hcu : CyclicallyReduced u) (hcv : CyclicallyReduced v)
        (hgen : PrimitivePair u v) (hlt : |u| < |v|) :
        List.IsPrefix u.toWord v.toWord ∨ List.IsSuffix u.toWord v.toWord ∨
        List.IsPrefix (u⁻¹).toWord v.toWord ∨ List.IsSuffix (u⁻¹).toWord v.toWord ∨
        List.IsPrefix u.toWord (v⁻¹).toWord ∨ List.IsSuffix u.toWord (v⁻¹).toWord ∨
        List.IsPrefix (u⁻¹).toWord (v⁻¹).toWord ∨
        List.IsSuffix (u⁻¹).toWord (v⁻¹).toWord
    -- i.e. "u^{±1} is a prefix or suffix of v^{±1}"; the eight disjuncts let
    -- each Fall-I absorption (against v or against v⁻¹) land directly.

    peel_equal_length (hu : u ≠ 1) (hv : v ≠ 1)
        (hcu : CyclicallyReduced u) (hcv : CyclicallyReduced v)
        (hgen : PrimitivePair u v) (heq : |u| = |v|) : |u| = 1

This file carries the vocabulary (definitions) and the provable low-level
structural lemmas (single-letter structure of length-1 words; cyclically
reduced ⟺ first letter not inverse of last; the word↔group bridges: a word
being a prefix/suffix of another is a group factorisation with additive
norm).  The two statements above are the open target (Nielsen §4-6
aggregate/absorption argument); do not mint weaker or guessed variants.
-/

namespace Submission.Nielsen

noncomputable section

open scoped BigOperators

/-- A reduced word is *cyclically reduced* when its first letter is not the
letter-inverse of its last letter.  (Words of length ≤ 1 are automatically
cyclically reduced.) -/
def CyclicallyReduced {n : ℕ} (x : FreeGroup (Fin n)) : Prop :=
  ∀ c : Fin n × Bool, firstLetter x = some c → lastLetter x ≠ some (letterInv c)

/-- The pair `(u, v)` generates the whole free group (a *primitive pair*). -/
def PrimitivePair (n : ℕ) (u v : FreeGroup (Fin n)) : Prop :=
  Subgroup.closure ({u, v} : Set (FreeGroup (Fin n))) = ⊤

/-- A letter is not its own letter-inverse. -/
lemma letterInv_ne_self {α : Type*} (l : α × Bool) : letterInv l ≠ l := by
  cases l with
  | mk a b => cases b <;> simp [letterInv]

/-- The letter-inverse of a letter with parity `b` has the opposite parity. -/
lemma letterInv_bool {α : Type*} (a : α) (b : Bool) : letterInv (a, b) = (a, !b) := by
  rfl

/-- A nonzero word of norm 1 is a single letter. -/
lemma toWord_singleton_of_norm_eq_one {n : ℕ} {x : FreeGroup (Fin n)} (hx : x ≠ 1)
    (h1 : FreeGroup.norm x = 1) : ∃ l : Fin n × Bool, x.toWord = [l] := by
  have hne : x.toWord ≠ [] := by
    intro hnil
    exact hx (FreeGroup.toWord_eq_nil_iff.mp hnil)
  obtain ⟨l, t, hc⟩ := List.exists_cons_of_ne_nil hne
  change x.toWord.length = 1 at h1
  rw [hc] at h1
  simp at h1
  exact ⟨l, by rw [hc, h1]⟩

/-- A single-letter word `[(i, b)]` represents `of i` (when `b = true`) or
`(of i)⁻¹` (when `b = false`). -/
lemma eq_of_of_singleton_true {n : ℕ} {i : Fin n} (x : FreeGroup (Fin n))
    (h : x.toWord = [(i, true)]) : x = FreeGroup.of i := by
  have hof : (FreeGroup.of i).toWord = [(i, true)] := by simp
  exact FreeGroup.toWord_inj.mp (by rw [h, hof])

lemma eq_inv_of_singleton_false {n : ℕ} {i : Fin n} (x : FreeGroup (Fin n))
    (h : x.toWord = [(i, false)]) : x = (FreeGroup.of i)⁻¹ := by
  have hof : ((FreeGroup.of i)⁻¹).toWord = [(i, false)] := by
    rw [FreeGroup.toWord_inv]
    rfl
  exact FreeGroup.toWord_inj.mp (by rw [h, hof])

/-- A word of length at most 1 is cyclically reduced. -/
lemma cyclRed_of_norm_le_one {n : ℕ} {x : FreeGroup (Fin n)} (h : FreeGroup.norm x ≤ 1) :
    CyclicallyReduced x := by
  intro c hf hlast
  by_cases hx : x = 1
  · subst x
    simp [firstLetter] at hf
  · have hnz : FreeGroup.norm x ≠ 0 := by
      intro hz
      exact hx (FreeGroup.norm_eq_zero.mp hz)
    have hone : FreeGroup.norm x = 1 := by omega
    rcases toWord_singleton_of_norm_eq_one hx hone with ⟨l, hl⟩
    change (FreeGroup.toWord x).head? = some c at hf
    change (FreeGroup.toWord x).getLast? = some (letterInv c) at hlast
    rw [hl] at hf hlast
    simp at hf hlast
    exact letterInv_ne_self c (hlast.symm.trans hf)


lemma commonPrefixLen_eq_zero {α : Type*} [DecidableEq α] (X Y : List α) :
    commonPrefixLen X Y = 0 ↔ X = [] ∨ Y = [] ∨ X.head? ≠ Y.head? := by
  constructor
  · intro h
    by_cases hX : X = []
    · exact Or.inl hX
    by_cases hY : Y = []
    · exact Or.inr (Or.inl hY)
    · right; right
      intro hh
      obtain ⟨a, X', hXc⟩ := List.exists_cons_of_ne_nil hX
      obtain ⟨b, Y', hYc⟩ := List.exists_cons_of_ne_nil hY
      subst X
      subst Y
      have hab : a = b := by
        simpa using hh
      have hge : commonPrefixLen (a :: X') (b :: Y') ≠ 0 := by
        rw [commonPrefixLen_cons]
        simp [hab]
      exact hge h
  · intro h
    induction X generalizing Y with
    | nil => simp [commonPrefixLen]
    | cons a X' ih =>
        cases Y with
        | nil => simp [commonPrefixLen]
        | cons b Y' =>
            by_cases hab : a = b
            · simp [hab] at h
            · rw [commonPrefixLen_cons]
              simp [hab]

lemma head?_invRev {α : Type*} (L : List (α × Bool)) :
    (FreeGroup.invRev L).head? = Option.map letterInv L.getLast? := by
  unfold FreeGroup.invRev letterInv
  rw [List.head?_reverse, List.getLast?_map]

lemma head?_invRev_of_getLast {α : Type*} (L : List (α × Bool)) (c : α × Bool)
    (h : L.getLast? = some c) : (FreeGroup.invRev L).head? = some (letterInv c) := by
  rw [head?_invRev, h]
  rfl

lemma reverse_map_letterInv {α : Type*} (L : List (α × Bool)) :
    L.reverse.map letterInv = FreeGroup.invRev L := by
  unfold FreeGroup.invRev
  rw [List.map_reverse]
  rfl

lemma no_cancel_of_align_eq_zero {α : Type*} [DecidableEq α] (L M : List (α × Bool))
    (h0 : align L M = 0) :
    ∀ a b, L.getLast? = some (a, b) → M.head? = some (a, !b) → False := by
  intro a b hlast hhead
  unfold align at h0
  rw [reverse_map_letterInv L] at h0
  rw [commonPrefixLen_eq_zero (FreeGroup.invRev L) M] at h0
  rcases h0 with hX | hY | hh
  · have hLne : L ≠ [] := by
      intro hE
      subst hE
      simp at hlast
    have hL : L = [] := by
      have h0' := congrArg FreeGroup.invRev hX
      simpa using h0'
    exact hLne hL
  · have hMne : M ≠ [] := by
      intro hE
      subst hE
      simp at hhead
    exact hMne hY
  · exact hh (by
      rw [head?_invRev_of_getLast L (a, b) hlast, hhead]
      rfl)



lemma word_prefix_iff_factor {n : ℕ} (u v : FreeGroup (Fin n)) :
    List.IsPrefix u.toWord v.toWord ↔
      ∃ w : FreeGroup (Fin n), v = u * w ∧ v.toWord = u.toWord ++ w.toWord := by
  constructor
  · intro hp
    rcases hp with ⟨t, ht⟩
    have ht_red : FreeGroup.IsReduced t := by
      have hd := FreeGroup.isReduced_toWord (x := v)
      have : t = v.toWord.drop u.toWord.length := by
        rw [← ht]
        simp
      rw [this]
      exact List.IsChain.drop hd u.toWord.length
    refine ⟨FreeGroup.mk t, ?_, ?_⟩
    · apply FreeGroup.toWord_inj.mp
      rw [FreeGroup.toWord_mul, FreeGroup.toWord_mk,
        FreeGroup.IsReduced.reduce_eq ht_red]
      rw [ht]
      exact (FreeGroup.IsReduced.reduce_eq (FreeGroup.isReduced_toWord (x := v))).symm
    · rw [FreeGroup.toWord_mk, FreeGroup.IsReduced.reduce_eq ht_red]
      exact ht.symm
  · rintro ⟨w, hvw, hw⟩
    exact ⟨w.toWord, hw.symm⟩

lemma word_suffix_iff_factor {n : ℕ} (u v : FreeGroup (Fin n)) :
    List.IsSuffix u.toWord v.toWord ↔
      ∃ w : FreeGroup (Fin n), v = w * u ∧ v.toWord = w.toWord ++ u.toWord := by
  constructor
  · intro hp
    rcases hp with ⟨t, ht⟩
    have ht_red : FreeGroup.IsReduced t := by
      have hd := FreeGroup.isReduced_toWord (x := v)
      have : t = v.toWord.take (v.toWord.length - u.toWord.length) := by
        rw [← ht]
        simp
      rw [this]
      exact List.IsChain.take hd (v.toWord.length - u.toWord.length)
    refine ⟨FreeGroup.mk t, ?_, ?_⟩
    · apply FreeGroup.toWord_inj.mp
      rw [FreeGroup.toWord_mul, FreeGroup.toWord_mk,
        FreeGroup.IsReduced.reduce_eq ht_red]
      rw [ht]
      exact (FreeGroup.IsReduced.reduce_eq (FreeGroup.isReduced_toWord (x := v))).symm
    · rw [FreeGroup.toWord_mk, FreeGroup.IsReduced.reduce_eq ht_red]
      exact ht.symm
  · rintro ⟨w, hvw, hw⟩
    exact ⟨w.toWord, hw.symm⟩

lemma norm_mul_eq_add_iff_append {n : ℕ} (u w : FreeGroup (Fin n)) :
    FreeGroup.norm (u * w) = FreeGroup.norm u + FreeGroup.norm w ↔
      (u * w).toWord = u.toWord ++ w.toWord := by
  constructor
  · intro hn
    change (u * w).toWord.length = u.toWord.length + w.toWord.length at hn
    rw [FreeGroup.toWord_mul] at hn
    have hredlen := reduce_append_align u.toWord w.toWord
      (FreeGroup.isReduced_toWord (x := u)) (FreeGroup.isReduced_toWord (x := w))
    have halign_le : 2 * align u.toWord w.toWord ≤ u.toWord.length + w.toWord.length := by
      have hl := align_le_length_left u.toWord w.toWord
      have hr := align_le_length_right u.toWord w.toWord
      omega
    have halign : align u.toWord w.toWord = 0 := by
      omega
    have hred : FreeGroup.reduce (u.toWord ++ w.toWord) = u.toWord ++ w.toWord := by
      refine reduce_append_no_junction u.toWord w.toWord
        (FreeGroup.isReduced_toWord (x := u)) (FreeGroup.isReduced_toWord (x := w)) ?_
      exact no_cancel_of_align_eq_zero u.toWord w.toWord halign
    rw [← hred]
    exact FreeGroup.toWord_mul u w
  · intro h
    change (u * w).toWord.length = u.toWord.length + w.toWord.length
    rw [h, List.length_append]

/-! ## Factor absorption (Nielsen §4-6): definitions, the single-neighbour
(Fall I) lemmas, and the open aggregate theorem

**General factor-absorption lemma** (the §4 claim; machine-validated on
~3500 random instances with 0 failures, plus all F₂ instances with words of
length ≤ 5): let `w₁,…,wₖ` (`k ≥ 2`) be nonempty reduced words with no
`wⱼ = invRev wⱼ₊₁` (an expression reduced over the factor alphabet), and
suppose `reduce (w₁ ++ ⋯ ++ wₖ)` has length `≤ 1`.  Then *some factor `wⱼ`
is absorbed by its ≤ 2 neighbours*: every letter of `wⱼ` cancels in the
reduction, and each of its letters is paired with a letter of `wⱼ₋₁` or
`wⱼ₊₁` only.  (Validated: product length 0 or 1 with `k ≥ 2`, arbitrary
reduced factors over alphabets of size 2-3: **0 failures** over ~3500
random instances; counterexamples exist at final length 2, e.g. two
single-letter factors — so length ≤ 1 is the right hypothesis.)

The classical proof runs through a folding argument on the concatenation
(if every factor kept an unpaired letter, the reduced word would be
nonempty with at least one surviving letter per factor, contradicting final
length ≤ 1).  **The `k = 2` base case is PROVEN below (`two_factor_peel`,
with the pure-list lemmas `commonPrefixLen_append_self`,
`commonPrefixLen_eq_length_left_iff_prefix`,
`commonPrefixLen_eq_length_right_iff_prefix`, `commonPrefixLen_comm`,
`prefix_invRev_iff_suffix_invRev`):** for two factors with reduced product of
length ≤ 1, the shorter factor is fully absorbed into the longer
(`AbsorbedRight`/`AbsorbedLeft`).  The general `k ≥ 3` statement (with the
two-neighbour Case II analysis) is open in Lean (the aggregate core).

**Single-neighbour (Fall I) step — PROVEN below.**  In the F₂ setting with
`|u| < |v|`, an `u^{±1}`-factor cannot be absorbed by an `u^{±1}`-neighbour
(that would force an adjacent inverse pair in the reduced expression), so an
`u^{±1}`-factor absorbed by a *single* neighbour must sit at the head or the
tail of a `v^{±1}`-neighbour.  "The factor `x` is fully absorbed into the
head of `y`" means `y = x⁻¹ * z` with additive norm — equivalently (bridge
`word_prefix_iff_factor`) the word of `x⁻¹` is a prefix of the word of `y`;
the mirror is "absorbed into the tail" (suffix).  These predicates, their `toWord` characterisations, and the Fall-I prefix/suffix conclusions (raw, against `v` and against `v⁻¹`; the peeling target is accordingly stated as "`u^{±1}` a prefix or suffix of `v^{±1}`") are below. -/

/-- The single-neighbour absorption of `x` into the head of `y`: multiplying
`x` against the left of `y` cancels `x` entirely, leaving `z`. -/
def AbsorbedRight {n : ℕ} (x y : FreeGroup (Fin n)) : Prop :=
  ∃ z : FreeGroup (Fin n), y = x⁻¹ * z ∧ y.toWord = (x⁻¹).toWord ++ z.toWord

/-- The single-neighbour absorption of `x` into the tail of `y`: multiplying
`x` against the right of `y` cancels `x` entirely, leaving `z`. -/
def AbsorbedLeft {n : ℕ} (x y : FreeGroup (Fin n)) : Prop :=
  ∃ z : FreeGroup (Fin n), y = z * x⁻¹ ∧ y.toWord = z.toWord ++ (x⁻¹).toWord

/-- `AbsorbedRight x y` iff the word of `x⁻¹` is a prefix of the word of `y`. -/
lemma absorbedRight_iff_prefix {n : ℕ} (x y : FreeGroup (Fin n)) :
    AbsorbedRight x y ↔ List.IsPrefix (x⁻¹).toWord y.toWord := by
  unfold AbsorbedRight
  exact (word_prefix_iff_factor (x⁻¹) y).symm

/-- `AbsorbedLeft x y` iff the word of `x⁻¹` is a suffix of the word of `y`. -/
lemma absorbedLeft_iff_suffix {n : ℕ} (x y : FreeGroup (Fin n)) :
    AbsorbedLeft x y ↔ List.IsSuffix (x⁻¹).toWord y.toWord := by
  unfold AbsorbedLeft
  exact (word_suffix_iff_factor (x⁻¹) y).symm

/-- Fall I (right): an `u`-factor absorbed into the head of `v` makes the
word of `u⁻¹` a prefix of the word of `v`. -/
lemma fallI_right_prefix {n : ℕ} {u v : FreeGroup (Fin n)} (h : AbsorbedRight u v) :
    List.IsPrefix (u⁻¹).toWord v.toWord := by
  exact (absorbedRight_iff_prefix u v).1 h

/-- Fall I (left): an `u`-factor absorbed into the tail of `v` makes the word
of `u⁻¹` a suffix of the word of `v`. -/
lemma fallI_left_suffix {n : ℕ} {u v : FreeGroup (Fin n)} (h : AbsorbedLeft u v) :
    List.IsSuffix (u⁻¹).toWord v.toWord := by
  exact (absorbedLeft_iff_suffix u v).1 h

/-- Fall I against `v⁻¹` (raw): an `u`-factor absorbed into the head of
`v⁻¹` makes the word of `u⁻¹` a prefix of the word of `v⁻¹`. -/
lemma fallI_right_prefix_inv {n : ℕ} {u v : FreeGroup (Fin n)} (h : AbsorbedRight u (v⁻¹)) :
    List.IsPrefix (u⁻¹).toWord (v⁻¹).toWord := by
  exact (absorbedRight_iff_prefix u (v⁻¹)).1 h

/-- Fall I against `v⁻¹` (raw): an `u`-factor absorbed into the tail of
`v⁻¹` makes the word of `u⁻¹` a suffix of the word of `v⁻¹`. -/
lemma fallI_left_suffix_inv {n : ℕ} {u v : FreeGroup (Fin n)} (h : AbsorbedLeft u (v⁻¹)) :
    List.IsSuffix (u⁻¹).toWord (v⁻¹).toWord := by
  exact (absorbedLeft_iff_suffix u (v⁻¹)).1 h



/-! ## Factor absorption — the two-factor base case (PROVEN)

The general factor-absorption claim (see the aggregate-core paragraph above)
holds for `k = 2` in the strongest possible form: two factors whose product
reduces to a word of length ≤ 1, with no further hypothesis, already have one
factor **fully absorbed into the other** (`AbsorbedRight w₁ w₂` if `w₁` is no
longer than `w₂`, `AbsorbedLeft w₂ w₁` otherwise).  The proof uses the
quantitative alignment identity: with `c := align w₁.toWord w₂.toWord` the
reduced length is `|w₁| + |w₂| − 2c`; since it is ≤ 1 and `c ≤ |w₁|,|w₂|`,
one of `c = |w₁|`, `c = |w₂|` must hold, which by the prefix characterisation
of `commonPrefixLen` says exactly that the whole word of the shorter factor
cancels into the end of the longer one.  (No "no-adjacent-inverse" or
non-triviality hypothesis is needed at `k = 2`: the conclusions hold even in
the degenerate cases.) -/

lemma commonPrefixLen_append_self {α : Type*} [DecidableEq α] (X t : List α) :
    commonPrefixLen X (X ++ t) = X.length := by
  induction X with
  | nil => rfl
  | cons a X' ih =>
      rw [List.cons_append, commonPrefixLen_cons, if_pos rfl]
      simp [ih]

lemma commonPrefixLen_eq_length_left_iff_prefix {α : Type*} [DecidableEq α] (X Y : List α) :
    commonPrefixLen X Y = X.length ↔ X <+: Y := by
  constructor
  · intro h
    induction X generalizing Y with
    | nil => exact ⟨Y, rfl⟩
    | cons a X' ih =>
        cases Y with
        | nil =>
            exfalso
            have hz : X'.length + 1 = 0 := by
              simpa [commonPrefixLen] using h.symm
            omega
        | cons b Y' =>
            rw [commonPrefixLen_cons] at h
            by_cases hab : a = b
            · have hrec : commonPrefixLen X' Y' = X'.length := by
                simp [hab] at h
                omega
              rcases ih Y' hrec with ⟨t, ht⟩
              refine ⟨t, ?_⟩
              simp [hab, ht]
            · exfalso
              have hz : X'.length + 1 = 0 := by
                simpa [hab, commonPrefixLen] using h.symm
              omega
  · intro h
    rcases h with ⟨t, ht⟩
    rw [← ht]
    exact commonPrefixLen_append_self X t

lemma commonPrefixLen_comm {α : Type*} [DecidableEq α] (X Y : List α) :
    commonPrefixLen X Y = commonPrefixLen Y X := by
  induction X generalizing Y with
  | nil => simp [commonPrefixLen]
  | cons a X' ih =>
      cases Y with
      | nil => simp [commonPrefixLen]
      | cons b Y' =>
          rw [commonPrefixLen_cons, commonPrefixLen_cons]
          by_cases hab : a = b
          · simp [hab, ih Y']
          · simp [hab]
            intro hba
            exact hab hba.symm

/-- Mirror of `commonPrefixLen_eq_length_left_iff_prefix`: the common prefix
has full length of the *right* word iff the right word is a prefix of the
left. -/
lemma commonPrefixLen_eq_length_right_iff_prefix {α : Type*} [DecidableEq α] (X Y : List α) :
    commonPrefixLen X Y = Y.length ↔ Y <+: X := by
  rw [← commonPrefixLen_comm Y X]
  exact commonPrefixLen_eq_length_left_iff_prefix Y X

lemma prefix_invRev_iff_suffix_invRev {α : Type*} (A B : List (α × Bool)) :
    A <+: FreeGroup.invRev B ↔ FreeGroup.invRev A <:+ B := by
  constructor
  · intro h
    rcases h with ⟨t, ht⟩
    have hr := congrArg FreeGroup.invRev ht
    rw [FreeGroup.invRev_append] at hr
    rw [FreeGroup.invRev_invRev] at hr
    exact ⟨FreeGroup.invRev t, hr⟩
  · intro h
    rcases h with ⟨t, ht⟩
    have hr := congrArg FreeGroup.invRev ht
    rw [FreeGroup.invRev_append] at hr
    rw [FreeGroup.invRev_invRev] at hr
    exact ⟨FreeGroup.invRev t, hr⟩

lemma two_factor_peel {n : ℕ} (w₁ w₂ : FreeGroup (Fin n))
    (hred : FreeGroup.norm (w₁ * w₂) ≤ 1) :
    AbsorbedRight w₁ w₂ ∨ AbsorbedLeft w₂ w₁ := by
  have hredlen : (FreeGroup.reduce (w₁.toWord ++ w₂.toWord)).length ≤ 1 := by
    rw [← FreeGroup.toWord_mul]
    change FreeGroup.norm (w₁ * w₂) ≤ 1
    exact hred
  have hred2 := reduce_append_align w₁.toWord w₂.toWord
    (FreeGroup.isReduced_toWord (x := w₁)) (FreeGroup.isReduced_toWord (x := w₂))
  have halign_le : 2 * align w₁.toWord w₂.toWord ≤ w₁.toWord.length + w₂.toWord.length := by
    have hl := align_le_length_left w₁.toWord w₂.toWord
    have hr := align_le_length_right w₁.toWord w₂.toWord
    omega
  by_cases hab : w₁.toWord.length ≤ w₂.toWord.length
  · have halign : align w₁.toWord w₂.toWord = w₁.toWord.length := by
      by_contra hne
      have hlt : align w₁.toWord w₂.toWord < w₁.toWord.length := by
        exact lt_of_le_of_ne (align_le_length_left w₁.toWord w₂.toWord) hne
      omega
    left
    rw [absorbedRight_iff_prefix]
    have hpfx : FreeGroup.invRev w₁.toWord <+: w₂.toWord := by
      have hc := commonPrefixLen_eq_length_left_iff_prefix (FreeGroup.invRev w₁.toWord) w₂.toWord
      have hcf : commonPrefixLen (FreeGroup.invRev w₁.toWord) w₂.toWord = w₁.toWord.length := by
        rw [← reverse_map_letterInv]
        exact halign
      exact hc.1 (by
        rw [FreeGroup.invRev_length]
        exact hcf)
    have hiw : (w₁⁻¹).toWord = FreeGroup.invRev w₁.toWord := by simp [FreeGroup.toWord_inv]
    rw [hiw]
    exact hpfx
  · have halign : align w₁.toWord w₂.toWord = w₂.toWord.length := by
      by_contra hne
      have hlt : align w₁.toWord w₂.toWord < w₂.toWord.length := by
        exact lt_of_le_of_ne (align_le_length_right w₁.toWord w₂.toWord) hne
      omega
    right
    rw [absorbedLeft_iff_suffix]
    have hw2p : w₂.toWord <+: FreeGroup.invRev w₁.toWord := by
      have hcf : commonPrefixLen (FreeGroup.invRev w₁.toWord) w₂.toWord = w₂.toWord.length := by
        rw [← reverse_map_letterInv]
        exact halign
      exact (commonPrefixLen_eq_length_right_iff_prefix
        (FreeGroup.invRev w₁.toWord) w₂.toWord).1 hcf
    have hsuf : FreeGroup.invRev w₂.toWord <:+ w₁.toWord := by
      exact (prefix_invRev_iff_suffix_invRev w₂.toWord w₁.toWord).1 hw2p
    have hiw : (w₂⁻¹).toWord = FreeGroup.invRev w₂.toWord := by simp [FreeGroup.toWord_inv]
    rw [hiw]
    exact hsuf


/-! ## Factor absorption for three factors: the Case II (two-neighbour) step

**Statement (`factor_absorption_three`, PROVEN — see
`Submission/Work/FactorAbsorption.lean`):** for elements `w₁, w₂, w₃` of the
free group with `norm (w₁ * w₂ * w₃) ≤ 1`, at least one factor is fully
absorbed by its ≤ 2 neighbours: either a single-neighbour absorption
(`AbsorbedRight`/`AbsorbedLeft`, Fall I) or the middle factor is absorbed by
both neighbours (Case II, `MiddleAbsorbed`).  The proof (in the module
`Submission.Nielsen` of `FactorAbsorption.lean`) is the assembly of the
alignment disjunction below; machine-validated exhaustively (2921 instances,
0 failures) and on random triples (single-neighbour *alone* fails — e.g.
`(a0⁻¹a1⁻¹, a1a0⁻¹, a0a0)`, where `w₂` is absorbed by both neighbours).

**The Case II side condition in alignment terms — PROVEN below.**  Whether the
left junction can absorb the first `r` letters of the middle is exactly an
`align` statement:

    junction_cancel_iff : r ≤ align X Y ⟺ X.drop (|X|−r) = invRev (Y.take r)

(i.e. the last `r` letters of `X` are the letter-inverses, reversed, of the
first `r` letters of `Y` — the tail of the left neighbour matches the head of
the middle).  Building on it, `two_neighbour_middle` proves: if the left
junction absorbs the first `r` letters of `w₂` (`r ≤ align w₁ w₂`) and the
right junction absorbs the rest (`|w₂|−r ≤ align w₂ w₃`), then the middle is
fully absorbed by its two neighbours (`MiddleAbsorbed w₁ w₂ w₃`: `w₂`'s word
splits `A₁ ++ A₂` with `w₁`'s tail `= x ++ invRev A₁` and `w₃`'s head
`= invRev A₂ ++ z`).  These are the precise alignment facts the `k = 3`
folding argument consumes. -/

lemma take_ne_nil_of_pos_of_ne_nil {α : Type*} (Y : List α) (r : ℕ) (hr : 0 < r)
    (hY : Y ≠ []) : Y.take r ≠ [] := by
  rcases Y with _ | ⟨y, Ys⟩
  · exact (hY rfl).elim
  · cases r with
    | zero => omega
    | succ r' => simp

lemma commonPrefixLen_ge_iff_take {α : Type*} [DecidableEq α] (X Y : List α) (r : ℕ)
    (hr : r ≤ Y.length) :
    r ≤ commonPrefixLen X Y ↔ X.take r = Y.take r := by
  induction X generalizing Y r with
  | nil =>
      constructor
      · intro h
        have : r = 0 := by
          simp [commonPrefixLen] at h
          omega
        simp [this]
      · intro h
        have hr0 : r = 0 := by
          by_contra hne
          have hrpos : 0 < r := by omega
          have hY : Y ≠ [] := by
            intro hE
            subst hE
            simp at hr
            omega
          have hnon := take_ne_nil_of_pos_of_ne_nil Y r hrpos hY
          have ht : Y.take r = [] := by
            simpa using h.symm
          exact hnon ht
        simp [commonPrefixLen, hr0]
  | cons a X' ih =>
      cases Y with
      | nil =>
          constructor
          · intro h
            have hr0 : r = 0 := by simpa using hr
            simp [commonPrefixLen]
            omega
          · intro h
            have hr0 : r = 0 := by simpa using hr
            simp [commonPrefixLen]
            omega
      | cons b Y' =>
          cases r with
          | zero => simp
          | succ r' =>
              by_cases hab : a = b
              · have hr' : r' ≤ Y'.length := by
                  change r' + 1 ≤ Y'.length + 1 at hr
                  omega
                constructor
                · intro h
                  rw [commonPrefixLen_cons, if_pos hab] at h
                  have h' : r' ≤ commonPrefixLen X' Y' := by omega
                  have hrec := (ih Y' r' hr').1 h'
                  simp [hab, hrec]
                · intro h
                  rw [commonPrefixLen_cons, if_pos hab]
                  have hrec : X'.take r' = Y'.take r' := by
                    have ht := congrArg List.tail h
                    simpa [hab] using ht
                  have hgt := (ih Y' r' hr').2 hrec
                  omega
              · constructor
                · intro h
                  rw [commonPrefixLen_cons, if_neg hab] at h
                  exfalso
                  omega
                · intro h
                  exfalso
                  have hhead := congrArg List.head? h
                  simp [hab] at hhead

lemma take_invRev_suffix {α : Type*} (X : List (α × Bool)) (r : ℕ) (hr : r ≤ X.length) :
    (FreeGroup.invRev X).take r = FreeGroup.invRev (X.drop (X.length - r)) := by
  have hAB : X = X.take (X.length - r) ++ X.drop (X.length - r) := by
    rw [List.take_append_drop]
  nth_rw 1 [hAB]
  rw [FreeGroup.invRev_append]
  have hlen : (FreeGroup.invRev (X.drop (X.length - r))).length = r := by
    rw [FreeGroup.invRev_length, List.length_drop]
    omega
  have hle : r ≤ (FreeGroup.invRev (X.drop (X.length - r))).length := by
    rw [hlen]
  rw [List.take_append_of_le_length hle]
  exact List.take_of_length_le (by simpa [hlen])

/-- The Case-II side condition in alignment terms: at least `r` letters cancel
at the junction of `X` and `Y` iff the last `r` letters of `X` are the
letter-inverses (reversed) of the first `r` letters of `Y`. -/
lemma junction_cancel_iff {α : Type*} [DecidableEq α] (X Y : List (α × Bool)) (r : ℕ)
    (hX : r ≤ X.length) (hY : r ≤ Y.length) :
    r ≤ align X Y ↔ X.drop (X.length - r) = FreeGroup.invRev (Y.take r) := by
  unfold align
  rw [reverse_map_letterInv X]
  rw [commonPrefixLen_ge_iff_take (FreeGroup.invRev X) Y r (by
    simpa [FreeGroup.invRev] using hY)]
  constructor
  · intro h
    have ht := congrArg FreeGroup.invRev h
    rw [take_invRev_suffix X r hX] at ht
    simpa [FreeGroup.invRev_invRev] using ht
  · intro h
    have ht := congrArg FreeGroup.invRev h
    simp only [FreeGroup.invRev_invRev] at ht
    rw [take_invRev_suffix X r hX]
    exact ht

/-- The middle factor `w₂` is fully absorbed by its two neighbours `w₁`, `w₃`
(Case II): its word splits `A₁ ++ A₂` with `w₁`'s tail absorbing `A₁` and
`w₃`'s head absorbing `A₂`. -/
def MiddleAbsorbed {n : ℕ} (w₁ w₂ w₃ : FreeGroup (Fin n)) : Prop :=
  ∃ A₁ A₂ : List (Fin n × Bool),
    w₂.toWord = A₁ ++ A₂ ∧
      (∃ x : List (Fin n × Bool), w₁.toWord = x ++ FreeGroup.invRev A₁) ∧
      (∃ z : List (Fin n × Bool), w₃.toWord = FreeGroup.invRev A₂ ++ z)

/-- Case II in alignment terms: if the left junction absorbs the first `r`
letters of the middle and the right junction absorbs the rest (`|w₂| − r`),
then the middle factor is fully absorbed by its two neighbours. -/
lemma two_neighbour_middle {n : ℕ} (w₁ w₂ w₃ : FreeGroup (Fin n)) (r : ℕ)
    (hr : r ≤ w₂.toWord.length)
    (hl : r ≤ align w₁.toWord w₂.toWord)
    (hrr : w₂.toWord.length - r ≤ align w₂.toWord w₃.toWord) :
    MiddleAbsorbed w₁ w₂ w₃ := by
  refine ⟨w₂.toWord.take r, w₂.toWord.drop r, ?_, ?_, ?_⟩
  · rw [List.take_append_drop]
  · have hleft : r ≤ w₁.toWord.length :=
      le_trans hl (align_le_length_left w₁.toWord w₂.toWord)
    have hc := (junction_cancel_iff w₁.toWord w₂.toWord r hleft hr).1 hl
    refine ⟨w₁.toWord.take (w₁.toWord.length - r), ?_⟩
    rw [hc.symm]
    rw [List.take_append_drop]
  · have hA2 : w₂.toWord.length - r ≤ w₃.toWord.length :=
      le_trans hrr (align_le_length_right w₂.toWord w₃.toWord)
    have hc := (junction_cancel_iff w₂.toWord w₃.toWord (w₂.toWord.length - r)
      (by omega) hA2).1 hrr
    have hEq : w₂.toWord.length - (w₂.toWord.length - r) = r := by omega
    rw [hEq] at hc
    refine ⟨w₃.toWord.drop (w₂.toWord.length - r), ?_⟩
    have hinv := congrArg FreeGroup.invRev hc
    have hinv' : FreeGroup.invRev (w₂.toWord.drop r) =
        w₃.toWord.take (w₂.toWord.length - r) := by
      simpa [FreeGroup.invRev_invRev] using hinv
    have ht : w₃.toWord.take (w₂.toWord.length - r) = FreeGroup.invRev (w₂.toWord.drop r) := by
      exact hinv'.symm
    nth_rw 1 [← List.take_append_drop (w₂.toWord.length - r) w₃.toWord]
    rw [ht]



/-! ## The folding argument for three factors: foundations and the alignment
disjunction to prove

**Reduction is associative** (PROVEN below): `reduce (A ++ B ++ C) =
reduce (reduce (A ++ B) ++ C)` and the right variant — so the reduction of a
triple can be computed junction by junction.  With the quantitative
two-word identity this yields **`triple_reduce_length`** (PROVEN): for reduced
`L₁, L₂, L₃`,

    |reduce (L₁ ++ L₂ ++ L₃)| = |L₁|+|L₂|+|L₃| − 2·align L₁ L₂
                               − 2·align (reduce (L₁ ++ L₂)) L₃

**The disjunction** (`triple_align_disjunction`, PROVEN below; machine-validated:
exhaustive over all triples with `|wᵢ| ≤ 3` over two generators — 2052 valid
instances, 0 failures — and on random triples with product of length ≤ 1):
for reduced `L₁ L₂ L₃` with reduced product of length ≤ 1,

    align L₁ L₂ = |L₁|  ∨  align L₁ L₂ = |L₂|  ∨
    align L₂ L₃ = |L₂|  ∨  align L₂ L₃ = |L₃|  ∨
    align L₁ L₂ + align L₂ L₃ ≥ |L₂|

Each disjunct is one of the absorptions of `factor_absorption_three`:
`align L₁ L₂ = |L₁|` ⟺ `w₁` is fully absorbed into the head of `w₂`
(`AbsorbedRight w₁ w₂`); `align L₁ L₂ = |L₂|` ⟺ `w₂` into the tail of `w₁`
(`AbsorbedLeft w₂ w₁`); symmetrically for the right junction; and
`align L₁ L₂ + align L₂ L₃ ≥ |L₂|` is the Case-II middle absorption
(`MiddleAbsorbed w₁ w₂ w₃`, via `two_neighbour_middle` with
`r := align L₁ L₂`, using `r ≤ |L₂|`).  This is precisely "what the total
reduced length ≤ 1 condition does to the two junction alignments"; the
folding case analysis (no-crossing, via `two_word_reduction_shape` and
`reduce_assoc_right`) deriving it is below.  With the assembly lemmas of
`Submission/Work/FactorAbsorption.lean` (`absorbedRight_of_align_eq_left`,
`absorbedLeft_of_align_eq_right`, `middleAbsorbed_of_align_ge`,
`reduce_triple_eq_toWord_mul`) it yields `factor_absorption_three`, the
`k = 3` case of the aggregate core.  The general-`k` aggregate (Nielsen's
"es muß ... mindestens eins geben, das von seinen beiden Nachbarelementen
ganz absorbiert wird", Math. Ann. 79 (1919) 270) is machine-validated for
`k ≤ 8` but open in Lean. -/

lemma reduce_assoc {α : Type*} [DecidableEq α] (A B C : List (α × Bool)) :
    FreeGroup.reduce (A ++ B ++ C) = FreeGroup.reduce (FreeGroup.reduce (A ++ B) ++ C) := by
  apply FreeGroup.reduce.sound
  calc
    FreeGroup.mk (A ++ B ++ C) = FreeGroup.mk ((A ++ B) ++ C) := rfl
    _ = FreeGroup.mk (A ++ B) * FreeGroup.mk C := by rw [FreeGroup.mul_mk]
    _ = FreeGroup.mk (FreeGroup.reduce (A ++ B)) * FreeGroup.mk C := by
        rw [← FreeGroup.reduce.self (L := A ++ B)]
    _ = FreeGroup.mk (FreeGroup.reduce (A ++ B) ++ C) := by rw [FreeGroup.mul_mk]

/-- Reduction is associative (right variant): reducing the last two factors
first gives the same word as reducing all three. -/
lemma reduce_assoc_right {α : Type*} [DecidableEq α] (A B C : List (α × Bool)) :
    FreeGroup.reduce (A ++ B ++ C) = FreeGroup.reduce (A ++ FreeGroup.reduce (B ++ C)) := by
  apply FreeGroup.reduce.sound
  calc
    FreeGroup.mk (A ++ B ++ C) = FreeGroup.mk (A ++ (B ++ C)) := by rw [List.append_assoc]
    _ = FreeGroup.mk A * FreeGroup.mk (B ++ C) := by rw [FreeGroup.mul_mk]
    _ = FreeGroup.mk A * FreeGroup.mk (FreeGroup.reduce (B ++ C)) := by
        rw [← FreeGroup.reduce.self (L := B ++ C)]
    _ = FreeGroup.mk (A ++ FreeGroup.reduce (B ++ C)) := by rw [FreeGroup.mul_mk]

/-- The reduced length of a three-factor concatenation splits over the two
junctions: `|P| = |L₁|+|L₂|+|L₃| − 2·align L₁ L₂ − 2·align (reduce (L₁++L₂)) L₃`. -/
lemma triple_reduce_length {α : Type*} [DecidableEq α] (L₁ L₂ L₃ : List (α × Bool))
    (hL1 : FreeGroup.IsReduced L₁) (hL2 : FreeGroup.IsReduced L₂)
    (hL3 : FreeGroup.IsReduced L₃) :
    (FreeGroup.reduce (L₁ ++ L₂ ++ L₃)).length =
      L₁.length + L₂.length + L₃.length
        - 2 * align L₁ L₂
        - 2 * align (FreeGroup.reduce (L₁ ++ L₂)) L₃ := by
  have hRred : FreeGroup.IsReduced (FreeGroup.reduce (L₁ ++ L₂)) :=
    FreeGroup.isReduced_iff_reduce_eq.mpr FreeGroup.reduce.idem
  have hlenR := reduce_append_align L₁ L₂ hL1 hL2
  -- hlenR : (reduce (L₁ ++ L₂)).length = L₁.length + L₂.length - 2 * align L₁ L₂
  have hlenP := reduce_append_align (FreeGroup.reduce (L₁ ++ L₂)) L₃ hRred hL3
  -- hlenP : (reduce (reduce (L₁++L₂) ++ L₃)).length = |R| + |L₃| − 2·align R L₃
  have hleR : 2 * align L₁ L₂ ≤ L₁.length + L₂.length := by
    have h1 := align_le_length_left L₁ L₂
    have h2 := align_le_length_right L₁ L₂
    omega
  have hleP : 2 * align (FreeGroup.reduce (L₁ ++ L₂)) L₃
      ≤ (FreeGroup.reduce (L₁ ++ L₂)).length + L₃.length := by
    have h1 := align_le_length_left (FreeGroup.reduce (L₁ ++ L₂)) L₃
    have h2 := align_le_length_right (FreeGroup.reduce (L₁ ++ L₂)) L₃
    omega
  rw [reduce_assoc L₁ L₂ L₃]
  omega


/-! ## The two-word reduction shape (PROVEN)

For reduced `L M`, reducing `L ++ M` removes exactly the `align L M` seam
letters and nothing crosses over: the survivors of `L` are its prefix of
length `|L| − align L M` and the survivors of `M` its suffix starting at
`align L M`:

    two_word_reduction_shape :
      reduce (L ++ M) = L.take (|L| − align L M) ++ M.drop (align L M)

Proof: write `L ++ M = A ++ mid ++ C` with `A := L.take(|L|−x)`,
`mid := L.drop(|L|−x) ++ M.take x`, `C := M.drop x`; the junction identity
`junction_cancel_iff` gives `mid = invRev (M.take x) ++ M.take x`, whose
reduction is empty, so the group elements of `L ++ M` and `A ++ C` coincide
(`reduce.sound`); then `A` and `C` are reduced (prefix/suffix of reduced
words) and `align A C = 0` (lengths agree with the two-word quantitative
identity), so `reduce (A ++ C) = A ++ C` by `reduce_append_no_junction`.
This is the survival-prefix/suffix fact the folding argument needs:
consecutive two-way reductions never re-couple words that have been separated,
and the surviving letters of the first word are exactly its leading
`|L| − x` letters. -/

lemma isReduced_take {α : Type*} (L : List (α × Bool)) (k : ℕ)
    (hL : FreeGroup.IsReduced L) : FreeGroup.IsReduced (L.take k) := by
  simpa [FreeGroup.IsReduced] using List.IsChain.take hL k

lemma isReduced_drop {α : Type*} (L : List (α × Bool)) (k : ℕ)
    (hL : FreeGroup.IsReduced L) : FreeGroup.IsReduced (L.drop k) := by
  simpa [FreeGroup.IsReduced] using List.IsChain.drop hL k

lemma two_word_reduction_shape {α : Type*} [DecidableEq α] (L M : List (α × Bool))
    (hL : FreeGroup.IsReduced L) (hM : FreeGroup.IsReduced M) :
    FreeGroup.reduce (L ++ M) = L.take (L.length - align L M) ++ M.drop (align L M) := by
  let x : ℕ := align L M
  let A : List (α × Bool) := L.take (L.length - x)
  let C : List (α × Bool) := M.drop x
  have hxL : x ≤ L.length := by simpa [x] using align_le_length_left L M
  have hxM : x ≤ M.length := by simpa [x] using align_le_length_right L M
  have hdecL : L = A ++ L.drop (L.length - x) := by
    simp [A, List.take_append_drop]
  have hdecM : M = M.take x ++ C := by
    simp [C, List.take_append_drop]
  have hmid : L.drop (L.length - x) = FreeGroup.invRev (M.take x) := by
    have hj := (junction_cancel_iff L M x hxL hxM).1 (by simp [x])
    simpa [x] using hj
  have hmkid : FreeGroup.mk (L.drop (L.length - x) ++ M.take x) = 1 := by
    have hred : FreeGroup.reduce (L.drop (L.length - x) ++ M.take x) = [] := by
      rw [hmid]
      simp [FreeGroup.reduce_invRev_left_cancel]
    have hself := FreeGroup.reduce.self (L := L.drop (L.length - x) ++ M.take x)
    rw [← hself, hred]
    rfl
  have hLm : FreeGroup.mk A * FreeGroup.mk (L.drop (L.length - x)) = FreeGroup.mk L := by
    rw [FreeGroup.mul_mk]
    rw [← hdecL]
  have hMm : FreeGroup.mk (M.take x) * FreeGroup.mk C = FreeGroup.mk M := by
    rw [FreeGroup.mul_mk]
    rw [← hdecM]
  have hbc : FreeGroup.mk (L.drop (L.length - x)) * FreeGroup.mk (M.take x) = 1 := by
    rw [FreeGroup.mul_mk]
    exact hmkid
  have hmk : FreeGroup.mk (L ++ M) = FreeGroup.mk (A ++ C) := by
    calc
      FreeGroup.mk (L ++ M) = FreeGroup.mk L * FreeGroup.mk M := by rw [FreeGroup.mul_mk]
      _ = (FreeGroup.mk A * FreeGroup.mk (L.drop (L.length - x))) *
          (FreeGroup.mk (M.take x) * FreeGroup.mk C) := by rw [← hLm, ← hMm]
      _ = FreeGroup.mk A *
          (FreeGroup.mk (L.drop (L.length - x)) * FreeGroup.mk (M.take x) * FreeGroup.mk C) := by
              rw [mul_assoc (FreeGroup.mk A) (FreeGroup.mk (L.drop (L.length - x)))
                (FreeGroup.mk (M.take x) * FreeGroup.mk C)]
              rw [← mul_assoc (FreeGroup.mk (L.drop (L.length - x))) (FreeGroup.mk (M.take x))
                (FreeGroup.mk C)]
      _ = FreeGroup.mk A * FreeGroup.mk C := by
              rw [hbc]
              simp
      _ = FreeGroup.mk (A ++ C) := by rw [FreeGroup.mul_mk]
  have hred := FreeGroup.reduce.sound hmk
  have hlenLM := reduce_append_align L M hL hM
  have hAred : FreeGroup.IsReduced A := by
    simpa [A] using isReduced_take L (L.length - x) hL
  have hCred : FreeGroup.IsReduced C := by
    simpa [C] using isReduced_drop M x hM
  have hA : A.length = L.length - x := by simp [A]
  have hC : C.length = M.length - x := by
    simp [C]
  have hlenAC : (FreeGroup.reduce (A ++ C)).length = A.length + C.length := by
    rw [← hred]
    rw [hlenLM]
    have hle : 2 * x ≤ L.length + M.length := by
      have h1 := align_le_length_left L M
      have h2 := align_le_length_right L M
      omega
    omega
  have halignAC := reduce_append_align A C hAred hCred
  have hleAC : 2 * align A C ≤ A.length + C.length := by
    have h1 := align_le_length_left A C
    have h2 := align_le_length_right A C
    omega
  have halign0 : align A C = 0 := by
    omega
  have hjoin : FreeGroup.reduce (A ++ C) = A ++ C := by
    refine reduce_append_no_junction A C hAred hCred ?_
    exact no_cancel_of_align_eq_zero A C halign0
  rw [hred, hjoin]


lemma cpl_append_eq_of_left_lt {α : Type*} [DecidableEq α] (X M N : List α)
    (h : commonPrefixLen X M < M.length) :
    commonPrefixLen X (M ++ N) = commonPrefixLen X M := by
  induction X generalizing M N with
  | nil => rfl
  | cons x X' ih =>
      cases M with
      | nil => simp at h
      | cons m M' =>
          rw [show (m :: M') ++ N = m :: (M' ++ N) by rfl]
          rw [commonPrefixLen_cons] at h
          by_cases hx : x = m
          · have h' : commonPrefixLen X' M' < M'.length := by
              simp [hx] at h
              omega
            have hrec := ih M' N h'
            simp [commonPrefixLen_cons, hx, hrec]
          · simp [commonPrefixLen_cons, hx]

lemma cpl_append_eq_of_total_lt {α : Type*} [DecidableEq α] (X M N : List α)
    (h : commonPrefixLen X (M ++ N) < M.length) :
    commonPrefixLen X (M ++ N) = commonPrefixLen X M := by
  induction X generalizing M N with
  | nil => rfl
  | cons x X' ih =>
      cases M with
      | nil => simp at h
      | cons m M' =>
          rw [show (m :: M') ++ N = m :: (M' ++ N) by rfl] at h ⊢
          rw [commonPrefixLen_cons] at h
          by_cases hx : x = m
          · have h' : commonPrefixLen X' (M' ++ N) < M'.length := by
              simp [hx] at h
              omega
            have hrec := ih M' N h'
            simp [commonPrefixLen_cons, hx, hrec]
          · simp [commonPrefixLen_cons, hx]

lemma align_eq_cpl_invRev {α : Type*} [DecidableEq α] (L M : List (α × Bool)) :
    align L M = commonPrefixLen (FreeGroup.invRev L) M := by
  unfold align
  rw [reverse_map_letterInv L]

theorem triple_align_disjunction {α : Type*} [DecidableEq α] (L₁ L₂ L₃ : List (α × Bool))
    (hL1 : FreeGroup.IsReduced L₁) (hL2 : FreeGroup.IsReduced L₂)
    (hL3 : FreeGroup.IsReduced L₃)
    (hshort : (FreeGroup.reduce (L₁ ++ L₂ ++ L₃)).length ≤ 1) :
    align L₁ L₂ = L₁.length ∨ align L₁ L₂ = L₂.length ∨
      align L₂ L₃ = L₂.length ∨ align L₂ L₃ = L₃.length ∨
      align L₁ L₂ + align L₂ L₃ ≥ L₂.length := by
  let x : ℕ := align L₁ L₂
  let z : ℕ := align L₂ L₃
  by_cases hC2 : x + z ≥ L₂.length
  · right; right; right; right
    rwa [show x = align L₁ L₂ by rfl, show z = align L₂ L₃ by rfl] at hC2
  · left
    have hx : x = align L₁ L₂ := rfl
    have hz : z = align L₂ L₃ := rfl
    have hxz : x + z < L₂.length := by omega
    have hxA : x ≤ L₁.length := by rw [hx]; exact align_le_length_left L₁ L₂
    have hxB : x ≤ L₂.length := by rw [hx]; exact align_le_length_right L₁ L₂
    have hzB : z ≤ L₂.length := by rw [hz]; exact align_le_length_left L₂ L₃
    have hzC : z ≤ L₃.length := by rw [hz]; exact align_le_length_right L₂ L₃
    have hxge : L₁.length ≤ x := by
      by_contra hlt
      let S₂₃ : List (α × Bool) := FreeGroup.reduce (L₂ ++ L₃)
      have hSred : FreeGroup.IsReduced S₂₃ := by
        unfold S₂₃
        exact FreeGroup.isReduced_iff_reduce_eq.mpr FreeGroup.reduce.idem
      let M : List (α × Bool) := L₂.take (L₂.length - z)
      have hSshape : S₂₃ = M ++ L₃.drop z := by
        have hsh := two_word_reduction_shape L₂ L₃ hL2 hL3
        rw [← hz] at hsh
        simpa [S₂₃, M] using hsh
      have hMlen : M.length = L₂.length - z := by simp [M]
      have hM_lt : x < M.length := by
        rw [hMlen]
        omega
      have hcplM : commonPrefixLen (FreeGroup.invRev L₁) M = x := by
        have hdec : L₂ = M ++ L₂.drop (L₂.length - z) := by
          simp [M, List.take_append_drop]
        have hcpl : commonPrefixLen (FreeGroup.invRev L₁) L₂ = x := by
          rw [← align_eq_cpl_invRev, ← hx]
        have hconf := cpl_append_eq_of_total_lt (FreeGroup.invRev L₁) M
          (L₂.drop (L₂.length - z)) (by
            rw [← hdec]
            rw [hcpl]
            exact hM_lt)
        rw [← hdec] at hconf
        rw [hcpl] at hconf
        exact hconf.symm
      have hcplS : commonPrefixLen (FreeGroup.invRev L₁) S₂₃ = x := by
        have hconf := cpl_append_eq_of_left_lt (FreeGroup.invRev L₁) M (L₃.drop z) (by
          rw [hcplM]
          exact hM_lt)
        rw [← hSshape] at hconf
        rw [hcplM] at hconf
        exact hconf
      have hw : align L₁ S₂₃ = x := by
        rw [align_eq_cpl_invRev]
        exact hcplS
      have hP : FreeGroup.reduce (L₁ ++ L₂ ++ L₃) = FreeGroup.reduce (L₁ ++ S₂₃) := by
        unfold S₂₃
        rw [reduce_assoc_right L₁ L₂ L₃]
      have hshape := two_word_reduction_shape L₁ S₂₃ hL1 hSred
      have hshape' : FreeGroup.reduce (L₁ ++ S₂₃) = L₁.take (L₁.length - x) ++ S₂₃.drop x := by
        rw [hw] at hshape
        exact hshape
      have hL1part : 1 ≤ L₁.length - x := by omega
      have hSlen : S₂₃.length = L₂.length + L₃.length - 2 * z := by
        have hlen := reduce_append_align L₂ L₃ hL2 hL3
        rw [← hz] at hlen
        unfold S₂₃
        exact hlen
      have hSpart : 1 ≤ S₂₃.length - x := by
        have hle : 2 * z ≤ L₂.length + L₃.length := by
          have h1 := align_le_length_left L₂ L₃
          have h2 := align_le_length_right L₂ L₃
          rw [hz]
          omega
        rw [hSlen]
        omega
      have hlenP : (FreeGroup.reduce (L₁ ++ S₂₃)).length = (L₁.length - x) + (S₂₃.length - x) := by
        rw [hshape']
        rw [List.length_append]
        rw [List.length_drop]
        have ht : (L₁.take (L₁.length - x)).length = L₁.length - x := by
          rw [List.length_take]
          rw [min_eq_left]
          omega
        rw [ht]
      have hgt : 2 ≤ (FreeGroup.reduce (L₁ ++ S₂₃)).length := by
        rw [hlenP]
        omega
      have hle1 : (FreeGroup.reduce (L₁ ++ S₂₃)).length ≤ 1 := by
        rw [← hP]
        exact hshort
      omega
    rw [← hx]
    exact le_antisymm hxA hxge

end

end Submission.Nielsen
