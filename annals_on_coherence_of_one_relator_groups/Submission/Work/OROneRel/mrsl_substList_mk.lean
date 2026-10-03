import Mathlib
import Submission.Work.OROneRel.substDefs
import Submission.Work.OROneRel.HNNStep

/-!
# `substList` computes the Magnus substitution

`substList t x p q L` (`Submission.Work.OROneRel.substDefs`) is the word obtained from `L` by
replacing every letter by its *block* (`blkLetter`), and `subst t x p q`
(`Submission.Work.OROneRel.HNNStep`) is the homomorphism of `F β` sending `t ↦ t ^ p`,
`x ↦ x * t ^ (-q)` and fixing every other generator.

This file proves that the letter-level construction computes the substitution at the level of the
free group:

`FreeGroup.mk (substList t x p q L) = subst t x p q (FreeGroup.mk L)`.

The proof is an induction on `L`.  The induction step uses `FreeGroup.mul_mk` (concatenation of
words is multiplication) together with the single-letter computation `blkLetter_mk`, which is a
case analysis matching the two `if`s defining `blkLetter` and `substFun` (they branch in the same
order, so no hypothesis such as `t ≠ x` is needed).
-/

namespace Work.OROneRel

universe u

variable {β : Type u}

/-! ### Elementary computations with `FreeGroup.mk` -/

/-- `mk` turns a cons into a product. -/
theorem mk_cons_eq (c : β × Bool) (L : List (β × Bool)) :
    FreeGroup.mk (c :: L) = FreeGroup.mk [c] * FreeGroup.mk L := by
  rw [← List.singleton_append, ← FreeGroup.mul_mk]

/-- `mk` of a repeated letter is a power. -/
theorem mk_replicate (c : β × Bool) (k : ℕ) :
    FreeGroup.mk (List.replicate k c) = (FreeGroup.mk [c]) ^ k := by
  induction k with
  | zero => rw [List.replicate_zero, ← FreeGroup.one_eq_mk, pow_zero]
  | succ k ih => rw [List.replicate_succ, mk_cons_eq, ih, pow_succ']

/-- The single negative letter represents the inverse of its generator. -/
theorem mk_singleton_false (a : β) :
    FreeGroup.mk [(a, false)] = (FreeGroup.of a)⁻¹ := by
  show FreeGroup.mk [(a, false)] = (FreeGroup.mk [(a, true)])⁻¹
  rw [FreeGroup.inv_mk]
  rfl

/-- A positive letter represents the first power of its generator. -/
theorem mk_singleton_zpow_true (a : β) :
    FreeGroup.mk [(a, true)] = (FreeGroup.of a) ^ (1 : ℤ) := by
  rw [show FreeGroup.mk [(a, true)] = FreeGroup.of a from rfl, zpow_one]

/-- A negative letter represents the `-1`-st power of its generator. -/
theorem mk_singleton_zpow_false (a : β) :
    FreeGroup.mk [(a, false)] = (FreeGroup.of a) ^ (-1 : ℤ) := by
  rw [mk_singleton_false, ← zpow_neg_one]

/-- `mk` of a run of positive letters is the corresponding natural power. -/
theorem mk_replicate_true (a : β) (k : ℕ) :
    FreeGroup.mk (List.replicate k (a, true)) = (FreeGroup.of a) ^ k := by
  rw [mk_replicate, mk_singleton_zpow_true, zpow_one]

/-- `mk` of a run of negative letters is the corresponding inverse power. -/
theorem mk_replicate_false (a : β) (k : ℕ) :
    FreeGroup.mk (List.replicate k (a, false)) = (FreeGroup.of a) ^ (-(k : ℤ)) := by
  rw [mk_replicate, mk_singleton_zpow_false, ← zpow_natCast, ← zpow_mul, neg_one_mul]

/-- The signed run `a ^ n` represents the `n`-th power of `of a`. -/
theorem mk_runLetters (a : β) (n : ℤ) :
    FreeGroup.mk (runLetters a n) = (FreeGroup.of a) ^ n := by
  rw [runLetters]
  by_cases h : 0 < n
  · have hle : (0 : ℤ) ≤ n := le_of_lt h
    have hna : n.natAbs = n.toNat := by
      have h1 : ((n.natAbs : ℕ) : ℤ) = n := Int.natAbs_of_nonneg hle
      have h2 : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg hle
      omega
    have hto : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg hle
    rw [decide_eq_true h, hna, mk_replicate_true, ← zpow_natCast, hto]
  · have h2 : (0 : ℤ) ≤ -n := by omega
    have hn : (((-n).toNat : ℕ) : ℤ) = -n := Int.toNat_of_nonneg h2
    have hna : n.natAbs = (-n).toNat := by
      have h1 : ((n.natAbs : ℕ) : ℤ) = -n := by
        rw [← Int.natAbs_neg n]
        exact Int.natAbs_of_nonneg h2
      omega
    rw [decide_eq_false h, hna, mk_replicate_false, hn, neg_neg]

/-! ### The image of a single generator under `subst` -/

/-- `subst` sends a generator to its prescribed image. -/
theorem subst_of {t x : β} {p q : ℤ} (a : β) :
    subst t x p q (FreeGroup.of a) = substFun t x p q a :=
  FreeGroup.lift_apply_of

/-- The value of `substFun` at the letter `t`. -/
theorem substFun_self {t x : β} {p q : ℤ} :
    substFun t x p q t = (FreeGroup.of t) ^ p := by
  rw [substFun]
  simp

/-- The value of `substFun` at the letter `x`, when `x ≠ t`. -/
theorem substFun_eq_x {t x : β} {p q : ℤ} (h : x ≠ t) :
    substFun t x p q x = FreeGroup.of x * (FreeGroup.of t) ^ (-q) := by
  rw [substFun]
  simp [h]

/-- The value of `substFun` at a letter different from both `t` and `x`. -/
theorem substFun_ne {t x : β} {p q : ℤ} (a : β) (h : a ≠ t) (h2 : a ≠ x) :
    substFun t x p q a = FreeGroup.of a := by
  rw [substFun]
  simp [h, h2]

/-- `subst` of the word consisting of a single positive letter. -/
theorem subst_mk_singleton_true {t x : β} {p q : ℤ} (a : β) :
    subst t x p q (FreeGroup.mk [(a, true)]) = substFun t x p q a := by
  change subst t x p q (FreeGroup.of a) = substFun t x p q a
  exact FreeGroup.lift_apply_of

/-- `subst` of the word consisting of a single negative letter. -/
theorem subst_mk_singleton_false {t x : β} {p q : ℤ} (a : β) :
    subst t x p q (FreeGroup.mk [(a, false)]) = (substFun t x p q a)⁻¹ := by
  rw [mk_singleton_false, map_inv, subst_of]

/-! ### The blocks, letter by letter -/

/-- The block of the letter `(t, true)`. -/
theorem blkLetter_tt {t x : β} {p q : ℤ} :
    blkLetter t x p q (t, true) = runLetters t p := by
  rw [blkLetter]
  simp

/-- The block of the letter `(t, false)`. -/
theorem blkLetter_tf {t x : β} {p q : ℤ} :
    blkLetter t x p q (t, false) = runLetters t (-p) := by
  rw [blkLetter]
  simp

/-- The block of the letter `(x, true)`, when `x ≠ t`. -/
theorem blkLetter_xt {t x : β} {p q : ℤ} (h : x ≠ t) :
    blkLetter t x p q (x, true) = [(x, true)] ++ runLetters t (-q) := by
  rw [blkLetter]
  simp [h]

/-- The block of the letter `(x, false)`, when `x ≠ t`. -/
theorem blkLetter_xf {t x : β} {p q : ℤ} (h : x ≠ t) :
    blkLetter t x p q (x, false) = runLetters t q ++ [(x, false)] := by
  rw [blkLetter]
  simp [h]

/-- The block of a letter different from both `t` and `x` is the letter itself. -/
theorem blkLetter_other {t x : β} {p q : ℤ} (a : β) (b : Bool) (h : a ≠ t) (h2 : a ≠ x) :
    blkLetter t x p q (a, b) = [(a, b)] := by
  rw [blkLetter]
  simp [h, h2]

/-! ### The single-letter case -/

/-- The block of a single letter represents the image of that letter under `subst`.  This is the
induction step of `mrsl_substList_mk`. -/
theorem blkLetter_mk (t x : β) (p q : ℤ) (c : β × Bool) :
    FreeGroup.mk (blkLetter t x p q c) = subst t x p q (FreeGroup.mk [c]) := by
  obtain ⟨a, b⟩ := c
  cases b with
  | true =>
    rw [subst_mk_singleton_true]
    by_cases h : a = t
    · subst h
      rw [blkLetter_tt, mk_runLetters, substFun_self]
    · by_cases hx : a = x
      · subst hx
        rw [blkLetter_xt h, ← FreeGroup.mul_mk, mk_runLetters,
          show FreeGroup.mk [(a, true)] = FreeGroup.of a from rfl, substFun_eq_x h]
      · rw [blkLetter_other a true h hx, mk_singleton_zpow_true, substFun_ne a h hx, zpow_one]
  | false =>
    rw [subst_mk_singleton_false]
    by_cases h : a = t
    · subst h
      rw [blkLetter_tf, mk_runLetters, substFun_self, zpow_neg]
    · by_cases hx : a = x
      · subst hx
        rw [blkLetter_xf h, ← FreeGroup.mul_mk, mk_runLetters, mk_singleton_false,
          substFun_eq_x h, mul_inv_rev, ← zpow_neg, neg_neg]
      · rw [blkLetter_other a false h hx, mk_singleton_zpow_false, substFun_ne a h hx,
          zpow_neg_one]

/-! ### The main statement -/

/-- `substList` of a cons. -/
theorem substList_cons {t x : β} {p q : ℤ} (c : β × Bool) (L : List (β × Bool)) :
    substList t x p q (c :: L) = blkLetter t x p q c ++ substList t x p q L := by
  rw [substList, List.map_cons, List.flatten_cons, substList]

/-- `substList` of the empty word. -/
theorem substList_nil {t x : β} {p q : ℤ} :
    substList t x p q ([] : List (β × Bool)) = [] := by
  rw [substList]
  rfl

theorem mrsl_substList_mk {β : Type u} (t x : β) (p q : ℤ) (L : List (β × Bool)) :
    FreeGroup.mk (Work.OROneRel.substList t x p q L) =
      Work.OROneRel.subst t x p q (FreeGroup.mk L) := by
  induction L with
  | nil => rw [substList_nil, ← FreeGroup.one_eq_mk, map_one]
  | cons c L ih =>
    rw [substList_cons, ← FreeGroup.mul_mk, ih, mk_cons_eq, map_mul, blkLetter_mk]

end Work.OROneRel
