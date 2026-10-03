import Mathlib
import Submission.Work.OROneRel.levelChain
import Submission.Work.OROneRel.decor_tlU_tlW_at
import Submission.Work.OROneRel.letters_closure_iff

/-!
# The `2`-cell relators supported in the level window `[0,b]` lie in the window subgroup

`WrelUp p q l b` (`Submission.Work.OROneRel.levelChain`) is the set of `2`-cell relators of the
level chain that are supported in the level window `[0,b]`: the classes

`FreeGroup.mk (decor (tlW p q) m (wordOf (tlU p q ^ l)))`,  `0 ≤ m`,  `m + p q ≤ b`.

The decorated walk of `tlU p q = a^p b^q` at level `m` climbs from `m` to `m + p q` (the `p`
copies of the first generator, each of weight `q`) and comes back down to `m` (the `q` copies of
the second generator, each of weight `-p`), so *all* of its edges lie in the window `[m, m+p q]`,
which is contained in `[0,b]` by the two hypotheses.  Hence each relator is a product of generators
`FreeGroup.of e` with `e ∈ Wedge p q 0 b`, i.e. an element of
`Subgroup.closure (FreeGroup.of '' Wedge p q 0 b)`.

Three ingredients are used:

* `decor_tlU_tlW_at` (proved elsewhere) computes the one-copy decorated walk explicitly;
* the total weight of `tlU p q` vanishes, so the decorated walk of `tlU p q ^ l` is the `l`-th power
  of the decorated walk of `tlU p q` (`wrelUp_mk_decor_pow`, from `wordOf_pow_flatten` and the
  additivity of `decor` under repeated blocks);
* `mk_mem_closure` (`letters_closure_iff`) turns a list all of whose letters lie in a generating set
  into an element of the corresponding subgroup.

The only genuinely arithmetic point is the window membership of the two families of edges, which is
`wrelUp_decor_tlU_letters_mem` below.
-/

namespace Work.OROneRel

universe u

/-- `FreeGroup.mk` of an `n`-fold concatenation of a word `W` is the `n`-th power of
`FreeGroup.mk W`. -/
theorem wrelUp_mk_flatten_replicate {β : Type*} (n : ℕ) (W : List (β × Bool)) :
    FreeGroup.mk (List.replicate n W).flatten = (FreeGroup.mk W) ^ n := by
  induction n with
  | zero => rw [List.replicate_zero, List.flatten_nil, pow_zero, FreeGroup.one_eq_mk]
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, ← FreeGroup.mul_mk, ih, pow_succ']

/-- **The decoration of a repeated block, at level `i`.**  If the block `L` has vanishing total
weight `lsig c L = 0`, then the running level returns to `i` after every copy, so the decoration of
`n` copies of `L` is the concatenation of `n` copies of the decoration of `L` read at level `i`. -/
theorem wrelUp_decor_flatten_replicate_at {α : Type u} (c : α → ℤ) (L : List (α × Bool))
    (hL : lsig c L = 0) (i : ℤ) (n : ℕ) :
    decor c i (List.flatten (List.replicate n L)) =
      List.flatten (List.replicate n (decor c i L)) := by
  induction n with
  | zero => simp [decor]
  | succ n ih =>
    simp only [List.replicate_succ, List.flatten_cons]
    rw [decor_append, hL, add_zero, ih]

/-- The weight `tlW p q` kills the two-letter relator `tlU p q`. -/
theorem wrelUp_lsig_tlW_tlU (p q : ℕ) :
    lsig (tlW p q) (wordOf (tlU p q)) = 0 := by
  rw [wordOf_tlU, decor_lsig_append, lsig_replicate_true, lsig_replicate_true, tlW_zero, tlW_one]
  ring

/-- `tlU p q` is cyclically reduced for every `q`, as soon as `p ≥ 1`.  (The library lemma
`tlU_isCyclicallyReduced` assumes `1 ≤ q`; the remaining case `q = 0`, where `tlU p 0 = a ^ p`, is
handled here.) -/
theorem wrelUp_tlU_isCyclicallyReduced (p q : ℕ) (hp : 1 ≤ p) :
    IsCyclicallyReducedRelator (tlU p q) := by
  rcases Nat.eq_zero_or_pos q with hq0 | hq
  · subst hq0
    show FreeGroup.IsCyclicallyReduced (wordOf (tlU p 0))
    rw [wordOf_tlU]
    simp only [List.replicate_zero, List.append_nil]
    rw [FreeGroup.isCyclicallyReduced_iff]
    refine ⟨List.isChain_replicate_of_rel p (by simp), ?_⟩
    intro x hx y hy _
    rw [Option.mem_def] at hx hy
    rw [List.getLast?_replicate] at hx
    rw [List.head?_replicate] at hy
    split_ifs at hx hy
    all_goals simp_all
  · exact tlU_isCyclicallyReduced p q hp hq

/-- The decorated walk of `u ^ l` started at level `m` is the `l`-th power of the decorated walk
of `u`. -/
theorem wrelUp_mk_decor_pow {α : Type u} [DecidableEq α] (c : α → ℤ) (u : FreeGroup α) (l : ℕ)
    (m : ℤ) (hcyc : IsCyclicallyReducedRelator u) (hu : lsig c (wordOf u) = 0) :
    FreeGroup.mk (decor c m (wordOf (u ^ l))) = (FreeGroup.mk (decor c m (wordOf u))) ^ l := by
  rw [wordOf_pow_flatten u l hcyc, wrelUp_decor_flatten_replicate_at c (wordOf u) hu m l,
    wrelUp_mk_flatten_replicate l (decor c m (wordOf u))]

/-- Every letter of the decorated word of `tlU p q` at level `m` lies in the window `Wedge p q 0 b`,
provided the whole cycle `[m, m + p q]` is contained in `[0, b]`. -/
theorem wrelUp_decor_tlU_letters_mem (p q : ℕ) (hp : 1 ≤ p) {m b : ℤ} (hm0 : 0 ≤ m)
    (hmb : m + (p : ℤ) * (q : ℤ) ≤ b) :
    ∀ (e : Fin 2 × ℤ) (bool : Bool), (e, bool) ∈ decor (tlW p q) m (wordOf (tlU p q)) →
      e ∈ Wedge p q 0 b := by
  intro e bool he
  rw [decor_tlU_tlW_at] at he
  rcases List.mem_append.mp he with h | h
  · rw [List.mem_ofFn] at h
    obtain ⟨j, hj⟩ := h
    simp only [Prod.mk.injEq] at hj
    obtain ⟨hj1, -⟩ := hj
    rw [← hj1]
    rw [mem_Wedge_zero]
    have hj0 : (0 : ℤ) ≤ (j : ℤ) := by exact_mod_cast Nat.zero_le j.val
    have hq0 : (0 : ℤ) ≤ (q : ℤ) := by exact_mod_cast Nat.zero_le q
    have hj1p : (j : ℤ) + 1 ≤ (p : ℤ) := by exact_mod_cast Nat.succ_le_of_lt j.isLt
    have key : ((j : ℤ) + 1) * (q : ℤ) ≤ (p : ℤ) * (q : ℤ) :=
      mul_le_mul_of_nonneg_right hj1p hq0
    exact ⟨by nlinarith [mul_nonneg hj0 hq0], by nlinarith [key]⟩
  · rw [List.mem_ofFn] at h
    obtain ⟨k, hk⟩ := h
    simp only [Prod.mk.injEq] at hk
    obtain ⟨hk1, -⟩ := hk
    rw [← hk1]
    rw [mem_Wedge_one]
    have hk0 : (0 : ℤ) ≤ (k : ℤ) := by exact_mod_cast Nat.zero_le k.val
    have hp0 : (0 : ℤ) ≤ (p : ℤ) := by exact_mod_cast Nat.zero_le p
    have hk1q : (k : ℤ) + 1 ≤ (q : ℤ) := by exact_mod_cast Nat.succ_le_of_lt k.isLt
    have key : ((k : ℤ) + 1) * (p : ℤ) ≤ (q : ℤ) * (p : ℤ) :=
      mul_le_mul_of_nonneg_right hk1q hp0
    have hkpq0 : (0 : ℤ) ≤ (k : ℤ) * (p : ℤ) := mul_nonneg hk0 hp0
    exact ⟨by nlinarith [key], by nlinarith [hkpq0]⟩

/-- The class of the decorated word of `tlU p q` at level `m` is a product of generators of the
window subgroup `closure (of '' Wedge p q 0 b)`. -/
theorem wrelUp_mk_decor_tlU_mem (p q : ℕ) (hp : 1 ≤ p) {m b : ℤ} (hm0 : 0 ≤ m)
    (hmb : m + (p : ℤ) * (q : ℤ) ≤ b) :
    FreeGroup.mk (decor (tlW p q) m (wordOf (tlU p q))) ∈
      Subgroup.closure (FreeGroup.of '' Wedge p q 0 b) :=
  mk_mem_closure (wrelUp_decor_tlU_letters_mem p q hp hm0 hmb)

/-- **The `2`-cell relators supported in the level window `[0,b]` are products of window
generators.** -/
theorem WrelUp_supported (p q l : ℕ) (hp : 1 ≤ p) {b : ℤ} :
    Work.OROneRel.WrelUp p q l b ⊆
      Subgroup.closure (FreeGroup.of '' Work.OROneRel.Wedge p q 0 b) := by
  rintro w ⟨m, hm0, hmb, rfl⟩
  rw [wrelUp_mk_decor_pow (tlW p q) (tlU p q) l m (wrelUp_tlU_isCyclicallyReduced p q hp)
    (wrelUp_lsig_tlW_tlU p q)]
  exact Subgroup.pow_mem _ (wrelUp_mk_decor_tlU_mem p q hp hm0 hmb) l

end Work.OROneRel
