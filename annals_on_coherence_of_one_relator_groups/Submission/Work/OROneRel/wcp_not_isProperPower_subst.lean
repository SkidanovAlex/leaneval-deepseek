/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The Magnus/Putman substitution preserves non-proper-power-ness

`Work.OROneRel.wcp_not_isProperPower_subst`: for a cyclically reduced relator `T` which is not a
proper power, with `σ_x T ≠ 0` and `x ≠ t`, the Magnus/Putman substitution
`subst t x (σ_x T) (σ_t T)` (i.e. `t ↦ t ^ (σ_x T)`, `x ↦ x * t ^ (-σ_t T)`, all other generators
fixed) sends `T` to a relator which is again not a proper power.

The mathematical content is the word-level statement that the letterwise block substitution
`t ↦ t ^ p` of a `k`-th power of a reduced word can only come from a `k`-th power of the original
word: `exists_replicate_flatten_of_blkT_eq_flatten` below.  It is proved by decomposing the word
into its maximal `t`-runs (`Work.OROneRel.parseT`), noticing that the block substitution multiplies
each run by `|p|`, and undoing the scaling on the runs (`Work.OROneRel.unblk`).

The two ingredients specific to this file are

* `blkT_isCyclicallyReduced` -- the block substitution of a cyclically reduced word is cyclically
  reduced, so the reduced word of `powSubst t p T` is the block substitution of the reduced word of
  `T` and is literally a `k`-th power; and
* the assembly of the group-level statement from the word-level core, using the factorisation
  `subst t x p q = (subst t x 1 q).comp (powSubst t p)` of
  `Submission.Work.OROneRel.isProperPower_subst_iff_powSubst`.

Everything not needed outside this file is `private`.
-/
import Mathlib
import Submission.Work.OROneRel.HNNStep
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.substDefs
import Submission.Work.OROneRel.npsubstDefs
import Submission.Work.OROneRel.powSubst_injective
import Submission.Work.OROneRel.FreiheitssatzDefs
import Submission.Work.OROneRel.psiSubstDefs
import Submission.Work.OROneRel.ne_one_of_not_isProperPower
import Submission.Work.OROneRel.eq_flatten_replicate_of_cyclicallyReduced_of_pow
import Submission.Work.OROneRel.isReduced_rotate_of_isCyclicallyReduced
import Submission.Work.OROneRel.rotate_flatten_replicate
import Submission.Work.OROneRel.isProperPower_subst_iff_powSubst
import Submission.Work.OROneRel.parseT_blkT
import Submission.Work.OROneRel.powSubst_toWord
import Submission.Work.OROneRel.parseT_append_of_startsNonT
import Submission.Work.OROneRel.assembleT_parseT_of_startsNonT
import Submission.Work.OROneRel.isTRun_of_mem_parseT
import Submission.Work.OROneRel.parseT_flatten_replicate_of_startsNonT
import Submission.Work.OROneRel.exists_common_power

namespace Work.OROneRel

universe u

/-! ## The block substitution `t ↦ t ^ p` preserves cyclic reducedness -/

/-- The common first and last letter of the block `blk t p c` (for `p ≠ 0`). -/
private def blkHead {β : Type*} [DecidableEq β] (t : β) (p : ℤ) (c : β × Bool) : β × Bool :=
  if c.1 = t then (t, signShift p c.2) else c

private theorem blk_head {β : Type*} [DecidableEq β] {t : β} {p : ℤ} (hp : p ≠ 0)
    (c : β × Bool) : (blk t p c).head? = some (blkHead t p c) := by
  by_cases h : c.1 = t
  · rw [blk_of_eq h, List.head?_replicate, if_neg (fun h0 => hp (Int.natAbs_eq_zero.mp h0))]
    simp [blkHead, h]
  · rw [blk_of_ne h]
    simp [blkHead, h]

private theorem blk_getLast {β : Type*} [DecidableEq β] {t : β} {p : ℤ} (hp : p ≠ 0)
    (c : β × Bool) : (blk t p c).getLast? = some (blkHead t p c) := by
  by_cases h : c.1 = t
  · rw [blk_of_eq h, List.getLast?_replicate, if_neg (fun h0 => hp (Int.natAbs_eq_zero.mp h0))]
    simp [blkHead, h]
  · rw [blk_of_ne h]
    simp [blkHead, h]

/-- The head (equivalently, the last letter) of a block respects the relations satisfied by
consecutive letters of a reduced word. -/
private theorem blkHead_rel {β : Type*} [DecidableEq β] (t : β) (p : ℤ) (c₁ c₂ : β × Bool)
    (h : c₁.1 = c₂.1 → c₁.2 = c₂.2) :
    (blkHead t p c₁).1 = (blkHead t p c₂).1 →
      (blkHead t p c₁).2 = (blkHead t p c₂).2 := by
  intro hcon
  by_cases h₁ : c₁.1 = t
  · by_cases h₂ : c₂.1 = t
    · have key : c₁.2 = c₂.2 := h (h₁.trans h₂.symm)
      rw [blkHead, if_pos h₁, blkHead, if_pos h₂, key]
    · rw [blkHead, if_pos h₁, blkHead, if_neg h₂] at hcon
      exact absurd hcon.symm h₂
  · by_cases h₂ : c₂.1 = t
    · rw [blkHead, if_neg h₁, blkHead, if_pos h₂] at hcon
      exact absurd hcon h₁
    · rw [blkHead, if_neg h₁, blkHead, if_neg h₂] at hcon ⊢
      exact h hcon

/-- `blk` in the form in which `Work.OROneRel.powSubst_toWord` states the block. -/
private theorem blk_eq_ite {β : Type*} [DecidableEq β] {t : β} {p : ℤ} (hp : p ≠ 0)
    (c : β × Bool) :
    blk t p c =
      (if c.1 = t then List.replicate p.natAbs (t, if 0 < p then c.2 else !c.2) else [c]) := by
  by_cases h : c.1 = t
  · rw [blk_of_eq h, if_pos h]
    have hsign : signShift p c.2 = (if 0 < p then c.2 else !c.2) := by
      rcases lt_or_gt_of_ne (Ne.symm hp) with hlt | hgt
      · rw [signShift_pos hlt, if_pos hlt]
      · rw [signShift_neg hgt, if_neg (by omega)]
    rw [hsign]
  · rw [blk_of_ne h, if_neg h]

private theorem blkT_ne_nil {β : Type*} [DecidableEq β] {t : β} {p : ℤ} (hp : p ≠ 0)
    {L : List (β × Bool)} (hL : L ≠ []) : blkT t p L ≠ [] := by
  intro h0
  exact hL ((blkT_eq_nil_iff (t := t) hp L).mp h0)

private theorem blkT_head? {β : Type*} [DecidableEq β] {t : β} {p : ℤ} (hp : p ≠ 0)
    (L : List (β × Bool)) :
    (blkT t p L).head? = (L.head?).map (blkHead t p) := by
  cases L with
  | nil => simp [blkT]
  | cons c rest =>
    rw [blkT_cons (t := t) p c rest, List.head?_append_of_ne_nil _ (blk_ne_nil hp c), blk_head hp]
    simp

private theorem blkT_getLast? {β : Type*} [DecidableEq β] {t : β} {p : ℤ} (hp : p ≠ 0)
    (L : List (β × Bool)) :
    (blkT t p L).getLast? = (L.getLast?).map (blkHead t p) := by
  induction L with
  | nil => simp [blkT]
  | cons c rest ih =>
    rw [blkT_cons (t := t) p c rest]
    rcases eq_or_ne rest [] with rfl | hne
    · rw [show blkT t p ([] : List (β × Bool)) = [] from rfl, List.append_nil, blk_getLast hp]
      simp
    · obtain ⟨d, rest', rfl⟩ := List.exists_cons_of_ne_nil hne
      rw [List.getLast?_append_of_ne_nil _ (blkT_ne_nil (t := t) hp (L := d :: rest') (by simp)),
        ih]
      simp only [List.getLast?_cons_cons]

/-- The letterwise block substitution of a reduced word is reduced. -/
private theorem blkT_isReduced {β : Type*} [DecidableEq β] {t : β} {p : ℤ} (hp : p ≠ 0)
    {L : List (β × Bool)} (hL : FreeGroup.IsReduced L) : FreeGroup.IsReduced (blkT t p L) := by
  rw [FreeGroup.IsReduced] at hL ⊢
  show List.IsChain (fun a b : β × Bool => a.1 = b.1 → a.2 = b.2)
    ((L.map (blk t p)).flatten)
  have hnil : ([] : List (β × Bool)) ∉ L.map (blk t p) := by
    intro hmem
    obtain ⟨c, -, hc⟩ := List.mem_map.mp hmem
    exact blk_ne_nil hp c hc
  rw [List.isChain_flatten hnil]
  refine ⟨?_, ?_⟩
  · intro l hl
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hl
    by_cases h : c.1 = t
    · rw [blk_of_eq h]
      exact FreeGroup.IsReduced.of_reduce_eq (FreeGroup.reduce_replicate _ _)
    · rw [blk_of_ne h]
      exact FreeGroup.IsReduced.singleton
  · refine List.isChain_map_of_isChain (blk t p) ?_ hL
    intro c₁ c₂ hQ u hu v hv
    rw [blk_getLast hp] at hu
    rw [blk_head hp] at hv
    simp only [Option.mem_some_iff] at hu hv
    subst hu
    subst hv
    exact blkHead_rel t p c₁ c₂ hQ

/-- The letterwise block substitution of a cyclically reduced word is cyclically reduced. -/
private theorem blkT_isCyclicallyReduced {β : Type*} [DecidableEq β] {t : β} {p : ℤ} (hp : p ≠ 0)
    {L : List (β × Bool)} (hcyc : FreeGroup.IsCyclicallyReduced L) :
    FreeGroup.IsCyclicallyReduced (blkT t p L) := by
  refine ⟨blkT_isReduced hp hcyc.1, ?_⟩
  intro a ha b hb hab
  rw [Option.mem_def, blkT_getLast? hp] at ha
  rw [Option.mem_def, blkT_head? hp] at hb
  obtain ⟨c, hc, hca⟩ := Option.map_eq_some_iff.mp ha
  obtain ⟨d, hd, hdb⟩ := Option.map_eq_some_iff.mp hb
  rw [← hca, ← hdb] at hab ⊢
  exact blkHead_rel t p c d (hcyc.2 c hc d hd) hab

/-- **The reduced word of `powSubst t p T` is cyclically reduced** when `T` is.  Together with
`Work.OROneRel.powSubst_toWord` (which identifies that reduced word with the block substitution of
the word of `T`) this is the last ingredient needed for the proper-power statement. -/
private theorem isCyclicallyReduced_powSubst_wcp {β : Type*} [DecidableEq β] (t : β) (p : ℤ)
    (hp : p ≠ 0) {L : List (β × Bool)} (hL : FreeGroup.IsReduced L)
    (hcyc : FreeGroup.IsCyclicallyReduced L) :
    FreeGroup.IsCyclicallyReduced (powSubst t p (FreeGroup.mk L)).toWord := by
  rw [powSubst_toWord t p hp hL]
  have heq : blkT t p L =
      (L.map (fun c : β × Bool =>
        if c.1 = t then List.replicate p.natAbs (t, if 0 < p then c.2 else !c.2) else [c])).flatten := by
    rw [blkT]
    exact congrArg List.flatten (List.map_congr_left fun c _ => blk_eq_ite hp c)
  rw [← heq]
  exact blkT_isCyclicallyReduced hp hcyc

/-! ## Elementary list facts -/

private theorem StartsNonT.append_of_left {β : Type*} [DecidableEq β] {t : β}
    {A B : List (β × Bool)} (hA : StartsNonT t A) (hne : A ≠ []) : StartsNonT t (A ++ B) := by
  intro c rest h
  obtain ⟨a, A', rfl⟩ := List.exists_cons_of_ne_nil hne
  have ha : a.1 ≠ t := hA a A' rfl
  rw [List.cons_append] at h
  injection h with h1 _
  rw [← h1]; exact ha

private theorem assembleT_eq_nil_iff {β : Type*} (P : List ((β × Bool) × List (β × Bool))) :
    assembleT P = [] ↔ P = [] := by
  constructor
  · intro h
    cases P with
    | nil => rfl
    | cons q P' =>
      obtain ⟨c, R⟩ := q
      rw [assembleT_cons] at h
      exact absurd h (by simp)
  · rintro rfl; rfl

private theorem head?_flatten_replicate {σ : Type*} {A : List σ} {k : ℕ} (hk : 1 ≤ k)
    (hA : A ≠ []) : ((List.replicate k A).flatten).head? = A.head? := by
  obtain ⟨a, A', rfl⟩ := List.exists_cons_of_ne_nil hA
  have hk' : k = (k - 1) + 1 := by omega
  conv_lhs => rw [hk']
  rw [List.replicate_succ, List.flatten_cons]
  simp

private theorem parseT_ne_nil_of_startsNonT {β : Type*} [DecidableEq β] {t : β}
    {L : List (β × Bool)} (hL : StartsNonT t L) (hne : L ≠ []) : parseT t L ≠ [] := by
  obtain ⟨c, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  rw [parseT_cons_of_ne (hL c rest rfl)]
  simp

private theorem blkT_length_of_all_fst_eq {β : Type*} [DecidableEq β] {t : β} (p : ℤ)
    {X : List (β × Bool)} (hX : ∀ c ∈ X, c.1 = t) :
    (blkT t p X).length = p.natAbs * X.length := by
  induction X with
  | nil => simp [blkT]
  | cons c rest ih =>
    have hc : c.1 = t := hX c (by simp)
    have hrest : ∀ d ∈ rest, d.1 = t := fun d hd => hX d (by simp [hd])
    rw [blkT_cons, List.length_append, blk_of_eq hc, List.length_replicate, ih hrest,
      List.length_cons]
    ring

/-! ## The word-level core

A `k`-th power of a word, substituted letter by letter by the blocks of `t ↦ t ^ p`, can only come
from a `k`-th power of the original word. -/

/-- **The core, for a word starting with a non-`t` letter.** -/
private theorem exists_replicate_flatten_of_blkT_eq_flatten_of_startsNonT {β : Type*}
    [DecidableEq β] {t : β} {p : ℤ} (hp : p ≠ 0) {L : List (β × Bool)} (hred : FreeGroup.IsReduced L)
    (hstarts : StartsNonT t L) {A : List (β × Bool)} {k : ℕ} (hk : 2 ≤ k) (hA : A ≠ [])
    (h : blkT t p L = (List.replicate k A).flatten) :
    ∃ V : List (β × Bool), V ≠ [] ∧ L = (List.replicate k V).flatten := by
  have hk1 : 1 ≤ k := by omega
  have hWstarts : StartsNonT t (blkT t p L) := startsNonT_blkT hstarts
  -- `A` starts with a non-`t` letter as well
  have hAstarts : StartsNonT t A := by
    intro c rest hc
    have hWhead : (blkT t p L).head? = some c := by
      rw [h, head?_flatten_replicate hk1 hA, hc]
      rfl
    obtain ⟨l, hl⟩ := List.head?_eq_some_iff.mp hWhead
    exact hWstarts c l hl
  -- the two run decompositions of `blkT t p L` agree
  have hpar : (parseT t L).map (fun q => (q.1, blkT t p q.2)) =
      (List.replicate k (parseT t A)).flatten := by
    rw [← parseT_blkT (t := t) p hstarts, h, parseT_flatten_replicate_of_startsNonT hAstarts k]
  -- undo the blocks on the runs
  have h3 : (parseT t L).map (fun q => (q.1, unblk t p (blkT t p q.2))) =
      ((List.replicate k (parseT t A)).flatten).map (fun q => (q.1, unblk t p q.2)) := by
    rw [← hpar, List.map_map]
    rfl
  have h4 : (parseT t L).map (fun q => (q.1, unblk t p (blkT t p q.2))) = parseT t L := by
    refine (List.map_congr_left fun q hq => ?_).trans (List.map_id (parseT t L))
    have hstep : unblk t p (blkT t p q.2) = q.2 :=
      unblk_blkT_of_isTRun (p := p) hp (isTRun_of_mem_parseT hred q hq)
    simp [hstep, Prod.mk.eta]
  have h5 : parseT t L =
      (List.replicate k ((parseT t A).map (fun q => (q.1, unblk t p q.2)))).flatten := by
    rw [← h4, h3, map_flatten_replicate]
  refine ⟨assembleT ((parseT t A).map (fun q => (q.1, unblk t p q.2))), ?_, ?_⟩
  · intro hnil
    have hP : (parseT t A).map (fun q => (q.1, unblk t p q.2)) = [] :=
      (assembleT_eq_nil_iff _).mp hnil
    exact parseT_ne_nil_of_startsNonT hAstarts hA (List.map_eq_nil_iff.mp hP)
  · rw [← assembleT_parseT_of_startsNonT hstarts, h5, assembleT_flatten_replicate]

/-- **The word-level core.**  If the block substitution of a cyclically reduced word is a `k`-th
power (as a word, `k ≥ 2`) of a nonempty word, then the word itself is a `k`-th power.  The all-`t`
case is excluded by the hypothesis that some letter of `L` differs from `t`. -/
private theorem exists_replicate_flatten_of_blkT_eq_flatten {β : Type*} [DecidableEq β] {t : β}
    {p : ℤ} (hp : p ≠ 0) {L : List (β × Bool)} (hcyc : FreeGroup.IsCyclicallyReduced L)
    (hnt : ∃ c ∈ L, c.1 ≠ t) {A : List (β × Bool)} {k : ℕ} (hk : 2 ≤ k) (hA : A ≠ [])
    (h : blkT t p L = (List.replicate k A).flatten) :
    ∃ V : List (β × Bool), V ≠ [] ∧ L = (List.replicate k V).flatten := by
  classical
  -- rotate `L` so that it starts with a non-`t` letter
  set R := L.takeWhile (isT t) with hR
  set M := L.dropWhile (isT t) with hM
  have hsplit : L = R ++ M := by
    rw [hR, hM]
    exact (List.takeWhile_append_dropWhile (p := isT t) (l := L)).symm
  have hnle : R.length ≤ L.length := by
    rw [hR]
    exact (List.takeWhile_prefix (isT t) (l := L)).sublist.length_le
  set L' := L.rotate R.length with hL'def
  have hL'eq : L' = M ++ R := by
    rw [hL'def, List.rotate_eq_drop_append_take hnle, hsplit, List.drop_left, List.take_left]
  have hMne : M ≠ [] := by
    intro hnil
    obtain ⟨c, hc, hct⟩ := hnt
    rw [hM] at hnil
    exact hct (isT_eq_true_iff.mp ((List.dropWhile_eq_nil_iff.mp hnil) c hc))
  have hstarts' : StartsNonT t L' := by
    rw [hL'eq]
    exact StartsNonT.append_of_left (hM ▸ startsNonT_dropWhile t L) hMne
  have hred' : FreeGroup.IsReduced L' :=
    isReduced_rotate_of_isCyclicallyReduced hcyc R.length
  have hlenR : (blkT t p R).length = p.natAbs * R.length := by
    rw [hR]
    exact blkT_length_of_all_fst_eq p (startsNonT_takeWhile_all t L)
  have hrot : (blkT t p L).rotate (p.natAbs * R.length) = blkT t p M ++ blkT t p R := by
    rw [← hlenR, hsplit, blkT_append]
    rw [List.rotate_eq_drop_append_take (by rw [List.length_append]; exact Nat.le_add_right _ _)]
    rw [List.drop_left, List.take_left]
  have h' : blkT t p L' = (List.replicate k (A.rotate (p.natAbs * R.length))).flatten := by
    calc blkT t p L' = blkT t p M ++ blkT t p R := by rw [hL'eq, blkT_append]
      _ = (blkT t p L).rotate (p.natAbs * R.length) := hrot.symm
      _ = ((List.replicate k A).flatten).rotate (p.natAbs * R.length) := by rw [h]
      _ = (List.replicate k (A.rotate (p.natAbs * R.length))).flatten :=
            rotate_flatten_replicate k _ A
  have hA' : A.rotate (p.natAbs * R.length) ≠ [] :=
    fun hnil => hA (List.rotate_eq_nil_iff.mp hnil)
  obtain ⟨V, hVne, hV⟩ :=
    exists_replicate_flatten_of_blkT_eq_flatten_of_startsNonT hp hred' hstarts' hk hA' h'
  refine ⟨V.rotate (L.length - R.length), fun hnil => hVne (List.rotate_eq_nil_iff.mp hnil), ?_⟩
  have hback : L = L'.rotate (L.length - R.length) := by
    rw [hL'def, List.rotate_rotate, Nat.add_sub_cancel' hnle, List.rotate_length]
  conv_lhs => rw [hback]
  rw [hV, rotate_flatten_replicate]

/-! ## The exponent sum sees only the letters of the word -/

/-- If the generator `a` does not occur in the word `L`, then the exponent sum of `a` in `mk L`
vanishes. -/
private theorem sigma_mk_eq_one_of_notMem {β : Type*} [DecidableEq β] (a : β) (L : List (β × Bool))
    (h : ∀ c ∈ L, c.1 ≠ a) : sigma a (FreeGroup.mk L) = 1 := by
  rw [sigma, FreeGroup.lift_mk]
  induction L with
  | nil => simp
  | cons c rest ih =>
    have hc : c.1 ≠ a := h c (by simp)
    have hrest : ∀ d ∈ rest, d.1 ≠ a := fun d hd => h d (by simp [hd])
    rw [List.map_cons, List.prod_cons, ih hrest, mul_one]
    cases c.2 <;> simp [hc]

/-! ## The group-level statement -/

theorem wcp_not_isProperPower_subst {α : Type u} (T : FreeGroup α) {t x : α} (hxt : x ≠ t)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator T)
    (hpp : ¬ Work.OROneRel.IsProperPower T)
    (hp : Multiplicative.toAdd (Work.OROneRel.sigma x T) ≠ 0) :
    ¬ Work.OROneRel.IsProperPower
      (Work.OROneRel.subst t x (Multiplicative.toAdd (Work.OROneRel.sigma x T))
        (Multiplicative.toAdd (Work.OROneRel.sigma t T)) T) := by
  classical
  intro hcon
  -- reduce to the Nielsen substitution `t ↦ t ^ p`, where `t ^ p` is the image of `t`
  have hpw : IsProperPower (powSubst t (Multiplicative.toAdd (sigma x T)) T) :=
    (isProperPower_subst_iff_powSubst T hxt (Multiplicative.toAdd (sigma x T))
      (Multiplicative.toAdd (sigma t T))).mp hcon
  obtain ⟨U, k, hk, hUk⟩ := hpw
  have hT1 : T ≠ 1 := ne_one_of_not_isProperPower hpp
  have hLred : FreeGroup.IsReduced T.toWord := FreeGroup.isReduced_toWord
  have hLcyc : FreeGroup.IsCyclicallyReduced T.toWord := hcyc
  have hredW : FreeGroup.IsReduced (powSubst t (Multiplicative.toAdd (sigma x T)) T).toWord :=
    FreeGroup.isReduced_toWord
  have hWcyc : FreeGroup.IsCyclicallyReduced
      (powSubst t (Multiplicative.toAdd (sigma x T)) T).toWord := by
    simpa [FreeGroup.mk_toWord] using
      isCyclicallyReduced_powSubst_wcp (L := T.toWord) t (Multiplicative.toAdd (sigma x T)) hp
        hLred hLcyc
  -- the reduced word of the substituted relator is a `k`-th power of a word
  obtain ⟨A, hA⟩ := eq_flatten_replicate_of_cyclicallyReduced_of_pow hredW hWcyc hk
    (by rw [FreeGroup.mk_toWord]; exact hUk)
  have hWne : (powSubst t (Multiplicative.toAdd (sigma x T)) T).toWord ≠ [] := by
    intro h0
    refine hT1 (powSubst_injective t (Multiplicative.toAdd (sigma x T)) hp ?_)
    rw [map_one, FreeGroup.toWord_eq_nil_iff.mp h0]
  have hAne : A ≠ [] := by
    intro h0
    exact hWne (by rw [hA, h0]; simp)
  -- hence so is the block substitution of the word of `T`
  have hblk : blkT t (Multiplicative.toAdd (sigma x T)) T.toWord
      = (List.replicate k A).flatten := by
    have hgen : blkT t (Multiplicative.toAdd (sigma x T)) T.toWord
        = (powSubst t (Multiplicative.toAdd (sigma x T)) (FreeGroup.mk T.toWord)).toWord := by
      rw [powSubst_toWord (L := T.toWord) t (Multiplicative.toAdd (sigma x T)) hp hLred]
      simp only [blkT]
      congr 1
      exact List.map_congr_left fun c _ => blk_eq_ite hp c
    have h1 : blkT t (Multiplicative.toAdd (sigma x T)) T.toWord
        = (powSubst t (Multiplicative.toAdd (sigma x T)) T).toWord := by
      simpa [FreeGroup.mk_toWord] using hgen
    rw [h1, hA]
  -- some letter of `T` is different from `t`: the letter `x`
  have hnt : ∃ c ∈ T.toWord, c.1 ≠ t := by
    have hσx : sigma x T ≠ 1 := fun h1 => hp (by rw [h1]; rfl)
    have hx : x ∈ relatorLetters T := by
      by_contra hxm
      have hnot : ∀ c ∈ T.toWord, c.1 ≠ x := by
        intro c hc hcon
        exact hxm (by rw [relatorLetters]; exact ⟨c.2, by rw [← hcon]; exact hc⟩)
      exact hσx (by
        rw [← FreeGroup.mk_toWord (x := T)]
        exact sigma_mk_eq_one_of_notMem x T.toWord hnot)
    rw [relatorLetters] at hx
    obtain ⟨b, hb⟩ := hx
    exact ⟨(x, b), hb, hxt⟩
  obtain ⟨V, hVne, hV⟩ :=
    exists_replicate_flatten_of_blkT_eq_flatten hp hLcyc hnt hk hAne hblk
  refine hpp ⟨FreeGroup.mk V, k, hk, ?_⟩
  rw [← FreeGroup.mk_toWord (x := T), hV, mk_flatten_replicate]

end Work.OROneRel
