/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).
-/
import Mathlib
import Submission.Work.OROneRel.padDefs

/-!
# Padded subwords of powers of a relator

The padding homomorphism `padHom c : F α →* F (Option α)` sends a generator `a` to the block
`a * z ^ (c a) * a`, where `z = none` is a fresh letter.  Such a block begins and ends with its own
letter `a`, so the blocks of a *reduced* word never cancel against each other; the reduced word of
`padHom c u` is therefore obtained from the reduced word of `u` by replacing every letter by its
block, i.e. `(padHom c u).toWord = padList c u.toWord`.  Since `padList c` is additive in the list,
a subword of `r ^ k` stays a subword after padding, which is the statement proved here.

The file only depends on `Submission/Work/OROneRel/padDefs`.

Note on `DecidableEq`: the word `u.toWord` of a free group element depends on a `DecidableEq`
instance for the generating type, and different instances are not definitionally equal even though
they are equal (`DecidableEq` is a subsingleton).  The key lemma `pad_toWord_padHom_padList` is
therefore stated with the two instances as *explicit* arguments, so that it can be applied to any
pair of instances (in particular to the ones occurring in the definition of `IsSubwordOf`).
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-! ### The middle of a padding block -/

/-- `padZPart y m` is the reduced word of `of y ^ (m : ℤ)`: `|m|` copies of the letter `y`, taken
positively if `0 ≤ m` and negatively if `m < 0`. -/
def padZPart (y : α) (m : ℤ) : List (α × Bool) :=
  if 0 ≤ m then List.replicate m.toNat (y, true) else List.replicate (-m).toNat (y, false)

theorem padZPart_zero (y : α) : padZPart y 0 = [] := by
  rw [padZPart, if_pos (le_refl (0 : ℤ))]
  rfl

theorem padZPart_natCast (y : α) (n : ℕ) :
    padZPart y (n : ℤ) = List.replicate n (y, true) := by
  rw [padZPart, if_pos (Int.natCast_nonneg n), Int.toNat_natCast]

theorem padZPart_negNatCast (y : α) (n : ℕ) :
    padZPart y (-(n : ℤ)) = List.replicate n (y, false) := by
  cases n with
  | zero =>
    rw [show -(↑(0 : ℕ) : ℤ) = (0 : ℤ) by norm_num, padZPart_zero]
    rfl
  | succ n => rw [padZPart, if_neg (by omega), neg_neg, Int.toNat_natCast]

theorem padZPart_fst_of_mem {y : α} {m : ℤ} {q : α × Bool} (hq : q ∈ padZPart y m) :
    q.1 = y := by
  unfold padZPart at hq
  split at hq <;> rw [List.eq_of_mem_replicate hq]

theorem padZPart_isReduced (y : α) (m : ℤ) : FreeGroup.IsReduced (padZPart y m) := by
  rw [FreeGroup.IsReduced, padZPart]
  by_cases h : 0 ≤ m
  · rw [if_pos h]
    exact List.isChain_replicate_of_rel _ (by simp)
  · rw [if_neg h]
    exact List.isChain_replicate_of_rel _ (by simp)

theorem padZPart_invRev (y : α) (m : ℤ) :
    FreeGroup.invRev (padZPart y m) = padZPart y (-m) := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · rw [padZPart_natCast, padZPart_negNatCast]
    simp [FreeGroup.invRev]
  · rw [padZPart_negNatCast, neg_neg, padZPart_natCast]
    simp [FreeGroup.invRev]

theorem pad_toWord_zpow [DecidableEq α] (y : α) (m : ℤ) :
    (FreeGroup.of y ^ m).toWord = padZPart y m := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · rw [zpow_natCast, FreeGroup.toWord_of_pow, padZPart_natCast]
  · rw [zpow_neg, zpow_natCast, FreeGroup.toWord_inv, FreeGroup.toWord_of_pow,
      ← padZPart_natCast, padZPart_invRev]

/-! ### Reducedness of concatenated blocks -/

/-- A letter `(x, b)`, followed by a reduced word all of whose letters have first component `y`,
is reduced, provided `x ≠ y`. -/
theorem pad_isReduced_cons_of_mem_fst_eq {x y : α} {b : Bool} {Z : List (α × Bool)}
    (hxy : x ≠ y) (hZ : FreeGroup.IsReduced Z) (hZm : ∀ p ∈ Z, p.1 = y) :
    FreeGroup.IsReduced ((x, b) :: Z) := by
  rw [FreeGroup.IsReduced]
  refine List.isChain_cons.2 ⟨?_, hZ⟩
  intro w hw h
  exact absurd (h.trans (hZm w (List.mem_of_mem_head? hw))) hxy

/-- The word `(x, b) :: Z ++ [(x, b)]`, where all letters of `Z` have first component `y ≠ x` and
`Z` is reduced, is reduced. -/
theorem pad_isReduced_sandwich {x y : α} {b : Bool} {Z : List (α × Bool)}
    (hxy : x ≠ y) (hZ : FreeGroup.IsReduced Z) (hZm : ∀ p ∈ Z, p.1 = y) :
    FreeGroup.IsReduced ((x, b) :: Z ++ [(x, b)]) := by
  refine List.IsChain.append (pad_isReduced_cons_of_mem_fst_eq hxy hZ hZm)
    FreeGroup.IsReduced.singleton ?_
  intro u hu v hv
  have hv' : (x, b) = v := by simpa using hv
  subst hv'
  cases Z with
  | nil =>
    have hu' : (x, b) = u := by simpa using hu
    subst hu'
    exact fun _ => rfl
  | cons z Z' =>
    have hu' : u ∈ (z :: Z').getLast? := by simpa using hu
    exact fun h => absurd (h.symm.trans (hZm u (List.mem_of_mem_getLast? hu'))) hxy

/-! ### The reduced word of a padding block -/

/-- `toWord` is additive across a product whose concatenated word is already reduced. -/
theorem pad_toWord_mul_of_isReduced [DecidableEq α] {a b : FreeGroup α}
    (h : FreeGroup.IsReduced (a.toWord ++ b.toWord)) :
    (a * b).toWord = a.toWord ++ b.toWord := by
  rw [FreeGroup.toWord_mul]
  exact h.reduce_eq

/-- The padding block of a generator: `toWord` of `of x * of y ^ m * of x` for `x ≠ y` is the
letter `x`, the `|m|` copies of `y`, and the letter `x` again. -/
theorem pad_toWord_of_mul_zpow_mul [DecidableEq α] {x y : α} (hxy : x ≠ y) (m : ℤ) :
    (FreeGroup.of x * FreeGroup.of y ^ m * FreeGroup.of x).toWord
      = (x, true) :: padZPart y m ++ [(x, true)] := by
  have h1 : (FreeGroup.of x * FreeGroup.of y ^ m).toWord = (x, true) :: padZPart y m := by
    rw [pad_toWord_mul_of_isReduced (a := FreeGroup.of x) (b := FreeGroup.of y ^ m) (h := by
      rw [FreeGroup.toWord_of, pad_toWord_zpow]
      exact pad_isReduced_cons_of_mem_fst_eq hxy (padZPart_isReduced y m)
        (fun q hq => padZPart_fst_of_mem hq))]
    rw [FreeGroup.toWord_of, pad_toWord_zpow, List.singleton_append] <;> rfl
  rw [pad_toWord_mul_of_isReduced (a := FreeGroup.of x * FreeGroup.of y ^ m)
      (b := FreeGroup.of x) (h := by
    rw [h1, FreeGroup.toWord_of]
    exact pad_isReduced_sandwich hxy (padZPart_isReduced y m)
      (fun q hq => padZPart_fst_of_mem hq)),
    h1, FreeGroup.toWord_of] <;> rfl

/-- The inverse of a padding block: `toWord` of the inverse of `of x * of y ^ m * of x`. -/
theorem pad_toWord_inv_mul_zpow_mul_inv [DecidableEq α] {x y : α} (hxy : x ≠ y) (m : ℤ) :
    ((FreeGroup.of x)⁻¹ * (FreeGroup.of y ^ m)⁻¹ * (FreeGroup.of x)⁻¹).toWord
      = (x, false) :: padZPart y (-m) ++ [(x, false)] := by
  have hE : (FreeGroup.of x)⁻¹ * (FreeGroup.of y ^ m)⁻¹ * (FreeGroup.of x)⁻¹
      = (FreeGroup.of x * FreeGroup.of y ^ m * FreeGroup.of x)⁻¹ := by group
  rw [hE, FreeGroup.toWord_inv, pad_toWord_of_mul_zpow_mul (x := x) (y := y) hxy m,
    List.cons_append, FreeGroup.invRev_cons, FreeGroup.invRev_append, padZPart_invRev]
  simp [FreeGroup.invRev]

/-! ### The padding blocks of `padBlock` -/

/-- The explicit form of a padding block: the letter `(some p.1, p.2)`, the `z`-part and the letter
`(some p.1, p.2)` again. -/
theorem pad_padBlock_eq (c : α → ℤ) (p : α × Bool) :
    padBlock c p
      = (some p.1, p.2) :: padZPart (none : PadT α) (if p.2 then c p.1 else -(c p.1))
          ++ [(some p.1, p.2)] := by
  classical
  obtain ⟨a, b⟩ := p
  cases b with
  | false =>
    have hb : padBlock c (a, false) = ((padGen c a)⁻¹).toWord := by simp [padBlock]
    have hE : (padGen c a)⁻¹
        = (FreeGroup.of (some a))⁻¹ * (FreeGroup.of (none : PadT α) ^ (c a))⁻¹
          * (FreeGroup.of (some a))⁻¹ := by
      rw [padGen]
      group
    rw [hb, hE,
      pad_toWord_inv_mul_zpow_mul_inv (x := some a) (y := (none : PadT α)) (by simp) (c a)]
    simp
  | true =>
    have hb : padBlock c (a, true) = (padGen c a).toWord := by simp [padBlock]
    rw [hb, padGen,
      pad_toWord_of_mul_zpow_mul (x := some a) (y := (none : PadT α)) (by simp) (c a)]
    simp

theorem pad_getLast?_append_singleton (a : α × Bool) (l : List (α × Bool)) :
    (l ++ [a]).getLast? = some a := by
  rw [List.getLast?_append_of_ne_nil _ (by simp : ([a] : List (α × Bool)) ≠ [])] <;> rfl

theorem pad_head?_padBlock (c : α → ℤ) (p : α × Bool) :
    (padBlock c p).head? = some (some p.1, p.2) := by
  rw [pad_padBlock_eq]
  rfl

theorem pad_getLast?_padBlock (c : α → ℤ) (p : α × Bool) :
    (padBlock c p).getLast? = some (some p.1, p.2) := by
  rw [pad_padBlock_eq]
  exact pad_getLast?_append_singleton _ _

theorem pad_padBlock_isReduced (c : α → ℤ) (p : α × Bool) :
    FreeGroup.IsReduced (padBlock c p) := by
  rw [pad_padBlock_eq]
  exact pad_isReduced_sandwich (x := some p.1) (y := (none : PadT α)) (b := p.2) (by simp)
    (padZPart_isReduced _ _) (fun q hq => padZPart_fst_of_mem hq)

theorem pad_padBlock_ne_nil (c : α → ℤ) (p : α × Bool) : padBlock c p ≠ [] := by
  intro h
  have h' : (padBlock c p).head? = none := (List.head?_eq_none_iff).2 h
  rw [pad_head?_padBlock] at h'
  exact Option.some_ne_none _ h'

/-! ### The padded word -/

theorem pad_padList_append (c : α → ℤ) (L₁ L₂ : List (α × Bool)) :
    padList c (L₁ ++ L₂) = padList c L₁ ++ padList c L₂ := by
  rw [padList, padList, padList, List.map_append, List.flatten_append]

/-- Consecutive blocks of a reduced word never cancel: the relation required by
`List.isChain_flatten` holds for `L.map (padBlock c)`. -/
theorem pad_padList_isChain (c : α → ℤ) (L : List (α × Bool)) (hL : FreeGroup.IsReduced L) :
    (L.map (padBlock c)).IsChain
      (fun l₁ l₂ => ∀ᵉ (x ∈ l₁.getLast?) (y ∈ l₂.head?), x.1 = y.1 → x.2 = y.2) :=
  List.isChain_map_of_isChain (padBlock c)
    (fun a b hab x hx y hy hxy => by
      have hx' : x = (some a.1, a.2) := by
        rw [pad_getLast?_padBlock] at hx
        exact (Option.mem_some_iff.mp hx).symm
      have hy' : y = (some b.1, b.2) := by
        rw [pad_head?_padBlock] at hy
        exact (Option.mem_some_iff.mp hy).symm
      rw [hx', hy'] at hxy ⊢
      exact hab (Option.some_inj.mp hxy)) hL

/-- The padding of a reduced word is reduced. -/
theorem pad_padList_isReduced (c : α → ℤ) {L : List (α × Bool)} (hL : FreeGroup.IsReduced L) :
    FreeGroup.IsReduced (padList c L) := by
  rw [FreeGroup.IsReduced, padList]
  refine (List.isChain_flatten ?_).2 ⟨?_, pad_padList_isChain c L hL⟩
  · intro h
    obtain ⟨p, -, hp⟩ := List.mem_map.mp h
    exact pad_padBlock_ne_nil c p hp
  · intro l hl
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hl
    exact pad_padBlock_isReduced c p

/-! ### The padding and `mk` -/

theorem pad_padHom_mk_singleton (c : α → ℤ) (p : α × Bool) :
    padHom c (FreeGroup.mk [p]) = FreeGroup.mk (padBlock c p) := by
  classical
  obtain ⟨a, b⟩ := p
  cases b with
  | false =>
    have h : FreeGroup.mk [(a, false)] = (FreeGroup.of a)⁻¹ := by
      rw [FreeGroup.of, FreeGroup.inv_mk]
      rfl
    rw [h, map_inv, padHom_of]
    rw [show padBlock c (a, false) = ((padGen c a)⁻¹).toWord by simp [padBlock]]
    exact (FreeGroup.mk_toWord (x := (padGen c a)⁻¹)).symm
  | true =>
    rw [← FreeGroup.of, padHom_of]
    rw [show padBlock c (a, true) = (padGen c a).toWord by simp [padBlock]]
    exact (FreeGroup.mk_toWord (x := padGen c a)).symm

/-- Padding commutes with `mk`. -/
theorem pad_padHom_mk_eq_mk_padList (c : α → ℤ) (L : List (α × Bool)) :
    padHom c (FreeGroup.mk L) = FreeGroup.mk (padList c L) := by
  induction L with
  | nil =>
    show padHom c (FreeGroup.mk ([] : List (α × Bool)))
      = FreeGroup.mk ([] : List (PadT α × Bool))
    rw [← FreeGroup.one_eq_mk, map_one] <;> rfl
  | cons p L ih =>
    have h1 : FreeGroup.mk (p :: L) = FreeGroup.mk [p] * FreeGroup.mk L := by
      have := FreeGroup.mul_mk (L₁ := [p]) (L₂ := L)
      simpa using this.symm
    have h2 : padList c (p :: L) = padBlock c p ++ padList c L := by
      simp [padList]
    rw [h1, map_mul, ih, pad_padHom_mk_singleton, h2, ← FreeGroup.mul_mk] <;> rfl

/-! ### The reduced word of a padded element -/

/-- `IsReduced` of the reduced word of a group element, at an arbitrary `DecidableEq` instance. -/
theorem pad_isReduced_toWord (i : DecidableEq α) (u : FreeGroup α) :
    FreeGroup.IsReduced (@FreeGroup.toWord α i u) := by
  have h : @FreeGroup.reduce α i (@FreeGroup.toWord α i u) = @FreeGroup.toWord α i u :=
    FreeGroup.reduce_toWord u
  exact FreeGroup.isReduced_iff_reduce_eq.mpr h

/-- Different `DecidableEq` instances give the same word: `DecidableEq` is a subsingleton. -/
theorem pad_toWord_inst_eq (i : DecidableEq α) (u : FreeGroup α) :
    @FreeGroup.toWord α i u = @FreeGroup.toWord α (Classical.decEq α) u := by
  have h : i = Classical.decEq α := by
    funext a b
    exact Subsingleton.elim _ _
  rw [h]

/-- **The reduced word of a padded element.**  The instances of `DecidableEq` for `α` and for
`Option α` are kept as explicit arguments, so that the lemma applies to any pair of instances. -/
theorem pad_toWord_padHom_padList (c : α → ℤ) (u : FreeGroup α)
    (iα : DecidableEq α) (iP : DecidableEq (PadT α)) :
    @FreeGroup.toWord (PadT α) iP (padHom c u) = padList c (@FreeGroup.toWord α iα u) := by
  have h : padHom c u = padHom c (FreeGroup.mk (@FreeGroup.toWord α iα u)) :=
    congrArg (padHom c) (FreeGroup.mk_toWord (x := u)).symm
  have hred : FreeGroup.IsReduced (padList c (@FreeGroup.toWord α iα u)) :=
    pad_padList_isReduced c (pad_isReduced_toWord iα u)
  calc @FreeGroup.toWord (PadT α) iP (padHom c u)
      = @FreeGroup.toWord (PadT α) iP
          (padHom c (FreeGroup.mk (@FreeGroup.toWord α iα u))) := by rw [h]
    _ = @FreeGroup.toWord (PadT α) iP
          (FreeGroup.mk (padList c (@FreeGroup.toWord α iα u))) := by
        rw [pad_padHom_mk_eq_mk_padList]
    _ = @FreeGroup.reduce (PadT α) iP (padList c (@FreeGroup.toWord α iα u)) :=
        FreeGroup.toWord_mk (L₁ := padList c (@FreeGroup.toWord α iα u))
    _ = padList c (@FreeGroup.toWord α iα u) := hred.reduce_eq

/-- The word of `padRel c r ^ k` decomposes as prescribed by a decomposition of the word of
`r ^ k`.  Again the `DecidableEq` instances are explicit arguments. -/
theorem pad_pad_subword_key (c : α → ℤ) (iα : DecidableEq α) (iP : DecidableEq (PadT α))
    {r v : FreeGroup α} {k : ℕ} {L₁ L₂ : List (α × Bool)}
    (hL : @FreeGroup.toWord α iα (r ^ k) = L₁ ++ @FreeGroup.toWord α iα v ++ L₂) :
    @FreeGroup.toWord (PadT α) iP (padRel c r ^ k)
      = padList c L₁ ++ @FreeGroup.toWord (PadT α) iP (padHom c v) ++ padList c L₂ := by
  have h1 : padRel c r ^ k = padHom c (r ^ k) := by rw [padRel, map_pow] <;> rfl
  rw [h1, pad_toWord_padHom_padList c (r ^ k) iα iP,
    pad_toWord_padHom_padList c v iα iP, hL, pad_padList_append, pad_padList_append] <;> rfl

theorem pad_subword_of_isSubwordOf_pow {α : Type u} (c : α → ℤ) {r v : FreeGroup α} {k : ℕ}
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator r)
    (h : Work.OROneRel.IsSubwordOf v (r ^ k)) :
    Work.OROneRel.IsSubwordOf (Work.OROneRel.padHom c v)
      (Work.OROneRel.padRel c r ^ k) := by
  classical
  rw [IsSubwordOf] at h ⊢
  obtain ⟨L₁, L₂, hL⟩ := h
  exact ⟨padList c L₁, padList c L₂, pad_pad_subword_key c _ _ hL⟩

end Work.OROneRel
