import Submission.Work.Confine
import Submission.Work.AggregateT1
import Submission.Work.FactorAbsorption
import Submission.Work.NielsenPeel

open Commons.GroupTheory.FreeGroup
set_option autoImplicit false

/-!
# Transfer from confined factors to the alignment form of T1 (junction mirror)

`Confine.lean` proves that a concatenation of reduced factors with at most one
survivor has a **confined** factor.  This module proves the *transfer*: the
geometry of the cancellation pairs across the junction between two adjacent
blocks.  For ANY two adjacent reduced blocks (no confinement needed), the
cancelled pairs whose endpoints lie in the two blocks — the *cross pairs* at
the junction — occupy exactly the mirror positions

    (BlockStart (t+1) - 1 - s, BlockStart (t+1) + s)        s < crossCount Fs t

(`junction_mirror`, PROVEN below), so by `pair_letters_inv` the letters of the
two factors match at those mirror offsets and the alignment is bounded below
by the cross count (`align_ge_crossCount`, PROVEN):  `align L_t L_{t+1} ≥
crossCount Fs t`.

## Proof structure

Fix a junction between block `t` (positions `[a, e)`) and block `t+1`
(`[e, f)`), `e := BlockStart Fs (t+1)`.  A **cross pair** is a cancelled pair
`(y, p)` with `y ∈ B_t`, `p ∈ B_{t+1}`; a **slot-`s` pair** is the mirror pair
`(e - 1 - s, e + s)`.

*If a cross pair exists then `(e-1, e)` is a pair* (`junction_innermost`): a
cross pair `(y, p)` with `p > e` forces, by interval completeness, the
position `e` to cancel with a letter `w ∈ B_t`, giving the cross pair
`(w, e)`; and a cross pair with right endpoint `e` must have left endpoint
`e-1`, since any `B_t`-letter strictly between would need a partner inside
the pair, which can neither lie in `B_t` (no pair inside a reduced factor)
nor in `B_{t+1}` (positions beyond `e` are not inside).

*If slots `0..s-1` are pairs and a cross pair not among them exists then slot
`s` is a pair* (`junction_slot_leftEndpoint` + `junction_step`): the fresh
pair's right endpoint cannot sit below `e+s` (partner uniqueness against the
earlier slots), and the interval argument, with the earlier slots' endpoints
excluded by partner uniqueness, pins the pair to the mirror slot `s`.

The main induction (`junction_mirror`): for `s < crossCount Fs t` the slot
`s` pair is present — the junction list (`junctionPairs_nodup`, from
`cancelledPairs_nodup`) has more elements than the `s` excluded slots
(`exists_mem_not_mem`), so a fresh cross pair exists and the step lemma
applies.  The cross count is bounded by both block lengths
(`crossCount_le_left_length` / `_right_length`).  Finally the letter content
of the mirror pairs (`pair_letter_option`, `mirror_invRev_prefix`) is exactly
the prefix condition of `align`, giving `align_ge_crossCount`.

## Next (T1 assembly)

The confined-factor counting (`confined_length_eq_crossCount_sum`): for a
confined factor `j` every letter of `B_j` is in a pair with partner in
`B_{j-1} ∪ B_{j+1}` (Confined), so `|L_j| = crossCount (j-1) + crossCount j`
(interior; one-sided at the ends) — together with `align_ge_crossCount` this
yields the align-level disjunction of T1 (`t1_align_general`), and via the
`FactorAbsorption` transfer lemmas the absorption-level general-`k` aggregate.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-! ## Definitions: junction cross pairs -/

variable {α : Type*}

/-- A pair of the flattened word crossing the junction between blocks `t` and
`t+1`: left endpoint in block `t`, right endpoint in block `t+1`. -/
def JunctionPair (Fs : List (List (α × Bool))) (t : ℕ)
    (pr : ℕ × ℕ) : Prop :=
  InBlock Fs t pr.1 ∧ InBlock Fs (t + 1) pr.2

/-- The cross pairs at the junction between blocks `t` and `t+1`. -/
noncomputable def junctionPairs {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) (t : ℕ) : List (ℕ × ℕ) := by
  classical
  exact (cancelledPairs Fs.flatten).filter (fun pr : ℕ × ℕ => JunctionPair Fs t pr)

/-- The number of cross pairs at the junction between blocks `t` and `t+1`. -/
noncomputable def crossCount {α : Type*} [DecidableEq α] (Fs : List (List (α × Bool)))
    (t : ℕ) : ℕ := (junctionPairs Fs t).length

/-- The mirror pair of the junction at offset `s`: the pair that cancels the
`s`-th letter of the right block against the `s`-th-from-the-end letter of the
left block. -/
def slotPair (Fs : List (List (α × Bool))) (t s : ℕ) : ℕ × ℕ :=
  (BlockStart Fs (t + 1) - 1 - s, BlockStart Fs (t + 1) + s)

/-- Membership in the junction cross-pair list: exactly the cancelled pairs of
the flattened word crossing the junction. -/
lemma mem_junctionPairs {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) (t : ℕ) (pr : ℕ × ℕ) :
    pr ∈ junctionPairs Fs t ↔
      pr ∈ cancelledPairs Fs.flatten ∧ JunctionPair Fs t pr := by
  classical
  unfold junctionPairs
  rw [List.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, decide_eq_true_iff.mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, decide_eq_true_iff.mpr h2⟩

/-- A member of the junction list is a cancelled pair crossing the junction. -/
lemma junctionPairs_mem_left {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) (t : ℕ) {pr : ℕ × ℕ}
    (h : pr ∈ junctionPairs Fs t) : pr ∈ cancelledPairs Fs.flatten :=
  (mem_junctionPairs Fs t pr).mp h |>.1

/-- A member of the junction list crosses the junction. -/
lemma junctionPairs_mem_junction {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) (t : ℕ) {pr : ℕ × ℕ}
    (h : pr ∈ junctionPairs Fs t) : JunctionPair Fs t pr :=
  (mem_junctionPairs Fs t pr).mp h |>.2

/-- A cancelled pair crossing the junction lies in the junction list. -/
lemma mem_junctionPairs_of {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) (t : ℕ) {i j : ℕ}
    (hp : (i, j) ∈ cancelledPairs Fs.flatten) (hi : InBlock Fs t i)
    (hj : InBlock Fs (t + 1) j) : (i, j) ∈ junctionPairs Fs t :=
  (mem_junctionPairs Fs t (i, j)).mpr ⟨hp, ⟨hi, hj⟩⟩

/-! ## Engine: if a cross pair exists, the innermost slot is a pair -/

/-- A letter `y` of block `t` paired with the first letter `e` of block `t+1`
must be the last letter of block `t` (`e - 1`): a letter of block `t` strictly
between `y` and `e` would be strictly inside the pair, and its partner would
need to lie in block `t` (impossible, a pair never lies inside one reduced
factor) or in block `t+1` before `e` (no such positions). -/
lemma junction_leftEndpoint_last {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) (hred : ∀ L ∈ Fs, FreeGroup.IsReduced L)
    {t : ℕ} (_ht : t + 1 < Fs.length)
    {y : ℕ} (hy : InBlock Fs t y)
    (hp : (y, BlockStart Fs (t + 1)) ∈ cancelledPairs Fs.flatten) :
    y = BlockStart Fs (t + 1) - 1 := by
  rcases hy with ⟨htj, hstart, hyend⟩
  let e : ℕ := BlockStart Fs (t + 1)
  have hye : y < e := by simpa [e] using hyend
  by_contra hne
  have hz2 : y + 1 < e := by
    have hle1 : y ≤ e - 1 := by omega
    have hlt : y < e - 1 := by omega
    omega
  rcases pair_interval_complete (Fs.flatten) hp (y + 1) (by omega) hz2 with
    ⟨w, hw1, hw2, hwpair⟩
  have hwB : InBlock Fs t w := by
    refine ⟨htj, ?_, hw2⟩
    omega
  have hy1B : InBlock Fs t (y + 1) := by
    refine ⟨htj, ?_, hz2⟩
    omega
  rcases hwpair with hwpair | hwpair
  · exact no_pair_inside_block Fs hred hwpair hy1B hwB
  · exact no_pair_inside_block Fs hred hwpair hwB hy1B

theorem junction_innermost {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) (hred : ∀ L ∈ Fs, FreeGroup.IsReduced L)
    {t : ℕ} (ht : t + 1 < Fs.length)
    (hx : ∃ y p : ℕ, InBlock Fs t y ∧ InBlock Fs (t + 1) p ∧
      (y, p) ∈ cancelledPairs Fs.flatten) :
    (BlockStart Fs (t + 1) - 1, BlockStart Fs (t + 1)) ∈ cancelledPairs Fs.flatten := by
  classical
  rcases hx with ⟨y, p, hy, hp, hpair⟩
  rcases hy with ⟨htj, hstart, hyend⟩
  rcases hp with ⟨hpj, hpe, hpend⟩
  let e : ℕ := BlockStart Fs (t + 1)
  have hye : y < e := by simpa [e] using hyend
  have hytot : p < Fs.flatten.length :=
    InBlock_lt_total (Fs := Fs) (j := t + 1) (p := p) (by exact ⟨hpj, hpe, hpend⟩)
  by_cases heq : p = e
  · have hy' : y = e - 1 := by
      apply junction_leftEndpoint_last Fs hred ht (by exact ⟨htj, hstart, hyend⟩)
      simpa [e, heq] using hpair
    change (e - 1, e) ∈ cancelledPairs Fs.flatten
    rw [← hy', ← heq]
    exact hpair
  · have hep_gt : e < p := by omega
    rcases pair_interval_complete (Fs.flatten) hpair e hye hep_gt with
      ⟨w, hw1, hw2, hwpair⟩
    rcases hwpair with hwpair | hwpair
    · -- (e, w): both endpoints beyond e, in block t+1: contradiction
      have hew : e < w := pair_lt Fs.flatten hwpair
      have heB : InBlock Fs (t + 1) e := by
        refine ⟨hpj, le_rfl, ?_⟩
        omega
      have hwB : InBlock Fs (t + 1) w := by
        refine ⟨hpj, ?_, ?_⟩
        · omega
        · omega
      exact False.elim (no_pair_inside_block Fs hred hwpair heB hwB)
    · -- (w, e): w < e, w in block t; by the engine lemma w = e - 1
      have hwe : w < e := pair_lt Fs.flatten hwpair
      have hwA : InBlock Fs t w := by
        refine ⟨htj, ?_, hwe⟩
        omega
      have hwlast : w = e - 1 := by
        apply junction_leftEndpoint_last Fs hred ht hwA
        simpa [e] using hwpair
      change (e - 1, e) ∈ cancelledPairs Fs.flatten
      rw [← hwlast]
      simpa [e] using hwpair


/-! ## Nodup and counting of the cross pairs -/

/-- The cancelled-pair list has no duplicate pairs. -/
lemma cancelledPairs_nodup {α : Type*} [DecidableEq α] (W : List (α × Bool)) :
    (cancelledPairs W).Nodup := by
  induction W with
  | nil => simp [cancelledPairs]
  | cons l t ih =>
      have hshift_inj : Function.Injective (fun ab : ℕ × ℕ => (ab.1 + 1, ab.2 + 1)) := by
        intro a b h
        apply Prod.ext
        · have h1 := congrArg Prod.fst h
          dsimp at h1
          omega
        · have h2 := congrArg Prod.snd h
          dsimp at h2
          omega
      cases hr : FreeGroup.reduce t with
      | nil =>
          rw [cancelledPairs_cons_nil hr]
          exact List.Nodup.map hshift_inj ih
      | cons hd tl =>
          cases hsp : survivorPos t with
          | nil =>
              have hz : FreeGroup.reduce t = [] := (survivorPos_eq_nil_iff t).mp hsp
              rw [hz] at hr
              simp at hr
          | cons p ptl =>
              by_cases hc : letterInv l = hd
              · rw [cancelledPairs_cons_cancel hr hsp hc]
                rw [List.nodup_cons]
                constructor
                · intro hmem
                  rcases mem_shiftPair (cancelledPairs t) hmem with ⟨i', j', hp', hi, hj⟩
                  omega
                · exact List.Nodup.map hshift_inj ih
              · rw [cancelledPairs_cons_nocancel hr hsp hc]
                exact List.Nodup.map hshift_inj ih

/-- The junction list has no duplicate pairs. -/
lemma junctionPairs_nodup {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) (t : ℕ) : (junctionPairs Fs t).Nodup := by
  unfold junctionPairs
  exact List.Nodup.filter _ (cancelledPairs_nodup (Fs.flatten))

/-- The number of cross pairs at a junction is bounded by the length of the
left block (distinct left endpoints). -/
lemma crossCount_le_left_length {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) {t : ℕ} (_ht : t + 1 < Fs.length) :
    crossCount Fs t ≤ BlockStart Fs (t + 1) - BlockStart Fs t := by
  classical
  unfold crossCount
  let l := junctionPairs Fs t
  have hnod : l.Nodup := junctionPairs_nodup Fs t
  have hlc : l.toFinset.card = l.length := List.toFinset_card_of_nodup hnod
  let a : ℕ := BlockStart Fs t
  let e : ℕ := BlockStart Fs (t + 1)
  have hfst : (l.toFinset : Set (ℕ × ℕ)).InjOn (fun x : ℕ × ℕ => x.1 - a) := by
    intro x hx y hy h
    have hxmem : x ∈ l := (List.mem_toFinset.mp hx)
    have hymem : y ∈ l := (List.mem_toFinset.mp hy)
    have hxJ := junctionPairs_mem_junction Fs t hxmem
    have hyJ := junctionPairs_mem_junction Fs t hymem
    have hxa : a ≤ x.1 := by
      unfold a
      exact hxJ.1.2.1
    have hya : a ≤ y.1 := by
      unfold a
      exact hyJ.1.2.1
    dsimp at h
    have hxy : x.1 = y.1 := by omega
    apply pair_eq_of_share (Fs.flatten) (junctionPairs_mem_left Fs t hxmem) (junctionPairs_mem_left Fs t hymem)
    left
    exact hxy
  have hmaps : Set.MapsTo (fun x : ℕ × ℕ => x.1 - a) (l.toFinset : Set (ℕ × ℕ))
      (Finset.range (e - a) : Set ℕ) := by
    intro x hx
    have hxmem : x ∈ l := (List.mem_toFinset.mp hx)
    have hxJ := junctionPairs_mem_junction Fs t hxmem
    have hxE : x.1 < e := by
      unfold e
      exact hxJ.1.2.2
    have hxa : a ≤ x.1 := by
      unfold a
      exact hxJ.1.2.1
    simp
    omega
  have hcard := Finset.card_le_card_of_injOn (fun x : ℕ × ℕ => x.1 - a) hmaps hfst
  -- hcard : #(l.toFinset) ≤ #(range (e-a))
  have hrange : (Finset.range (e - a)).card = e - a := Finset.card_range _
  rw [hlc, hrange] at hcard
  unfold a e at hcard
  simpa using hcard

/-- The number of cross pairs at a junction is bounded by the length of the
right block (distinct right endpoints). -/
lemma crossCount_le_right_length {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) {t : ℕ} (_ht : t + 1 < Fs.length) :
    crossCount Fs t ≤ BlockStart Fs (t + 2) - BlockStart Fs (t + 1) := by
  classical
  unfold crossCount
  let l := junctionPairs Fs t
  have hnod : l.Nodup := junctionPairs_nodup Fs t
  have hlc : l.toFinset.card = l.length := List.toFinset_card_of_nodup hnod
  let e : ℕ := BlockStart Fs (t + 1)
  let f : ℕ := BlockStart Fs (t + 2)
  have hsnd : (l.toFinset : Set (ℕ × ℕ)).InjOn (fun x : ℕ × ℕ => x.2 - e) := by
    intro x hx y hy h
    have hxmem : x ∈ l := (List.mem_toFinset.mp hx)
    have hymem : y ∈ l := (List.mem_toFinset.mp hy)
    have hxJ := junctionPairs_mem_junction Fs t hxmem
    have hyJ := junctionPairs_mem_junction Fs t hymem
    have hxe : e ≤ x.2 := by
      unfold e
      exact hxJ.2.2.1
    have hye : e ≤ y.2 := by
      unfold e
      exact hyJ.2.2.1
    dsimp at h
    have hxy : x.2 = y.2 := by omega
    apply pair_eq_of_share (Fs.flatten) (junctionPairs_mem_left Fs t hxmem) (junctionPairs_mem_left Fs t hymem)
    right; right; right
    exact hxy
  have hmaps : Set.MapsTo (fun x : ℕ × ℕ => x.2 - e) (l.toFinset : Set (ℕ × ℕ))
      (Finset.range (f - e) : Set ℕ) := by
    intro x hx
    have hxmem : x ∈ l := (List.mem_toFinset.mp hx)
    have hxJ := junctionPairs_mem_junction Fs t hxmem
    have hxf : x.2 < f := by
      unfold f
      exact hxJ.2.2.2
    have hxe : e ≤ x.2 := by
      unfold e
      exact hxJ.2.2.1
    simp
    omega
  have hcard := Finset.card_le_card_of_injOn (fun x : ℕ × ℕ => x.2 - e) hmaps hsnd
  have hrange : (Finset.range (f - e)).card = f - e := Finset.card_range _
  rw [hlc, hrange] at hcard
  unfold e f at hcard
  simpa using hcard


/-- The cross count at a junction is at most the length of the left factor. -/
lemma crossCount_le_factor_left {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) {t : ℕ} (ht : t + 1 < Fs.length) :
    crossCount Fs t ≤ (Fs[t]).length := by
  have hb := crossCount_le_left_length Fs ht
  have hsucc : BlockStart Fs (t + 1) = BlockStart Fs t + Fs[t].length :=
    BlockStart_succ_in Fs (j := t) (by omega)
  rw [hsucc] at hb
  omega

/-- The cross count at a junction is at most the length of the right factor. -/
lemma crossCount_le_factor_right {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) {t : ℕ} (ht : t + 1 < Fs.length) :
    crossCount Fs t ≤ (Fs[t + 1]).length := by
  have hb := crossCount_le_right_length Fs ht
  have hsucc : BlockStart Fs (t + 2) = BlockStart Fs (t + 1) + Fs[t + 1].length :=
    BlockStart_succ_in Fs (j := t + 1) ht
  rw [hsucc] at hb
  omega

/-! ## Counting lemmas for lists (generic) -/

/-- A Nodup list contained in another list has length at most it. -/
lemma nodup_length_le_of_subset {β : Type*} [DecidableEq β] {l slots : List β}
    (hnodl : l.Nodup) (hsub : ∀ x ∈ l, x ∈ slots) : l.length ≤ slots.length := by
  classical
  have h1 : l.toFinset ⊆ slots.toFinset := by
    intro x hx
    exact List.mem_toFinset.mpr (hsub x (List.mem_toFinset.mp hx))
  calc
    l.length = l.toFinset.card := (List.toFinset_card_of_nodup hnodl).symm
    _ ≤ slots.toFinset.card := Finset.card_le_card h1
    _ ≤ slots.length := List.toFinset_card_le slots

/-- If a Nodup list is longer than another, some element of it is outside the
other. -/
lemma exists_mem_not_mem {β : Type*} [DecidableEq β] {l slots : List β}
    (hnodl : l.Nodup) (hlen : slots.length < l.length) :
    ∃ x : β, x ∈ l ∧ x ∉ slots := by
  classical
  by_contra h
  have hsub : ∀ x ∈ l, x ∈ slots := by
    intro x hx
    by_contra hx'
    exact h ⟨x, hx, hx'⟩
  have hle := nodup_length_le_of_subset (β := β) hnodl hsub
  omega

/-! ## The general step: slot `s` follows from slots `< s` and a fresh pair -/

/-- A letter `w` of block `t` paired with the position `E + s` (the slot-`s`
mirror partner) must be `E - 1 - s`, provided the earlier mirror slots
`0..s-1` are cancelled (partner uniqueness excludes them). -/
lemma junction_slot_leftEndpoint {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) (hred : ∀ L ∈ Fs, FreeGroup.IsReduced L)
    {t : ℕ} (_ht : t + 1 < Fs.length) {s : ℕ}
    (hslots : ∀ u : ℕ, u < s →
      (BlockStart Fs (t + 1) - 1 - u, BlockStart Fs (t + 1) + u) ∈ cancelledPairs Fs.flatten)
    {w : ℕ} (hw : InBlock Fs t w)
    (hp : (w, BlockStart Fs (t + 1) + s) ∈ cancelledPairs Fs.flatten) :
    w = BlockStart Fs (t + 1) - 1 - s := by
  classical
  let E : ℕ := BlockStart Fs (t + 1)
  rcases hw with ⟨htj, hstart, hwend⟩
  have hwE : w < E := by simpa [E] using hwend
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- w < E - 1 - s: the position E-1-s lies strictly inside the pair (w, E+s)
    have hs1 : 1 ≤ E - 1 - s := by omega
    have hz2 : E - 1 - s < E + s := by omega
    rcases pair_interval_complete (Fs.flatten) hp (E - 1 - s) hlt hz2 with
      ⟨z, hz1, hz2', hzpair⟩
    by_cases hzE : z < E
    · -- z in block t: the pair lies inside block t
      have hEA : InBlock Fs t (E - 1 - s) := by
        refine ⟨htj, ?_, ?_⟩
        · omega
        · omega
      have hzA : InBlock Fs t z := by
        refine ⟨htj, ?_, hzE⟩
        omega
      rcases hzpair with hzpair | hzpair
      · exact False.elim (no_pair_inside_block Fs hred hzpair hEA hzA)
      · exact False.elim (no_pair_inside_block Fs hred hzpair hzA hEA)
    · -- z ≥ E: z = E + u with u < s; the slot-u pair shares z
      have hzu : z - E < s := by omega
      have hzcalc : z = E + (z - E) := by omega
      have hslotp : (E - 1 - (z - E), E + (z - E)) ∈ cancelledPairs Fs.flatten := by
        exact hslots (z - E) hzu
      rcases hzpair with hzpair | hzpair
      · -- (E-1-s, z): shares z with the slot-(z-E) pair
        have hshare : E - 1 - s = E - 1 - (z - E) ∨ E - 1 - s = E + (z - E) ∨
            z = E - 1 - (z - E) ∨ z = E + (z - E) := by
          right; right; right
          exact hzcalc
        have heq := pair_eq_of_share (Fs.flatten) hzpair hslotp hshare
        have hfst := congrArg Prod.fst heq
        omega
      · -- (z, E-1-s): z < E-1-s contradicts E ≤ z
        have hzlt := pair_lt (Fs.flatten) hzpair
        omega
  · -- E - 1 - s < w: w is the left endpoint of the slot-(E-1-w) pair
    have hwu : E - 1 - w < s := by omega
    have hcalc : w = E - 1 - (E - 1 - w) := by omega
    have hslotp : (E - 1 - (E - 1 - w), E + (E - 1 - w)) ∈ cancelledPairs Fs.flatten := by
      exact hslots (E - 1 - w) hwu
    have hshare : w = E - 1 - (E - 1 - w) ∨ w = E + (E - 1 - w) ∨
        E + s = E - 1 - (E - 1 - w) ∨ E + s = E + (E - 1 - w) := by
      left
      exact hcalc
    have heq := pair_eq_of_share (Fs.flatten) hp hslotp hshare
    have hsnd := congrArg Prod.snd heq
    omega

/-- The general step: if the mirror slots `0..s-1` are cancelled and a cross
pair outside them exists, then slot `s` is cancelled. -/
lemma junction_step {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) (hred : ∀ L ∈ Fs, FreeGroup.IsReduced L)
    {t : ℕ} (ht : t + 1 < Fs.length) {s : ℕ}
    (hslots : ∀ u : ℕ, u < s → slotPair Fs t u ∈ cancelledPairs Fs.flatten)
    (hrem : ∃ y p : ℕ, InBlock Fs t y ∧ InBlock Fs (t + 1) p ∧
      (y, p) ∈ cancelledPairs Fs.flatten ∧ ∀ u < s, (y, p) ≠ slotPair Fs t u) :
    slotPair Fs t s ∈ cancelledPairs Fs.flatten := by
  classical
  rcases hrem with ⟨y, p, hy, hp, hpair, hnot⟩
  rcases hy with ⟨htj, hstart, hyend⟩
  rcases hp with ⟨hpj, hpe, hpend⟩
  let E : ℕ := BlockStart Fs (t + 1)
  have hyE : y < E := by simpa [E] using hyend
  have hEp : E ≤ p := by simpa [E] using hpe
  have hslotpairs : ∀ u : ℕ, u < s →
      (E - 1 - u, E + u) ∈ cancelledPairs Fs.flatten := by
    intro u hu
    simpa [slotPair, E] using hslots u hu
  -- p ≥ E + s: otherwise p = E + u with u < s and the slot-u pair shares p
  have hp_ge : E + s ≤ p := by
    by_contra h
    have hpu : p - E < s := by omega
    have hzcalc : p = E + (p - E) := by omega
    have hslotp : (E - 1 - (p - E), E + (p - E)) ∈ cancelledPairs Fs.flatten :=
      hslotpairs (p - E) hpu
    have hshare : y = E - 1 - (p - E) ∨ y = E + (p - E) ∨
        p = E - 1 - (p - E) ∨ p = E + (p - E) := by
      right; right; right
      exact hzcalc
    have heq := pair_eq_of_share (Fs.flatten) hpair hslotp hshare
    exact hnot (p - E) hpu (by simpa [slotPair, E] using heq)
  by_cases hpeq : p = E + s
  · -- right endpoint exactly at slot s: the left endpoint is E-1-s
    have hyle := junction_slot_leftEndpoint Fs hred ht (s := s) hslotpairs
      (by exact ⟨htj, hstart, hyend⟩) (by simpa [E, hpeq] using hpair)
    change (E - 1 - s, E + s) ∈ cancelledPairs Fs.flatten
    rw [← hyle]
    simpa [E, hpeq] using hpair
  · -- p > E + s: the position E+s cancels with a letter of block t
    have hp_gt : E + s < p := by omega
    have hz1 : y < E + s := by omega
    rcases pair_interval_complete (Fs.flatten) hpair (E + s) hz1 hp_gt with
      ⟨q, hq1, hq2, hqpair⟩
    rcases hqpair with hqpair | hqpair
    · -- (E+s, q): both endpoints in block t+1
      have hEltq : E + s < q := pair_lt (Fs.flatten) hqpair
      have hzB : InBlock Fs (t + 1) (E + s) := by
        refine ⟨hpj, ?_, ?_⟩
        · omega
        · omega
      have hqB : InBlock Fs (t + 1) q := by
        refine ⟨hpj, ?_, ?_⟩
        · omega
        · omega
      exact False.elim (no_pair_inside_block Fs hred hqpair hzB hqB)
    · -- (q, E+s): if q in block t+1 the pair lies inside it; else q in block t
      have hqlt : q < E + s := pair_lt (Fs.flatten) hqpair
      by_cases hqE : E ≤ q
      · have hqB : InBlock Fs (t + 1) q := by
          refine ⟨hpj, hqE, ?_⟩
          omega
        have hzB : InBlock Fs (t + 1) (E + s) := by
          refine ⟨hpj, ?_, ?_⟩
          · omega
          · omega
        exact False.elim (no_pair_inside_block Fs hred hqpair hqB hzB)
      · have hqltE : q < E := by omega
        have hqA : InBlock Fs t q := by
          refine ⟨htj, ?_, hqltE⟩
          omega
        have hqle := junction_slot_leftEndpoint Fs hred ht (s := s) hslotpairs hqA
          (by simpa [E] using hqpair)
        change (E - 1 - s, E + s) ∈ cancelledPairs Fs.flatten
        rw [← hqle]
        simpa [E] using hqpair

/-! ## The junction mirror theorem -/

/-- **Junction mirror theorem.**  For two adjacent blocks of a concatenation
of reduced words, the cross pairs at their junction occupy exactly the mirror
slots `s < crossCount Fs t`: the `s`-th-from-the-end letter of the left block
is cancelled against the `s`-th letter of the right block. -/
theorem junction_mirror {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) (hred : ∀ L ∈ Fs, FreeGroup.IsReduced L)
    {t : ℕ} (ht : t + 1 < Fs.length) :
    ∀ s : ℕ, s < crossCount Fs t → slotPair Fs t s ∈ cancelledPairs Fs.flatten := by
  classical
  have hmain : ∀ s : ℕ, s < crossCount Fs t → slotPair Fs t s ∈ cancelledPairs Fs.flatten := by
    intro s
    refine Nat.strong_induction_on s ?_
    intro s ih hs
    -- slots below s are cancelled (strong induction hypothesis)
    have hslots : ∀ u : ℕ, u < s → slotPair Fs t u ∈ cancelledPairs Fs.flatten := by
      intro u hu
      exact ih u hu (lt_trans hu hs)
    -- a fresh cross pair exists: the junction list has crossCount Fs t > s
    -- elements while only s slots are excluded
    let sl : List (ℕ × ℕ) := (List.range s).map (fun u => slotPair Fs t u)
    have hlen : sl.length < (junctionPairs Fs t).length := by
      rw [crossCount] at hs
      simp [sl]
      exact hs
    rcases exists_mem_not_mem (β := ℕ × ℕ) (junctionPairs_nodup Fs t) hlen with
      ⟨x, hxmem, hxnot⟩
    rcases x with ⟨y, p⟩
    have hnot : ∀ u : ℕ, u < s → (y, p) ≠ slotPair Fs t u := by
      intro u hu hEq
      apply hxnot
      rw [List.mem_map]
      refine ⟨u, List.mem_range.mpr hu, ?_⟩
      exact hEq.symm
    have hJ := junctionPairs_mem_junction Fs t hxmem
    exact junction_step Fs hred ht (s := s) hslots
      ⟨y, p, hJ.1, hJ.2, junctionPairs_mem_left Fs t hxmem, hnot⟩
  intro s hs
  exact hmain s hs


/-! ## From mirror pairs to the alignment inequality -/

/-- The letter of the flattened word at the block-`j` position with offset `r`
is the letter of factor `j`. -/
lemma flatten_getElem_block {α : Type*} (Fs : List (List α)) {j r : ℕ}
    (hj : j < Fs.length) (hr : r < Fs[j].length) :
    Fs.flatten[BlockStart Fs j + r]? = Fs[j][r]? := by
  let A : List α := (Fs.take j).flatten
  let F : List α := Fs[j]
  let B : List α := (Fs.drop (j + 1)).flatten
  have hsplit : Fs.flatten = A ++ (F ++ B) := by
    simpa [A, F, B] using flatten_middle Fs hj
  have hA : A.length = BlockStart Fs j := by
    simpa [A] using (BlockStart_eq_take Fs j).symm
  have hpos : BlockStart Fs j + r = A.length + r := by omega
  rw [hsplit, hpos]
  exact block_getElem_right A F B hr

/-- The letter of the flattened word at the `s`-th mirror position from the
right of block `t` is the `(|Fs[t]| - 1 - s)`-th letter of factor `t`. -/
lemma flatten_left_mirror_pos {α : Type*} (Fs : List (List α)) {t s : ℕ}
    (ht : t + 1 < Fs.length) (hs : s < Fs[t].length) :
    Fs.flatten[BlockStart Fs (t + 1) - 1 - s]? = Fs[t][Fs[t].length - 1 - s]? := by
  have hEq : BlockStart Fs (t + 1) - 1 - s = BlockStart Fs t + (Fs[t].length - 1 - s) := by
    have hsucc : BlockStart Fs (t + 1) = BlockStart Fs t + Fs[t].length :=
      BlockStart_succ_in Fs (j := t) (by omega)
    omega
  rw [hEq]
  exact flatten_getElem_block Fs (j := t) (by omega : t < Fs.length)
    (by omega : Fs[t].length - 1 - s < Fs[t].length)

/-- The letter of the flattened word at the `s`-th position of block `t+1`
(from its start) is the `s`-th letter of factor `t+1`. -/
lemma flatten_right_mirror_pos {α : Type*} (Fs : List (List α)) {t s : ℕ}
    (ht : t + 1 < Fs.length) (hs : s < Fs[t + 1].length) :
    Fs.flatten[BlockStart Fs (t + 1) + s]? = Fs[t + 1][s]? := by
  exact flatten_getElem_block Fs (j := t + 1) ht hs

/-- The endpoint letters of a cancelled pair are letter-inverses (Option
form): mapping letter-inversion over the left letter yields the right. -/
lemma pair_letter_option {α : Type*} [DecidableEq α] (W : List (α × Bool))
    {i j : ℕ} (hp : (i, j) ∈ cancelledPairs W) :
    Option.map letterInv (W[i]?) = W[j]? := by
  have hij := pair_lt W hp
  have hj := pair_lt_length W hp
  have hi : i < W.length := lt_trans hij hj
  rw [List.getElem?_eq_getElem hi]
  rw [List.getElem?_eq_getElem hj]
  have hlv := pair_letters_inv W hp (W[i]) (W[j])
    (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hj)
  simp [hlv]

/-- For `s < crossCount`, the letters of `invRev (Fs[t])` and `Fs[t+1]` agree
at position `s` (the mirror letters are letter-inverses). -/
lemma mirror_invRev_prefix {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) (hred : ∀ L ∈ Fs, FreeGroup.IsReduced L)
    {t : ℕ} (ht : t + 1 < Fs.length) (s : ℕ) (hs : s < crossCount Fs t) :
    ((Fs[t]).reverse.map letterInv)[s]? = (Fs[t + 1])[s]? := by
  classical
  have hc1 : crossCount Fs t ≤ (Fs[t]).length := crossCount_le_factor_left Fs ht
  have hc2 : crossCount Fs t ≤ (Fs[t + 1]).length := crossCount_le_factor_right Fs ht
  have hs1 : s < (Fs[t]).length := lt_of_lt_of_le hs hc1
  have hs2 : s < (Fs[t + 1]).length := lt_of_lt_of_le hs hc2
  let i : ℕ := BlockStart Fs (t + 1) - 1 - s
  let j : ℕ := BlockStart Fs (t + 1) + s
  have hpair : slotPair Fs t s ∈ cancelledPairs Fs.flatten := junction_mirror Fs hred ht s hs
  have hopt := pair_letter_option (Fs.flatten) (i := i) (j := j) (by simpa [slotPair, i, j] using hpair)
  have hleft : (Fs.flatten)[i]? = (Fs[t])[Fs[t].length - 1 - s]? := by
    simpa [i] using flatten_left_mirror_pos Fs ht hs1
  have hright : (Fs.flatten)[j]? = (Fs[t + 1])[s]? := by
    simpa [j] using flatten_right_mirror_pos Fs ht hs2
  calc
    ((Fs[t]).reverse.map letterInv)[s]? = Option.map letterInv ((Fs[t]).reverse[s]?) := by
        rw [List.getElem?_map]
    _ = Option.map letterInv ((Fs[t])[Fs[t].length - 1 - s]?) := by
        rw [List.getElem?_reverse hs1]
    _ = Option.map letterInv ((Fs.flatten)[i]?) := by rw [← hleft]
    _ = (Fs.flatten)[j]? := hopt
    _ = (Fs[t + 1])[s]? := hright

/-- The alignment at a junction is at least the number of cross pairs. -/
theorem align_ge_crossCount {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) (hred : ∀ L ∈ Fs, FreeGroup.IsReduced L)
    {t : ℕ} (ht : t + 1 < Fs.length) :
    align (Fs[t]) (Fs[t + 1]) ≥ crossCount Fs t := by
  classical
  have hc1 : crossCount Fs t ≤ (Fs[t]).length := crossCount_le_factor_left Fs ht
  have hc2 : crossCount Fs t ≤ (Fs[t + 1]).length := crossCount_le_factor_right Fs ht
  let X : List (α × Bool) := (Fs[t]).reverse.map letterInv
  let Y : List (α × Bool) := Fs[t + 1]
  have hpre : ∀ s : ℕ, s < crossCount Fs t → X[s]? = Y[s]? := by
    intro s hs
    exact mirror_invRev_prefix Fs hred ht s hs
  have hlenX : X.length = (Fs[t]).length := by simp [X]
  have hcX : crossCount Fs t ≤ X.length := by rw [hlenX]; exact hc1
  have htake : X.take (crossCount Fs t) = Y.take (crossCount Fs t) := by
    apply List.ext_getElem
    · rw [List.length_take, List.length_take, min_eq_left hcX, min_eq_left hc2]
    · intro i hi1 hi2
      have hic : i < crossCount Fs t := by
        rw [List.length_take, min_eq_left hcX] at hi1
        exact hi1
      rw [List.getElem_take, List.getElem_take]
      have hopt := hpre i hic
      have hiX : i < X.length := lt_of_lt_of_le hic hcX
      have hiY : i < Y.length := lt_of_lt_of_le hic hc2
      have hXsome : X[i]? = some (X[i]) := List.getElem?_eq_getElem hiX
      have hYsome : Y[i]? = some (Y[i]) := List.getElem?_eq_getElem hiY
      rw [hXsome] at hopt
      rw [hYsome] at hopt
      exact Option.some.inj hopt
  have hcpl : crossCount Fs t ≤ commonPrefixLen X Y :=
    (commonPrefixLen_ge_iff_take X Y (crossCount Fs t) hc2).2 htake
  have hEq : commonPrefixLen X Y = align (Fs[t]) (Fs[t + 1]) := by
    unfold X Y align
    rfl
  rwa [← hEq]

end Submission.Nielsen
