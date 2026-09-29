import Mathlib
import Submission.Work.SynFFT.axisKit
import Submission.Work.SynFFT.axisMergeMath
import Submission.Work.SynFFT.axisSlices
import Submission.Work.SynFFT.axisSizeFacts
import Submission.Work.Resample.pbApplyKit

/-!
# Encoding sizes along the axis-transpose decomposition (`Work.SynFFT.axisSizes`)

The transpose word of `HasAxisTranspose` (`axisDefs.lean`) sends `ofList es` to
`ofList (List.flatten (HvdH.slices A t B es))` by cutting `es` into `A` blocks of `t*B` elements,
exploding each block into `t` rows of `B` singleton columns and merging the groups with `zipCat`.
The cost of the merge words is governed by `HvdH.vsz` of the intermediate values, so the area
needs uniform bounds on the encoded sizes of

* the blocks `blocksOf A t B es`, their elements, and `ofList` of a block;
* the leaf states `stateVal ((rowsOf t B blk).map exploded)` and their merge `mAll`;
* the arrays `ofList (blocks.map ofList)` and `ofList (blocks.map stateVal …)`;
* the output `ofList (List.flatten (HvdH.slices A t B es))`.

The mathematical input is the elementary identity
`vsz (ofList xs) = Σ_{x∈xs} vsz x + xs.length + 1` (`axsz_vsz_ofList`) and the fact that
`blocksOf` / `rowsOf` cut `es` into sublists.  The merge phase is handled by the *row mass*
`axszMass g = Σ_{r∈g} (vsz (ofList r) + 1) = vsz (grpVal g) - 1`: one `mLevel` never increases the
total mass (`axszMass_zipCat_le`, from `axsz_sum1_zipCat_le`), and since `mAll` leaves at most one
group, `vsz (stateVal (mAll gs)) ≤ axszMassAll gs + 3` — the `+3` makes the bound uniform in `B`
(also for the degenerate `B = 0`, where every group is empty and the whole state collapses).

The last conjunct (the size of the output array) is delegated to
`Work.Resample.flatten_slices_length` / `mem_flatten_slices` / `vsz_ofList_le_tight`.
-/

set_option autoImplicit false

namespace Work.SynFFT

open HvdH

/-! ## Generic size helpers -/

/-- A sum of values bounded by `M` is at most `length * M`. -/
theorem axsz_sum_map_le {α : Type} (l : List α) (f : α → ℕ) (M : ℕ)
    (h : ∀ x ∈ l, f x ≤ M) : (l.map f).sum ≤ l.length * M := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      have ih' := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
      have ha := h a List.mem_cons_self
      omega

/-- A singleton list encodes to `vsz x + 2` (the `cons` cell and the terminal `nil`). -/
theorem axsz_vsz_ofList_singleton (x : Val) : vsz (ofList [x]) = vsz x + 2 := by
  simp [axsz_vsz_cons]

/-- `ofList` of a list of values bounded by `L` encodes to at most `length * (L+1) + 1`. -/
theorem axsz_sum_le_ofList (xs : List Val) (L : ℕ) (h : ∀ x ∈ xs, vsz x ≤ L) :
    vsz (ofList xs) ≤ xs.length * (L + 1) + 1 := by
  have hs := axsz_sum_map_le xs vsz L h
  calc vsz (ofList xs) = (xs.map vsz).sum + xs.length + 1 := axsz_vsz_ofList xs
    _ ≤ xs.length * L + xs.length + 1 := by omega
    _ = xs.length * (L + 1) + 1 := by ring

/-- `ofList` of a `map`ped list whose values are bounded by `C`. -/
theorem axsz_sum_le_ofList_map (l : List (List Val)) (f : List Val → Val) (C : ℕ)
    (h : ∀ x ∈ l, vsz (f x) ≤ C) :
    vsz (ofList (l.map f)) ≤ l.length * (C + 1) + 1 := by
  have h2 : ∀ x ∈ l.map f, vsz x ≤ C := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact h y hy
  have h3 := axsz_sum_le_ofList (l.map f) C h2
  rwa [List.length_map] at h3

/-! ## Blocks and rows -/

/-- Every element of a block `blk ∈ blocksOf A t B es` is an element of `es`. -/
theorem axsz_mem_block_le {A t B L : ℕ} {es : List Val} (hL : ∀ x ∈ es, vsz x ≤ L)
    {blk : List Val} (hblk : blk ∈ blocksOf A t B es) {x : Val} (hx : x ∈ blk) : vsz x ≤ L := by
  simp only [blocksOf, List.mem_map] at hblk
  obtain ⟨a, -, rfl⟩ := hblk
  exact hL x (List.mem_of_mem_drop (List.mem_of_mem_take hx))

/-- Every row of a block of length `t*B` has length `B`. -/
theorem axsz_rows_length {t B : ℕ} {blk : List Val} (hlen : blk.length = t * B) :
    ∀ r ∈ rowsOf t B blk, r.length = B := by
  intro r hr
  simp only [rowsOf, List.mem_map, List.mem_range] at hr
  obtain ⟨j, hj, rfl⟩ := hr
  rw [List.length_take, List.length_drop, hlen]
  have h2 : j * B + B ≤ t * B := by
    have h3 : (j + 1) * B ≤ t * B := Nat.mul_le_mul_right B (Nat.succ_le_of_lt hj)
    rwa [Nat.succ_mul] at h3
  omega

/-- Every element of a row of `blk` is an element of `blk`. -/
theorem axsz_mem_rows {t B : ℕ} {blk : List Val} {r : List Val} (hr : r ∈ rowsOf t B blk)
    {x : Val} (hx : x ∈ r) : x ∈ blk := by
  simp only [rowsOf, List.mem_map] at hr
  obtain ⟨j, -, rfl⟩ := hr
  exact List.mem_of_mem_drop (List.mem_of_mem_take hx)

/-! ## Row mass of a state -/

/-- The total size of the rows of a group: `Σ_{r∈g} (vsz (ofList r) + 1) = vsz (grpVal g) - 1`. -/
abbrev axszMass (g : List (List Val)) : ℕ := (g.map (fun r => vsz (ofList r) + 1)).sum

/-- The total row mass of a state (a list of groups). -/
abbrev axszMassAll (gs : List (List (List Val))) : ℕ := (gs.map axszMass).sum

/-- One merge level never increases the mass of a group (`zipCat` only concatenates rows). -/
theorem axszMass_zipCat_le (g₁ g₂ : List (List Val)) :
    axszMass (zipCat g₁ g₂) ≤ axszMass g₁ + axszMass g₂ :=
  axsz_sum1_zipCat_le g₁ g₂

/-- One merge level never increases the total mass of a state. -/
theorem axszMassAll_mLevel_le : ∀ gs : List (List (List Val)),
    axszMassAll (mLevel gs) ≤ axszMassAll gs
  | [] => le_refl 0
  | [g] => le_refl _
  | g₁ :: g₂ :: rest => by
      have ih := axszMassAll_mLevel_le rest
      have hz := axszMass_zipCat_le g₁ g₂
      rw [mLevel_cons_cons]
      simp only [axszMassAll, List.map_cons, List.sum_cons] at ih ⊢
      omega

/-- Iterating merge levels never increases the total mass of a state. -/
theorem axszMassAll_iter_le : ∀ (k : ℕ) (gs : List (List (List Val))),
    axszMassAll (iter k gs) ≤ axszMassAll gs
  | 0, gs => le_refl _
  | k + 1, gs => by
      rw [iter_succ]
      exact le_trans (axszMassAll_iter_le k (mLevel gs)) (axszMassAll_mLevel_le gs)

/-- The merge phase never increases the total mass of a state. -/
theorem axszMassAll_mAll_le (gs : List (List (List Val))) :
    axszMassAll (mAll gs) ≤ axszMassAll gs := by
  have := axszMassAll_iter_le gs.length gs
  simpa [mAll] using this

/-- Exact size of a state in terms of its mass and its number of groups. -/
theorem axsz_vsz_stateVal_eq (gs : List (List (List Val))) :
    vsz (stateVal gs) = axszMassAll gs + 2 * gs.length + 1 := by
  have h1 : ∀ g ∈ gs, vsz (grpVal g) + 1 = axszMass g + 2 := by
    intro g _
    rw [axsz_grpVal_size]
  have hmap : gs.map (fun g => vsz (grpVal g) + 1) = gs.map (fun g => axszMass g + 2) :=
    List.map_congr_left h1
  have hsum : (gs.map (fun g => axszMass g + 2)).sum = (gs.map axszMass).sum + 2 * gs.length :=
    axsz_sum_map_add_const gs axszMass 2
  rw [axsz_stateVal_size, hmap, hsum]

/-- The merged state has at most one group, so it is bounded by the mass plus a constant. -/
theorem axsz_vsz_stateVal_mAll_le (gs : List (List (List Val))) :
    vsz (stateVal (mAll gs)) ≤ axszMassAll gs + 3 := by
  rw [axsz_vsz_stateVal_eq]
  have h1 := axszMassAll_mAll_le gs
  have h2 := mAll_length_le_one gs
  omega

/-- The mass of an exploded row: every entry is a singleton list, so each entry costs
`vsz x + 3`. -/
theorem axszMass_exploded_le {r : List Val} {L : ℕ} (h : ∀ x ∈ r, vsz x ≤ L) :
    axszMass (exploded r) ≤ r.length * (L + 3) := by
  have h2 : ∀ s ∈ exploded r, vsz (ofList s) + 1 ≤ L + 3 := by
    intro s hs
    rw [exploded, List.mem_map] at hs
    obtain ⟨x, hx, rfl⟩ := hs
    rw [axsz_vsz_ofList_singleton]
    have hx' := h x hx
    omega
  have h3 := axsz_sum_map_le (exploded r) (fun s => vsz (ofList s) + 1) (L + 3) h2
  rwa [exploded, List.length_map] at h3

/-- The mass of `(rowsOf t B blk).map exploded` is at most `t*B*(L+3)`. -/
theorem axszMassAll_rows_exploded_le {t B L : ℕ} {blk : List Val}
    (hlen : blk.length = t * B) (h : ∀ x ∈ blk, vsz x ≤ L) :
    axszMassAll ((rowsOf t B blk).map exploded) ≤ t * B * (L + 3) := by
  have hrows : (rowsOf t B blk).length = t := rowsOf_length t B blk
  have h1 : ∀ r ∈ rowsOf t B blk, axszMass (exploded r) ≤ B * (L + 3) := by
    intro r hr
    have hrlen : r.length = B := axsz_rows_length hlen r hr
    have hb : ∀ x ∈ r, vsz x ≤ L := fun x hx => h x (axsz_mem_rows hr hx)
    have hm := axszMass_exploded_le hb
    rwa [hrlen] at hm
  have h2 := axsz_sum_map_le (rowsOf t B blk) (fun r => axszMass (exploded r))
    (B * (L + 3)) h1
  rw [hrows, ← Nat.mul_assoc] at h2
  show (List.map axszMass (List.map exploded (rowsOf t B blk))).sum ≤ t * B * (L + 3)
  rw [List.map_map]
  exact h2

/-- Size of the leaf state of a block of length `t*B`: `mAll` of the exploded rows keeps at most
one group, so the mass bound `t*B*(L+3)` plus `3` suffices; here we add the `2*t` groups. -/
theorem axsz_stateVal_rows_le {t B L : ℕ} {blk : List Val} (hlen : blk.length = t * B)
    (h : ∀ x ∈ blk, vsz x ≤ L) :
    vsz (stateVal ((rowsOf t B blk).map exploded)) ≤ t * (B * (L + 3) + 2) + 1 := by
  have hrows : ((rowsOf t B blk).map exploded).length = t := by
    rw [List.length_map, rowsOf_length]
  have hmass := axszMassAll_rows_exploded_le hlen h
  rw [axsz_vsz_stateVal_eq, hrows]
  have e : t * B * (L + 3) + 2 * t = t * (B * (L + 3) + 2) := by ring
  rw [← e]
  omega

/-! ## Arithmetic of the bounds -/

/-- `t*(B*(L+3)+2)+1` is below the threshold of the leaf-state bound (needs `1 ≤ B`). -/
theorem axsz_arith_leaf {t B L : ℕ} (_ht : 1 ≤ t) (hB : 1 ≤ B) :
    t * (B * (L + 3) + 2) + 1 ≤ t * B * (L + 1) + 3 * (t * B) + t + 2 := by
  have h1 : t ≤ t * B := by
    calc t = t * 1 := (Nat.mul_one t).symm
      _ ≤ t * B := Nat.mul_le_mul_left t hB
  have e1 : t * (B * (L + 3) + 2) = t * B * (L + 3) + 2 * t := by ring
  have e2 : t * B * (L + 3) = t * B * (L + 1) + 2 * (t * B) := by ring
  rw [e1, e2]
  omega

/-- `t*B*(L+3)+3` is below the threshold of the merged-state bound. -/
theorem axsz_arith_merged {t B L : ℕ} :
    t * B * (L + 3) + 3 ≤ t * B * (L + 1) + 3 * (t * B) + t + 3 := by
  have e : t * B * (L + 3) = t * B * (L + 1) + 2 * (t * B) := by ring
  rw [e]
  omega

/-! ## The area statement -/

theorem axisSizes :
    (∀ (A t B L : ℕ) (es : List HvdH.Val), es.length = A * t * B → 1 ≤ t → 1 ≤ B →
      (∀ x ∈ es, HvdH.vsz x ≤ L) →
      ∀ blk ∈ Work.SynFFT.blocksOf A t B es, ∀ x ∈ blk, HvdH.vsz x ≤ L) ∧
    (∀ (A t B L : ℕ) (es : List HvdH.Val), es.length = A * t * B → 1 ≤ t → 1 ≤ B →
      (∀ x ∈ es, HvdH.vsz x ≤ L) →
      ∀ blk ∈ Work.SynFFT.blocksOf A t B es, HvdH.vsz (HvdH.ofList blk) ≤ t * B * (L + 1) + 1) ∧
    (∀ (A t B L : ℕ) (es : List HvdH.Val), es.length = A * t * B → 1 ≤ t → 1 ≤ B →
      (∀ x ∈ es, HvdH.vsz x ≤ L) →
      ∀ blk ∈ Work.SynFFT.blocksOf A t B es,
        HvdH.vsz (Work.SynFFT.stateVal ((Work.SynFFT.rowsOf t B blk).map Work.SynFFT.exploded)) ≤
          t * B * (L + 1) + 3 * (t * B) + t + 2) ∧
    (∀ (t B L : ℕ) (blk : List HvdH.Val), 1 ≤ t → blk.length = t * B →
      (∀ x ∈ blk, HvdH.vsz x ≤ L) →
      HvdH.vsz (Work.SynFFT.stateVal (Work.SynFFT.mAll
        ((Work.SynFFT.rowsOf t B blk).map Work.SynFFT.exploded))) ≤
        t * B * (L + 1) + 3 * (t * B) + t + 3) ∧
    (∀ (A t B L : ℕ) (es : List HvdH.Val), es.length = A * t * B → 1 ≤ t → 1 ≤ B →
      (∀ x ∈ es, HvdH.vsz x ≤ L) →
      HvdH.vsz (HvdH.ofList ((Work.SynFFT.blocksOf A t B es).map HvdH.ofList)) ≤
        A * (t * B * (L + 1) + 2) + 1) ∧
    (∀ (A t B L : ℕ) (es : List HvdH.Val), es.length = A * t * B → 1 ≤ t → 1 ≤ B →
      (∀ x ∈ es, HvdH.vsz x ≤ L) →
      HvdH.vsz (HvdH.ofList ((Work.SynFFT.blocksOf A t B es).map
        (fun blk => Work.SynFFT.stateVal ((Work.SynFFT.rowsOf t B blk).map Work.SynFFT.exploded)))) ≤
        A * (t * B * (L + 1) + 3 * (t * B) + t + 3) + 1) ∧
    (∀ (A t B L : ℕ) (es : List HvdH.Val), es.length = A * t * B → 1 ≤ t → 1 ≤ B →
      (∀ x ∈ es, HvdH.vsz x ≤ L) →
      HvdH.vsz (HvdH.ofList (List.flatten (HvdH.slices A t B es))) ≤ A * t * B * (L + 1) + 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) elements of a block
    intro A t B L es hlen ht hB hL blk hblk x hx
    exact axsz_mem_block_le hL hblk hx
  · -- (2) `ofList` of a block
    intro A t B L es hlen ht hB hL blk hblk
    have hlenblk : blk.length = t * B := blocksOf_mem_length A t B es hlen ht hB blk hblk
    have hb : ∀ x ∈ blk, vsz x ≤ L := fun x hx => axsz_mem_block_le hL hblk hx
    have h2 := axsz_sum_le_ofList blk L hb
    rwa [hlenblk] at h2
  · -- (3) the leaf state of a block
    intro A t B L es hlen ht hB hL blk hblk
    have hlenblk : blk.length = t * B := blocksOf_mem_length A t B es hlen ht hB blk hblk
    have hb : ∀ x ∈ blk, vsz x ≤ L := fun x hx => axsz_mem_block_le hL hblk hx
    exact le_trans (axsz_stateVal_rows_le hlenblk hb) (axsz_arith_leaf ht hB)
  · -- (4) the merged state of a block (no hypothesis on `B`)
    intro t B L blk ht hlenblk hb
    have hmass := axszMassAll_rows_exploded_le hlenblk hb
    have h1 : vsz (stateVal (mAll ((rowsOf t B blk).map exploded))) ≤
        axszMassAll ((rowsOf t B blk).map exploded) + 3 :=
      axsz_vsz_stateVal_mAll_le _
    exact le_trans (le_trans h1 (by omega)) (axsz_arith_merged)
  · -- (5) the array of blocks
    intro A t B L es hlen ht hB hL
    have hentry : ∀ blk ∈ blocksOf A t B es, vsz (ofList blk) ≤ t * B * (L + 1) + 1 := by
      intro blk hblk
      have hlenblk : blk.length = t * B := blocksOf_mem_length A t B es hlen ht hB blk hblk
      have hb : ∀ x ∈ blk, vsz x ≤ L := fun x hx => axsz_mem_block_le hL hblk hx
      have h2 := axsz_sum_le_ofList blk L hb
      rwa [hlenblk] at h2
    have h3 := axsz_sum_le_ofList_map (blocksOf A t B es) ofList (t * B * (L + 1) + 1) hentry
    rw [blocksOf_length] at h3
    simpa using h3
  · -- (6) the array of merged states
    intro A t B L es hlen ht hB hL
    have hentry : ∀ blk ∈ blocksOf A t B es,
        vsz (stateVal ((rowsOf t B blk).map exploded)) ≤ t * B * (L + 1) + 3 * (t * B) + t + 2 := by
      intro blk hblk
      have hlenblk : blk.length = t * B := blocksOf_mem_length A t B es hlen ht hB blk hblk
      have hb : ∀ x ∈ blk, vsz x ≤ L := fun x hx => axsz_mem_block_le hL hblk hx
      exact le_trans (axsz_stateVal_rows_le hlenblk hb) (axsz_arith_leaf ht hB)
    have h3 := axsz_sum_le_ofList_map (blocksOf A t B es)
      (fun blk => stateVal ((rowsOf t B blk).map exploded))
      (t * B * (L + 1) + 3 * (t * B) + t + 2) hentry
    rw [blocksOf_length] at h3
    simpa using h3
  · -- (7) the output array
    intro A t B L es hlen ht hB hL
    have h1 : ∀ x ∈ List.flatten (HvdH.slices A t B es), vsz x ≤ L :=
      fun x hx => hL x (Work.Resample.mem_flatten_slices A t B es hlen hx)
    have h2 := Work.Resample.vsz_ofList_le_tight h1
    rwa [Work.Resample.flatten_slices_length A t B es] at h2

end Work.SynFFT
