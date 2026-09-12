import Mathlib
import Submission.Work.Polygon.DiscreteConvex
import Submission.Work.Polygon.Lemma4Algebra

/-!
# Canonical angular ranks / maximal constant-slope blocks of a discrete-convex function

The Grayson polygon `c = largestConvexMinorant d g` of the §3 route is
`DiscreteConvexOn c d` (slopes `dslope c i = c(i+1) − c i` non-decreasing on `0 ≤ i < d`)
and vanishes at the endpoints when the data `g` does (`largestConvexMinorant_ends_zero`).
The paper §3 (Prop 4, Lemma 4, Prop 5) works with the **angular points**
`J = {j₁ < ⋯ < j_r}` of such a polygon: the interior vertices at which the slope
changes, so that `c` is affine (constant slope `Λ`) on each maximal block between two
consecutive angular points.

This module develops, once and for all, the canonical constant-slope block structure of
an *arbitrary* function `c : ℕ → ℝ` on the slope range `{0,…,d−1}` (junk values beyond
`d` are irrelevant; all statements are total), building the runs of the sequence
`σ = dslope c`:

- `runEnd d σ i` — the first index `k ≥ i` in `{i,…,d}` with `k = d` or `σ k ≠ σ i` (the
  right end of the maximal run of value `σ i` starting at `i`);
- `blockStart d c` — the boundary sequence `b₀ = 0 ≤ b₁ ≤ …` with
  `bₙ₊₁ = runEnd d (dslope c) (bₙ)`: the runs are the intervals `[bₛ, bₛ₊₁)`;
- `numBlocks d c` — the number `N` of maximal runs: `b_N = d` and `bₛ < d` for `s < N`,
  so `[b₀,b₁) ∪ … ∪ [b_{N−1}, b_N)` partitions `{0,…,d−1}`;

and the theorems (all Mathlib-only apart from the `DiscreteConvex`/`Lemma4Algebra`
imports):

1. **Constancy on blocks** (`dslope_eq_on_block`): every slope index of block `s` has the
   same value `dslope c (blockStart d c s)` (= `Λ_{jₛ+1}` in the paper's 1-indexed
   slope notation `Λ_i = c(i) − c(i−1)`).
2. **The blocks partition the slope range**: `sum_range_eq_sum_blocks` (sum form) and
   `exists_blockStart_containing` (every `0 ≤ i < d` lies in exactly one block).
3. **Canonical decomposition identities**:
   `sum_block_slopes_eq_sub` (`Σₛ (bₛ₊₁−bₛ)·Λₛ = c d − c 0`, with the
   `= 0` corollary `sum_block_slopes_zero_of_ends` when the endpoints vanish — the
   `Σₛ (jₛ₊₁−jₛ)·Λ_{jₛ₊₁} = Σᵢ Λᵢ = c(d)−c(0) = 0` identity of Lemma 4's proof),
   `slopeInner_eq_block_sum` (the block regroup `⟨u,c⟩ = Σₛ (u(bₛ₊₁)−u(bₛ))·Λₛ` in
   canonical form — the `block_regroup`/`block_inner` lemmas of `Lemma4Algebra` made
   explicit for the canonical angular partition).
   Items 1.–3. need **no convexity**.
4. **Angular ranks** (needs `DiscreteConvexOn c d`, i.e. `σ` non-decreasing):
   `dslope_mono_of_convex`, consecutive block slopes strictly increase
   (`blockSlope_lt_succ`), the canonical boundaries are exactly the vertices where the
   slope changes (`angular_iff_boundary`: `dslope c (j−1) < dslope c j` holds for a
   vertex `1 ≤ j < d` iff `j = blockStart d c s` for a block boundary
   `1 ≤ s < numBlocks d c`), together with the local facts
   `dslope_strict_of_blockStart` (boundaries are angular) and
   `dslope_eq_inside_block` (interior vertices are not angular).
5. **Pointwise congruence**: the whole canonical structure depends only on the values of
   `c` on `{0,…,d}` — `runEnd_congr`/`blockStart_congr`/`numBlocks_congr` transfer it
   along pointwise equalities (used to move from the model Vee function to the Grayson
   polygon `largestConvexMinorant d g`, which agrees with it pointwise on `{0,…,d}`).
-/

open scoped BigOperators

set_option autoImplicit false

noncomputable section

namespace Submission.AngularRanks

open Submission.Polygon

/-! ## The run machinery -/

/-- The first index `k ≥ i` in `{i,…,d}` with `k = d` or `σ k ≠ σ i` (the right end of
the maximal run of value `σ i` starting at `i`); returns `i` when `d < i` (junk). -/
noncomputable def runEnd (d : ℕ) (σ : ℕ → ℝ) (i : ℕ) : ℕ :=
  if hi : i ≤ d then
    ((Finset.Icc i d).filter (fun k => k = d ∨ σ k ≠ σ i)).min' (by
      refine ⟨d, ?_⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_Icc.mpr ⟨hi, le_rfl⟩, Or.inl rfl⟩)
  else i

/-- `runEnd` is a member of the defining filter set. -/
lemma runEnd_mem_filter {d σ i} (hi : i ≤ d) :
    runEnd d σ i ∈ (Finset.Icc i d).filter (fun k => k = d ∨ σ k ≠ σ i) := by
  have hne : Finset.Nonempty ((Finset.Icc i d).filter (fun k => k = d ∨ σ k ≠ σ i)) := by
    refine ⟨d, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_Icc.mpr ⟨hi, le_rfl⟩, Or.inl rfl⟩
  rw [runEnd, dif_pos hi]
  exact Finset.min'_mem _ hne

/-- `runEnd` is at least the starting index. -/
lemma runEnd_ge {d σ i} : i ≤ runEnd d σ i := by
  by_cases hi : i ≤ d
  · have hmem := runEnd_mem_filter (d := d) (σ := σ) (i := i) hi
    exact (Finset.mem_Icc.mp ((Finset.mem_filter.mp hmem).1)).1
  · simp [runEnd, hi]

/-- `runEnd` does not exceed `d` (when starting at `i ≤ d`). -/
lemma runEnd_le_d {d σ i} (hi : i ≤ d) : runEnd d σ i ≤ d := by
  have hmem := runEnd_mem_filter (d := d) (σ := σ) (i := i) hi
  exact (Finset.mem_Icc.mp ((Finset.mem_filter.mp hmem).1)).2

/-- At `runEnd`, either we have reached `d` or the value has changed. -/
lemma runEnd_spec {d σ i} (hi : i ≤ d) : runEnd d σ i = d ∨ σ (runEnd d σ i) ≠ σ i := by
  have hmem := runEnd_mem_filter (d := d) (σ := σ) (i := i) hi
  exact (Finset.mem_filter.mp hmem).2

/-- A run starting strictly below `d` ends strictly after its start. -/
lemma runEnd_gt {d σ i} (hi : i < d) : i < runEnd d σ i := by
  by_contra hnot
  have hge := runEnd_ge (d := d) (σ := σ) (i := i)
  have hle : runEnd d σ i ≤ i := by omega
  have heq : runEnd d σ i = i := le_antisymm hle hge
  have hspec := runEnd_spec (d := d) (σ := σ) (i := i) (le_of_lt hi)
  rw [heq] at hspec
  rcases hspec with hd | hne
  · omega
  · exact hne rfl

/-- The sequence `σ` is constant on the half-open run `[i, runEnd)`. -/
lemma dslope_eq_of_lt_runEnd {d : ℕ} (c : ℕ → ℝ) {i k : ℕ} (hi : i ≤ d) (hik : i ≤ k)
    (hk : k < runEnd d (dslope c) i) : dslope c k = dslope c i := by
  by_contra hne
  have hklem : k ∈ (Finset.Icc i d).filter (fun j => j = d ∨ dslope c j ≠ dslope c i) := by
    rw [Finset.mem_filter]
    constructor
    · exact Finset.mem_Icc.mpr ⟨hik, by
        have h := runEnd_le_d (d := d) (σ := dslope c) (i := i) hi
        omega⟩
    · exact Or.inr hne
  have hle' : runEnd d (dslope c) i ≤ k := by
    have hle := Finset.min'_le ((Finset.Icc i d).filter (fun j => j = d ∨ dslope c j ≠ dslope c i)) k hklem
    simpa [runEnd, hi] using hle
  omega

/-- The canonical block-boundary sequence: `b₀ = 0`, `bₙ₊₁ = runEnd (dslope c) (bₙ)`. -/
def blockStart (d : ℕ) (c : ℕ → ℝ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => runEnd d (dslope c) (blockStart d c n)

/-- The first boundary is `0`. -/
lemma blockStart_zero (d : ℕ) (c : ℕ → ℝ) : blockStart d c 0 = 0 := rfl

/-- Successive boundaries are obtained by `runEnd`. -/
lemma blockStart_succ (d : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    blockStart d c (n + 1) = runEnd d (dslope c) (blockStart d c n) := rfl

/-- All boundaries lie in `{0,…,d}`. -/
lemma blockStart_le_d (d : ℕ) (c : ℕ → ℝ) : ∀ n : ℕ, blockStart d c n ≤ d := by
  intro n
  induction n with
  | zero => simp [blockStart]
  | succ n ih =>
      rw [blockStart_succ]
      exact runEnd_le_d (d := d) (σ := dslope c) (i := blockStart d c n) ih

/-- The boundary sequence is non-decreasing. -/
lemma blockStart_mono (d : ℕ) (c : ℕ → ℝ) : ∀ n : ℕ,
    blockStart d c n ≤ blockStart d c (n + 1) := by
  intro n
  rw [blockStart_succ]
  exact runEnd_ge (d := d) (σ := dslope c) (i := blockStart d c n)

/-- A boundary strictly below `d` is followed by a strictly larger boundary. -/
lemma blockStart_strict (d : ℕ) (c : ℕ → ℝ) {n : ℕ} (hn : blockStart d c n < d) :
    blockStart d c n < blockStart d c (n + 1) := by
  rw [blockStart_succ]
  exact runEnd_gt (d := d) (σ := dslope c) (i := blockStart d c n) hn

/-- Once a boundary reaches `d` it stays at `d`. -/
lemma blockStart_succ_eq_d (d : ℕ) (c : ℕ → ℝ) {n : ℕ} (hn : blockStart d c n = d) :
    blockStart d c (n + 1) = d := by
  rw [blockStart_succ, hn]
  exact le_antisymm (runEnd_le_d (d := d) (σ := dslope c) (i := d) (le_rfl : d ≤ d))
    (runEnd_ge (d := d) (σ := dslope c) (i := d))

/-- The `n`-th boundary is at least `n` (for `n ≤ d`): the sequence escapes `0` at unit
speed until it is saturated at `d`. -/
lemma blockStart_n_ge (d : ℕ) (c : ℕ → ℝ) : ∀ n : ℕ, n ≤ d → n ≤ blockStart d c n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      intro hn
      have hn' : n ≤ d := by omega
      have hib : n ≤ blockStart d c n := ih hn'
      by_cases hd : blockStart d c n = d
      · have hsucc := blockStart_succ_eq_d d c hd
        rw [hsucc]
        omega
      · have hlt : blockStart d c n < d := lt_of_le_of_ne (blockStart_le_d d c n) hd
        have hst := blockStart_strict d c hlt
        omega

/-- After at most `d` steps the boundary sequence reaches `d`. -/
lemma blockStart_d_eq_d (d : ℕ) (c : ℕ → ℝ) : blockStart d c d = d := by
  apply le_antisymm (blockStart_le_d d c d)
  exact blockStart_n_ge d c d (le_rfl)

/-- The number of maximal constant-slope blocks: the first `n` with `blockStart n = d`. -/
noncomputable def numBlocks (d : ℕ) (c : ℕ → ℝ) : ℕ :=
  Nat.find (show ∃ n : ℕ, blockStart d c n = d from ⟨d, blockStart_d_eq_d d c⟩)

/-- After exactly `numBlocks` steps the boundary sequence has reached `d`. -/
lemma blockStart_numBlocks (d : ℕ) (c : ℕ → ℝ) : blockStart d c (numBlocks d c) = d :=
  Nat.find_spec (show ∃ n : ℕ, blockStart d c n = d from ⟨d, blockStart_d_eq_d d c⟩)

/-- Before `numBlocks` the boundary sequence is strictly below `d`. -/
lemma blockStart_lt_numBlocks (d : ℕ) (c : ℕ → ℝ) {n : ℕ} (hn : n < numBlocks d c) :
    blockStart d c n < d := by
  apply lt_of_le_of_ne (blockStart_le_d d c n)
  intro hp
  have hle := Nat.find_min' (show ∃ n : ℕ, blockStart d c n = d from ⟨d, blockStart_d_eq_d d c⟩) hp
  have hle' : numBlocks d c ≤ n := by simpa [numBlocks] using hle
  omega

/-- For `0 < d` there is at least one block. -/
lemma numBlocks_pos {d : ℕ} (c : ℕ → ℝ) (hd : 0 < d) : 0 < numBlocks d c := by
  by_contra h
  have h0 : numBlocks d c = 0 := by omega
  have hb : blockStart d c 0 = d := by simpa [h0] using blockStart_numBlocks d c
  have hb0 : blockStart d c 0 = 0 := blockStart_zero d c
  omega

/-- After `numBlocks` the boundary sequence is constantly `d`. -/
lemma blockStart_eq_d_of_ge_numBlocks (d : ℕ) (c : ℕ → ℝ) {n : ℕ} (hn : numBlocks d c ≤ n) :
    blockStart d c n = d := by
  induction n with
  | zero =>
      have h : numBlocks d c = 0 := by omega
      simpa [h] using blockStart_numBlocks d c
  | succ n ih =>
      by_cases hle : numBlocks d c ≤ n
      · exact blockStart_succ_eq_d d c (ih hle)
      · have hnum : numBlocks d c = n + 1 := by omega
        simpa [hnum] using blockStart_numBlocks d c

/-! ## Constancy on blocks and the partition of the slope range -/

/-- **Constancy on blocks**: on the interval `[bₛ, bₛ₊₁)` of slope indices the slope
`dslope c` is constantly `dslope c (bₛ)` — the paper's `Λ_{jₛ+1}` where `jₛ = bₛ`.
(For `s ≥ numBlocks` the interval is empty, so the statement is vacuous; the non-empty
blocks are precisely `s < numBlocks`.) -/
lemma dslope_eq_on_block (c : ℕ → ℝ) (d : ℕ) (s : ℕ) {i : ℕ}
    (h1 : blockStart d c s ≤ i) (h2 : i < blockStart d c (s + 1)) :
    dslope c i = dslope c (blockStart d c s) := by
  have hle : blockStart d c s ≤ d := blockStart_le_d d c s
  exact dslope_eq_of_lt_runEnd (d := d) c hle h1 (by simpa [blockStart_succ d c s] using h2)

/-- The interval `[0, d)` is the disjoint union of the blocks `[bₛ, bₛ₊₁)`,
`s = 0, …, numBlocks−1` (sum form). -/
lemma sum_range_eq_sum_blocks {d : ℕ} (c : ℕ → ℝ) (f : ℕ → ℝ) :
    (∑ i ∈ Finset.range d, f i) =
      ∑ s ∈ Finset.range (numBlocks d c),
        (∑ i ∈ Finset.Ico (blockStart d c s) (blockStart d c (s + 1)), f i) := by
  let T : ℕ → ℝ := fun k => ∑ i ∈ Finset.range (blockStart d c k), f i
  have hblocks : ∀ s ∈ Finset.range (numBlocks d c),
      (∑ i ∈ Finset.Ico (blockStart d c s) (blockStart d c (s + 1)), f i) = T (s + 1) - T s := by
    intro s hs
    dsimp [T]
    exact Finset.sum_Ico_eq_sub f (blockStart_mono d c s)
  calc
    (∑ i ∈ Finset.range d, f i)
        = T (numBlocks d c) - T 0 := by
          dsimp [T]
          rw [blockStart_numBlocks d c, blockStart_zero]
          simp
    _ = ∑ s ∈ Finset.range (numBlocks d c), (T (s + 1) - T s) := by
          exact (Finset.sum_range_sub (f := T) (n := numBlocks d c)).symm
    _ = ∑ s ∈ Finset.range (numBlocks d c),
        (∑ i ∈ Finset.Ico (blockStart d c s) (blockStart d c (s + 1)), f i) := by
          apply Finset.sum_congr rfl
          intro s hs
          exact (hblocks s hs).symm

/-- Every slope index `0 ≤ i < d` belongs to exactly one block: there is a unique
`s < numBlocks d c` with `bₛ ≤ i < bₛ₊₁`. -/
lemma exists_blockStart_containing (c : ℕ → ℝ) (d : ℕ) {i : ℕ} (hid : i < d) :
    ∃ s : ℕ, s < numBlocks d c ∧ blockStart d c s ≤ i ∧ i < blockStart d c (s + 1) := by
  have hex : ∃ t : ℕ, i < blockStart d c (t + 1) := by
    refine ⟨numBlocks d c, ?_⟩
    have hsat : blockStart d c (numBlocks d c + 1) = d :=
      blockStart_eq_d_of_ge_numBlocks d c (by omega : numBlocks d c ≤ numBlocks d c + 1)
    rw [hsat]
    exact hid
  set s : ℕ := Nat.find hex with hsdef
  have hspec : i < blockStart d c (s + 1) := by
    simpa [hsdef] using (Nat.find_spec hex)
  have hmin : ∀ t : ℕ, t < s → ¬ i < blockStart d c (t + 1) := by
    intro t ht hp
    have hle := Nat.find_min' hex hp
    rw [← hsdef] at hle
    omega
  have hbs : blockStart d c s ≤ i := by
    by_cases hs0 : s = 0
    · rw [hs0]
      simp [blockStart]
    · have hs' : s - 1 < s := Nat.sub_lt (Nat.pos_of_ne_zero hs0) zero_lt_one
      have hp : ¬ i < blockStart d c ((s - 1) + 1) := hmin (s - 1) hs'
      have hconv : (s - 1) + 1 = s := Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hs0))
      rw [hconv] at hp
      omega
  have hsN : s < numBlocks d c := by
    by_contra hnot
    have hge : numBlocks d c ≤ s := by omega
    have hb : blockStart d c s = d := blockStart_eq_d_of_ge_numBlocks d c hge
    omega  -- uses hb : b_s = d, hbs : b_s ≤ i, hid : i < d
  exact ⟨s, hsN, hbs, hspec⟩

/-! ## Canonical block sums

The canonical partition by maximal constant-slope blocks makes the `block_regroup`
machinery of `Lemma4Algebra` explicit: per block `s` the block sum of the slope inner
product is `(u(bₛ₊₁) − u(bₛ))·Λₛ` (`slopeInner_eq_block_sum`, the paper's Lemma-4 first
displayed identity with `u := ċ_t`, `c := c_t`) and the block-weighted slope total is
`Σₛ (bₛ₊₁−bₛ)·Λₛ = c d − c 0` (`sum_block_slopes_eq_sub`), which vanishes when the
polygon endpoints vanish (`sum_block_slopes_zero_of_ends`, the Lemma-4 step
`Σₛ (jₛ₊₁−jₛ)·Λ_{jₛ+1} = Σᵢ Λᵢ = c(d) − c(0) = 0`). -/

/-- The sum of the slopes over one block is the block length times the block slope. -/
lemma sum_dslope_Ico_eq_mul (c : ℕ → ℝ) (d : ℕ) (s : ℕ) :
    (∑ i ∈ Finset.Ico (blockStart d c s) (blockStart d c (s + 1)), dslope c i) =
      ((blockStart d c (s + 1) - blockStart d c s : ℕ) : ℝ) * dslope c (blockStart d c s) := by
  calc
    (∑ i ∈ Finset.Ico (blockStart d c s) (blockStart d c (s + 1)), dslope c i)
        = ∑ _ ∈ Finset.Ico (blockStart d c s) (blockStart d c (s + 1)),
            dslope c (blockStart d c s) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact dslope_eq_on_block c d s (Finset.mem_Ico.mp hi).1 (Finset.mem_Ico.mp hi).2
    _ = ((blockStart d c (s + 1) - blockStart d c s : ℕ) : ℝ) *
        dslope c (blockStart d c s) := by
            rw [Finset.sum_const]
            simp [nsmul_eq_mul, Nat.card_Ico]

/-- **Canonical block-weighted slope total**: `Σₛ (bₛ₊₁−bₛ)·Λₛ = c d − c 0` (each block
`[bₛ, bₛ₊₁)` of length `bₛ₊₁−bₛ` contributes that many slopes, all equal to `Λₛ`). -/
lemma sum_block_slopes_eq_sub (c : ℕ → ℝ) (d : ℕ) :
    (∑ s ∈ Finset.range (numBlocks d c),
      ((blockStart d c (s + 1) - blockStart d c s : ℕ) : ℝ) * dslope c (blockStart d c s)) =
        c d - c 0 := by
  calc
    (∑ s ∈ Finset.range (numBlocks d c),
        ((blockStart d c (s + 1) - blockStart d c s : ℕ) : ℝ) * dslope c (blockStart d c s))
        = ∑ s ∈ Finset.range (numBlocks d c),
            (∑ i ∈ Finset.Ico (blockStart d c s) (blockStart d c (s + 1)), dslope c i) := by
            apply Finset.sum_congr rfl
            intro s hs
            exact (sum_dslope_Ico_eq_mul c d s).symm
    _ = ∑ i ∈ Finset.range d, dslope c i := by
            exact (sum_range_eq_sum_blocks c (dslope c)).symm
    _ = c d - c 0 := telescope c d

/-- **Vanishing block-weighted slope total**: with `c 0 = c d = 0` (Grayson polygon of a
unimodular lattice, via `largestConvexMinorant_ends_zero`), `Σₛ (bₛ₊₁−bₛ)·Λₛ = 0`. -/
lemma sum_block_slopes_zero_of_ends (c : ℕ → ℝ) (d : ℕ) (hc0 : c 0 = 0) (hcd : c d = 0) :
    (∑ s ∈ Finset.range (numBlocks d c),
      ((blockStart d c (s + 1) - blockStart d c s : ℕ) : ℝ) * dslope c (blockStart d c s)) = 0 := by
  rw [sum_block_slopes_eq_sub, hcd, hc0]
  ring

/-- **Canonical block regroup of the slope inner product** (Lemma 4, move 1, canonical
form): `⟨u, c⟩ = Σₛ (u(bₛ₊₁) − u(bₛ))·Λₛ` for the canonical angular partition. -/
lemma slopeInner_eq_block_sum (u c : ℕ → ℝ) (d : ℕ) :
    slopeInner d u c =
      ∑ s ∈ Finset.range (numBlocks d c),
        (u (blockStart d c (s + 1)) - u (blockStart d c s)) * dslope c (blockStart d c s) := by
  calc
    slopeInner d u c
        = ∑ i ∈ Finset.range d, dslope u i * dslope c i := rfl
    _ = ∑ s ∈ Finset.range (numBlocks d c),
          (∑ i ∈ Finset.Ico (blockStart d c s) (blockStart d c (s + 1)),
            dslope u i * dslope c i) := by
          exact sum_range_eq_sum_blocks c (fun i => dslope u i * dslope c i)
    _ = ∑ s ∈ Finset.range (numBlocks d c),
          (u (blockStart d c (s + 1)) - u (blockStart d c s)) * dslope c (blockStart d c s) := by
          apply Finset.sum_congr rfl
          intro s hs
          exact block_inner u c (blockStart_mono d c s) (dslope c (blockStart d c s))
            (by intro i hi1 hi2; exact dslope_eq_on_block c d s hi1 hi2)

/-! ## Angular ranks (convex case)

For a discrete-convex `c` (`DiscreteConvexOn c d`, i.e. the slope sequence is
non-decreasing) the canonical block boundaries are exactly the **angular ranks** of the
paper: the interior vertices `j = bₛ` (`1 ≤ s < numBlocks`) at which the slope strictly
increases.  We record the slope monotonicity lemma used here, the strict increase of
consecutive block slopes, and the two local angular facts (boundaries are angular,
interiors are not), plus the full characterization `angular_iff_boundary`. -/

/-- The slopes of a discrete-convex function are non-decreasing over the whole slope
range `{0,…,d−1}` (includes the last slope, unlike `slope_le_of_le`). -/
lemma dslope_mono_of_convex {c : ℕ → ℝ} {d : ℕ} (hcvx : DiscreteConvexOn c d) :
    ∀ {i j : ℕ}, i ≤ j → j < d → dslope c i ≤ dslope c j := by
  intro i j
  induction j with
  | zero =>
      intro hij hj
      have : i = 0 := by omega
      subst i
      rfl
  | succ j ih =>
      intro hij hj
      by_cases h : i ≤ j
      · have h1 : dslope c i ≤ dslope c j := ih h (by omega)
        have h2 : dslope c j ≤ dslope c (j + 1) := by
          apply hcvx j
          omega
        exact le_trans h1 h2
      · have hi : i = j + 1 := by omega
        subst i
        rfl

/-- The slopes of the block starts strictly increase across consecutive blocks:
`Λₛ < Λₛ₊₁` (needs convexity — the slope sequence is non-decreasing and changes at each
canonical boundary). -/
lemma blockSlope_lt_succ {c : ℕ → ℝ} {d : ℕ} (hcvx : DiscreteConvexOn c d) {s : ℕ}
    (hs : s + 1 < numBlocks d c) :
    dslope c (blockStart d c s) < dslope c (blockStart d c (s + 1)) := by
  have hb1 : blockStart d c s < d := blockStart_lt_numBlocks d c (by omega)
  have hb2 : blockStart d c (s + 1) < d := blockStart_lt_numBlocks d c hs
  have hmono := dslope_mono_of_convex hcvx (blockStart_mono d c s) hb2
  have hne : dslope c (blockStart d c (s + 1)) ≠ dslope c (blockStart d c s) := by
    have hspec := runEnd_spec (d := d) (σ := dslope c) (i := blockStart d c s)
      (blockStart_le_d d c s)
    have hrun : runEnd d (dslope c) (blockStart d c s) = blockStart d c (s + 1) :=
      (blockStart_succ d c s).symm
    rw [hrun] at hspec
    rcases hspec with hd | hne
    · omega  -- b_{s+1} = d contradicts b_{s+1} < d
    · exact hne
  exact lt_of_le_of_ne hmono (fun h => hne h.symm)

/-- **Interior vertices are not angular**: inside a block the slope does not change
(`j−1` and `j` lie in the same constant-slope block, so `dslope c (j−1) = dslope c j`). -/
lemma dslope_eq_inside_block (c : ℕ → ℝ) (d : ℕ) (s : ℕ) {j : ℕ}
    (h1 : blockStart d c s < j) (h2 : j < blockStart d c (s + 1)) :
    dslope c (j - 1) = dslope c j := by
  have hj1a : blockStart d c s ≤ j - 1 := by omega
  have hj1b : j - 1 < blockStart d c (s + 1) := by omega
  have hj2a : blockStart d c s ≤ j := by omega
  have hA : dslope c (j - 1) = dslope c (blockStart d c s) :=
    dslope_eq_on_block c d s hj1a hj1b
  have hB : dslope c j = dslope c (blockStart d c s) := dslope_eq_on_block c d s hj2a h2
  rw [hA, hB]

/-- **Boundaries are angular** (convex case): at the interior boundary vertex
`j = bₛ` (`1 ≤ s < numBlocks`) the slope strictly increases:
`dslope c (j−1) < dslope c j`. -/
lemma dslope_strict_of_blockStart {c : ℕ → ℝ} {d : ℕ} (hcvx : DiscreteConvexOn c d)
    {s : ℕ} (hs1 : 1 ≤ s) (hs : s < numBlocks d c) :
    dslope c (blockStart d c s - 1) < dslope c (blockStart d c s) := by
  have hsN : s - 1 < numBlocks d c := by omega
  have hconv : (s - 1) + 1 = s := Nat.sub_add_cancel hs1
  have hb_prev : blockStart d c (s - 1) < d := blockStart_lt_numBlocks d c hsN
  have hb_lt : blockStart d c (s - 1) < blockStart d c s := by
    have hstep := blockStart_strict d c hb_prev
    rw [hconv] at hstep
    exact hstep
  have hconst : dslope c (blockStart d c s - 1) = dslope c (blockStart d c (s - 1)) := by
    -- i := b_s − 1 lies in block s−1 = [b_{s−1}, b_s), whose slope is σ(b_{s−1})
    have h1' : blockStart d c (s - 1) ≤ blockStart d c s - 1 := by omega
    have h2' : blockStart d c s - 1 < blockStart d c ((s - 1) + 1) := by
      rw [hconv]
      omega
    exact dslope_eq_on_block c d (s - 1) h1' h2'
  have hlt : dslope c (blockStart d c (s - 1)) < dslope c (blockStart d c s) := by
    have hsN' : (s - 1) + 1 < numBlocks d c := by
      rw [hconv]
      exact hs
    have hstep := blockSlope_lt_succ hcvx (s := s - 1) hsN'
    rw [hconv] at hstep
    exact hstep
  rw [hconst]
  exact hlt

/-- **Characterization of the angular ranks** (convex case): for an interior vertex
`1 ≤ j < d`, the slope strictly increases at `j` (`dslope c (j−1) < dslope c j`) iff `j`
is one of the canonical block boundaries `bₛ`, `1 ≤ s < numBlocks d c`. -/
lemma angular_iff_boundary {c : ℕ → ℝ} {d : ℕ} (hcvx : DiscreteConvexOn c d) {j : ℕ}
    (hj1 : 1 ≤ j) (hjd : j < d) :
    (dslope c (j - 1) < dslope c j) ↔
      ∃ s : ℕ, 1 ≤ s ∧ s < numBlocks d c ∧ blockStart d c s = j := by
  constructor
  · intro hlt
    rcases exists_blockStart_containing c d hjd with ⟨s, hsN, hb_le, hb_gt⟩
    by_cases h : blockStart d c s = j
    · refine ⟨s, ?_, hsN, h⟩
      have hs0 : s ≠ 0 := by
        intro hs0
        subst s
        have : blockStart d c 0 = j := h
        have hb0 : blockStart d c 0 = 0 := blockStart_zero d c
        omega  -- j = 0 contradicts 1 ≤ j
      exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hs0)
    · exfalso
      have hlt_j : blockStart d c s < j := lt_of_le_of_ne hb_le h
      have heq := dslope_eq_inside_block c d s hlt_j hb_gt
      rw [heq] at hlt
      exact (lt_irrefl (dslope c j) hlt)
  · rintro ⟨s, hs1, hsN, hjs⟩
    subst j
    exact dslope_strict_of_blockStart hcvx hs1 hsN

/-! ## Pointwise congruence

The block machinery depends only on the values of `c` on `{0,…,d}` (slopes at indices
`< d`), so a pointwise agreement `c = c'` on `{0,…,d}` transfers the whole canonical
structure.  This is how the §3-route facts are transported from the concrete model Vee
function to the Grayson polygon `largestConvexMinorant d g` (which equals the Vee
pointwise on `{0,…,d}` under the model-data hypotheses — see `ModelGraysonData`). -/

/-- `runEnd` depends only on the sequence values below `d`. -/
lemma runEnd_congr {d : ℕ} {σ σ' : ℕ → ℝ} (hσ : ∀ k : ℕ, k < d → σ k = σ' k)
    {i : ℕ} (hi : i ≤ d) : runEnd d σ i = runEnd d σ' i := by
  have hF : (Finset.Icc i d).filter (fun k => k = d ∨ σ k ≠ σ i) =
      (Finset.Icc i d).filter (fun k => k = d ∨ σ' k ≠ σ' i) := by
    apply Finset.filter_congr
    intro k hk
    have hik : i ≤ k := (Finset.mem_Icc.mp hk).1
    have hkd : k ≤ d := (Finset.mem_Icc.mp hk).2
    by_cases hkd0 : k = d
    · simp [hkd0]
    · have hklt : k < d := lt_of_le_of_ne hkd hkd0
      have hile : i < d := lt_of_le_of_lt hik hklt
      have hk' : σ k = σ' k := hσ k hklt
      have hi' : σ i = σ' i := hσ i hile
      simp [hk', hi']
  apply le_antisymm
  · have hmem' : runEnd d σ' i ∈
        (Finset.Icc i d).filter (fun k => k = d ∨ σ k ≠ σ i) := by
      rw [hF]
      exact runEnd_mem_filter (d := d) (σ := σ') hi
    have hle := Finset.min'_le ((Finset.Icc i d).filter (fun k => k = d ∨ σ k ≠ σ i))
      (runEnd d σ' i) hmem'
    rw [runEnd, dif_pos hi]
    simpa using hle
  · have hmem : runEnd d σ i ∈
        (Finset.Icc i d).filter (fun k => k = d ∨ σ' k ≠ σ' i) := by
      rw [← hF]
      exact runEnd_mem_filter (d := d) (σ := σ) hi
    have hle := Finset.min'_le ((Finset.Icc i d).filter (fun k => k = d ∨ σ' k ≠ σ' i))
      (runEnd d σ i) hmem
    rw [runEnd, dif_pos hi]
    simpa using hle

/-- The canonical boundary sequence depends only on the values of `c` on `{0,…,d}`. -/
lemma blockStart_congr {d : ℕ} {c c' : ℕ → ℝ} (hc : ∀ i : ℕ, i ≤ d → c i = c' i) :
    ∀ n : ℕ, blockStart d c n = blockStart d c' n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      have hσ : ∀ k : ℕ, k < d → dslope c k = dslope c' k := by
        intro k hk
        change c (k + 1) - c k = c' (k + 1) - c' k
        rw [hc k (by omega), hc (k + 1) (by omega)]
      rw [blockStart_succ, blockStart_succ, ih]
      exact runEnd_congr hσ (blockStart_le_d d c' n)

/-- The number of canonical blocks depends only on the values of `c` on `{0,…,d}`. -/
lemma numBlocks_congr {d : ℕ} {c c' : ℕ → ℝ} (hc : ∀ i : ℕ, i ≤ d → c i = c' i) :
    numBlocks d c = numBlocks d c' := by
  apply le_antisymm
  · have hb : blockStart d c (numBlocks d c') = d := by
      rw [blockStart_congr hc]
      exact blockStart_numBlocks d c'
    have hex : ∃ n : ℕ, blockStart d c n = d := ⟨d, blockStart_d_eq_d d c⟩
    have hle := Nat.find_min' hex hb
    simpa [numBlocks] using hle
  · have hb : blockStart d c' (numBlocks d c) = d := by
      rw [← blockStart_congr hc]
      exact blockStart_numBlocks d c
    have hex : ∃ n : ℕ, blockStart d c' n = d := ⟨d, blockStart_d_eq_d d c'⟩
    have hle := Nat.find_min' hex hb
    simpa [numBlocks] using hle

end Submission.AngularRanks
