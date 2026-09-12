import Mathlib

/-!
# E2b parameter selection (angular windows around spike directions)

The E2b contour deformation (Plan.md DESIGN NOTE 25/27) parts the annulus
between the outer circle and the star into per-spike "above-the-tip" cells
(angular windows `[x_j − δ, x_j + δ]` around each spike direction `x_j`) and
"gap cells" (angular ranges strictly between consecutive directions).  This
requires a positive angular half-width `δ` such that:

* (separation of windows) the closed windows around *consecutive* directions
  are disjoint: `x_{j+1} − x_j > 2δ` for `j < s − 1`, and around the circle:
  `2π + x₀ − x_{s−1} > 2δ` (the *wrap gap* between the last and the first
  direction, going through the seam `2π`).
* (consequently no other direction lies in any window, and every gap
  `(x_j + δ, x_{j+1} − δ)` is nonempty and direction-free).

Such a `δ` exists because the directions are pairwise distinct modulo `2π`
(a finite set of points on the circle has a positive minimal gap).  This
module proves existence of `δ` with the two inequalities; the E2b assembly
modules then use it.

Input shape: `x : Fin s → ℝ` (`0 < s`) with all `x i ∈ (-π, π]`, pairwise
distinct, and sorted so that the *cyclic* order is `x 0 < x 1 < … < x (s−1)`
with wrap `x 0 + 2π` above `x (s−1)`.  (In the application `x` is obtained
from `Submission.DirCycle.dirList S`.)  Since the sort order is cumbersome
for children, we instead take the *list* `xs : List ℝ` which is
strictly increasing, length `s ≥ 1`, entries in `(-π, π]`, and prove the
selection for the list; the wrap gap uses the first and last entries.

## Statements to prove (no sorries may remain)

1. `exists_delta` : for `xs : List ℝ`, `SortedLT xs`, `0 < xs.length`,
   `∀ x ∈ xs, x ∈ Set.Ioc (-Real.pi) Real.pi`, and with the wrap gap
   `wrapGap xs := 2 * Real.pi + xs.head! - xs.getLast!` positive, there is
   `δ > 0` with:
     (a) `∀ i : Fin (xs.length − 1), xs.get ⟨i, …⟩ + 2*δ < xs.get ⟨i+1, …⟩`
         (strictly; use `<` so that `gap = x_{i+1} − x_i > 2δ`);
     (b) `wrapGap xs > 2*δ`.
2. `exists_delta'` (cleaner list form): `∃ δ > 0, (∀ j < xs.length − 1,
   xs.get ⟨j+1, …⟩ − xs.get ⟨j, …⟩ > 2*δ) ∧ (2*Real.pi + xs.head! −
   xs.getLast! > 2*δ)`.
3. If desired, also: `δ_small_positive` versions with an extra upper bound
   `δ < ε` for any given `ε > 0` (so the assembly can later shrink `δ`
   below any E1 fattening radius): `∃ δ, 0 < δ ∧ δ < ε ∧ (window/gap
   inequalities)`.

## Proof guidance

- The minimal positive gap over the finite set of pairwise-circle-distinct
  angles is positive.  Work with the list directly:
  * `gaps := [x₁ − x₀, …, x_{s−1} − x_{s−2}]` are all `> 0` (strictly
    increasing list), and the wrap gap `w := 2π + x₀ − x_{s−1} > 0` (this is
    the key hypothesis: use the fact that `x₀ + 2π > x_{s−1}`; derive it from
    pairwise distinctness modulo `2π` of entries in `(-π, π]` — note if some
    entry equals `π` it represents the same direction as `−π`; handle the
    wrap-gap positivity by the geometric fact that the s points
    `{x i mod 2π}` on the circle are distinct, so the arc from the largest to
    the smallest (through `2π`) has positive length; simplest: take the
    hypothesis `0 < wrapGap xs` as an *input* and do not prove it here —
    a separate module derives it from `dirSet` data via `DirCycle`).
  * `δ := (min of all consecutive gaps and the wrap gap)/3` works
    (divide by `3` to keep strictness and margin); formalize the minimum of
    a Finset/List of positive reals via `List.min'`/`Finset.min'` or simply
    argue with `exists_forall_lt` style: since the finite set of positive
    numbers `{x_{i+1} − x_i} ∪ {wrap}` has a minimum `m > 0`, take
    `δ := m/2`.
  * Cleaner: prove by `let m : ℝ := Finset.min' … ; refine ⟨m/2, …⟩` and
    handle the Fin-index arithmetic with `omega`.
- Real arithmetic for the strict inequalities: `linarith`/`nlinarith`.
- List indexing: prefer `xs.get ⟨j, hj⟩`; for `j+1` entries provide bounds
  by `omega`.

You may add helper lemmas.  Keep `namespace Submission.E2bParam`.
-/

noncomputable section

open scoped Real
open List

namespace Submission.E2bParam

/-- The wrap gap: the angular distance (through `2π`) from the last to the
first direction, going around the circle. -/
def wrapGap (xs : List ℝ) : ℝ :=
  2 * Real.pi + xs.head! - xs.getLast!

/-! ## Helper lemmas -/

/-- A nonempty list has positive length. -/
lemma length_pos_of_ne_nil {xs : List ℝ} (hne : xs ≠ []) : 0 < xs.length := by
  cases xs with
  | nil => exact False.elim (hne rfl)
  | cons a l => simp

/-- From `a < n - 1` and `0 < n` we get `a + 1 < n` (index successor stays
in range). -/
lemma add_one_lt_of_lt_pred {a n : ℕ} (h : a < n - 1) (hn : 0 < n) : a + 1 < n := by
  omega

/-- From `a < n - 1` we get `a < n` (`n - 1 ≤ n` in `ℕ`). -/
lemma lt_of_lt_pred {a n : ℕ} (h : a < n - 1) : a < n := by
  omega

/-- From `a + 1 < n` and `0 < n` we get `a < n - 1`. -/
lemma lt_pred_of_add_one_lt {a n : ℕ} (h : a + 1 < n) (hn : 0 < n) : a < n - 1 := by
  omega

/-- `SortedLT` is `StrictMono get`: the entry at a smaller index is strictly
smaller. -/
lemma get_lt_get_of_val_lt {xs : List ℝ} (hs : xs.SortedLT) {i j : ℕ}
    (hi : i < xs.length) (hj : j < xs.length) (hij : i < j) :
    xs.get ⟨i, hi⟩ < xs.get ⟨j, hj⟩ := by
  exact hs (a := ⟨i, hi⟩) (b := ⟨j, hj⟩) (Fin.mk_lt_mk.mpr hij)

/-- A consecutive gap of a strictly increasing list is positive. -/
lemma consec_gap_pos (xs : List ℝ) (hs : xs.SortedLT) {j : ℕ}
    (hj : j + 1 < xs.length) :
    0 < xs.get ⟨j + 1, hj⟩ - xs.get ⟨j, Nat.lt_trans (Nat.lt_succ_self j) hj⟩ := by
  have hlt : xs.get ⟨j, Nat.lt_trans (Nat.lt_succ_self j) hj⟩ < xs.get ⟨j + 1, hj⟩ :=
    get_lt_get_of_val_lt hs (Nat.lt_trans (Nat.lt_succ_self j) hj) hj (Nat.lt_succ_self j)
  linarith

/-- A finite (nonempty) set of positive reals has a positive number `δ` such
that twice `δ` is strictly below every element (take `δ` a third of the
minimum, for strictness margin). -/
lemma exists_delta_of_finset (S : Finset ℝ) (hS : S.Nonempty)
    (hpos : ∀ x ∈ S, 0 < x) : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S, 2 * δ < x := by
  classical
  let m := S.min' hS
  have hm_mem : m ∈ S := Finset.min'_mem S hS
  have hm_pos : 0 < m := hpos m hm_mem
  refine ⟨m / 3, ?_, ?_⟩
  · positivity
  · intro x hx
    have hle : m ≤ x := Finset.min'_le S x hx
    have hgt : 2 * (m / 3) < m := by
      calc
        2 * (m / 3) = (2 / 3) * m := by ring
        _ < 1 * m := by
          gcongr
          norm_num
        _ = m := by ring
    exact lt_of_lt_of_le hgt hle

/-- **Existence of the angular half-width.**  For a strictly increasing,
nonempty list of directions in `(-π, π]` with positive wrap gap, there is a
positive `δ` such that consecutive directions are more than `2δ` apart and
the wrap gap exceeds `2δ`. -/
lemma exists_delta (xs : List ℝ) (hne : xs ≠ []) (hsorted : xs.SortedLT)
    (hIoc : ∀ x ∈ xs, x ∈ Set.Ioc (-Real.pi) Real.pi)
    (hwrap : 0 < wrapGap xs) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ (j : ℕ) (hj : j + 1 < xs.length),
        xs.get ⟨j + 1, hj⟩ - xs.get ⟨j, Nat.lt_trans (Nat.lt_succ_self j) hj⟩ > 2 * δ) ∧
      wrapGap xs > 2 * δ := by
  classical
  have hn : 0 < xs.length := length_pos_of_ne_nil hne
  -- the consecutive gaps, indexed by `Fin (xs.length - 1)`
  let gap : Fin (xs.length - 1) → ℝ := fun i =>
    xs.get ⟨i.val + 1, add_one_lt_of_lt_pred i.isLt hn⟩ - xs.get ⟨i.val, lt_of_lt_pred i.isLt⟩
  -- every consecutive gap plus the wrap gap (a finite set of reals)
  let S : Finset ℝ := (Finset.univ : Finset (Fin (xs.length - 1))).image gap ∪
    ({wrapGap xs} : Finset ℝ)
  have hSne : S.Nonempty := by
    refine ⟨wrapGap xs, ?_⟩
    simp [S]
  have hSpos : ∀ x ∈ S, 0 < x := by
    intro x hx
    dsimp [S] at hx
    rcases (Finset.mem_union.mp hx) with hx | hx
    · rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
      have hlt : xs.get ⟨i.val, lt_of_lt_pred i.isLt⟩ <
          xs.get ⟨i.val + 1, add_one_lt_of_lt_pred i.isLt hn⟩ :=
        get_lt_get_of_val_lt hsorted (lt_of_lt_pred i.isLt)
          (add_one_lt_of_lt_pred i.isLt hn) (Nat.lt_succ_self i.val)
      change 0 < xs.get ⟨i.val + 1, add_one_lt_of_lt_pred i.isLt hn⟩ -
          xs.get ⟨i.val, lt_of_lt_pred i.isLt⟩
      linarith
    · rw [Finset.mem_singleton.mp hx]
      exact hwrap
  rcases exists_delta_of_finset S hSne hSpos with ⟨δ, hδpos, hδall⟩
  refine ⟨δ, hδpos, ?_, ?_⟩
  · intro j hj
    have hjlt : j < xs.length - 1 := lt_pred_of_add_one_lt hj hn
    let i : Fin (xs.length - 1) := ⟨j, hjlt⟩
    have hmem : gap i ∈ S := by
      apply Finset.mem_union.mpr
      left
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    have hgt : 2 * δ < gap i := hδall (gap i) hmem
    change 2 * δ < xs.get ⟨j + 1, hj⟩ - xs.get ⟨j, Nat.lt_trans (Nat.lt_succ_self j) hj⟩
    simpa [gap, i] using hgt
  · exact hδall (wrapGap xs) (by simp [S])

/-- Existence with an extra upper bound `δ < ε` (shrinking below any later
fattening radius). -/
lemma exists_delta_lt (xs : List ℝ) (hne : xs ≠ []) (hsorted : xs.SortedLT)
    (hIoc : ∀ x ∈ xs, x ∈ Set.Ioc (-Real.pi) Real.pi)
    (hwrap : 0 < wrapGap xs) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
      (∀ (j : ℕ) (hj : j + 1 < xs.length),
        xs.get ⟨j + 1, hj⟩ - xs.get ⟨j, Nat.lt_trans (Nat.lt_succ_self j) hj⟩ > 2 * δ) ∧
      wrapGap xs > 2 * δ := by
  classical
  rcases exists_delta xs hne hsorted hIoc hwrap with ⟨δ, hδpos, hgap, hwrapδ⟩
  let d : ℝ := min δ (ε / 2)
  have hdpos : 0 < d := by
    dsimp [d]
    exact lt_min hδpos (by positivity)
  have hdlt : d < ε := by
    dsimp [d]
    have h1 : min δ (ε / 2) ≤ ε / 2 := min_le_right δ (ε / 2)
    have h2 : ε / 2 < ε := by linarith
    linarith
  refine ⟨d, hdpos, hdlt, ?_, ?_⟩
  · intro j hj
    have h1 : 2 * d ≤ 2 * δ := by
      dsimp [d]
      have hmin : min δ (ε / 2) ≤ δ := min_le_left δ (ε / 2)
      linarith
    exact lt_of_le_of_lt h1 (hgap j hj)
  · have h1 : 2 * d ≤ 2 * δ := by
      dsimp [d]
      have hmin : min δ (ε / 2) ≤ δ := min_le_left δ (ε / 2)
      linarith
    exact lt_of_le_of_lt h1 hwrapδ

end Submission.E2bParam

end
