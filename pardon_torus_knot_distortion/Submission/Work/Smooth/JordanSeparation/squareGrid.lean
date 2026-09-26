import Mathlib

/-!
# The square lemma from the finite `4`/`8` Hex duality (grid reduction)

Proved here: the *square lemma* follows from the finite `4`/`8` Hex duality
(`Submission.Work.Smooth.JordanSeparation.hex_duality_finite`), by a grid argument:

* `K1 := S1 ∩ Q`, `K2 := S2 ∩ Q`, `K := (S1 ∪ S2) ∩ Q` are compact, and each of the four pairs
  `(K1, L)`, `(K2, R)`, `(K, B ∪ T)`, `(K1, K2)` consists of disjoint compact (or closed) sets, so
  there is `ε > 0` smaller than all four distances (`exists_pos_dist_le_of_compact_closed`).
* Choose `N` with `2/N < ε`; the `N × N` grid of `cell N i j` has mesh `1/N`.
* Call a cell *blocked* if it meets `S := S1 ∪ S2`.  No blocked cell lies in the leftmost or
  rightmost column together with `S1`/`S2` (see `hnot1`, `hnot2` below), and a blocked `8`-chain
  from the leftmost to the rightmost column is impossible: extracting a point of `S` from each cell
  of the chain gives a sequence with steps `< ε` starting in `S2` (near the left edge) and ending
  in `S1` (near the right edge), so two consecutive points would lie in `S2 ∩ Q` and `S1 ∩ Q` at
  distance `< ε`, contradiction.
* Hence the Hex duality gives a `4`-chain of free cells from the bottom row to the top row; the
  union of those cells together with the bottom and top edges is preconnected, avoids `S`, and
  contains `(0,0)` and `(0,1)`.

This reduces the square lemma to the finite combinatorial statement `hexDuality` (see
`Submission.Work.Smooth.JordanSeparation.hexDualityHints`).
-/

namespace Work.Smooth.JordanSeparation

open Set Metric

noncomputable section

/-- The left edge of the unit square. -/
def sqLeft : Set (ℝ × ℝ) := ({0} : Set ℝ) ×ˢ Set.Icc (0:ℝ) 1

/-- The right edge of the unit square. -/
def sqRight : Set (ℝ × ℝ) := ({1} : Set ℝ) ×ˢ Set.Icc (0:ℝ) 1

/-- The bottom edge of the unit square. -/
def sqBot : Set (ℝ × ℝ) := Set.Icc (0:ℝ) 1 ×ˢ ({0} : Set ℝ)

/-- The top edge of the unit square. -/
def sqTop : Set (ℝ × ℝ) := Set.Icc (0:ℝ) 1 ×ˢ ({1} : Set ℝ)

/-- The unit square. -/
def sqUnit : Set (ℝ × ℝ) := Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1

/-- The `(i,j)`-th cell of the `N × N` grid of the unit square. -/
def cell (N : ℕ) (i j : Fin N) : Set (ℝ × ℝ) :=
  Set.Icc ((i:ℝ)/N) (((i:ℝ)+1)/N) ×ˢ Set.Icc ((j:ℝ)/N) (((j:ℝ)+1)/N)

/-- Casting an equality of naturals `m + 1 = n` to `ℝ`. -/
theorem nat_cast_eq_add_one {m n : ℕ} (h : m + 1 = n) : (n:ℝ) = (m:ℝ) + 1 := by
  have := congrArg (fun k : ℕ => (k:ℝ)) h
  push_cast at this
  linarith

theorem mem_sqLeft {p : ℝ × ℝ} : p ∈ sqLeft ↔ p.1 = 0 ∧ p.2 ∈ Set.Icc (0:ℝ) 1 := by
  rw [sqLeft, Set.mem_prod, Set.mem_singleton_iff, Set.mem_Icc]

theorem mem_sqRight {p : ℝ × ℝ} : p ∈ sqRight ↔ p.1 = 1 ∧ p.2 ∈ Set.Icc (0:ℝ) 1 := by
  rw [sqRight, Set.mem_prod, Set.mem_singleton_iff, Set.mem_Icc]

theorem mem_sqBot {p : ℝ × ℝ} : p ∈ sqBot ↔ p.1 ∈ Set.Icc (0:ℝ) 1 ∧ p.2 = 0 := by
  rw [sqBot, Set.mem_prod, Set.mem_singleton_iff, Set.mem_Icc]

theorem mem_sqTop {p : ℝ × ℝ} : p ∈ sqTop ↔ p.1 ∈ Set.Icc (0:ℝ) 1 ∧ p.2 = 1 := by
  rw [sqTop, Set.mem_prod, Set.mem_singleton_iff, Set.mem_Icc]

theorem mem_sqUnit {p : ℝ × ℝ} : p ∈ sqUnit ↔ p.1 ∈ Set.Icc (0:ℝ) 1 ∧ p.2 ∈ Set.Icc (0:ℝ) 1 := by
  rw [sqUnit, Set.mem_prod]

theorem isCompact_sqLeft : IsCompact sqLeft :=
  isCompact_singleton.prod isCompact_Icc

theorem isCompact_sqRight : IsCompact sqRight :=
  isCompact_singleton.prod isCompact_Icc

theorem isCompact_sqBot : IsCompact sqBot := isCompact_Icc.prod isCompact_singleton

theorem isCompact_sqTop : IsCompact sqTop := isCompact_Icc.prod isCompact_singleton

theorem isPreconnected_sqBot : IsPreconnected sqBot :=
  ((convex_Icc (0:ℝ) 1).prod (convex_singleton (0:ℝ))).isPreconnected

theorem isPreconnected_sqTop : IsPreconnected sqTop :=
  ((convex_Icc (0:ℝ) 1).prod (convex_singleton (1:ℝ))).isPreconnected

theorem isPreconnected_sqUnit : IsPreconnected sqUnit :=
  ((convex_Icc (0:ℝ) 1).prod (convex_Icc (0:ℝ) 1)).isPreconnected

theorem isPreconnected_cell {N : ℕ} (i j : Fin N) : IsPreconnected (cell N i j) :=
  ((convex_Icc _ _).prod (convex_Icc _ _)).isPreconnected

theorem isCompact_sqUnit : IsCompact sqUnit := isCompact_Icc.prod isCompact_Icc

/-- **Separation of a compact set from a disjoint closed set.** -/
theorem exists_pos_dist_le_of_compact_closed {A B : Set (ℝ × ℝ)}
    (hA : IsCompact A) (hB : IsClosed B) (hAB : Disjoint A B) :
    ∃ ε > 0, ∀ a ∈ A, ∀ b ∈ B, ε ≤ dist a b := by
  have hsub : A ⊆ Bᶜ := fun a ha => by
    rw [Set.mem_compl_iff]
    intro haB
    exact Set.disjoint_left.mp hAB ha haB
  obtain ⟨δ, hδ, hδsub⟩ := hA.exists_thickening_subset_open (isOpen_compl_iff.mpr hB) hsub
  refine ⟨δ, hδ, fun a ha b hb => ?_⟩
  by_contra hlt
  push_neg at hlt
  have hlt' : dist b a < δ := by rwa [dist_comm] at hlt
  exact hδsub (mem_thickening_iff.mpr ⟨a, ha, hlt'⟩) hb

/-- A cell of the grid is nonempty. -/
theorem cell_nonempty {N : ℕ} (hN : 0 < N) (i j : Fin N) : (cell N i j).Nonempty := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hi : (i:ℝ) + 1 ≤ (N:ℝ) := by
    have : (i:ℕ) + 1 ≤ N := Nat.succ_le_of_lt i.2
    exact_mod_cast this
  have hj : (j:ℝ) + 1 ≤ (N:ℝ) := by
    have : (j:ℕ) + 1 ≤ N := Nat.succ_le_of_lt j.2
    exact_mod_cast this
  refine ⟨(((i:ℝ) + 1) / N, ((j:ℝ) + 1) / N), ?_⟩
  rw [cell, Set.mem_prod]
  refine ⟨⟨?_, le_rfl⟩, ⟨?_, le_rfl⟩⟩
  · rw [div_le_div_iff₀ hNpos hNpos]; linarith
  · rw [div_le_div_iff₀ hNpos hNpos]; linarith

theorem cell_subset_sqUnit {N : ℕ} (hN : 0 < N) (i j : Fin N) : cell N i j ⊆ sqUnit := by
  intro p hp
  rw [cell, Set.mem_prod] at hp
  obtain ⟨h1, h2⟩ := hp
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hi1 : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg _
  have hj1 : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg _
  have hi2 : (i:ℝ) + 1 ≤ (N:ℝ) := by
    have : (i:ℕ) + 1 ≤ N := Nat.succ_le_of_lt i.2
    exact_mod_cast this
  have hj2 : (j:ℝ) + 1 ≤ (N:ℝ) := by
    have : (j:ℕ) + 1 ≤ N := Nat.succ_le_of_lt j.2
    exact_mod_cast this
  have hile : ((i:ℝ) + 1) / N ≤ 1 := by rw [div_le_one hNpos]; linarith
  have hjle : ((j:ℝ) + 1) / N ≤ 1 := by rw [div_le_one hNpos]; linarith
  rw [mem_sqUnit]
  exact ⟨⟨le_trans (div_nonneg hi1 hNpos.le) h1.1, le_trans h1.2 hile⟩,
         ⟨le_trans (div_nonneg hj1 hNpos.le) h2.1, le_trans h2.2 hjle⟩⟩

theorem cell_first_le {N : ℕ} (i j : Fin N) {p : ℝ × ℝ} (hp : p ∈ cell N i j) :
    p.1 ≤ ((i:ℝ) + 1) / N := (Set.mem_prod.mp hp).1.2

theorem cell_first_ge {N : ℕ} (i j : Fin N) {p : ℝ × ℝ} (hp : p ∈ cell N i j) :
    (i:ℝ) / N ≤ p.1 := (Set.mem_prod.mp hp).1.1

theorem cell_second_le {N : ℕ} (i j : Fin N) {p : ℝ × ℝ} (hp : p ∈ cell N i j) :
    p.2 ≤ ((j:ℝ) + 1) / N := (Set.mem_prod.mp hp).2.2

theorem cell_second_ge {N : ℕ} (i j : Fin N) {p : ℝ × ℝ} (hp : p ∈ cell N i j) :
    (j:ℝ) / N ≤ p.2 := (Set.mem_prod.mp hp).2.1

/-- Arithmetic helper: if `A/N ≤ a ≤ A'/N`, `B/N ≤ b ≤ B'/N` and `A' - B ≤ 2`, `B' - A ≤ 2`,
then `|a - b| ≤ 2/N`. -/
theorem abs_sub_le_two_div {N : ℕ} (hN : 0 < N) {a b A A' B B' : ℝ}
    (ha : A/N ≤ a) (ha' : a ≤ A'/N) (hb : B/N ≤ b) (hb' : b ≤ B'/N)
    (h1 : A' - B ≤ 2) (h2 : B' - A ≤ 2) : |a - b| ≤ 2/N := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  rw [abs_sub_le_iff]
  constructor
  · have hle : a - b ≤ A'/N - B/N := by linarith
    have heq : A'/N - B/N = (A' - B)/N := by rw [sub_div]
    rw [heq] at hle
    exact le_trans hle (div_le_div_of_nonneg_right h1 hNpos.le)
  · have hle : b - a ≤ B'/N - A/N := by linarith
    have heq : B'/N - A/N = (B' - A)/N := by rw [sub_div]
    rw [heq] at hle
    exact le_trans hle (div_le_div_of_nonneg_right h2 hNpos.le)

/-- Two points in `8`-adjacent cells are at distance at most `2/N` (max-metric on `ℝ × ℝ`). -/
theorem dist_le_of_cells {N : ℕ} (hN : 0 < N) {i j i' j' : Fin N} {p q : ℝ × ℝ}
    (hp : p ∈ cell N i j) (hq : q ∈ cell N i' j')
    (hi1 : (i':ℝ) ≤ (i:ℝ) + 1) (hi2 : (i:ℝ) ≤ (i':ℝ) + 1)
    (hj1 : (j':ℝ) ≤ (j:ℝ) + 1) (hj2 : (j:ℝ) ≤ (j':ℝ) + 1) :
    dist p q ≤ 2 / N := by
  rw [Prod.dist_eq, max_le_iff]
  refine ⟨?_, ?_⟩
  · rw [Real.dist_eq]
    exact abs_sub_le_two_div hN (cell_first_ge i j hp) (cell_first_le i j hp)
      (cell_first_ge i' j' hq) (cell_first_le i' j' hq) (by linarith) (by linarith)
  · rw [Real.dist_eq]
    exact abs_sub_le_two_div hN (cell_second_ge i j hp) (cell_second_le i j hp)
      (cell_second_ge i' j' hq) (cell_second_le i' j' hq) (by linarith) (by linarith)

/-- Cells of the `N × N` grid. -/
abbrev Cells (N : ℕ) := Fin N × Fin N

/-- Two cells share an edge. -/
def Adj4g {N : ℕ} (a b : Cells N) : Prop :=
  (a.1 = b.1 ∧ (a.2.1 + 1 = b.2.1 ∨ b.2.1 + 1 = a.2.1)) ∨
  (a.2 = b.2 ∧ (a.1.1 + 1 = b.1.1 ∨ b.1.1 + 1 = a.1.1))

/-- Two cells share an edge or a corner. -/
def Adj8g {N : ℕ} (a b : Cells N) : Prop :=
  (a.1 = b.1 ∨ a.1.1 + 1 = b.1.1 ∨ b.1.1 + 1 = a.1.1) ∧
  (a.2 = b.2 ∨ a.2.1 + 1 = b.2.1 ∨ b.2.1 + 1 = a.2.1)

/-- The finite Hex duality, as an explicit hypothesis. -/
def HexDuality : Prop :=
  ∀ {N : ℕ}, 0 < N → ∀ blocked : Cells N → Prop,
    (∃ m : ℕ, ∃ f : Fin (m + 1) → Cells N, (∀ i, ¬ blocked (f i)) ∧
        (∀ i : Fin m, Adj4g (f i.castSucc) (f i.succ)) ∧
        (f 0).2.1 = 0 ∧ (f (Fin.last m)).2.1 + 1 = N) ∨
    (∃ m : ℕ, ∃ f : Fin (m + 1) → Cells N, (∀ i, blocked (f i)) ∧
        (∀ i : Fin m, Adj8g (f i.castSucc) (f i.succ)) ∧
        (f 0).1.1 = 0 ∧ (f (Fin.last m)).1.1 + 1 = N)

/-- `8`-adjacent cells have indices differing by at most one in each coordinate. -/
theorem adj8_components {N : ℕ} {a b : Cells N} (h : Adj8g a b) :
    (b.1.1 : ℝ) ≤ (a.1.1 : ℝ) + 1 ∧ (a.1.1 : ℝ) ≤ (b.1.1 : ℝ) + 1 ∧
    (b.2.1 : ℝ) ≤ (a.2.1 : ℝ) + 1 ∧ (a.2.1 : ℝ) ≤ (b.2.1 : ℝ) + 1 := by
  have key : ∀ x y : ℕ, (x = y ∨ x + 1 = y ∨ y + 1 = x) →
      (y:ℝ) ≤ (x:ℝ) + 1 ∧ (x:ℝ) ≤ (y:ℝ) + 1 := by
    intro x y hxy
    rcases hxy with h | h | h
    · subst h; constructor <;> linarith
    · have hc : (y:ℝ) = (x:ℝ) + 1 := nat_cast_eq_add_one h
      constructor <;> linarith
    · have hc : (x:ℝ) = (y:ℝ) + 1 := nat_cast_eq_add_one h
      constructor <;> linarith
  obtain ⟨h1, h2⟩ := h
  have h1' : a.1.1 = b.1.1 ∨ a.1.1 + 1 = b.1.1 ∨ b.1.1 + 1 = a.1.1 := by
    rcases h1 with hh | hh | hh
    · exact Or.inl (by rw [hh])
    · exact Or.inr (Or.inl hh)
    · exact Or.inr (Or.inr hh)
  have h2' : a.2.1 = b.2.1 ∨ a.2.1 + 1 = b.2.1 ∨ b.2.1 + 1 = a.2.1 := by
    rcases h2 with hh | hh | hh
    · exact Or.inl (by rw [hh])
    · exact Or.inr (Or.inl hh)
    · exact Or.inr (Or.inr hh)
  obtain ⟨k1, k2⟩ := key a.1.1 b.1.1 h1'
  obtain ⟨k3, k4⟩ := key a.2.1 b.2.1 h2'
  exact ⟨k1, k2, k3, k4⟩

/-- Membership in a cell, unfolded. -/
theorem mem_cell_iff {N : ℕ} {i j : Fin N} {p : ℝ × ℝ} :
    p ∈ cell N i j ↔ (i:ℝ)/N ≤ p.1 ∧ p.1 ≤ ((i:ℝ)+1)/N ∧
      (j:ℝ)/N ≤ p.2 ∧ p.2 ≤ ((j:ℝ)+1)/N := by
  rw [cell, Set.mem_prod, Set.mem_Icc, Set.mem_Icc]
  tauto

/-- Two cells in the same column whose rows are adjacent meet. -/
theorem inter_nonempty_same_col {N : ℕ} {i j j' : Fin N}
    (h : j.1 + 1 = j'.1 ∨ j'.1 + 1 = j.1) :
    (cell N i j ∩ cell N i j').Nonempty := by
  have hNle : (0:ℝ) ≤ N := by positivity
  have key : ∀ x : ℕ, (x:ℝ) ≤ (x:ℝ) + 1 := fun x => by linarith
  rcases h with h | h
  · have hj : (j'.1 : ℝ) = (j.1 : ℝ) + 1 := nat_cast_eq_add_one h
    refine ⟨((i:ℝ)/N, ((j:ℝ)+1)/N), ?_, ?_⟩
    · rw [mem_cell_iff]
      exact ⟨le_rfl, div_le_div_of_nonneg_right (by linarith) hNle,
        div_le_div_of_nonneg_right (key j.1) hNle, le_rfl⟩
    · rw [mem_cell_iff, ← hj]
      exact ⟨le_rfl, div_le_div_of_nonneg_right (by linarith) hNle,
        le_rfl, div_le_div_of_nonneg_right (key _) hNle⟩
  · have hj : (j.1 : ℝ) = (j'.1 : ℝ) + 1 := nat_cast_eq_add_one h
    refine ⟨((i:ℝ)/N, ((j':ℝ)+1)/N), ?_, ?_⟩
    · rw [mem_cell_iff, ← hj]
      exact ⟨le_rfl, div_le_div_of_nonneg_right (by linarith) hNle,
        le_rfl, div_le_div_of_nonneg_right (key _) hNle⟩
    · rw [mem_cell_iff]
      exact ⟨le_rfl, div_le_div_of_nonneg_right (by linarith) hNle,
        div_le_div_of_nonneg_right (key j'.1) hNle, le_rfl⟩

/-- Two cells in the same row whose columns are adjacent meet. -/
theorem inter_nonempty_same_row {N : ℕ} {i i' j : Fin N}
    (h : i.1 + 1 = i'.1 ∨ i'.1 + 1 = i.1) :
    (cell N i j ∩ cell N i' j).Nonempty := by
  have hNle : (0:ℝ) ≤ N := by positivity
  have key : ∀ x : ℕ, (x:ℝ) ≤ (x:ℝ) + 1 := fun x => by linarith
  rcases h with h | h
  · have hi : (i'.1 : ℝ) = (i.1 : ℝ) + 1 := nat_cast_eq_add_one h
    refine ⟨(((i:ℝ)+1)/N, (j:ℝ)/N), ?_, ?_⟩
    · rw [mem_cell_iff]
      exact ⟨div_le_div_of_nonneg_right (key i.1) hNle, le_rfl, le_rfl,
        div_le_div_of_nonneg_right (by linarith) hNle⟩
    · rw [mem_cell_iff, ← hi]
      exact ⟨le_rfl, div_le_div_of_nonneg_right (key _) hNle, le_rfl,
        div_le_div_of_nonneg_right (by linarith) hNle⟩
  · have hi : (i.1 : ℝ) = (i'.1 : ℝ) + 1 := nat_cast_eq_add_one h
    refine ⟨(((i':ℝ)+1)/N, (j:ℝ)/N), ?_, ?_⟩
    · rw [mem_cell_iff, ← hi]
      exact ⟨le_rfl, div_le_div_of_nonneg_right (key _) hNle, le_rfl,
        div_le_div_of_nonneg_right (by linarith) hNle⟩
    · rw [mem_cell_iff]
      exact ⟨div_le_div_of_nonneg_right (key i'.1) hNle, le_rfl, le_rfl,
        div_le_div_of_nonneg_right (by linarith) hNle⟩

/-- `4`-adjacent cells meet. -/
theorem inter_nonempty_of_adj4 {N : ℕ} {a b : Cells N} (h : Adj4g a b) :
    (cell N a.1 a.2 ∩ cell N b.1 b.2).Nonempty := by
  rcases h with ⟨h1, h2⟩ | ⟨h2, h1⟩
  · rw [← h1]
    exact inter_nonempty_same_col h2
  · rw [Set.inter_comm, ← h2]
    exact inter_nonempty_same_row (h1.elim Or.inr Or.inl)

/-- A `4`-chain of sets (indexed by `Fin (n+1)`) whose consecutive members meet has a
preconnected union. -/
theorem isPreconnected_iUnion_range {n : ℕ} {u : Fin (n + 1) → Set (ℝ × ℝ)}
    (h : ∀ i, IsPreconnected (u i)) (hne : ∀ i : Fin n, (u i.castSucc ∩ u i.succ).Nonempty) :
    IsPreconnected (⋃ i, u i) := by
  induction n with
  | zero =>
      have h1 : (⋃ i : Fin 1, u i) = u 0 := by
        ext x
        rw [mem_iUnion]
        exact ⟨fun ⟨i, hi⟩ => by rwa [Subsingleton.elim i 0] at hi, fun hx => ⟨0, hx⟩⟩
      rw [h1]; exact h 0
  | succ n ih =>
      have hcast : IsPreconnected (⋃ i : Fin (n + 1), u i.castSucc) := by
        refine ih (u := fun i : Fin (n + 1) => u i.castSucc) (fun i => h _) (fun i => ?_)
        have hh := hne i.castSucc
        rw [Fin.castSucc_succ]
        exact hh
      have hattach : ((⋃ i : Fin (n + 1), u i.castSucc) ∩ u (Fin.last (n + 1))).Nonempty := by
        obtain ⟨y, hy⟩ := hne (Fin.last n)
        refine ⟨y, mem_iUnion.mpr ⟨Fin.last n, ?_⟩, ?_⟩
        · simpa using hy.1
        · exact Fin.succ_last n ▸ hy.2
      have hdec : (⋃ i : Fin (n + 2), u i)
          = (⋃ i : Fin (n + 1), u i.castSucc) ∪ u (Fin.last (n + 1)) := by
        ext x
        simp only [mem_union, mem_iUnion]
        constructor
        · rintro ⟨i, hi⟩
          rcases Fin.eq_castSucc_or_eq_last i with ⟨k, rfl⟩ | rfl
          · exact Or.inl ⟨k, hi⟩
          · exact Or.inr hi
        · rintro (⟨k, hk⟩ | hi)
          · exact ⟨k.castSucc, hk⟩
          · exact ⟨Fin.last (n+1), hi⟩
      rw [hdec]
      exact hcast.union _ hattach.choose_spec.1 hattach.choose_spec.2 (h _)


/-- Consecutive points of an `8`-chain of blocked cells of the grid have distance `< ε`. -/
theorem dist_lt_of_adj8 {N : ℕ} (hN : 0 < N) {ε : ℝ} (hNlt : 2/N < ε)
    {a b : Cells N} (h : Adj8g a b) {p q : ℝ × ℝ}
    (hp : p ∈ cell N a.1 a.2) (hq : q ∈ cell N b.1 b.2) : dist p q < ε := by
  obtain ⟨h1, h2, h3, h4⟩ := adj8_components h
  exact lt_of_le_of_lt (dist_le_of_cells hN hp hq h1 h2 h3 h4) hNlt

/-- **The square lemma from the finite Hex duality.** -/
theorem squareLemma_of_hex (hex : HexDuality) {S1 S2 : Set (ℝ × ℝ)}
    (h1c : IsClosed S1) (h2c : IsClosed S2) (hdisj : Disjoint S1 S2)
    (hL : S1 ∩ sqLeft = ∅) (hR : S2 ∩ sqRight = ∅)
    (hB : (S1 ∪ S2) ∩ sqBot = ∅) (hT : (S1 ∪ S2) ∩ sqTop = ∅) :
    ((0,1) : ℝ × ℝ) ∈ connectedComponentIn (S1 ∪ S2)ᶜ ((0,0) : ℝ × ℝ) := by
  classical
  have hSc : IsClosed (S1 ∪ S2) := h1c.union h2c
  have hK1 : IsCompact (S1 ∩ sqUnit) := by rw [Set.inter_comm]; exact isCompact_sqUnit.inter_right h1c
  have hK2 : IsCompact (S2 ∩ sqUnit) := by rw [Set.inter_comm]; exact isCompact_sqUnit.inter_right h2c
  have hKu : IsCompact ((S1 ∪ S2) ∩ sqUnit) := by
    rw [Set.inter_comm]; exact isCompact_sqUnit.inter_right hSc
  have hd1 : Disjoint (S1 ∩ sqUnit) sqLeft := by
    rw [Set.disjoint_left]
    rintro x ⟨hx1, -⟩ hxL
    exact (Set.eq_empty_iff_forall_notMem.mp hL) x ⟨hx1, hxL⟩
  have hd2 : Disjoint (S2 ∩ sqUnit) sqRight := by
    rw [Set.disjoint_left]
    rintro x ⟨hx2, -⟩ hxR
    exact (Set.eq_empty_iff_forall_notMem.mp hR) x ⟨hx2, hxR⟩
  have hd3 : Disjoint ((S1 ∪ S2) ∩ sqUnit) (sqBot ∪ sqTop) := by
    rw [Set.disjoint_left]
    rintro x ⟨hxS, -⟩ (hxB | hxT)
    · exact (Set.eq_empty_iff_forall_notMem.mp hB) x ⟨hxS, hxB⟩
    · exact (Set.eq_empty_iff_forall_notMem.mp hT) x ⟨hxS, hxT⟩
  have hd4 : Disjoint (S1 ∩ sqUnit) (S2 ∩ sqUnit) := by
    rw [Set.disjoint_left]
    rintro x ⟨hx1, -⟩ ⟨hx2, -⟩
    exact Set.disjoint_left.mp hdisj hx1 hx2
  obtain ⟨e1, he1, hs1⟩ :=
    exists_pos_dist_le_of_compact_closed hK1 isCompact_sqLeft.isClosed hd1
  obtain ⟨e2, he2, hs2⟩ :=
    exists_pos_dist_le_of_compact_closed hK2 isCompact_sqRight.isClosed hd2
  obtain ⟨e3, he3, hs3⟩ :=
    exists_pos_dist_le_of_compact_closed hKu (isCompact_sqBot.union isCompact_sqTop).isClosed hd3
  obtain ⟨e4, he4, hs4⟩ := exists_pos_dist_le_of_compact_closed hK1 hK2.isClosed hd4
  set ε : ℝ := min (min e1 e2) (min e3 e4) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]
    exact lt_min (lt_min he1 he2) (lt_min he3 he4)
  have hε1 : ε ≤ e1 := by
    rw [hεdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hε2 : ε ≤ e2 := by
    rw [hεdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hε4 : ε ≤ e4 := by
    rw [hεdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  obtain ⟨N, hNpos, hNlt⟩ : ∃ N : ℕ, 0 < N ∧ (2:ℝ)/N < ε := by
    obtain ⟨k, hk⟩ := exists_nat_gt (2/ε)
    have hkpos : (0:ℝ) < (k:ℝ) := lt_trans (by positivity) hk
    refine ⟨k, by exact_mod_cast hkpos, ?_⟩
    have h2 : (2:ℝ) < ε * (k:ℝ) := by
      have h3 : (2/ε) * ε < (k:ℝ) * ε := mul_lt_mul_of_pos_right hk hεpos
      have h4 : (2/ε) * ε = 2 := div_mul_cancel₀ 2 (ne_of_gt hεpos)
      linarith
    rw [div_lt_iff₀ hkpos]
    linarith
  have hNposR : (0:ℝ) < N := by exact_mod_cast hNpos
  have hNle : (0:ℝ) ≤ N := hNposR.le
  have hNne : (N:ℝ) ≠ 0 := ne_of_gt hNposR
  set blocked : Cells N → Prop :=
    fun c => (cell N c.1 c.2 ∩ (S1 ∪ S2)).Nonempty with hblocked
  rcases hex hNpos blocked with
    ⟨m, f, hfree, hadj4, h0row, hlastrow⟩ | ⟨m, f, hblk, hadj8, h0col, hlastcol⟩
  · -- free cells: build the connecting preconnected set
    have hfree' : ∀ i : Fin (m+1), cell N (f i).1 (f i).2 ∩ (S1 ∪ S2) = ∅ := by
      intro i
      have h := hfree i
      rw [hblocked] at h
      exact Set.not_nonempty_iff_eq_empty.mp h
    have hUpre : IsPreconnected (⋃ i, cell N (f i).1 (f i).2) :=
      isPreconnected_iUnion_range (fun i => isPreconnected_cell _ _)
        (fun i => inter_nonempty_of_adj4 (hadj4 i))
    have hBotc : (((f 0).1.1 : ℝ)/N, (0:ℝ)) ∈ cell N (f 0).1 (f 0).2 := by
      have hj : ((f 0).2.1 : ℝ) = 0 := by rw [h0row]; simp
      rw [mem_cell_iff]
      refine ⟨le_rfl, div_le_div_of_nonneg_right (by linarith) hNle, ?_, ?_⟩
      · rw [hj]; simp
      · rw [hj]; positivity
    have hBotsq : (((f 0).1.1 : ℝ)/N, (0:ℝ)) ∈ sqBot := by
      rw [mem_sqBot]
      refine ⟨⟨by positivity, ?_⟩, rfl⟩
      rw [div_le_one hNposR]
      exact_mod_cast le_of_lt (f 0).1.2
    have hTopc : (((f (Fin.last m)).1.1 : ℝ)/N, (1:ℝ))
        ∈ cell N (f (Fin.last m)).1 (f (Fin.last m)).2 := by
      have hj : ((f (Fin.last m)).2.1 : ℝ) = (N:ℝ) - 1 := by
        have hc1 : (f (Fin.last m)).2.1 + 1 = N := hlastrow
        have hc2 : (N:ℝ) = ((f (Fin.last m)).2.1 : ℝ) + 1 := nat_cast_eq_add_one hc1
        linarith
      rw [mem_cell_iff]
      refine ⟨le_rfl, div_le_div_of_nonneg_right (by linarith) hNle, ?_, ?_⟩
      · rw [hj]
        rw [div_le_one hNposR]
        linarith
      · rw [hj]
        rw [show ((N:ℝ) - 1) + 1 = N by ring, div_self hNne]
    have hTopsq : (((f (Fin.last m)).1.1 : ℝ)/N, (1:ℝ)) ∈ sqTop := by
      rw [mem_sqTop]
      refine ⟨⟨by positivity, ?_⟩, rfl⟩
      rw [div_le_one hNposR]
      exact_mod_cast le_of_lt (f (Fin.last m)).1.2
    have hZpre : IsPreconnected
        (((⋃ i, cell N (f i).1 (f i).2) ∪ sqBot) ∪ sqTop) := by
      have h1 : IsPreconnected ((⋃ i, cell N (f i).1 (f i).2) ∪ sqBot) :=
        hUpre.union (((f 0).1.1 : ℝ)/N, (0:ℝ))
          (mem_iUnion.mpr ⟨0, hBotc⟩) hBotsq isPreconnected_sqBot
      exact h1.union (((f (Fin.last m)).1.1 : ℝ)/N, (1:ℝ))
        (Or.inl (mem_iUnion.mpr ⟨Fin.last m, hTopc⟩)) hTopsq isPreconnected_sqTop
    have hZsub : (((⋃ i, cell N (f i).1 (f i).2) ∪ sqBot) ∪ sqTop) ⊆ (S1 ∪ S2)ᶜ := by
      rintro p ((hpU | hpB) | hpT)
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hpU
        rw [Set.mem_compl_iff]
        intro hpS
        exact (Set.eq_empty_iff_forall_notMem.mp (hfree' i)) p ⟨hi, hpS⟩
      · rw [mem_sqBot] at hpB
        rw [Set.mem_compl_iff]
        intro hpS
        exact (Set.eq_empty_iff_forall_notMem.mp hB) p ⟨hpS, hpB⟩
      · rw [mem_sqTop] at hpT
        rw [Set.mem_compl_iff]
        intro hpS
        exact (Set.eq_empty_iff_forall_notMem.mp hT) p ⟨hpS, hpT⟩
    have hZ00 : ((0,0) : ℝ × ℝ) ∈ ((⋃ i, cell N (f i).1 (f i).2) ∪ sqBot) ∪ sqTop :=
      Or.inl (Or.inr (by rw [mem_sqBot]; exact ⟨⟨le_rfl, zero_le_one⟩, rfl⟩))
    have hZ01 : ((0,1) : ℝ × ℝ) ∈ ((⋃ i, cell N (f i).1 (f i).2) ∪ sqBot) ∪ sqTop :=
      Or.inr (by rw [mem_sqTop]; exact ⟨⟨le_rfl, zero_le_one⟩, rfl⟩)
    exact (hZpre.subset_connectedComponentIn hZ00 hZsub) hZ01
  · -- blocked cells: contradiction
    choose x hx using fun i => by
      have h := hblk i
      rw [hblocked] at h
      exact h
    have hxS : ∀ i : Fin (m+1), x i ∈ S1 ∪ S2 := fun i => (hx i).2
    have hxU : ∀ i : Fin (m+1), x i ∈ sqUnit := fun i =>
      cell_subset_sqUnit hNpos _ _ (hx i).1
    have hx0 : x 0 ∉ S1 := by
      intro hmem
      have hc := (hx 0).1
      have hK : x 0 ∈ S1 ∩ sqUnit := ⟨hmem, hxU 0⟩
      have hL' : ((0, (x 0).2) : ℝ × ℝ) ∈ sqLeft := by
        rw [mem_sqLeft]
        exact ⟨rfl, (mem_sqUnit.mp (hxU 0)).2⟩
      have hge : (0:ℝ) ≤ (x 0).1 := by
        have h2 := cell_first_ge (f 0).1 (f 0).2 hc
        have h3 : ((f 0).1.1 : ℝ) = 0 := by rw [h0col]; simp
        rw [h3] at h2
        simpa using h2
      have hdist : dist (x 0) ((0, (x 0).2) : ℝ × ℝ) ≤ 1/N := by
        rw [Prod.dist_eq, max_le_iff]
        constructor
        · rw [Real.dist_eq, sub_zero, abs_of_nonneg hge]
          have h2 := cell_first_le (f 0).1 (f 0).2 hc
          have h3 : ((f 0).1.1 : ℝ) = 0 := by rw [h0col]; simp
          rw [h3] at h2
          simpa using h2
        · rw [dist_self]; positivity
      have h := hs1 (x 0) hK ((0, (x 0).2) : ℝ × ℝ) hL'
      have h1N : (1:ℝ)/N < ε := by
        have h2 : (1:ℝ) ≤ 2 := by norm_num
        have h3 : (1:ℝ)/N ≤ 2/N := div_le_div_of_nonneg_right h2 hNle
        linarith
      linarith [h, hdist, hε1, h1N]
    have hxlast : x (Fin.last m) ∉ S2 := by
      intro hmem
      have hc := (hx (Fin.last m)).1
      have hK : x (Fin.last m) ∈ S2 ∩ sqUnit := ⟨hmem, hxU (Fin.last m)⟩
      have hL' : ((1, (x (Fin.last m)).2) : ℝ × ℝ) ∈ sqRight := by
        rw [mem_sqRight]
        exact ⟨rfl, (mem_sqUnit.mp (hxU (Fin.last m))).2⟩
      have hz : ((f (Fin.last m)).1.1 : ℝ) = (N:ℝ) - 1 := by
        have hc1 : (f (Fin.last m)).1.1 + 1 = N := hlastcol
        have hc2 : (N:ℝ) = ((f (Fin.last m)).1.1 : ℝ) + 1 := nat_cast_eq_add_one hc1
        linarith
      have hdist : dist (x (Fin.last m)) ((1, (x (Fin.last m)).2) : ℝ × ℝ) ≤ 1/N := by
        rw [Prod.dist_eq, max_le_iff]
        constructor
        · rw [Real.dist_eq]
          have h2 := cell_first_le (f (Fin.last m)).1 (f (Fin.last m)).2 hc
          have h3 : (((f (Fin.last m)).1.1 : ℝ) + 1)/N
              = ((f (Fin.last m)).1.1 : ℝ)/N + 1/N := by ring
          rw [h3] at h2
          have h4 : ((f (Fin.last m)).1.1 : ℝ)/N + 1/N = 1 := by
            rw [hz]
            rw [show ((N:ℝ) - 1)/N + 1/N = ((N:ℝ) - 1 + 1)/N by ring]
            rw [show ((N:ℝ) - 1) + 1 = N by ring, div_self hNne]
          rw [h4] at h2
          have h5 : (1:ℝ) - 1/N ≤ (x (Fin.last m)).1 := by
            have h6 := cell_first_ge (f (Fin.last m)).1 (f (Fin.last m)).2 hc
            rw [hz] at h6
            rw [sub_div, div_self hNne] at h6
            linarith
          rw [abs_of_nonpos (by linarith)]
          linarith
        · rw [dist_self]; positivity
      have h := hs2 (x (Fin.last m)) hK ((1, (x (Fin.last m)).2) : ℝ × ℝ) hL'
      have h1N : (1:ℝ)/N < ε := by
        have h2 : (1:ℝ) ≤ 2 := by norm_num
        have h3 : (1:ℝ)/N ≤ 2/N := div_le_div_of_nonneg_right h2 hNle
        linarith
      linarith [h, hdist, hε2, h1N]
    have hstep : ∀ i : Fin m, x i.castSucc ∈ S2 → x i.succ ∈ S2 := by
      intro i hi2
      by_contra hcon
      have hi1 : x i.succ ∈ S1 := by
        rcases hxS i.succ with h | h
        · exact h
        · exact absurd h hcon
      have hK2' : x i.castSucc ∈ S2 ∩ sqUnit := ⟨hi2, hxU i.castSucc⟩
      have hK1' : x i.succ ∈ S1 ∩ sqUnit := ⟨hi1, hxU i.succ⟩
      have hdist : dist (x i.succ) (x i.castSucc) ≤ 2/N := by
        obtain ⟨g1, g2, g3, g4⟩ := adj8_components (hadj8 i)
        exact dist_le_of_cells hNpos (hx i.succ).1 (hx i.castSucc).1 g2 g1 g4 g3
      have h := hs4 (x i.succ) hK1' (x i.castSucc) hK2'
      linarith [h, hdist, hε4, hNlt]
    have hall : ∀ i : Fin (m+1), x i ∈ S2 := by
      intro i
      induction i using Fin.induction with
      | zero =>
          rcases hxS 0 with h | h
          · exact absurd h hx0
          · exact h
      | succ i ih => exact hstep i ih
    exact absurd (hall (Fin.last m)) hxlast

end

end Work.Smooth.JordanSeparation
