import Mathlib
import Submission.Work.ThomBordism.TwoSet.exists_cellHomeo
import Submission.Work.RatHurewicz.Triad.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Definitions for the grid induction of the preparation theorem (tom Dieck 6.9.2)

This file contains only *definitions* (plus the trivial monotonicity lemmas); the lemmas about
them are proved elsewhere.  See `Triad/NOTES_triadCompression.md`, session 12, for the design.

* `Lab`, `labelSet`, `LabGood` — the three-fold labelling of the grid cells coming from the
  Lebesgue subdivision for the open cover `{B ∩ C, B ∖ C, C ∖ B}` of `X`, together with the two
  properties that are used by the induction: `Φ` maps a cell into the label's set, and the
  labelling is compatible with taking subcells.
* `SmallIn`, `LargeIn`, `KW`, `GW` — the cell-local (ambient-index) "half of the grid interval"
  conditions.  They are the weaker (pointwise, `Fin j`-indexed) relatives of
  `Work.RatHurewicz.Triad.IsSmall`/`IsLarge`, chosen so that they transfer along the flow
  (`Triad/NOTES_triadCompression.md`, session 12, "Transfer") and so that the owner of a point
  turns them into `IsSmall`/`IsLarge` (`SmallIn_cOf_iff` below).
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz.Triad

open Work.ThomBordism.TwoSet

noncomputable section

/-- The three labels of a grid cell in the triad picture: `U` = the cell is mapped into
`B ∩ C`, `V` = into `B ∖ C`, `W` = into `C ∖ B`. -/
inductive Lab where
  | U : Lab
  | V : Lab
  | W : Lab
  deriving DecidableEq

/-- The set of values corresponding to a label. -/
def labelSet {X : Type} (B C : Set X) : Lab → Set X
  | Lab.U => B ∩ C
  | Lab.V => B \ C
  | Lab.W => C \ B

/-- **The labelling data.**  `label` is a labelling of the cells of the `N`-grid which is
`Φ`-compatible (each cell is mapped into the label's set) and compatible with subcells.  The
existence of such a labelling from the Lebesgue subdivision is `exists_gridLabel`. -/
def LabGood {X : Type} [TopologicalSpace X] {j N : ℕ} (B C : Set X)
    (Φ : C(IC j, X)) (label : CellIdx j N → Lab) : Prop :=
  (∀ c : CellIdx j N, ∀ z : IC j, z ∈ cellSet c → Φ z ∈ labelSet B C (label c)) ∧
  (∀ c c' : CellIdx j N, (∀ i, c.lo i ≤ c'.lo i ∧ c'.hi i ≤ c.hi i) →
    (label c = Lab.U → label c' = Lab.U) ∧
    (label c = Lab.V → label c' = Lab.U ∨ label c' = Lab.V) ∧
    (label c = Lab.W → label c' = Lab.U ∨ label c' = Lab.W))

/-- **The lower-half condition in the ambient direction `i`.**  For `z ∈ cellSet c` and `i` an
interval direction of `c` this says that the local coordinate of `z` in direction `i` is `< 1/2`
(and it forces `z` to be far from the upper end of the grid interval). -/
def SmallIn (N : ℕ) {j : ℕ} (c : CellIdx j N) (z : IC j) (i : Fin j) : Prop :=
  c.lo i < c.hi i ∧ (N : ℝ) * (z i : ℝ) < (c.lo i : ℝ) + 1 / 2

/-- **The upper-half condition in the ambient direction `i`.** -/
def LargeIn (N : ℕ) {j : ℕ} (c : CellIdx j N) (z : IC j) (i : Fin j) : Prop :=
  c.lo i < c.hi i ∧ (c.lo i : ℝ) + 1 / 2 < (N : ℝ) * (z i : ℝ)

/-- **The `K`-witnesses of a cell at a point**: at least `P` ambient directions satisfying
`SmallIn`. -/
def KW (N P : ℕ) {j : ℕ} (c : CellIdx j N) (z : IC j) : Prop :=
  ∃ L : Finset (Fin j), P ≤ L.card ∧ ∀ i ∈ L, SmallIn N c z i

/-- **The `G`-witnesses of a cell at a point**: at least `P` ambient directions satisfying
`LargeIn`. -/
def GW (N P : ℕ) {j : ℕ} (c : CellIdx j N) (z : IC j) : Prop :=
  ∃ L : Finset (Fin j), P ≤ L.card ∧ ∀ i ∈ L, LargeIn N c z i

/-- A `KW`-witness set of a smaller size may be enlarged: this is the form in which the `K`-trick
conclusions (with `P = p+2`) are converted into the pointwise statements of `triadUrysohn`
(with `p+1` space directions). -/
theorem KW_mono {N P P' : ℕ} {j : ℕ} {c : CellIdx j N} {z : IC j} (h : P' ≤ P)
    (H : KW N P c z) : KW N P' c z :=
  ⟨H.choose, le_trans h H.choose_spec.1, H.choose_spec.2⟩

theorem GW_mono {N P P' : ℕ} {j : ℕ} {c : CellIdx j N} {z : IC j} (h : P' ≤ P)
    (H : GW N P c z) : GW N P' c z :=
  ⟨H.choose, le_trans h H.choose_spec.1, H.choose_spec.2⟩

/-- `SmallIn` at an interval direction of a cell is a statement about the *interval* of the cell,
so it is inherited by any cell with the same coordinate interval in that direction. -/
theorem SmallIn_of_eq {N : ℕ} {j : ℕ} {c c' : CellIdx j N} {z : IC j} {i : Fin j}
    (hlo : c.lo i = c'.lo i) (hhi : c.hi i = c'.hi i) (h : SmallIn N c z i) :
    SmallIn N c' z i := by
  obtain ⟨hlt, hhalf⟩ := h
  refine ⟨?_, ?_⟩
  · rw [← hlo, ← hhi]; exact hlt
  · rw [← hlo]; exact hhalf

theorem LargeIn_of_eq {N : ℕ} {j : ℕ} {c c' : CellIdx j N} {z : IC j} {i : Fin j}
    (hlo : c.lo i = c'.lo i) (hhi : c.hi i = c'.hi i) (h : LargeIn N c z i) :
    LargeIn N c' z i := by
  obtain ⟨hlt, hhalf⟩ := h
  refine ⟨?_, ?_⟩
  · rw [← hlo, ← hhi]; exact hlt
  · rw [← hlo]; exact hhalf

/-- **The pointwise conditions at the owner of a point.**  `SmallIn` at the cell `cOf N z` is
exactly `IsSmall`: `(cOf N z).lo i = ⌊N zᵢ⌋₊`, the interval condition says `N zᵢ ∉ ℤ`, and the
half condition says `N zᵢ < ⌊N zᵢ⌋₊ + 1/2`. -/
theorem isSmall_of_smallIn_cOf {N : ℕ} {j : ℕ} {z : IC j} {i : Fin j}
    (h : SmallIn N (cOf N z) z i) : IsSmall N z i := by
  obtain ⟨hlt, hhalf⟩ := h
  have hlt' : ⌊(N : ℝ) * (z i : ℝ)⌋₊ < ⌈(N : ℝ) * (z i : ℝ)⌉₊ := by
    simpa only [cOf_lo, cOf_hi] using hlt
  refine ⟨?_, ?_⟩
  · intro hcon
    have h2 : ⌈(N : ℝ) * (z i : ℝ)⌉₊ = ⌊(N : ℝ) * (z i : ℝ)⌋₊ := by
      conv_lhs => rw [hcon]
      exact Nat.ceil_natCast (R := ℝ) _
    omega
  · simpa only [cOf_lo] using hhalf

theorem isLarge_of_largeIn_cOf {N : ℕ} {j : ℕ} {z : IC j} {i : Fin j}
    (h : LargeIn N (cOf N z) z i) : IsLarge N z i := by
  simpa only [cOf_lo, LargeIn, IsLarge] using h.2

end

end Work.RatHurewicz.Triad
