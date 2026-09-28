import Mathlib
import Submission.Work.RatHurewicz.Triad.Rule
import Submission.Work.ThomBordism.TwoSet.Subdivision

/-!
# The two-set labelling of the grid cells

Given an open cover `X = B ∪ C` of a space `X` and a continuous map `Φ : I^j → X`, the Lebesgue
subdivision `Work.ThomBordism.TwoSet.Subdivision` provides `N ≥ 1` such that every closed *box*
of the `N`-grid of `I^j` is mapped by `Φ` into `B` or into `C`.  Every *cell* of the `N`-grid
(in the sense of `Work.ThomBordism.TwoSet.CellIdx`, i.e. a product of grid intervals and grid
points) is contained in a box, so the box labelling descends to the cells: this is
`twoSetLabel`.

It is the existence half of the "labelling data" used by the preparation theorem of the triad
argument (see `Triad/Rule.lean` and `Triad/NOTES_triadCompression.md`); the per-cell rule of the
induction is stated in terms of the *properties* `CellB`/`CellC` precisely because the two-set
labelling carries no face compatibility.

The containment of a cell in a box is proved here rather than imported from
`Work.ThomBordism.TwoSet.Setup` because the latter (through `TwoSet.Process`, `...SpreadDefs`)
cannot be imported together with `Triad.Rule` (`TwoSet.SpreadDefs` and `Triad.SpreadDefs` declare
the same constant `Work.ThomBordism.TwoSet.pushT`).
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

open Work.ThomBordism.TwoSet

/-- **Every cell of the `N`-grid is contained in a box of the `N`-grid.**  With the box
`m i := min (N-1) (c.lo i)`: the lower end is `≤ c.lo i`, and the upper end is either `c.lo i`
(if `c.lo i ≤ N-1`, so that `c.hi i ≤ c.lo i + 1` finishes) or `N-1` (if `c.lo i = N`, in which
case every point of the cell has coordinate `1`). -/
theorem exists_box_of_cellSet_sub {j N : ℕ} (hN : 1 ≤ N) (c : CellIdx j N) :
    ∃ m : Fin j → Fin N, ∀ y : IC j, y ∈ cellSet c →
      ∀ i, (m i : ℝ) ≤ (N : ℝ) * (y i : ℝ) ∧ (N : ℝ) * (y i : ℝ) ≤ (m i : ℝ) + 1 := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  let m : Fin j → Fin N :=
    fun i => ⟨min (N - 1) (c.lo i), lt_of_le_of_lt (Nat.min_le_left _ _) (by omega)⟩
  refine ⟨m, fun y hy i => ?_⟩
  have hyc := hy i
  have hmval : ((m i : ℕ) : ℝ) = ((min (N - 1) (c.lo i) : ℕ) : ℝ) := rfl
  rw [hmval]
  have h1 : ((min (N - 1) (c.lo i) : ℕ) : ℝ) ≤ (c.lo i : ℝ) := by
    exact_mod_cast Nat.min_le_right (N - 1) (c.lo i)
  constructor
  · have h3 := (div_le_iff₀ hNpos).mp hyc.1
    nlinarith [h1, h3]
  · rcases le_or_gt (c.lo i) (N - 1) with h | h
    · have hmin : min (N - 1) (c.lo i) = c.lo i := min_eq_right h
      rw [hmin]
      have h4 := (le_div_iff₀ hNpos).mp hyc.2
      have hhi : (c.hi i : ℝ) ≤ (c.lo i : ℝ) + 1 := by
        have hs := c.hstep i
        have : (c.hi i : ℝ) ≤ ((c.lo i + 1 : ℕ) : ℝ) := by exact_mod_cast hs
        push_cast at this; linarith
      linarith
    · have hmin : min (N - 1) (c.lo i) = N - 1 := min_eq_left (le_of_lt h)
      rw [hmin]
      have hy1 : (y i : ℝ) ≤ 1 := (y i).2.2
      have hcast : (((N - 1 : ℕ)) : ℝ) = (N : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ N)]; norm_num
      rw [hcast]
      nlinarith

theorem twoSetLabel {X : Type} [TopologicalSpace X] {B C : Set X} (hB : IsOpen B) (hC : IsOpen C)
    (hBC : B ∪ C = Set.univ) {j : ℕ} (Φ : C(Work.ThomBordism.TwoSet.IC j, X)) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ c : Work.ThomBordism.TwoSet.CellIdx j N,
      Work.RatHurewicz.Triad.CellB B Φ c ∨ Work.RatHurewicz.Triad.CellC C Φ c := by
  classical
  obtain ⟨N, hN, hlab⟩ := Subdivision hB hC hBC Φ
  refine ⟨N, hN, fun c => ?_⟩
  obtain ⟨m, hm⟩ := exists_box_of_cellSet_sub hN c
  rcases hlab m with h | h
  · exact Or.inl fun z hz => h z (hm z hz)
  · exact Or.inr fun z hz => h z (hm z hz)

end Work.RatHurewicz
