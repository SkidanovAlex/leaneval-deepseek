import Mathlib
import Submission.Work.ThomBordism.TwoSet.Cells

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The cutoffs of the spreading construction

For a grid cell `c` of the `N`-grid (`N ≥ 1`) we build:

* `cellDist c : I^j → ℝ`, measuring how far (in `N`-scaled units) the coordinates of a point are
  from the coordinate intervals of `c`; it vanishes exactly on `cellSet c`;
* `sigOf c : I^j → [0,1]`, the "junction time", vanishing exactly on `cellSet c`;
* `lamOf c : I^j → [0,1]`, the "drag amplitude", equal to `1` wherever `sigOf c < 1`, and vanishing
  as soon as `cellDist c ≥ 1/4`.

On the support of `lamOf` every coordinate of `x` is within `1/4` (in `N`-scaled units) of the
corresponding coordinate interval of `c`, which is the hypothesis of
`Work.ThomBordism.TwoSet.clampCell_mem_cOf`.
-/

open scoped Topology unitInterval

namespace Work.ThomBordism.TwoSet

variable {j N : ℕ}

/-- The distance of the `i`-th `N`-scaled coordinate of `x` to the `i`-th coordinate interval of
`c`, in units of `1/N`. -/
noncomputable def cellDistCoord (c : CellIdx j N) (i : Fin j) (x : IC j) : ℝ :=
  max 0 (max ((c.lo i : ℝ) - (N : ℝ) * (x i : ℝ)) ((N : ℝ) * (x i : ℝ) - (c.hi i : ℝ)))

theorem continuous_cellDistCoord (c : CellIdx j N) (i : Fin j) :
    Continuous (cellDistCoord c i) := by
  have h : Continuous fun x : IC j => (N : ℝ) * (x i : ℝ) :=
    continuous_const.mul (continuous_subtype_val.comp (continuous_apply i))
  have h1 : Continuous fun x : IC j => (c.lo i : ℝ) - (N : ℝ) * (x i : ℝ) :=
    continuous_const.sub h
  have h2 : Continuous fun x : IC j => (N : ℝ) * (x i : ℝ) - (c.hi i : ℝ) :=
    h.sub continuous_const
  exact continuous_const.max (h1.max h2)

theorem cellDistCoord_nonneg (c : CellIdx j N) (i : Fin j) (x : IC j) :
    0 ≤ cellDistCoord c i x := le_max_left _ _

theorem cellDistCoord_le (c : CellIdx j N) (i : Fin j) (x : IC j) :
    (c.lo i : ℝ) - (N : ℝ) * (x i : ℝ) ≤ cellDistCoord c i x :=
  le_trans (le_max_left _ _) (le_max_right _ _)

theorem cellDistCoord_le' (c : CellIdx j N) (i : Fin j) (x : IC j) :
    (N : ℝ) * (x i : ℝ) - (c.hi i : ℝ) ≤ cellDistCoord c i x :=
  le_trans (le_max_right _ _) (le_max_right _ _)

theorem cellDistCoord_eq_zero_iff (c : CellIdx j N) (i : Fin j) (x : IC j) :
    cellDistCoord c i x = 0 ↔
      (c.lo i : ℝ) ≤ (N : ℝ) * (x i : ℝ) ∧ (N : ℝ) * (x i : ℝ) ≤ (c.hi i : ℝ) := by
  show max 0 (max ((c.lo i : ℝ) - (N : ℝ) * (x i : ℝ))
      ((N : ℝ) * (x i : ℝ) - (c.hi i : ℝ))) = 0 ↔ _
  constructor
  · intro h
    have hA : max ((c.lo i : ℝ) - (N : ℝ) * (x i : ℝ))
        ((N : ℝ) * (x i : ℝ) - (c.hi i : ℝ)) ≤ 0 := le_of_le_of_eq (le_max_right _ _) h
    exact ⟨by linarith [le_trans (le_max_left _ _) hA], by linarith [le_trans (le_max_right _ _) hA]⟩
  · rintro ⟨h1, h2⟩
    have hA : max ((c.lo i : ℝ) - (N : ℝ) * (x i : ℝ))
        ((N : ℝ) * (x i : ℝ) - (c.hi i : ℝ)) ≤ 0 :=
      max_le (by linarith) (by linarith)
    exact le_antisymm (max_le le_rfl hA) (le_max_left _ _)

/-- The coordinatewise distance of the `N`-scaled coordinates of `x` to the coordinate intervals
of `c`; it vanishes exactly on `cellSet c`. -/
noncomputable def cellDist (c : CellIdx j N) (x : IC j) : ℝ :=
  ∑ i : Fin j, cellDistCoord c i x

theorem continuous_cellDist (c : CellIdx j N) : Continuous (cellDist c) := by
  exact continuous_finset_sum _ (fun i _ => continuous_cellDistCoord c i)

theorem cellDist_nonneg (c : CellIdx j N) (x : IC j) : 0 ≤ cellDist c x :=
  Finset.sum_nonneg (fun i _ => cellDistCoord_nonneg c i x)

theorem cellDistCoord_le_cellDist (c : CellIdx j N) (i : Fin j) (x : IC j) :
    cellDistCoord c i x ≤ cellDist c x :=
  Finset.single_le_sum (fun k _ => cellDistCoord_nonneg c k x) (Finset.mem_univ i)

theorem cellDist_eq_zero_iff (hN : 1 ≤ N) (c : CellIdx j N) (x : IC j) :
    cellDist c x = 0 ↔ x ∈ cellSet c := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  constructor
  · intro h i
    have h2 := cellDistCoord_le_cellDist c i x
    have h3 := cellDistCoord_nonneg c i x
    rw [h] at h2
    have h1 : cellDistCoord c i x = 0 := le_antisymm h2 h3
    obtain ⟨h4, h5⟩ := (cellDistCoord_eq_zero_iff c i x).mp h1
    exact ⟨by rw [div_le_iff₀ hNpos]; linarith, by rw [le_div_iff₀ hNpos]; linarith⟩
  · intro h
    refine Finset.sum_eq_zero (fun i _ => ?_)
    refine (cellDistCoord_eq_zero_iff c i x).mpr ⟨?_, ?_⟩
    · have := (mem_cellSet.mp h i).1
      rw [div_le_iff₀ hNpos] at this; linarith
    · have := (mem_cellSet.mp h i).2
      rw [le_div_iff₀ hNpos] at this; linarith

/-- The junction time of the spreading construction: it vanishes exactly on `cellSet c`. -/
noncomputable def sigOf (c : CellIdx j N) (x : IC j) : unitInterval :=
  ⟨min 1 (16 * cellDist c x), by
    refine ⟨le_min zero_le_one (by have := cellDist_nonneg c x; linarith), min_le_left _ _⟩⟩

@[simp] theorem sigOf_val (c : CellIdx j N) (x : IC j) :
    ((sigOf c x : unitInterval) : ℝ) = min 1 (16 * cellDist c x) := rfl

theorem continuous_sigOf (c : CellIdx j N) : Continuous (sigOf c) :=
  Continuous.subtype_mk
    (continuous_const.min (continuous_const.mul (continuous_cellDist c))) _

/-- The drag amplitude: it equals `1` wherever `sigOf c < 1` and vanishes for `cellDist c ≥ 1/4`. -/
noncomputable def lamOf (c : CellIdx j N) (x : IC j) : unitInterval :=
  ⟨min 1 (max 0 (2 - 8 * cellDist c x)), by
    refine ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩⟩

@[simp] theorem lamOf_val (c : CellIdx j N) (x : IC j) :
    ((lamOf c x : unitInterval) : ℝ) = min 1 (max 0 (2 - 8 * cellDist c x)) := rfl

theorem continuous_lamOf (c : CellIdx j N) : Continuous (lamOf c) :=
  Continuous.subtype_mk
    (continuous_const.min (continuous_const.max
      (continuous_const.sub (continuous_const.mul (continuous_cellDist c))))) _

theorem sigOf_eq_zero_iff (hN : 1 ≤ N) (c : CellIdx j N) (x : IC j) :
    sigOf c x = 0 ↔ x ∈ cellSet c := by
  rw [← cellDist_eq_zero_iff hN c x]
  constructor
  · intro h
    have h1 : min 1 (16 * cellDist c x) = 0 := by
      have := congrArg Subtype.val h
      simpa [sigOf_val] using this
    have h1' : min 1 (16 * cellDist c x) ≤ 0 := h1.le
    have h2 : 16 * cellDist c x ≤ 0 := by
      rcases le_total (16 * cellDist c x) 1 with hc | hc
      · have : min 1 (16 * cellDist c x) = 16 * cellDist c x :=
          le_antisymm (min_le_right _ _) (le_min hc le_rfl)
        rw [this] at h1'; exact h1'
      · have : min 1 (16 * cellDist c x) = 1 :=
          le_antisymm (min_le_left _ _) (le_min le_rfl hc)
        rw [this] at h1'; norm_num at h1'
    have h3 := cellDist_nonneg c x
    linarith
  · intro h
    apply Subtype.ext
    rw [sigOf_val, h]
    norm_num

theorem lamOf_eq_one_of_sigOf_lt_one (c : CellIdx j N) {x : IC j}
    (h : (sigOf c x : ℝ) < 1) : lamOf c x = 1 := by
  have h1 : min 1 (16 * cellDist c x) < 1 := by rw [← sigOf_val]; exact h
  have h2 : 16 * cellDist c x < 1 := by
    rcases (min_lt_iff.mp h1) with hc | hc
    · exact absurd hc (lt_irrefl 1)
    · exact hc
  have h3 : 1 ≤ 2 - 8 * cellDist c x := by linarith
  apply Subtype.ext
  rw [lamOf_val]
  exact le_antisymm (min_le_left _ _) (le_min le_rfl (le_trans h3 (le_max_right _ _)))

theorem lamOf_eq_zero_of_le (c : CellIdx j N) {x : IC j} (h : 1/4 ≤ cellDist c x) :
    lamOf c x = 0 := by
  have h1 : 2 - 8 * cellDist c x ≤ 0 := by linarith
  have h2 : max 0 (2 - 8 * cellDist c x) = 0 :=
    le_antisymm (max_le le_rfl h1) (le_max_left _ _)
  apply Subtype.ext
  rw [lamOf_val, h2]
  norm_num

/-- On the support of `lamOf c` the point is close to `cellSet c`. -/
theorem cellDist_lt_of_lamOf_pos (c : CellIdx j N) {x : IC j} (h : 0 < (lamOf c x : ℝ)) :
    cellDist c x < 1/4 := by
  rw [lamOf_val] at h
  have h1 : 0 < max 0 (2 - 8 * cellDist c x) := lt_of_lt_of_le h (min_le_right _ _)
  have h2 : 0 < 2 - 8 * cellDist c x := by
    rcases max_choice 0 (2 - 8 * cellDist c x) with hc | hc <;> rw [hc] at h1
    · exact absurd h1 (lt_irrefl 0)
    · exact h1
  linarith

/-- On the support of `lamOf c` every coordinate of `x` is within `1/4` (in `N`-scaled units) of
the coordinate interval of `c` — the hypothesis of `clampCell_mem_cOf`. -/
theorem close_of_lamOf_pos (c : CellIdx j N) {x : IC j} (h : 0 < (lamOf c x : ℝ)) :
    ∀ i : Fin j, (c.lo i : ℝ) - 1/4 < (N : ℝ) * (x i : ℝ) ∧
      (N : ℝ) * (x i : ℝ) < (c.hi i : ℝ) + 1/4 := by
  intro i
  have h1 : cellDistCoord c i x < 1/4 := by
    have h2 := cellDistCoord_le_cellDist c i x
    have h3 := cellDist_lt_of_lamOf_pos c h
    linarith
  have h2 := cellDistCoord_le c i x
  have h3 := cellDistCoord_le' c i x
  exact ⟨by linarith, by linarith⟩

end Work.ThomBordism.TwoSet
