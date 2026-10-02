import Mathlib
import Submission.Work.ThomBordism.TwoSet.exists_cellHomeo

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The flow of the spreading construction

Let `c` be a grid cell of the `N`-grid of `I^j`, `κ : I^j → I` a cutoff (think: supported on a
small "star-collar" of `c` and vanishing on `c`), `η : I^j → I` a second cutoff (the push time).
This file defines

* the *flow point* `flowPt c hN κ x t = segMap x (clamp_c x) (t · κ x)`: the point obtained by
  sliding `x` a fraction `t·κ x` of the way towards its coordinatewise clamp into `c`;
* the *push time* `pushT η x t = t · η x`;
* the relative interior `cellRelint c = cellSet c \ cellRelbd c` of a cell;

together with the elementary properties used by `Work.ThomBordism.TwoSet.exists_spread`
(the lemma that spreads a homotopy defined on a cell to a homotopy of the whole cube).
-/

open scoped Topology unitInterval

namespace Work.ThomBordism.TwoSet

variable {j N : ℕ}

/-- The product of two points of `[0,1]`. -/
noncomputable def mulI (t s : I) : I :=
  ⟨(t : ℝ) * (s : ℝ), by
    refine ⟨mul_nonneg t.2.1 s.2.1, ?_⟩
    nlinarith [t.2.2, s.2.2, t.2.1, s.2.1]⟩

@[simp] theorem mulI_val (t s : I) : ((mulI t s : I) : ℝ) = (t : ℝ) * (s : ℝ) := rfl

@[simp] theorem mulI_zero_left (s : I) : mulI 0 s = 0 := by
  apply Subtype.ext; simp [mulI]

@[simp] theorem mulI_zero_right (t : I) : mulI t 0 = 0 := by
  apply Subtype.ext; simp [mulI]

@[simp] theorem mulI_one_right (t : I) : mulI t 1 = t := by
  apply Subtype.ext; simp [mulI]

/-- The relative interior of a cell: its points off the relative boundary. -/
noncomputable def cellRelint (c : CellIdx j N) : Set (IC j) := cellSet c \ cellRelbd c

@[simp] theorem mem_cellRelint {c : CellIdx j N} {x : IC j} :
    x ∈ cellRelint c ↔ x ∈ cellSet c ∧ x ∉ cellRelbd c := Iff.rfl

/-- **The flow point**: `x` slid a fraction `t·κ x` of the way towards its coordinatewise clamp
into the cell `c`. -/
noncomputable def flowPt (c : CellIdx j N) (hN : 1 ≤ N) (κ : C(IC j, I)) (x : IC j) (t : I) :
    IC j := segMap x (clampCell c hN x) (mulI t (κ x))

/-- **The push time** at a point: `t · η x`. -/
noncomputable def pushT (η : C(IC j, I)) (x : IC j) (t : I) : I := mulI t (η x)

@[simp] theorem flowPt_zero (c : CellIdx j N) (hN : 1 ≤ N) (κ : C(IC j, I)) (x : IC j) :
    flowPt c hN κ x 0 = x := by
  simp [flowPt]

theorem flowPt_eq_self {c : CellIdx j N} (hN : 1 ≤ N) {κ : C(IC j, I)} {x : IC j}
    (h : κ x = 0) (t : I) : flowPt c hN κ x t = x := by
  simp [flowPt, h]

theorem continuous_mulI :
    Continuous fun p : I × I => mulI p.1 p.2 :=
  Continuous.subtype_mk ((continuous_subtype_val.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)) _

theorem continuous_flowPt (c : CellIdx j N) (hN : 1 ≤ N) (κ : C(IC j, I)) :
    Continuous fun p : IC j × I => flowPt c hN κ p.1 p.2 := by
  have h : Continuous fun p : IC j × I =>
      (p.1, ((clampCell c hN) p.1, mulI p.2 (κ p.1))) :=
    (continuous_fst).prodMk
      (((clampCell c hN).continuous.comp continuous_fst).prodMk
        (continuous_mulI.comp (continuous_snd.prodMk
          (κ.continuous.comp continuous_fst))))
  exact (continuous_segMap j).comp h

theorem continuous_pushT (η : C(IC j, I)) :
    Continuous fun p : IC j × I => pushT η p.1 p.2 := by
  refine Continuous.subtype_mk ?_ _
  exact (continuous_subtype_val.comp continuous_snd).mul
    (continuous_subtype_val.comp (η.continuous.comp continuous_fst))

@[simp] theorem pushT_val (η : C(IC j, I)) (x : IC j) (t : I) :
    ((pushT η x t : I) : ℝ) = (t : ℝ) * (η x : ℝ) := rfl

/-- A cell of the grid is convex: the segment between two of its points stays in it. -/
theorem segMap_mem_cellSet {c : CellIdx j N} {x y : IC j} (hx : x ∈ cellSet c)
    (hy : y ∈ cellSet c) (t : I) : segMap x y t ∈ cellSet c := by
  intro i
  have h1 := hx i
  have h2 := hy i
  have h3 := (t : I).2.1
  have h4 := (t : I).2.2
  simp only [segMap]
  constructor
  · have : (0:ℝ) ≤ 1 - (t : ℝ) := by linarith
    nlinarith [h1.1, h2.1, h3]
  · nlinarith [h1.2, h2.2, h3, h4]

theorem clampCell_mem_cellSet' (c : CellIdx j N) (hN : 1 ≤ N) (x : IC j) :
    clampCell c hN x ∈ cellSet c := clampCell_mem c hN x

/-- If `c` is a subcell of `c'` (coordinatewise), then `cellSet c ⊆ cellSet c'`. -/
theorem cellSet_mono {c c' : CellIdx j N} (hlo : ∀ i, c'.lo i ≤ c.lo i)
    (hhi : ∀ i, c.hi i ≤ c'.hi i) : cellSet c ⊆ cellSet c' := by
  intro x hx i
  have h := hx i
  have hN : (0:ℝ) ≤ N := Nat.cast_nonneg N
  constructor
  · have : ((c'.lo i : ℕ) : ℝ) ≤ ((c.lo i : ℕ) : ℝ) := by exact_mod_cast hlo i
    have : (c'.lo i : ℝ) / N ≤ (c.lo i : ℝ) / N := by
      exact div_le_div_of_nonneg_right this hN
    linarith [h.1]
  · have : ((c.hi i : ℕ) : ℝ) ≤ ((c'.hi i : ℕ) : ℝ) := by exact_mod_cast hhi i
    have : (c.hi i : ℝ) / N ≤ (c'.hi i : ℝ) / N := by
      exact div_le_div_of_nonneg_right this hN
    linarith [h.2]

/-- The flow point of a point of a cell `c' ⊇ c` stays in `c'`. -/
theorem flowPt_mem_of_sub {c c' : CellIdx j N} (hN : 1 ≤ N) (κ : C(IC j, I))
    (hcc' : cellSet c ⊆ cellSet c') {x : IC j} (hx : x ∈ cellSet c') (t : I) :
    flowPt c hN κ x t ∈ cellSet c' := by
  simpa [flowPt] using
    segMap_mem_cellSet hx (hcc' (clampCell_mem c hN x)) (mulI t (κ x))

end Work.ThomBordism.TwoSet
