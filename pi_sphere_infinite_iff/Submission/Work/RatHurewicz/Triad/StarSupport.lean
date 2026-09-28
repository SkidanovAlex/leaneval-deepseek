import Mathlib
import Submission.Work.ThomBordism.TwoSet.exists_cellHomeo
import Submission.Work.RatHurewicz.Triad.Star
import Submission.Work.RatHurewicz.Triad.SpreadDefs

/-!
# The support of the treatment of a cell, the flow, and the push time

For the preparation theorem (tom Dieck 6.9.2) a cell `c` of the grid is "treated" by a homotopy of
the whole cube which

* is trivial outside the **support** `cellStar c ε` (the closed interval of `c` in its interval
  directions, the `ε`-collar of the node in its node directions);
* applies the cell homotopy of `c` (compression / `K`-trick) to the points of `cellSet c`;
* moves the points of the support towards `c` by the *flow* `flowCell`.

The rate `μ` is **real-valued** (it must be allowed to exceed `1`: the flow reaches the cell at time
`1/μ x`, so `μ ≥ 2` on the cell means the arrival occurs strictly before time `1` and the push time
`pushTime` can grow to its full value `ν x` by time `1`).
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz.Triad

noncomputable section

open Work.ThomBordism.TwoSet

variable {j N : ℕ}

/-- **The support of the treatment of `c`**: the closed interval of `c` in its interval directions
and the `ε`-collar of the node in its node directions. -/
noncomputable def cellStar (c : CellIdx j N) (ε : ℝ) : Set (IC j) :=
  {x | (∀ i, c.lo i < c.hi i →
          (c.lo i : ℝ) / N ≤ (x i : ℝ) ∧ (x i : ℝ) ≤ (c.hi i : ℝ) / N) ∧
       (∀ i, c.lo i = c.hi i → |(x i : ℝ) - (c.lo i : ℝ) / N| ≤ ε)}

@[simp] theorem mem_cellStar {c : CellIdx j N} {ε : ℝ} {x : IC j} :
    x ∈ cellStar c ε ↔
      (∀ i, c.lo i < c.hi i →
          (c.lo i : ℝ) / N ≤ (x i : ℝ) ∧ (x i : ℝ) ≤ (c.hi i : ℝ) / N) ∧
      (∀ i, c.lo i = c.hi i → |(x i : ℝ) - (c.lo i : ℝ) / N| ≤ ε) := Iff.rfl

/-- The cell is contained in its support. -/
theorem cellSet_subset_cellStar {c : CellIdx j N} {ε : ℝ} (hε : 0 ≤ ε) :
    cellSet c ⊆ cellStar c ε := by
  intro x hx
  refine ⟨fun i _ => hx i, fun i hi => ?_⟩
  have h1 := (hx i).1
  have h2 := (hx i).2
  rw [← hi] at h2
  have : (x i : ℝ) = (c.lo i : ℝ) / N := le_antisymm h2 h1
  simp [this, hε]

/-- The interpolation parameter `min 1 (max 0 (s·μ x))`, an element of `[0,1]`. -/
noncomputable def flowParam (μ : C(IC j, ℝ)) (x : IC j) (s : I) : I :=
  ⟨min 1 (max 0 ((s : ℝ) * μ x)),
    ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩⟩

@[simp] theorem flowParam_val (μ : C(IC j, ℝ)) (x : IC j) (s : I) :
    ((flowParam μ x s : I) : ℝ) = min 1 (max 0 ((s : ℝ) * μ x)) := rfl

theorem flowParam_nonneg (μ : C(IC j, ℝ)) (x : IC j) (s : I) :
    0 ≤ ((flowParam μ x s : I) : ℝ) := (flowParam μ x s).2.1

theorem flowParam_le_one (μ : C(IC j, ℝ)) (x : IC j) (s : I) :
    ((flowParam μ x s : I) : ℝ) ≤ 1 := (flowParam μ x s).2.2

@[simp] theorem flowParam_zero (μ : C(IC j, ℝ)) (x : IC j) : flowParam μ x 0 = 0 := by
  apply Subtype.ext
  simp [flowParam]

/-- The segment between a point and itself is constant. -/
theorem segMap_self (x : IC j) (t : I) : segMap x x t = x := by
  funext i
  apply Subtype.ext
  simp only [segMap]
  ring_nf

/-- **The flow**: `x` slid towards its coordinatewise clamp into the cell, with rate `μ`. -/
noncomputable def flowCell (c : CellIdx j N) (hN : 1 ≤ N) (μ : C(IC j, ℝ)) (x : IC j) (s : I) :
    IC j := segMap x (clampCell c hN x) (flowParam μ x s)

@[simp] theorem flowCell_zero (c : CellIdx j N) (hN : 1 ≤ N) (μ : C(IC j, ℝ)) (x : IC j) :
    flowCell c hN μ x 0 = x := by
  simp [flowCell]

/-- Where the rate vanishes, the flow is trivial. -/
theorem flowCell_eq_self_of_mu_eq_zero {c : CellIdx j N} (hN : 1 ≤ N) {μ : C(IC j, ℝ)}
    {x : IC j} (h : μ x = 0) (s : I) : flowCell c hN μ x s = x := by
  have hp : flowParam μ x s = 0 := by
    apply Subtype.ext
    simp [flowParam, h]
  simp [flowCell, hp]

/-- Where the rate is nonpositive, the flow is trivial. -/
theorem flowCell_eq_self_of_mu_nonpos {c : CellIdx j N} (hN : 1 ≤ N) {μ : C(IC j, ℝ)}
    {x : IC j} (h : μ x ≤ 0) (s : I) : flowCell c hN μ x s = x := by
  have hp : flowParam μ x s = 0 := by
    apply Subtype.ext
    have h1 : (s : ℝ) * μ x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos s.2.1 h
    simp [flowParam_val, max_eq_left h1]
  simp [flowCell, hp]

/-- The flow fixes the cell. -/
theorem flowCell_eq_self_of_mem {c : CellIdx j N} (hN : 1 ≤ N) (μ : C(IC j, ℝ)) {x : IC j}
    (hx : x ∈ cellSet c) (s : I) : flowCell c hN μ x s = x := by
  rw [flowCell, clampCell_eq_self c hN hx, segMap_self]

/-- The flow stays in the support. -/
theorem flowCell_mem_cellStar {c : CellIdx j N} (hN : 1 ≤ N) (μ : C(IC j, ℝ)) {ε : ℝ}
    (hε : 0 ≤ ε) {x : IC j} (hx : x ∈ cellStar c ε) (s : I) :
    flowCell c hN μ x s ∈ cellStar c ε := by
  obtain ⟨hint, hnode⟩ := hx
  have hp0 := flowParam_nonneg μ x s
  have hp1 := flowParam_le_one μ x s
  have hcoord : ∀ i, ((flowCell c hN μ x s i : unitInterval) : ℝ) =
      (1 - ((flowParam μ x s : I) : ℝ)) * (x i : ℝ) +
        ((flowParam μ x s : I) : ℝ) *
          (((clampCell c hN x) i : unitInterval) : ℝ) := by
    intro i
    simp only [flowCell, segMap]
  refine ⟨fun i hlt => ?_, fun i heq => ?_⟩
  · have hcl := clampCell_mem c hN x i
    have hxi := hint i hlt
    have hb1 : (c.lo i : ℝ) / N ≤
        (1 - ((flowParam μ x s : I) : ℝ)) * (x i : ℝ) +
          ((flowParam μ x s : I) : ℝ) * (((clampCell c hN x) i : unitInterval) : ℝ) := by
      nlinarith [hxi.1, hcl.1, hp0, hp1]
    have hb2 : (1 - ((flowParam μ x s : I) : ℝ)) * (x i : ℝ) +
          ((flowParam μ x s : I) : ℝ) * (((clampCell c hN x) i : unitInterval) : ℝ) ≤
        (c.hi i : ℝ) / N := by
      nlinarith [hxi.2, hcl.2, hp0, hp1]
    rw [hcoord i]
    exact ⟨hb1, hb2⟩
  · have hstep : c.hi i = c.lo i := heq.symm
    have hcl : (((clampCell c hN x) i : unitInterval) : ℝ) = (c.lo i : ℝ) / N := by
      rw [clampCell_val, clampR, hstep]
      rw [max_eq_left]
      exact min_le_left _ _
    have hxi := hnode i heq
    rw [abs_le] at hxi ⊢
    rw [hcoord i, hcl]
    constructor <;> nlinarith [hxi.1, hxi.2, hp0, hp1]

/-- Once the flow time reaches `1/μ x`, the point is in the cell. -/
theorem flowCell_mem_cellSet_of_arrived {c : CellIdx j N} (hN : 1 ≤ N) (μ : C(IC j, ℝ))
    {x : IC j} {s : I} (h : 1 ≤ (s : ℝ) * μ x) : flowCell c hN μ x s ∈ cellSet c := by
  have hpar : flowParam μ x s = 1 := by
    apply Subtype.ext
    simp only [flowParam_val]
    exact min_eq_left (le_trans h (le_max_right 0 ((s : ℝ) * μ x)))
  rw [flowCell, hpar, segMap_one]
  exact clampCell_mem c hN x

/-- **The push time**: `0` until the flow arrives (`1 ≤ s·μ x`), then growing to `ν x` at `s = 1`. -/
noncomputable def pushTime (μ : C(IC j, ℝ)) (ν : C(IC j, I)) (x : IC j) (s : I) : I :=
  mulI ⟨min 1 (max 0 ((s : ℝ) * μ x - 1)),
    ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩⟩ (ν x)

@[simp] theorem pushTime_val (μ : C(IC j, ℝ)) (ν : C(IC j, I)) (x : IC j) (s : I) :
    ((pushTime μ ν x s : I) : ℝ) =
      min 1 (max 0 ((s : ℝ) * μ x - 1)) * (ν x : ℝ) := rfl

/-- Before the arrival, the push time is `0`. -/
theorem pushTime_eq_zero_of_le {μ : C(IC j, ℝ)} {ν : C(IC j, I)} {x : IC j} {s : I}
    (h : (s : ℝ) * μ x ≤ 1) : pushTime μ ν x s = 0 := by
  apply Subtype.ext
  simp only [pushTime_val]
  rw [max_eq_left (by linarith)]
  simp

/-- At time `1`, when the rate is at least `2` on the cell and `ν = 1` there, the push is complete. -/
theorem pushTime_one_eq {μ : C(IC j, ℝ)} {ν : C(IC j, I)} {x : IC j}
    (hμ : 2 ≤ μ x) (hν : ν x = 1) : pushTime μ ν x 1 = ν x := by
  apply Subtype.ext
  have hμ1 : (1:ℝ) ≤ μ x - 1 := by linarith
  have hν1 : ((ν x : I) : ℝ) = 1 := by rw [hν]; rfl
  have h1 : ((1 : I) : ℝ) = 1 := rfl
  simp only [pushTime_val, hν1, h1, one_mul]
  rw [max_eq_right (by linarith : (0:ℝ) ≤ μ x - 1), min_eq_left hμ1]
  norm_num

/-- **The enlarged support**: an `ε`-collar of the cell in *all* directions. Unlike `cellStar c ε`
(which is exact in the interval directions of `c` and hence has a complement whose closure meets
`cellSet c`), `cellCollar c ε` has `cellSet c ⊆ interior (cellCollar c ε)` for `ε > 0`, which is what
lets the cutoffs of the treatment exist (a colleague's counterexample shows that `cellStar` cannot be
used for that; see `Triad/NOTES_triadCompression.md`, session 5c). -/
noncomputable def cellCollar (c : CellIdx j N) (ε : ℝ) : Set (IC j) :=
  {x | ∀ i, (c.lo i : ℝ) / N - ε ≤ (x i : ℝ) ∧ (x i : ℝ) ≤ (c.hi i : ℝ) / N + ε}

@[simp] theorem mem_cellCollar {c : CellIdx j N} {ε : ℝ} {x : IC j} :
    x ∈ cellCollar c ε ↔
      ∀ i, (c.lo i : ℝ) / N - ε ≤ (x i : ℝ) ∧ (x i : ℝ) ≤ (c.hi i : ℝ) / N + ε := Iff.rfl

theorem cellCollar_isClosed {c : CellIdx j N} (ε : ℝ) : IsClosed (cellCollar c ε) := by
  have h : cellCollar c ε =
      ⋂ i, {x : IC j | (c.lo i : ℝ) / N - ε ≤ (x i : ℝ)} ∩
        {x : IC j | (x i : ℝ) ≤ (c.hi i : ℝ) / N + ε} := by
    ext x; simp [cellCollar]
  rw [h]
  exact isClosed_iInter fun i =>
    (isClosed_le continuous_const (continuous_subtype_val.comp (continuous_apply i))).inter
      (isClosed_le (continuous_subtype_val.comp (continuous_apply i)) continuous_const)

theorem cellSet_subset_cellCollar {c : CellIdx j N} {ε : ℝ} (hε : 0 ≤ ε) :
    cellSet c ⊆ cellCollar c ε := by
  intro x hx i
  have h1 := (hx i).1
  have h2 := (hx i).2
  constructor
  · have : ((c.lo i : ℝ)) / N ≤ (x i : ℝ) := h1
    linarith
  · have : (x i : ℝ) ≤ ((c.hi i : ℝ)) / N := h2
    linarith

/-- For `ε > 0` the cell is contained in the *interior* of the collar. -/
theorem cellSet_subset_interior_cellCollar {c : CellIdx j N} {ε : ℝ} (hε : 0 < ε) :
    cellSet c ⊆ interior (cellCollar c ε) := by
  intro x hx
  refine mem_interior_iff_mem_nhds.mpr ?_
  refine Filter.mem_of_superset (Metric.ball_mem_nhds x (by linarith : (0:ℝ) < ε / 2)) ?_
  intro y hy i
  have hd : dist (y i) (x i) < ε / 2 :=
    lt_of_le_of_lt (dist_le_pi_dist y x i) hy
  rw [Subtype.dist_eq, Real.dist_eq, abs_lt] at hd
  have h1 := (hx i).1
  have h2 := (hx i).2
  constructor <;> linarith [hd.1, hd.2]

end

end Work.RatHurewicz.Triad
