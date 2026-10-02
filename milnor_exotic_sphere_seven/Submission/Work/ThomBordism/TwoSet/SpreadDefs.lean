import Mathlib
import Submission.Work.ThomBordism.TwoSet.Cells
import Submission.Work.ThomBordism.TwoSet.Cutoff

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The spreading retraction of a cell homotopy

For a grid cell `c` of the `N`-grid (`N ≥ 1`) we build a retraction `spreadMap c hN` of `I^j × I`
onto `(I^j × {0}) ∪ (cellSet c × I)`, used to spread a homotopy defined on `cellSet c` to the whole
cube.  In scaled units (`N`-times the coordinates), with `r(x) = min 1 (cellDist c x)` the scaled
distance to `cellSet c` and `ν(x) = max 0 (1 - 4 r(x))` the amplitude (`1` on `cellSet c`, `0` as
soon as `r ≥ 1/4`):

* `spreadPt x τ = segMap x (clampCell c hN x) (clamp01 (τ * ν(x) / r(x)))`, the point obtained by
  flowing from `x` towards the clamp;
* `pushAmount x τ = max 0 (τ * ν(x) - r(x))`, positive exactly when the flow has arrived.

Because the flow coefficient is `clamp01 (τν/r)` and `|clampCell c hN x - x| ≤ cellDist c x / N`
(with `cellDist c x → 0` as `r(x) → 0`), the map is continuous even at the points where `r = 0`
and the coefficient jumps.
-/

open scoped Topology unitInterval

namespace Work.ThomBordism.TwoSet

variable {j N : ℕ}

/-- Clamping a real number to `[0,1]`. -/
noncomputable def clamp01 (t : ℝ) : ℝ := max 0 (min 1 t)

theorem clamp01_nonneg (t : ℝ) : 0 ≤ clamp01 t := le_max_left _ _

theorem clamp01_le_one (t : ℝ) : clamp01 t ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem continuous_clamp01 : Continuous clamp01 :=
  continuous_const.max (continuous_const.min continuous_id)

theorem clamp01_eq_zero_of_nonpos {t : ℝ} (h : t ≤ 0) : clamp01 t = 0 := by
  rw [clamp01, min_eq_right (le_trans h zero_le_one), max_eq_left h]

theorem clamp01_eq_one_of_one_le {t : ℝ} (h : 1 ≤ t) : clamp01 t = 1 := by
  rw [clamp01, min_eq_left h, max_eq_right zero_le_one]

/-- The scaled distance to `cellSet c`. -/
noncomputable def rOf (c : CellIdx j N) (x : IC j) : ℝ := min 1 (cellDist c x)

/-- The amplitude of the spreading of the cell `c`. -/
noncomputable def nuOf (c : CellIdx j N) (x : IC j) : ℝ := max 0 (1 - 4 * rOf c x)

theorem rOf_nonneg (c : CellIdx j N) (x : IC j) : 0 ≤ rOf c x :=
  le_min zero_le_one (cellDist_nonneg c x)

theorem rOf_le_one (c : CellIdx j N) (x : IC j) : rOf c x ≤ 1 := min_le_left _ _

theorem rOf_le_cellDist (c : CellIdx j N) (x : IC j) : rOf c x ≤ cellDist c x := min_le_right _ _

theorem continuous_rOf (c : CellIdx j N) : Continuous (rOf c) :=
  continuous_const.min (continuous_cellDist c)

theorem nuOf_nonneg (c : CellIdx j N) (x : IC j) : 0 ≤ nuOf c x := le_max_left _ _

theorem nuOf_le_one (c : CellIdx j N) (x : IC j) : nuOf c x ≤ 1 := by
  rw [nuOf]; refine max_le zero_le_one ?_; linarith [rOf_nonneg c x]

theorem continuous_nuOf (c : CellIdx j N) : Continuous (nuOf c) :=
  continuous_const.max (continuous_const.sub (continuous_const.mul (continuous_rOf c)))

theorem nuOf_pos_iff (c : CellIdx j N) (x : IC j) : 0 < nuOf c x ↔ rOf c x < 1/4 := by
  have h : nuOf c x = max 0 (1 - 4 * rOf c x) := rfl
  rw [h, lt_max_iff]
  exact ⟨fun h => h.elim (fun h0 => absurd h0 (lt_irrefl 0)) (fun h0 => by linarith),
    fun h => Or.inr (by linarith)⟩

theorem nuOf_eq_zero_iff (c : CellIdx j N) (x : IC j) : nuOf c x = 0 ↔ 1/4 ≤ rOf c x := by
  constructor
  · intro hz
    by_contra hlt
    exact absurd ((nuOf_pos_iff c x).mpr (not_le.mp hlt)) (by rw [hz]; exact lt_irrefl 0)
  · intro hle
    refine le_antisymm ?_ (nuOf_nonneg c x)
    by_contra hlt
    exact absurd ((nuOf_pos_iff c x).mp (not_le.mp hlt)) (by linarith)

theorem nuOf_eq_one_of_rOf_eq_zero {c : CellIdx j N} {x : IC j} (hx : rOf c x = 0) :
    nuOf c x = 1 := by rw [nuOf, hx]; norm_num

theorem rOf_eq_zero_iff (hN : 1 ≤ N) (c : CellIdx j N) (x : IC j) :
    rOf c x = 0 ↔ x ∈ cellSet c := by
  constructor
  · intro h
    have hcd : cellDist c x = 0 := by
      rcases min_choice (1:ℝ) (cellDist c x) with hc | hc
      · rw [rOf, hc] at h; exact absurd h (by norm_num)
      · rw [rOf, hc] at h; exact h
    exact (cellDist_eq_zero_iff hN c x).mp hcd
  · intro h
    rw [rOf, (cellDist_eq_zero_iff hN c x).mpr h]
    exact min_eq_right (by norm_num)

/-- The flow coefficient of the spreading of the cell `c`. -/
noncomputable def flowCoef (c : CellIdx j N) (x : IC j) (τ : I) : ℝ :=
  clamp01 ((τ : ℝ) * nuOf c x / rOf c x)

theorem flowCoef_nonneg (c : CellIdx j N) (x : IC j) (τ : I) : 0 ≤ flowCoef c x τ :=
  clamp01_nonneg _

theorem flowCoef_le_one (c : CellIdx j N) (x : IC j) (τ : I) : flowCoef c x τ ≤ 1 :=
  clamp01_le_one _

/-- The point reached by the flow of the spreading of the cell `c`. -/
noncomputable def spreadPt (c : CellIdx j N) (hN : 1 ≤ N) (x : IC j) (τ : I) : IC j :=
  segMap x (clampCell c hN x)
    ⟨flowCoef c x τ, flowCoef_nonneg c x τ, flowCoef_le_one c x τ⟩

/-- The push time of the spreading of the cell `c`. -/
noncomputable def pushAmount (c : CellIdx j N) (x : IC j) (τ : I) : ℝ :=
  max 0 ((τ : ℝ) * nuOf c x - rOf c x)

theorem pushT_nonneg (c : CellIdx j N) (x : IC j) (τ : I) : 0 ≤ pushAmount c x τ :=
  le_max_left _ _

theorem pushT_le_one (c : CellIdx j N) (x : IC j) (τ : I) : pushAmount c x τ ≤ 1 := by
  rw [pushAmount]
  refine max_le (by norm_num) ?_
  have hτ : (τ : ℝ) ≤ 1 := τ.2.2
  nlinarith [nuOf_nonneg c x, nuOf_le_one c x, rOf_nonneg c x]

/-- The push time as an element of `I`. -/
noncomputable def pushI (c : CellIdx j N) (x : IC j) (τ : I) : I :=
  ⟨pushAmount c x τ, pushT_nonneg c x τ, pushT_le_one c x τ⟩

/-- **The spreading retraction** of the cell `c`. -/
noncomputable def spreadMap (c : CellIdx j N) (hN : 1 ≤ N) (x : IC j) (τ : I) : IC j × I :=
  (spreadPt c hN x τ, pushI c x τ)

@[simp] theorem spreadMap_fst (c : CellIdx j N) (hN : 1 ≤ N) (x : IC j) (τ : I) :
    (spreadMap c hN x τ).1 = spreadPt c hN x τ := rfl

@[simp] theorem spreadMap_snd (c : CellIdx j N) (hN : 1 ≤ N) (x : IC j) (τ : I) :
    ((spreadMap c hN x τ).2 : ℝ) = pushAmount c x τ := rfl

theorem flowCoef_eq_zero_of_nuOf_eq_zero (c : CellIdx j N) {x : IC j} (τ : I)
    (h : nuOf c x = 0) : flowCoef c x τ = 0 := by
  rw [flowCoef, h, mul_zero, zero_div]
  exact clamp01_eq_zero_of_nonpos le_rfl

theorem flowCoef_eq_one_of_pos (c : CellIdx j N) {x : IC j} {τ : I}
    (h : rOf c x ≤ (τ : ℝ) * nuOf c x) (h0 : 0 < rOf c x) : flowCoef c x τ = 1 := by
  rw [flowCoef]
  refine clamp01_eq_one_of_one_le ?_
  rw [one_le_div h0]; linarith

theorem spreadPt_eq_self_of_nuOf_eq_zero (c : CellIdx j N) (hN : 1 ≤ N) {x : IC j} (τ : I)
    (h : nuOf c x = 0) : spreadPt c hN x τ = x := by
  have hfc : flowCoef c x τ = 0 := flowCoef_eq_zero_of_nuOf_eq_zero c τ h
  have hf : (⟨flowCoef c x τ, flowCoef_nonneg c x τ, flowCoef_le_one c x τ⟩ : I) = 0 :=
    Subtype.ext hfc
  rw [spreadPt, hf, segMap_zero]

theorem spreadPt_eq_clamp_of_le (c : CellIdx j N) (hN : 1 ≤ N) {x : IC j} {τ : I}
    (h : rOf c x ≤ (τ : ℝ) * nuOf c x) : spreadPt c hN x τ = clampCell c hN x := by
  rcases eq_or_lt_of_le (rOf_nonneg c x) with h0 | h0
  · have hr0 : rOf c x = 0 := h0.symm
    have hfc : flowCoef c x τ = 0 := by
      rw [flowCoef, hr0, div_zero]
      exact clamp01_eq_zero_of_nonpos le_rfl
    have hf : (⟨flowCoef c x τ, flowCoef_nonneg c x τ, flowCoef_le_one c x τ⟩ : I) = 0 :=
      Subtype.ext hfc
    have hcl : clampCell c hN x = x := clampCell_eq_self c hN ((rOf_eq_zero_iff hN c x).mp hr0)
    rw [spreadPt, hf, segMap_zero, hcl]
  · have hfc : flowCoef c x τ = 1 := flowCoef_eq_one_of_pos c h h0
    have hf : (⟨flowCoef c x τ, flowCoef_nonneg c x τ, flowCoef_le_one c x τ⟩ : I) = 1 :=
      Subtype.ext hfc
    rw [spreadPt, hf, segMap_one]

theorem spreadMap_zero (c : CellIdx j N) (hN : 1 ≤ N) (x : IC j) :
    spreadMap c hN x 0 = (x, 0) := by
  have hfc : flowCoef c x 0 = 0 := by
    rw [flowCoef]; norm_num
    exact clamp01_eq_zero_of_nonpos le_rfl
  have hf : (⟨flowCoef c x 0, flowCoef_nonneg c x 0, flowCoef_le_one c x 0⟩ : I) = 0 :=
    Subtype.ext hfc
  have hp : pushAmount c x 0 = 0 := by
    rw [pushAmount, show (((0:I):ℝ)) = 0 from rfl, zero_mul, zero_sub]
    exact max_eq_left (by linarith [rOf_nonneg c x])
  refine Prod.ext ?_ ?_
  · show spreadPt c hN x 0 = x
    rw [spreadPt, hf, segMap_zero]
  · apply Subtype.ext
    show pushAmount c x 0 = ((0:I):ℝ)
    rw [hp]; rfl

theorem spreadMap_self (c : CellIdx j N) (hN : 1 ≤ N) {z : IC j} (hz : z ∈ cellSet c) (τ : I) :
    spreadMap c hN z τ = (z, τ) := by
  have hr : rOf c z = 0 := (rOf_eq_zero_iff hN c z).mpr hz
  have hnu : nuOf c z = 1 := nuOf_eq_one_of_rOf_eq_zero hr
  have hc : clampCell c hN z = z := clampCell_eq_self c hN hz
  have hfc : flowCoef c z τ = 0 := by
    rw [flowCoef, hr, div_zero]; exact clamp01_eq_zero_of_nonpos le_rfl
  have hf : (⟨flowCoef c z τ, flowCoef_nonneg c z τ, flowCoef_le_one c z τ⟩ : I) = 0 :=
    Subtype.ext hfc
  have hp : pushAmount c z τ = (τ : ℝ) := by
    rw [pushAmount, hr, hnu, mul_one, sub_zero]
    exact max_eq_right τ.2.1
  refine Prod.ext ?_ ?_
  · show spreadPt c hN z τ = z
    rw [spreadPt, hf, segMap_zero]
  · apply Subtype.ext
    show pushAmount c z τ = (τ:ℝ)
    rw [hp]

theorem spreadPt_mem_of_pushT_pos (c : CellIdx j N) (hN : 1 ≤ N) {x : IC j} {τ : I}
    (h : 0 < pushAmount c x τ) : spreadPt c hN x τ ∈ cellSet c := by
  have hlt : rOf c x < (τ : ℝ) * nuOf c x := by
    have h' : 0 < (τ:ℝ) * nuOf c x - rOf c x := by
      rcases max_choice 0 ((τ:ℝ) * nuOf c x - rOf c x) with hc | hc
      · rw [pushAmount, hc] at h; exact absurd h (lt_irrefl (0:ℝ))
      · rw [pushAmount, hc] at h; exact h
    linarith
  rw [spreadPt_eq_clamp_of_le c hN (le_of_lt hlt)]
  exact clampCell_mem c hN x

/-- `cellSet c` is convex. -/
theorem segMap_mem_cellSet {c : CellIdx j N} {x y : IC j} (hx : x ∈ cellSet c)
    (hy : y ∈ cellSet c) (t : I) : segMap x y t ∈ cellSet c := by
  intro i
  have hx' := hx i
  have hy' := hy i
  have ht0 : (0:ℝ) ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have h1 : 0 ≤ 1 - (t : ℝ) := by linarith
  constructor
  · calc (c.lo i : ℝ)/N
        = (1 - (t:ℝ)) * ((c.lo i : ℝ)/N) + (t:ℝ) * ((c.lo i : ℝ)/N) := by ring
      _ ≤ (1 - (t:ℝ)) * (x i : ℝ) + (t:ℝ) * (y i : ℝ) :=
          add_le_add (mul_le_mul_of_nonneg_left hx'.1 h1)
            (mul_le_mul_of_nonneg_left hy'.1 ht0)
  · calc (1 - (t:ℝ)) * (x i : ℝ) + (t:ℝ) * (y i : ℝ)
        ≤ (1 - (t:ℝ)) * ((c.hi i : ℝ)/N) + (t:ℝ) * ((c.hi i : ℝ)/N) :=
          add_le_add (mul_le_mul_of_nonneg_left hx'.2 h1)
            (mul_le_mul_of_nonneg_left hy'.2 ht0)
      _ = (c.hi i : ℝ)/N := by ring

/-- The value of `spreadPt` at time `1` in the "not yet arrived" regime. -/
theorem spreadPt_one_of_lt (c : CellIdx j N) (hN : 1 ≤ N) {x : IC j} (h : nuOf c x < rOf c x) :
    spreadPt c hN x 1 = segMap x (clampCell c hN x)
      ⟨nuOf c x / rOf c x, div_nonneg (nuOf_nonneg c x) (rOf_nonneg c x),
        div_le_one_of_le₀ (le_of_lt h) (rOf_nonneg c x)⟩ := by
  rw [spreadPt]
  congr 1
  apply Subtype.ext
  show clamp01 (((1:I):ℝ) * nuOf c x / rOf c x) = nuOf c x / rOf c x
  rw [show (((1:I):ℝ)) = 1 from rfl, one_mul, clamp01,
    min_eq_right (div_le_one_of_le₀ (le_of_lt h) (rOf_nonneg c x)),
    max_eq_right (div_nonneg (nuOf_nonneg c x) (rOf_nonneg c x))]

end Work.ThomBordism.TwoSet
