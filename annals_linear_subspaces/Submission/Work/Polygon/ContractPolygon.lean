import Mathlib
import Submission.Work.Polygon.DiscreteConvex
import Submission.GeometryOfNumbers.WedgeContract

/-!
# The model contracting polygon segment (polygon/hook layer)

For the model exponential-flow lattice (`a = exp(−t/ℓ)` on the first `ℓ` contracting
directions), the Grayson polygon is linear on its contracting block: successive minima
`λ_i = exp(−t/ℓ)` give `log λ_i = c(i) − c(i−1) = −t/ℓ` for `1 ≤ i ≤ ℓ`, i.e.
`c_t(i) = −t·(i/ℓ)` with `c_t(0) = 0`.

This module records that segment as `modelContractPolygon t ℓ` and proves the **hinge**:
its first-`k` slope sum equals the first-block exponent of the §3 estimate
(`Submission.WedgeContract.wedgeContract_firstBlock_slope_sum`):

* `dslope_modelContractPolygon`: every slope is the constant `−t/ℓ`;
* `modelContractPolygon_convex`: the segment is discrete-convex
  (`Submission.Polygon.DiscreteConvexOn`);
* `firstSegment_slope_sum`: `Σ_{i < k} dslope c_t i = −t·(k/ℓ)` (telescoping);
* **`firstBlock_slope_sum_match`** — the hinge: that slope sum equals the first-block
  exponent `−t·(k/ℓ)` of `wedgeContract_firstBlock_slope_sum`.

All declarations are Mathlib-only (besides the Submission polygon/wedge modules).
-/

noncomputable section

open scoped BigOperators
set_option autoImplicit false

namespace Submission.ContractPolygon

/-- The model contracting polygon segment: `c_t(i) = -t * (i / ℓ)` (linear of slope `−t/ℓ`
per step, `c_t(0) = 0`), the Grayson polygon of the model exponential-flow lattice on its
contracting block (successive minima `exp(−t/ℓ)`, so `log λ_i = c(i) − c(i−1) = −t/ℓ`). -/
def modelContractPolygon (t ℓ : ℝ) : ℕ → ℝ := fun i => -t * ((i : ℝ) / ℓ)

/-- `c_t(0) = 0`. -/
lemma modelContractPolygon_zero (t ℓ : ℝ) : modelContractPolygon t ℓ 0 = 0 := by
  simp [modelContractPolygon]

/-- The slope of the model contracting polygon is the constant `−t/ℓ` at every step
(`dslope c i = Λ_{i+1}` in the paper's notation). -/
lemma dslope_modelContractPolygon (t ℓ : ℝ) (i : ℕ) :
    Submission.Polygon.dslope (modelContractPolygon t ℓ) i = -t / ℓ := by
  unfold Submission.Polygon.dslope modelContractPolygon
  rw [div_eq_mul_inv]
  rw [Nat.cast_add]
  ring

/-- The model contracting polygon segment is discrete-convex on any `{0, …, d}` (its slopes
are constant, hence non-decreasing). -/
lemma modelContractPolygon_convex (t ℓ : ℝ) (d : ℕ) :
    Submission.Polygon.DiscreteConvexOn (modelContractPolygon t ℓ) d := by
  intro i hi
  rw [dslope_modelContractPolygon t ℓ i, dslope_modelContractPolygon t ℓ (i + 1)]

/-- Telescoped first-segment slope sum: `Σ_{i < k} dslope c_t i = c_t k − c_t 0 =
−t·(k/ℓ)`. -/
lemma firstSegment_slope_sum (t ℓ : ℝ) (k : ℕ) :
    (∑ i ∈ Finset.range k, Submission.Polygon.dslope (modelContractPolygon t ℓ) i) =
      -t * ((k : ℝ) / ℓ) := by
  rw [Submission.Polygon.telescope (modelContractPolygon t ℓ) k]
  dsimp [modelContractPolygon]
  simp

/-- **Hinge**: the first-`k` slope sum of the model contracting polygon equals the
first-block exponent `−t·(k/ℓ)` recorded by
`Submission.WedgeContract.wedgeContract_firstBlock_slope_sum`: the polygon slope `−t/ℓ`
per step over `k` steps reproduces exactly the exponent of the first-block log estimate. -/
lemma firstBlock_slope_sum_match (ℓ : ℕ) (t : ℝ) (k : ℕ) :
    (∑ i ∈ Finset.range k, Submission.Polygon.dslope (modelContractPolygon t (ℓ : ℝ)) i) =
      (∑ _ : Fin k, Real.log (Real.exp (-t / (ℓ : ℝ)))) := by
  rw [firstSegment_slope_sum t (ℓ : ℝ) k]
  rw [Submission.WedgeContract.wedgeContract_firstBlock_slope_sum (ℓ := ℓ) (t := t) (k := k)]
  ring

/-! ### The full V-shaped model polygon on `{0, …, d}`

The complete Grayson polygon of the model exponential-flow lattice (unimodular:
`c(0) = c(d) = 0`): the contracting segment `c(i) = −t·(i/ℓ)` on `[0, ℓ]` (slope `−t/ℓ`),
joined continuously at `(ℓ, −t)` to the expanding linear segment of slope
`+t/(d−ℓ)` ending at `(d, 0)`.

* `modelVeePolygon t d ℓ`: the V-shaped function;
* endpoints `c(0) = 0`, `c(d) = 0`, corner `c(ℓ) = −t`;
* `dslope_modelVeePolygon`: slopes are `−t/ℓ` for steps `i < ℓ` and `+t/(d−ℓ)` for
  `i ≥ ℓ` (the single jump at the corner from `−t/ℓ` to `+t/(d−ℓ)` is between the slope
  indices `ℓ−1` and `ℓ`);
* `modelVeePolygon_convex`: with `0 ≤ t` the slopes are non-decreasing, so the V is
  discrete-convex.
-/

/-- The full V-shaped model polygon on `{0,…,d}`: `−t·(i/ℓ)` on the contracting block
`[0, ℓ]`, and the linear segment of slope `+t/(d−ℓ)` from `(ℓ, −t)` to `(d, 0)` on the
expanding block `[ℓ, d]`. -/
def modelVeePolygon (t : ℝ) (d ℓ : ℕ) : ℕ → ℝ := fun i =>
  if i ≤ ℓ then -t * ((i : ℝ) / (ℓ : ℝ))
  else -t + ((i : ℝ) - (ℓ : ℝ)) * (t / ((d : ℝ) - (ℓ : ℝ)))

/-- On the contracting block `[0, ℓ]`, the V-polygon agrees with the contracting segment
`modelContractPolygon`. -/
lemma modelVeePolygon_eq_contractPolygon (t : ℝ) (d ℓ : ℕ) {i : ℕ} (hi : i ≤ ℓ) :
    modelVeePolygon t d ℓ i = modelContractPolygon t (ℓ : ℝ) i := by
  simp [modelVeePolygon, modelContractPolygon, hi]

/-- On the expanding block `[ℓ, d]`, the V-polygon is the affine segment of slope
`+t/(d−ℓ)` through `(ℓ, −t)`. -/
lemma modelVeePolygon_right (t : ℝ) (d ℓ : ℕ) (hℓ0 : 0 < ℓ) {i : ℕ} (hi : ℓ ≤ i) :
    modelVeePolygon t d ℓ i = -t + ((i : ℝ) - (ℓ : ℝ)) * (t / ((d : ℝ) - (ℓ : ℝ))) := by
  by_cases hle : i ≤ ℓ
  · -- i = ℓ: left formula gives −t·(ℓ/ℓ) = −t, equal to the affine value at ℓ
    have hiℓ : i = ℓ := le_antisymm hle hi
    subst i
    have hℓR : (ℓ : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hℓ0)
    simp [modelVeePolygon, div_self hℓR]
  · -- i > ℓ: the else-branch of the definition
    simp [modelVeePolygon, hle]

/-- `c(0) = 0`. -/
lemma modelVeePolygon_zero (t : ℝ) (d ℓ : ℕ) : modelVeePolygon t d ℓ 0 = 0 := by
  simp [modelVeePolygon]

/-- The corner value: `c(ℓ) = −t`. -/
lemma modelVeePolygon_corner (t : ℝ) (d ℓ : ℕ) (hℓ0 : 0 < ℓ) :
    modelVeePolygon t d ℓ ℓ = -t := by
  have hℓR : (ℓ : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hℓ0)
  simp [modelVeePolygon, div_self hℓR]

/-- The right endpoint: `c(d) = 0` (for `ℓ < d`). -/
lemma modelVeePolygon_end (t : ℝ) (d ℓ : ℕ) (hℓd : ℓ < d) :
    modelVeePolygon t d ℓ d = 0 := by
  have hnot : ¬ d ≤ ℓ := by exact not_le_of_gt hℓd
  have hx : (d : ℝ) - (ℓ : ℝ) ≠ 0 := by
    rw [← Nat.cast_sub (le_of_lt hℓd)]
    exact_mod_cast (ne_of_gt (Nat.sub_pos_of_lt hℓd))
  have hstep : (↑d - ↑ℓ) * (t / (↑d - ↑ℓ)) = t := by
    field_simp [hx]
  simp [modelVeePolygon, hnot]
  rw [hstep]
  ring

/-- The slopes of the V-polygon: `−t/ℓ` for the contracting steps (`i < ℓ`), and
`+t/(d−ℓ)` for the expanding steps (`i ≥ ℓ`). -/
lemma dslope_modelVeePolygon (t : ℝ) (d ℓ : ℕ) (hℓ0 : 0 < ℓ) (i : ℕ) :
    Submission.Polygon.dslope (modelVeePolygon t d ℓ) i =
      if i < ℓ then -t / (ℓ : ℝ) else t / ((d : ℝ) - (ℓ : ℝ)) := by
  by_cases hi : i < ℓ
  · -- contracting step: both endpoints in [0, ℓ]
    have hi1 : i + 1 ≤ ℓ := by omega
    have hile : i ≤ ℓ := by omega
    calc
      Submission.Polygon.dslope (modelVeePolygon t d ℓ) i
          = modelVeePolygon t d ℓ (i + 1) - modelVeePolygon t d ℓ i := rfl
      _ = modelContractPolygon t (ℓ : ℝ) (i + 1) - modelContractPolygon t (ℓ : ℝ) i := by
            rw [modelVeePolygon_eq_contractPolygon t d ℓ hi1,
              modelVeePolygon_eq_contractPolygon t d ℓ hile]
      _ = Submission.Polygon.dslope (modelContractPolygon t (ℓ : ℝ)) i := rfl
      _ = -t / (ℓ : ℝ) := dslope_modelContractPolygon t (ℓ : ℝ) i
      _ = (if i < ℓ then -t / (ℓ : ℝ) else t / ((d : ℝ) - (ℓ : ℝ))) := by simp [hi]
  · -- expanding step (or corner step at i = ℓ): both endpoints satisfy the right formula
    have hℓi : ℓ ≤ i := le_of_not_gt hi
    have hℓi1 : ℓ ≤ i + 1 := by omega
    calc
      Submission.Polygon.dslope (modelVeePolygon t d ℓ) i
          = modelVeePolygon t d ℓ (i + 1) - modelVeePolygon t d ℓ i := rfl
      _ = (-t + (((i + 1 : ℕ) : ℝ) - (ℓ : ℝ)) * (t / ((d : ℝ) - (ℓ : ℝ)))) -
            (-t + ((i : ℝ) - (ℓ : ℝ)) * (t / ((d : ℝ) - (ℓ : ℝ)))) := by
            rw [modelVeePolygon_right t d ℓ hℓ0 hℓi1, modelVeePolygon_right t d ℓ hℓ0 hℓi]
      _ = t / ((d : ℝ) - (ℓ : ℝ)) := by
            rw [Nat.cast_add]
            ring
      _ = (if i < ℓ then -t / (ℓ : ℝ) else t / ((d : ℝ) - (ℓ : ℝ))) := by simp [hi]

/-- The corner slope comparison needed for convexity: `−t/ℓ ≤ +t/(d−ℓ)` (for `0 ≤ t`). -/
lemma corner_slope_le (t : ℝ) (d ℓ : ℕ) (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (ht : 0 ≤ t) :
    -t / (ℓ : ℝ) ≤ t / ((d : ℝ) - (ℓ : ℝ)) := by
  have hℓp : 0 < (ℓ : ℝ) := by exact_mod_cast hℓ0
  have hdp : 0 < (d : ℝ) - (ℓ : ℝ) := by
    rw [← Nat.cast_sub (le_of_lt hℓd)]
    exact_mod_cast (Nat.sub_pos_of_lt hℓd)
  have htd : 0 ≤ t * (d : ℝ) := mul_nonneg ht (Nat.cast_nonneg d)
  field_simp [ne_of_gt hℓp, ne_of_gt hdp]
  nlinarith

/-- The V-shaped model polygon is discrete-convex on `{0,…,d}` for `0 ≤ t` (slopes constant
`−t/ℓ` then `+t/(d−ℓ)`, with the single corner jump `−t/ℓ ≤ +t/(d−ℓ)`). -/
lemma modelVeePolygon_convex (t : ℝ) (d ℓ : ℕ) (hℓ0 : 0 < ℓ) (hℓd : ℓ < d)
    (ht : 0 ≤ t) : Submission.Polygon.DiscreteConvexOn (modelVeePolygon t d ℓ) d := by
  intro i hi
  have hs := dslope_modelVeePolygon t d ℓ hℓ0
  have hcorner := corner_slope_le t d ℓ hℓ0 hℓd ht
  rw [hs i, hs (i + 1)]
  by_cases hi1 : i + 1 < ℓ
  · -- both slopes contracting
    have hi2 : i < ℓ := by omega
    simp [hi1, hi2]
  · -- i + 1 ≥ ℓ: contracting-to-expanding or expanding-to-expanding
    by_cases hi3 : i < ℓ
    · -- the corner jump: slope(i) = −t/ℓ, slope(i+1) = +t/(d−ℓ)
      have hcorner' := hcorner
      simp [hi1, hi3]
      exact hcorner'
    · -- both expanding
      simp [hi1, hi3]


/-! ### The V-polygon is THE polygon (largest convex minorant of the model data)

The model data function `g(i)` — the minimal rank-`i` log-covolume of the exp-flow
lattice, attained on the coordinate sub-lattice of the `i` smallest scales — takes exactly
the values of `modelVeePolygon t d ℓ`: for `i ≤ ℓ` it is the product of `i` contracting
directions (`log = −t·(i/ℓ)`), and for `i > ℓ` all `ℓ` contracting directions plus `i − ℓ`
expanding ones (`log = −t + (i−ℓ)·t/(d−ℓ)`); the formal identification `data = V` is the
§3 covolume/successive-minima computation.  Hence the greatest-convex-minorant bridge
reduces to the convex case: since `modelVeePolygon` is discrete-convex
(`modelVeePolygon_convex`), it is its own largest convex minorant
(`Submission.Polygon.largestConvexMinorant_eq_self_of_convex`) — so once the data function
is identified with `V`, `V` is THE polygon the Grayson machinery works with.
-/

/-- **The V-polygon is the largest convex minorant of the model data**: for `i ≤ d`,
`largestConvexMinorant d (modelVeePolygon t d ℓ) i = modelVeePolygon t d ℓ i`. -/
theorem modelVeePolygon_is_largestConvexMinorant (t : ℝ) (d ℓ : ℕ) (hℓ0 : 0 < ℓ)
    (hℓd : ℓ < d) (ht : 0 ≤ t) {i : ℕ} (hi : i ≤ d) :
    Submission.Polygon.largestConvexMinorant d (modelVeePolygon t d ℓ) i =
      modelVeePolygon t d ℓ i := by
  exact Submission.Polygon.largestConvexMinorant_eq_self_of_convex d (modelVeePolygon t d ℓ)
    (modelVeePolygon_convex t d ℓ hℓ0 hℓd ht) hi


end Submission.ContractPolygon
