import Mathlib
import Submission.Work.ThomBordism.TwoSet.Cells

/-!
# The repaired cutoff lemma: the support must be a neighbourhood of the cell

`Work.RatHurewicz.exists_cutoffs` is **false as stated** (see
`Submission/Work/RatHurewicz/exists_cutoffs.lean` for the counterexample): the support
`Work.RatHurewicz.Triad.cellStar c ε` uses the *exact* closed interval
`[c.lo i / N, c.hi i / N]` in every *interval* direction `i` of `c` and only carries the `ε`-collar
in the node directions.  Hence for any cell with an interval direction away from the boundary of
the cube (`1 ≤ c.lo i` or `c.hi i ≤ N - 1`, which happens as soon as `N ≥ 2`) the wall points of
`cellSet c` lie on the boundary of the support, and a *continuous* `μ` with `μ = 0` off the support
cannot satisfy `2 ≤ μ` on `cellSet c`: continuity forces `μ = 0` on the walls.

In fact the two clauses

* `x ∉ S → μ x = 0`  and  * `x ∈ T → 2 ≤ μ x`

for a continuous `μ` force `T ⊆ interior S`.  Since the requested statement takes `T = cellSet c`,
any valid support `S` must be a **neighbourhood** of `cellSet c`.

This file provides the minimal such support, the **collared support**

`cellStarCollar c ε = {x | ∀ i, c.lo i / N - ε ≤ x i ∧ x i ≤ c.hi i / N + ε}`,

which agrees with `cellStar` in the node directions and enlarges the interval directions by `ε`,
and proves the four clauses for it, with explicit polynomial/cutoff witnesses (no Urysohn lemma
needed).  On `cellSet c` the rate is exactly `2` and the push time exactly `1`.

*Caveat.* Enlarging the support in the interval directions is exactly what makes the "damage" of
the treatment of `c` spill onto the *equidimensional crossing cells* adjacent to its walls (see
`Triad/NOTES_triadCompression.md`, §"What remains", item 2); the bookkeeping of
`triadPreparation` has to be re-examined accordingly.  What this file pins down is that the
support *cannot* be the uncollared `cellStar`.
-/

open scoped Topology unitInterval BigOperators

namespace Work.RatHurewicz

open Work.ThomBordism.TwoSet

noncomputable section

variable {j N : ℕ}

/-- The **collared support** of a cell: the cell thickened by `ε` in *every* direction.  In the
node directions (`c.lo i = c.hi i`) this is the same `ε`-collar as
`Work.RatHurewicz.Triad.cellStar`; in the interval directions it is strictly larger.  -/
noncomputable def cellStarCollar (c : CellIdx j N) (ε : ℝ) : Set (IC j) :=
  {x | ∀ i, (c.lo i : ℝ) / N - ε ≤ (x i : ℝ) ∧ (x i : ℝ) ≤ (c.hi i : ℝ) / N + ε}

theorem mem_cellStarCollar {c : CellIdx j N} {ε : ℝ} {x : IC j} :
    x ∈ cellStarCollar c ε ↔
      ∀ i, (c.lo i : ℝ) / N - ε ≤ (x i : ℝ) ∧ (x i : ℝ) ≤ (c.hi i : ℝ) / N + ε := Iff.rfl

/-- The cell is contained in its collared support (for `ε ≥ 0`). -/
theorem cellSet_subset_cellStarCollar {c : CellIdx j N} {ε : ℝ} (hε : 0 ≤ ε) :
    cellSet c ⊆ cellStarCollar c ε := by
  intro x hx i
  have h := hx i
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- The `i`-th cutoff factor: `1` on the `i`-th coordinate interval of `c` and `0` as soon as the
scaled coordinate is `ε` beyond it. -/
noncomputable def cutoffFactor (c : CellIdx j N) (ε : ℝ) (x : IC j) (i : Fin j) : ℝ :=
  min 1 (max 0 (((N:ℝ) * (x i : ℝ) - (c.lo i : ℝ) + (N:ℝ) * ε) / ((N:ℝ) * ε)))
    * min 1 (max 0 (((c.hi i : ℝ) - (N:ℝ) * (x i : ℝ) + (N:ℝ) * ε) / ((N:ℝ) * ε)))

theorem continuous_cutoffFactor (c : CellIdx j N) (ε : ℝ) (i : Fin j) :
    Continuous fun x : IC j => cutoffFactor c ε x i := by
  have hx : Continuous fun x : IC j => (x i : ℝ) :=
    continuous_subtype_val.comp (continuous_apply i)
  unfold cutoffFactor
  exact (continuous_const.min (continuous_const.max
      (((continuous_const.mul hx).sub continuous_const).add continuous_const |>.div_const _))).mul
    (continuous_const.min (continuous_const.max
      (((continuous_const.sub (continuous_const.mul hx)).add continuous_const) |>.div_const _)))

theorem clamp_zero_one_eq_zero_iff {r : ℝ} : min 1 (max 0 r) = 0 ↔ r ≤ 0 := by
  constructor
  · intro h
    have h1 : max 0 r ≤ 0 := by
      by_contra hlt
      push_neg at hlt
      have : 0 < min 1 (max 0 r) := lt_min (by norm_num) hlt
      linarith
    exact le_trans (le_max_right _ _) h1
  · intro h
    rw [max_eq_left h]; norm_num

theorem clamp_zero_one_eq_one_iff {r : ℝ} : min 1 (max 0 r) = 1 ↔ 1 ≤ r := by
  constructor
  · intro h
    have h1 : (1:ℝ) ≤ max 0 r := by
      have := min_le_right (1:ℝ) (max 0 r)
      rwa [h] at this
    have h2 : (0:ℝ) < max 0 r := lt_of_lt_of_le zero_lt_one h1
    have h3 : (0:ℝ) < r := (lt_max_iff.mp h2).resolve_left (lt_irrefl 0)
    have h4 : max 0 r = r := max_eq_right (le_of_lt h3)
    linarith
  · intro h
    have h4 : max 0 r = r := max_eq_right (le_trans (by norm_num) h)
    rw [h4, min_eq_left h]

/-- The cutoff factor vanishes below the collared coordinate interval. -/
theorem cutoffFactor_eq_zero_of_lt (c : CellIdx j N) {ε : ℝ} (hε : 0 < ε) (hN : 1 ≤ N)
    {x : IC j} {i : Fin j} (hi : (x i : ℝ) < (c.lo i : ℝ)/N - ε) :
    cutoffFactor c ε x i = 0 := by
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hεNpos : (0:ℝ) < (N:ℝ)*ε := mul_pos hNpos hε
  unfold cutoffFactor
  have h1 : (((N:ℝ) * (x i : ℝ) - (c.lo i : ℝ) + (N:ℝ) * ε) / ((N:ℝ) * ε)) < 0 := by
    apply div_neg_of_neg_of_pos _ hεNpos
    have hmul : (N:ℝ) * (x i : ℝ) < (N:ℝ) * ((c.lo i : ℝ)/N - ε) :=
      mul_lt_mul_of_pos_left hi hNpos
    have heq : (N:ℝ) * ((c.lo i : ℝ)/N) = (c.lo i : ℝ) := by field_simp
    nlinarith [hmul, heq]
  rw [clamp_zero_one_eq_zero_iff.mpr (le_of_lt h1), zero_mul]

/-- The cutoff factor vanishes above the collared coordinate interval. -/
theorem cutoffFactor_eq_zero_of_gt (c : CellIdx j N) {ε : ℝ} (hε : 0 < ε) (hN : 1 ≤ N)
    {x : IC j} {i : Fin j} (hi : (c.hi i : ℝ)/N + ε < (x i : ℝ)) :
    cutoffFactor c ε x i = 0 := by
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hεNpos : (0:ℝ) < (N:ℝ)*ε := mul_pos hNpos hε
  unfold cutoffFactor
  have h1 : (((c.hi i : ℝ) - (N:ℝ) * (x i : ℝ) + (N:ℝ) * ε) / ((N:ℝ) * ε)) < 0 := by
    apply div_neg_of_neg_of_pos _ hεNpos
    have hmul : (N:ℝ) * ((c.hi i : ℝ)/N + ε) < (N:ℝ) * (x i : ℝ) :=
      mul_lt_mul_of_pos_left hi hNpos
    have heq : (N:ℝ) * ((c.hi i : ℝ)/N) = (c.hi i : ℝ) := by field_simp
    nlinarith [hmul, heq]
  rw [clamp_zero_one_eq_zero_iff.mpr (le_of_lt h1), mul_zero]

/-- The cutoff factor equals `1` on the coordinate interval of `c`. -/
theorem cutoffFactor_eq_one_of_mem (c : CellIdx j N) {ε : ℝ} (hε : 0 < ε) (hN : 1 ≤ N)
    {x : IC j} {i : Fin j} (h1 : (c.lo i : ℝ)/N ≤ (x i : ℝ))
    (h2 : (x i : ℝ) ≤ (c.hi i : ℝ)/N) : cutoffFactor c ε x i = 1 := by
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hεNpos : (0:ℝ) < (N:ℝ)*ε := mul_pos hNpos hε
  unfold cutoffFactor
  have hA : min 1 (max 0 (((N:ℝ) * (x i : ℝ) - (c.lo i : ℝ) + (N:ℝ) * ε) / ((N:ℝ) * ε))) = 1 := by
    rw [clamp_zero_one_eq_one_iff, le_div_iff₀ hεNpos]
    have hmul := mul_le_mul_of_nonneg_left h1 (le_of_lt hNpos)
    have heq : (N:ℝ) * ((c.lo i : ℝ)/N) = (c.lo i : ℝ) := by field_simp
    linarith
  have hB : min 1 (max 0 (((c.hi i : ℝ) - (N:ℝ) * (x i : ℝ) + (N:ℝ) * ε) / ((N:ℝ) * ε))) = 1 := by
    rw [clamp_zero_one_eq_one_iff, le_div_iff₀ hεNpos]
    have hmul := mul_le_mul_of_nonneg_left h2 (le_of_lt hNpos)
    have heq : (N:ℝ) * ((c.hi i : ℝ)/N) = (c.hi i : ℝ) := by field_simp
    linarith
  rw [hA, hB, mul_one]

/-- **The repaired cutoff lemma.**  For the *collared* support `cellStarCollar c ε` the four
clauses of `Work.RatHurewicz.exists_cutoffs` hold, with explicit witnesses.  (`cellStar c ε`, the
uncollared support, is refuted in `Submission/Work/RatHurewicz/exists_cutoffs.lean`.) -/
theorem exists_cutoffs_collar {j N : ℕ} (hN : 1 ≤ N) (c : CellIdx j N) {ε : ℝ} (hε : 0 < ε) :
    ∃ (μ : C(IC j, ℝ)) (ν : C(IC j, unitInterval)),
      (∀ x, x ∉ cellStarCollar c ε → μ x = 0) ∧
      (∀ x, x ∈ cellSet c → 2 ≤ μ x) ∧
      (∀ x, x ∈ cellSet c → ν x = 1) ∧
      (∀ x, μ x ≤ 1 → ν x = 0) := by
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hεNpos : (0:ℝ) < (N:ℝ) * ε := mul_pos hNpos hε
  set μfun : IC j → ℝ := fun x => 2 * ∏ i : Fin j, cutoffFactor c ε x i with hμfun
  have hμcont : Continuous μfun := by
    rw [hμfun]
    exact continuous_const.mul (continuous_finsetProd _ (fun i _ => continuous_cutoffFactor c ε i))
  let νfun : IC j → unitInterval := fun x =>
    ⟨min 1 (max 0 (μfun x - 1)), ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩⟩
  have hνcont : Continuous νfun :=
    Continuous.subtype_mk
      (continuous_const.min (continuous_const.max (hμcont.sub continuous_const))) _
  have hx' : ∀ x : IC j, x ∉ cellStarCollar c ε →
      ∃ i : Fin j, (x i : ℝ) < (c.lo i : ℝ)/N - ε ∨ (c.hi i : ℝ)/N + ε < (x i : ℝ) := by
    intro x hx
    by_contra hc
    push_neg at hc
    exact hx fun i => hc i
  have hmemfac : ∀ x, x ∈ cellSet c → ∀ i : Fin j, cutoffFactor c ε x i = 1 := by
    intro x hx i
    exact cutoffFactor_eq_one_of_mem c hε hN (mem_cellSet.mp hx i).1 (mem_cellSet.mp hx i).2
  have hzero : ∀ x, x ∉ cellStarCollar c ε → μfun x = 0 := by
    intro x hx
    obtain ⟨i, hi | hi⟩ := hx' x hx
    · change 2 * ∏ k : Fin j, cutoffFactor c ε x k = 0
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (cutoffFactor_eq_zero_of_lt c hε hN hi), mul_zero]
    · change 2 * ∏ k : Fin j, cutoffFactor c ε x k = 0
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (cutoffFactor_eq_zero_of_gt c hε hN hi), mul_zero]
  have hge : ∀ x, x ∈ cellSet c → 2 ≤ μfun x := by
    intro x hx
    change 2 ≤ 2 * ∏ k : Fin j, cutoffFactor c ε x k
    have hp : (∏ k : Fin j, cutoffFactor c ε x k) = 1 :=
      Finset.prod_eq_one (fun i _ => hmemfac x hx i)
    rw [hp, mul_one]
  have hν1 : ∀ x, x ∈ cellSet c → νfun x = 1 := by
    intro x hx
    have h2 : μfun x = 2 := by
      change 2 * ∏ k : Fin j, cutoffFactor c ε x k = 2
      have hp : (∏ k : Fin j, cutoffFactor c ε x k) = 1 :=
        Finset.prod_eq_one (fun i _ => hmemfac x hx i)
      rw [hp, mul_one]
    apply Subtype.ext
    change min 1 (max 0 (μfun x - 1)) = ((1 : unitInterval) : ℝ)
    rw [h2]
    norm_num
  have hν0 : ∀ x, μfun x ≤ 1 → νfun x = 0 := by
    intro x hx
    apply Subtype.ext
    change min 1 (max 0 (μfun x - 1)) = ((0 : unitInterval) : ℝ)
    have hle : μfun x - 1 ≤ 0 := by linarith
    rw [max_eq_left hle]
    norm_num
  exact ⟨⟨μfun, hμcont⟩, ⟨νfun, hνcont⟩, hzero, hge, hν1, hν0⟩

end

end Work.RatHurewicz
