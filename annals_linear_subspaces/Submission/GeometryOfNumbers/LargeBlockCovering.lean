import Mathlib
import Submission.GeometryOfNumbers.LargeBlockMinima

/-!
# Covering radius of the expanding block and lattice points near unit directions

The mirror of `BlockCovering` on the **expanding** coordinates `j.val ≥ ℓ`.  For the
two-scale flow with scale `b > 0` on the last `d − ℓ` coordinates, the expanding block
`largeFlow a b ℓ` (the `ℤ`-span of `b e_j`, `j.val ≥ ℓ`) acts on its real span
`largeSpan ℓ = Span {(B d) j | j.val ≥ ℓ}` (the coordinate subspace of dimension `d − ℓ`).
Its successive minima are all exactly `b` (`LargeBlockMinima.successiveMinimum_largeFlow_eq`),
and here we prove the metric core of the paper §3 Prop-5 "approach unit directions with
block-lattice vectors of controlled size in an annulus" step on the expanding side, again
**without** any full-rank `IsZLattice` instance:

* `covering_radius_large`: every `x ∈ largeSpan ℓ` is within `(d−ℓ:ℝ)·b` of a point of
  `largeFlow` — an *exact* bound with no slack; proof by direct floor-rounding of the block
  coordinates (write `x = Σ c_j • e_j` over the expanding coordinates, take
  `v = Σ ⌊c_j/b⌋ • (b e_j) ∈ largeFlow`; each rounding error is `≤ b`, so
  `‖x − v‖ ≤ Σ |c_j − b·⌊c_j/b⌋| ≤ (d−ℓ)·b`);
* `exists_largePoint_near_direction`: for a unit vector `u ∈ largeSpan ℓ` and `M ≥ 0`, there
  is a block lattice point `v` with `‖v − M·u‖ ≤ (d−ℓ:ℝ)·b` and
  `‖v‖ ∈ [M − (d−ℓ:ℝ)b, M + (d−ℓ:ℝ)b]`;
* **`exists_largePoint_annulus`** — the model Prop-5 block-approximation step on the
  expanding side: with the anchor `M = 11·(d−ℓ:ℝ)b`, one obtains `v ∈ largeFlow` of norm in
  `[10·(d−ℓ:ℝ)b, 12·(d−ℓ:ℝ)b]` within `(d−ℓ:ℝ)b` of the point `11·(d−ℓ:ℝ)b·u` (hence of the
  line `ℝ·u`); `exists_largeFamily_annulus` is the same for a family of unit directions.

All of the above come in two-scale form (parameters `a b`) and in exponential-flow form
(`a = exp(-t/ℓ)`, `b = exp(t/(d-ℓ))` — suffix `_exp`), the expanding block of the model §3
lattice `a_t ℤᵈ` with expanding directions of scale `exp(t/(d-ℓ))`.

All results are Mathlib-only.
-/

noncomputable section

open Set Filter Metric MeasureTheory Module Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open LinearSubspaces
open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.FlowLattice

namespace Submission.LargeBlockCovering

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- The standard basis vectors of the expanding block (unit, pairwise orthogonal), indexed
by the coordinates at or above `ℓ`. -/
def largeAmb (ℓ : ℕ) (j : {j : Fin d // ℓ ≤ j.val}) : ℝᵈ := (B d) j.1

/-- The real span of the expanding block: the coordinate subspace
`Span {(B d) j | j.val ≥ ℓ}` (dimension `d − ℓ`). -/
abbrev largeSpan (ℓ : ℕ) : Submodule ℝ ℝᵈ :=
  Submodule.span ℝ (Set.range (largeAmb (d := d) ℓ))

/-- The flow image of a standard basis vector of the expanding block. -/
abbrev largeBlockVec (a b : ℝ) (ℓ : ℕ) (j : {j : Fin d // ℓ ≤ j.val}) : ℝᵈ :=
  scaleMap (twoScale a b ℓ) ((B d) j.1)

/-- Each expanding generator is the `b`-multiple of the ambient basis vector `largeAmb`
(because `ℓ ≤ j.val`, the two-scale flow coefficient at `j` is `b`). -/
lemma largeBlockVec_eq_smul {a b : ℝ} (ℓ : ℕ) (j : {j : Fin d // ℓ ≤ j.val}) :
    largeBlockVec (d := d) a b ℓ j = b • largeAmb (d := d) (ℓ := ℓ) j := by
  unfold largeBlockVec largeAmb
  rw [scaleMap_basis, twoScale_apply]
  have hnot : ¬ j.1.val < ℓ := not_lt_of_ge j.2
  simp [hnot]

/-- The ambient norm of an expanding basis vector is `1`. -/
lemma largeAmb_norm (ℓ : ℕ) (j : {j : Fin d // ℓ ≤ j.val}) :
    ‖largeAmb (d := d) (ℓ := ℓ) j‖ = 1 := by
  simp [largeAmb]

/-- A ℤ-combination of the expanding block generators is a member of the large block (the
block is by definition their `ℤ`-span). -/
lemma largeComb_mem_largeFlow {a b : ℝ} (ℓ : ℕ) (n : {j : Fin d // ℓ ≤ j.val} → ℤ) :
    (∑ j : {j : Fin d // ℓ ≤ j.val}, (n j : ℤ) • largeBlockVec (d := d) a b ℓ j) ∈
      Submission.LargeBlockMinima.largeFlow (d := d) a b ℓ := by
  unfold Submission.LargeBlockMinima.largeFlow
  exact Submodule.sum_mem _ (by
    intro j hj
    exact Submodule.smul_mem _ (n j) (Submodule.subset_span ⟨j, rfl⟩))

/-- The cardinality of the expanding-block index type is `d − ℓ`. -/
lemma card_large_index (ℓ : ℕ) (hℓd : ℓ ≤ d) :
    Fintype.card {j : Fin d // ℓ ≤ j.val} = d - ℓ := by
  classical
  let e : {j : Fin d // ℓ ≤ j.val} ≃ Fin (d - ℓ) :=
    { toFun := fun j => ⟨j.1.val - ℓ, by
          have hlt : j.1.val < d := j.1.isLt
          omega⟩
      invFun := fun r => ⟨⟨ℓ + r.val, by
          have hr : r.val < d - ℓ := r.isLt
          omega⟩, by
          exact Nat.le_add_right ℓ r.val⟩
      left_inv := by
        intro j
        apply Subtype.ext
        apply Fin.ext
        exact Nat.add_sub_of_le j.2
      right_inv := by
        intro r
        apply Fin.ext
        exact Nat.add_sub_cancel_left ℓ r.val }
  rw [Fintype.card_congr e, Fintype.card_fin]

/-- **Covering radius of the expanding block**: for `0 < b`, every point
`x ∈ largeSpan ℓ` (the coordinate subspace spanned by the block) is within distance
`(d−ℓ:ℝ)·b` of a point of `largeFlow a b ℓ` (no slack: the block generators have norm
exactly `b`, so the rounding is exact).  Proof: write `x = Σ c_j • e_j` (block
coordinates), round each `c_j / b` to the integer `n_j = ⌊c_j/b⌋`, and let
`v = Σ n_j • (b e_j) ∈ largeFlow`; then `‖x − v‖ ≤ Σ |c_j − b n_j| ≤ (d−ℓ)·b`. -/
theorem covering_radius_large (ℓ : ℕ) (hℓd : ℓ ≤ d) {a b : ℝ} (hb0 : 0 < b)
    {x : ℝᵈ} (hx : x ∈ largeSpan (d := d) ℓ) :
    ∃ v : Submission.LargeBlockMinima.largeFlow (d := d) a b ℓ,
      ‖x - (v : ℝᵈ)‖ ≤ ((d - ℓ : ℕ) : ℝ) * b := by
  classical
  let L : Type := {j : Fin d // ℓ ≤ j.val}
  let S : Submodule ℤ ℝᵈ := Submission.LargeBlockMinima.largeFlow (d := d) a b ℓ
  have hx' : x ∈ Submodule.span ℝ (Set.range (largeAmb (d := d) ℓ)) := by
    simpa [largeSpan] using hx
  rcases (Submodule.mem_span_range_iff_exists_fun (R := ℝ)).mp hx' with ⟨c, hc⟩
  let n : L → ℤ := fun j => Int.floor (c j / b)
  let v : S := ⟨∑ j : L, (n j : ℤ) • largeBlockVec (d := d) a b ℓ j, by
    exact largeComb_mem_largeFlow (d := d) (a := a) (b := b) ℓ n⟩
  have hv_eq : ((v : S) : ℝᵈ) = ∑ j : L, (((n j : ℤ) : ℝ) * b) • largeAmb (d := d) (ℓ := ℓ) j := by
    calc
      ((v : S) : ℝᵈ) = ∑ j : L, (n j : ℤ) • largeBlockVec (d := d) a b ℓ j := by
        rfl
      _ = ∑ j : L, (((n j : ℤ) : ℝ) • largeBlockVec (d := d) a b ℓ j) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (Int.cast_smul_eq_zsmul ℝ (n j) (largeBlockVec (d := d) a b ℓ j)).symm
      _ = ∑ j : L, (((n j : ℤ) : ℝ) * b) • largeAmb (d := d) (ℓ := ℓ) j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [largeBlockVec_eq_smul (d := d) (a := a) (b := b) ℓ j]
        rw [mul_smul]
  have hδ0 : ∀ j : L, 0 ≤ c j - ((n j : ℤ) : ℝ) * b := by
    intro j
    have hfl : ((n j : ℤ) : ℝ) ≤ c j / b := by
      dsimp [n]
      exact Int.floor_le (c j / b)
    have hfl' : ((n j : ℤ) : ℝ) * b ≤ c j := by
      have hm := mul_le_mul_of_nonneg_right hfl (le_of_lt hb0)
      rwa [div_mul_cancel₀ (c j) (ne_of_gt hb0)] at hm
    linarith
  have hδa : ∀ j : L, c j - ((n j : ℤ) : ℝ) * b ≤ b := by
    intro j
    have hlt : c j / b < ((n j : ℤ) : ℝ) + 1 := by
      dsimp [n]
      exact Int.lt_floor_add_one (c j / b)
    have hlt' : c j < ((n j : ℤ) : ℝ) * b + b := by
      have hm := mul_lt_mul_of_pos_right hlt hb0
      rwa [div_mul_cancel₀ (c j) (ne_of_gt hb0), add_mul, one_mul] at hm
    linarith
  refine ⟨v, ?_⟩
  have hdiff : x - ((v : S) : ℝᵈ) = ∑ j : L,
      (c j - ((n j : ℤ) : ℝ) * b) • largeAmb (d := d) (ℓ := ℓ) j := by
    calc
      x - ((v : S) : ℝᵈ)
          = (∑ j : L, c j • largeAmb (d := d) (ℓ := ℓ) j) -
              (∑ j : L, (((n j : ℤ) : ℝ) * b) • largeAmb (d := d) (ℓ := ℓ) j) := by
              rw [← hc, hv_eq]
      _ = ∑ j : L,
              (c j • largeAmb (d := d) (ℓ := ℓ) j -
                (((n j : ℤ) : ℝ) * b) • largeAmb (d := d) (ℓ := ℓ) j) := by
              rw [← Finset.sum_sub_distrib]
      _ = ∑ j : L,
              (c j - ((n j : ℤ) : ℝ) * b) • largeAmb (d := d) (ℓ := ℓ) j := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [← sub_smul]
  calc
    ‖x - ((v : S) : ℝᵈ)‖
        = ‖∑ j : L,
            (c j - ((n j : ℤ) : ℝ) * b) • largeAmb (d := d) (ℓ := ℓ) j‖ := by rw [hdiff]
    _ ≤ ∑ j : L, ‖((c j - ((n j : ℤ) : ℝ) * b) • largeAmb (d := d) (ℓ := ℓ) j)‖ := norm_sum_le _ _
    _ ≤ ∑ j : L, b := by
        apply Finset.sum_le_sum
        intro j hj
        calc
          ‖((c j - ((n j : ℤ) : ℝ) * b) • largeAmb (d := d) (ℓ := ℓ) j)‖
              = |c j - ((n j : ℤ) : ℝ) * b| * ‖largeAmb (d := d) (ℓ := ℓ) j‖ := by
                  rw [norm_smul, Real.norm_eq_abs]
          _ = |c j - ((n j : ℤ) : ℝ) * b| := by rw [largeAmb_norm (d := d) ℓ j, mul_one]
          _ = c j - ((n j : ℤ) : ℝ) * b := abs_of_nonneg (hδ0 j)
          _ ≤ b := hδa j
    _ = (Fintype.card L : ℝ) * b := by simp
    _ = ((d - ℓ : ℕ) : ℝ) * b := by
          rw [card_large_index (d := d) ℓ hℓd]

/-- **Expanding-block lattice point near a prescribed unit direction, with controlled
size**: for `0 < b`, a unit vector `u ∈ largeSpan ℓ` and `M ≥ 0`, there is an expanding
block lattice point `v` within distance `(d−ℓ:ℝ)·b` of `M·u`, whose norm lies in the
interval `[M − (d−ℓ:ℝ)b, M + (d−ℓ:ℝ)b]`.  (Metric core of paper §3 Prop 5 on the expanding
side: taking `M := 11C` with `C := (d−ℓ:ℝ)b` places `‖v‖` in `[10C, 12C]` at distance
`≤ C` from the line `ℝ·u`.) -/
theorem exists_largePoint_near_direction (ℓ : ℕ) (hℓd : ℓ ≤ d) {a b : ℝ} (hb0 : 0 < b)
    {u : ℝᵈ} (hu : u ∈ largeSpan (d := d) ℓ) (hu1 : ‖u‖ = 1)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ v : Submission.LargeBlockMinima.largeFlow (d := d) a b ℓ,
      ‖(v : ℝᵈ) - M • u‖ ≤ ((d - ℓ : ℕ) : ℝ) * b ∧
      M - ((d - ℓ : ℕ) : ℝ) * b ≤ ‖(v : ℝᵈ)‖ ∧
      ‖(v : ℝᵈ)‖ ≤ M + ((d - ℓ : ℕ) : ℝ) * b := by
  classical
  let C : ℝ := ((d - ℓ : ℕ) : ℝ) * b
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (Nat.cast_nonneg (d - ℓ)) (le_of_lt hb0)
  have hMmem : M • u ∈ largeSpan (d := d) ℓ := Submodule.smul_mem _ M hu
  obtain ⟨v, hv⟩ := covering_radius_large (d := d) ℓ hℓd (a := a) (b := b) hb0 (x := M • u) hMmem
  have hvM : ‖M • u - (v : ℝᵈ)‖ ≤ C := by
    simpa [C] using hv
  have hvM' : ‖(v : ℝᵈ) - M • u‖ ≤ C := by
    simpa [norm_sub_rev] using hvM
  have hmul : ‖M • u‖ = M := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hM, hu1, mul_one]
  refine ⟨v, ?_, ?_, ?_⟩
  · simpa [C] using hvM'
  · have hveq : (M • u - (v : ℝᵈ)) + (v : ℝᵈ) = M • u := by abel
    have hmain : ‖(M • u - (v : ℝᵈ)) + (v : ℝᵈ)‖ ≤ ‖M • u - (v : ℝᵈ)‖ + ‖(v : ℝᵈ)‖ :=
      norm_add_le _ _
    have h₀ : ‖M • u‖ ≤ ‖M • u - (v : ℝᵈ)‖ + ‖(v : ℝᵈ)‖ := by
      simpa [hveq] using hmain
    rw [hmul] at h₀
    linarith
  · have hveq : ((v : ℝᵈ) - M • u) + M • u = (v : ℝᵈ) := by abel
    have hmain : ‖((v : ℝᵈ) - M • u) + M • u‖ ≤ ‖(v : ℝᵈ) - M • u‖ + ‖M • u‖ :=
      norm_add_le _ _
    have h₀ : ‖(v : ℝᵈ)‖ ≤ ‖(v : ℝᵈ) - M • u‖ + ‖M • u‖ := by
      simpa [hveq] using hmain
    rw [hmul] at h₀
    linarith

end Submission.LargeBlockCovering

namespace Submission.LargeBlockCovering

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- **Covering radius of the expanding block in the exponential flow**: every
`x ∈ largeSpan ℓ` is within `(d−ℓ:ℝ)·exp(t/(d−ℓ))` of a point of the expanding block of
`a_t ℤᵈ` (`a = exp(-t/ℓ)`, `b = exp(t/(d−ℓ))`) — the model instance of the paper §3
lattice `a_t ℤᵈ`. -/
theorem covering_radius_large_exp (ℓ : ℕ) (hℓd : ℓ < d)
    {t : ℝ} {x : ℝᵈ} (hx : x ∈ largeSpan (d := d) ℓ) :
    ∃ v : Submission.LargeBlockMinima.largeFlow (d := d)
        (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ,
      ‖x - (v : ℝᵈ)‖ ≤ ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) := by
  rcases covering_radius_large (d := d) ℓ (le_of_lt hℓd)
    (a := Real.exp (-t / (ℓ : ℝ))) (b := Real.exp (t / ((d : ℝ) - (ℓ : ℝ))))
    (Real.exp_pos _) (x := x) hx with ⟨v, hv⟩
  exact ⟨v, by simpa using hv⟩

/-- **Expanding-block lattice point near a prescribed unit direction in the exponential
flow**: a unit `u ∈ largeSpan ℓ` and `M ≥ 0`, there is a point `v` of the expanding block
of `a_t ℤᵈ` within `(d−ℓ:ℝ)·exp(t/(d−ℓ))` of `M·u`, of norm in
`[M − (d−ℓ:ℝ)exp(t/(d−ℓ)), M + (d−ℓ:ℝ)exp(t/(d−ℓ))]`. -/
theorem exists_largePoint_near_direction_exp (ℓ : ℕ) (hℓd : ℓ < d)
    {t : ℝ} {u : ℝᵈ} (hu : u ∈ largeSpan (d := d) ℓ) (hu1 : ‖u‖ = 1)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ v : Submission.LargeBlockMinima.largeFlow (d := d)
        (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ,
      ‖(v : ℝᵈ) - M • u‖ ≤ ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) ∧
      M - ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) ≤ ‖(v : ℝᵈ)‖ ∧
      ‖(v : ℝᵈ)‖ ≤ M + ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) := by
  rcases exists_largePoint_near_direction (d := d) ℓ (le_of_lt hℓd)
    (a := Real.exp (-t / (ℓ : ℝ))) (b := Real.exp (t / ((d : ℝ) - (ℓ : ℝ))))
    (Real.exp_pos _) (u := u) hu hu1 (M := M) hM with ⟨v, hd, hl, hu'⟩
  exact ⟨v, by simpa using hd, by simpa using hl, by simpa using hu'⟩

end Submission.LargeBlockCovering

namespace Submission.LargeBlockCovering

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- **Prop-5 block-approximation, expanding block**: for a unit direction
`u ∈ largeSpan ℓ` (the real span of the block) and `0 < b`, there is an expanding block
lattice point `v` of norm in `[10·(d−ℓ:ℝ)b, 12·(d−ℓ:ℝ)b]` whose distance to the point
`11·(d−ℓ:ℝ)b · u` (hence to the line `ℝ·u`) is at most `(d−ℓ:ℝ)b`.  This is the paper §3
Prop 5 metric step on the expanding side (mirror of `BlockCovering.exists_blockPoint_annulus`). -/
theorem exists_largePoint_annulus (ℓ : ℕ) (hℓd : ℓ ≤ d) {a b : ℝ} (hb0 : 0 < b)
    {u : ℝᵈ} (hu : u ∈ largeSpan (d := d) ℓ) (hu1 : ‖u‖ = 1) :
    ∃ v : Submission.LargeBlockMinima.largeFlow (d := d) a b ℓ,
      ‖(v : ℝᵈ) - ((11 : ℝ) * ((d - ℓ : ℕ) : ℝ) * b) • u‖ ≤ ((d - ℓ : ℕ) : ℝ) * b ∧
      (10 : ℝ) * ((d - ℓ : ℕ) : ℝ) * b ≤ ‖(v : ℝᵈ)‖ ∧
      ‖(v : ℝᵈ)‖ ≤ (12 : ℝ) * ((d - ℓ : ℕ) : ℝ) * b := by
  classical
  have hpos : 0 ≤ ((d - ℓ : ℕ) : ℝ) * b := mul_nonneg (Nat.cast_nonneg (d - ℓ)) (le_of_lt hb0)
  rcases exists_largePoint_near_direction (d := d) ℓ hℓd (a := a) (b := b) hb0
    (u := u) hu hu1 (M := 11 * (((d - ℓ : ℕ) : ℝ) * b))
    (by exact mul_nonneg (by norm_num) hpos) with ⟨v, hd, hl, hu'⟩
  refine ⟨v, ?_, ?_, ?_⟩
  · have hs : ((11 : ℝ) * ((d - ℓ : ℕ) : ℝ)) * b = 11 * (((d - ℓ : ℕ) : ℝ) * b) := by ring
    rw [hs]
    exact hd
  · have hs : ((10 : ℝ) * ((d - ℓ : ℕ) : ℝ)) * b = 11 * (((d - ℓ : ℕ) : ℝ) * b) - ((d - ℓ : ℕ) : ℝ) * b := by ring
    rw [hs]
    exact hl
  · have hs : ((12 : ℝ) * ((d - ℓ : ℕ) : ℝ)) * b = 11 * (((d - ℓ : ℕ) : ℝ) * b) + ((d - ℓ : ℕ) : ℝ) * b := by ring
    rw [hs]
    exact hu'

/-- **Prop-5 block-approximation in the exponential flow (expanding block)**: for a unit
`u ∈ largeSpan ℓ`, there is a point `v` of the expanding block of `a_t ℤᵈ` of norm in
`[10·(d−ℓ:ℝ)e^{t/(d−ℓ)}, 12·(d−ℓ:ℝ)e^{t/(d−ℓ)}]` within `(d−ℓ:ℝ)e^{t/(d−ℓ)}` of the point
`11·(d−ℓ:ℝ)e^{t/(d−ℓ)}·u` (hence of the line `ℝ·u`). -/
theorem exists_largePoint_annulus_exp (ℓ : ℕ) (hℓd : ℓ < d)
    {t : ℝ} {u : ℝᵈ} (hu : u ∈ largeSpan (d := d) ℓ) (hu1 : ‖u‖ = 1) :
    ∃ v : Submission.LargeBlockMinima.largeFlow (d := d)
        (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ,
      ‖(v : ℝᵈ) - ((11 : ℝ) * ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) • u‖ ≤
        ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) ∧
      (10 : ℝ) * ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) ≤ ‖(v : ℝᵈ)‖ ∧
      ‖(v : ℝᵈ)‖ ≤ (12 : ℝ) * ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) := by
  rcases exists_largePoint_annulus (d := d) ℓ (le_of_lt hℓd)
    (a := Real.exp (-t / (ℓ : ℝ))) (b := Real.exp (t / ((d : ℝ) - (ℓ : ℝ))))
    (Real.exp_pos _) (u := u) hu hu1 with ⟨v, hd, hl, hu'⟩
  exact ⟨v, by simpa using hd, by simpa using hl, by simpa using hu'⟩

/-- **Prop-5 block-approximation for a family of unit directions (expanding block)**: for a
family `u : Fin m → ℝᵈ` of unit vectors in `largeSpan ℓ` and `0 < b`, there are expanding
block lattice points `v i` (one per direction), each of norm in `[10·C, 12·C]` and within
`C` of the point `11·C·u i` on its line, `C := (d−ℓ:ℝ)·b`. -/
theorem exists_largeFamily_annulus (ℓ : ℕ) (hℓd : ℓ ≤ d) {a b : ℝ} (hb0 : 0 < b)
    {m : ℕ} {u : Fin m → ℝᵈ} (hu : ∀ i, u i ∈ largeSpan (d := d) ℓ)
    (hu1 : ∀ i, ‖u i‖ = 1) :
    ∃ v : Fin m → Submission.LargeBlockMinima.largeFlow (d := d) a b ℓ,
      ∀ i, ‖(v i : ℝᵈ) - ((11 : ℝ) * ((d - ℓ : ℕ) : ℝ) * b) • u i‖ ≤ ((d - ℓ : ℕ) : ℝ) * b ∧
        (10 : ℝ) * ((d - ℓ : ℕ) : ℝ) * b ≤ ‖(v i : ℝᵈ)‖ ∧
        ‖(v i : ℝᵈ)‖ ≤ (12 : ℝ) * ((d - ℓ : ℕ) : ℝ) * b := by
  classical
  refine ⟨fun i => Classical.choose (exists_largePoint_annulus (d := d) ℓ hℓd (a := a)
    (b := b) hb0 (u := u i) (hu i) (hu1 i)), ?_⟩
  intro i
  exact Classical.choose_spec (exists_largePoint_annulus (d := d) ℓ hℓd (a := a)
    (b := b) hb0 (u := u i) (hu i) (hu1 i))

/-- **Prop-5 block-approximation for a family of unit directions in the exponential flow
(expanding block)**: for unit `u i ∈ largeSpan ℓ`, there are points `v i` of the expanding
block of `a_t ℤᵈ`, each of norm in `[10·C, 12·C]` and within `C` of `11·C·u i`,
`C := (d−ℓ:ℝ)·e^{t/(d−ℓ)}`. -/
theorem exists_largeFamily_annulus_exp (ℓ : ℕ) (hℓd : ℓ < d)
    {t : ℝ} {m : ℕ} {u : Fin m → ℝᵈ} (hu : ∀ i, u i ∈ largeSpan (d := d) ℓ)
    (hu1 : ∀ i, ‖u i‖ = 1) :
    ∃ v : Fin m → Submission.LargeBlockMinima.largeFlow (d := d)
        (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ,
      ∀ i, ‖(v i : ℝᵈ) -
            ((11 : ℝ) * ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) • u i‖ ≤
            ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) ∧
        (10 : ℝ) * ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) ≤ ‖(v i : ℝᵈ)‖ ∧
        ‖(v i : ℝᵈ)‖ ≤ (12 : ℝ) * ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) := by
  classical
  refine ⟨fun i => Classical.choose (exists_largePoint_annulus_exp (d := d) ℓ hℓd
    (u := u i) (hu i) (hu1 i)), ?_⟩
  intro i
  exact Classical.choose_spec (exists_largePoint_annulus_exp (d := d) ℓ hℓd
    (u := u i) (hu i) (hu1 i))

/-- **`k`-dependent block-approximation, expanding block**: for a unit direction
`u ∈ largeSpan ℓ` and `1 ≤ k`, there is an expanding block lattice point `v` of norm in
`[(11k−1)·C, (11k+1)·C]` whose distance to `(11k)·C·u` (hence to the line `ℝ·u`) is at most
`C`, `C := (d−ℓ:ℝ)·b` — the general-`k` anchor (`k = 1` recovers the `[10C, 12C]` annulus
of `exists_largePoint_annulus`; the direction error `‖v/‖v‖ − u‖ ≤ 2/(11k−1)` shrinks like
`1/k`, feeding the general-`k` wedge lower bound). -/
theorem exists_largePoint_annulus_k (ℓ : ℕ) (hℓd : ℓ ≤ d) {a b : ℝ} (hb0 : 0 < b)
    {u : ℝᵈ} (hu : u ∈ largeSpan (d := d) ℓ) (hu1 : ‖u‖ = 1) {k : ℕ} (hk : 1 ≤ k) :
    ∃ v : Submission.LargeBlockMinima.largeFlow (d := d) a b ℓ,
      ‖(v : ℝᵈ) - (((11 : ℝ) * (k : ℝ)) * ((d - ℓ : ℕ) : ℝ) * b) • u‖ ≤ ((d - ℓ : ℕ) : ℝ) * b ∧
      (((11 : ℝ) * (k : ℝ) - 1) * ((d - ℓ : ℕ) : ℝ)) * b ≤ ‖(v : ℝᵈ)‖ ∧
      ‖(v : ℝᵈ)‖ ≤ (((11 : ℝ) * (k : ℝ) + 1) * ((d - ℓ : ℕ) : ℝ)) * b := by
  classical
  let C : ℝ := ((d - ℓ : ℕ) : ℝ) * b
  have hpos : 0 ≤ C := mul_nonneg (Nat.cast_nonneg (d - ℓ)) (le_of_lt hb0)
  have hkR0 : 0 ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
  have hMpos : 0 ≤ ((11 : ℝ) * (k : ℝ)) * C := by
    exact mul_nonneg (mul_nonneg (by norm_num) hkR0) hpos
  rcases exists_largePoint_near_direction (d := d) ℓ hℓd (a := a) (b := b) hb0
    (u := u) hu hu1 (M := ((11 : ℝ) * (k : ℝ)) * C) hMpos with ⟨v, hd, hl, hu'⟩
  refine ⟨v, ?_, ?_, ?_⟩
  · have hs : ((11 : ℝ) * (k : ℝ)) * ((d - ℓ : ℕ) : ℝ) * b =
        ((11 : ℝ) * (k : ℝ)) * C := by
      dsimp [C]
      ring
    rw [hs]
    exact hd
  · have hs : (((11 : ℝ) * (k : ℝ) - 1) * ((d - ℓ : ℕ) : ℝ)) * b =
        ((11 : ℝ) * (k : ℝ)) * C - C := by
      dsimp [C]
      ring
    rw [hs]
    exact hl
  · have hs : (((11 : ℝ) * (k : ℝ) + 1) * ((d - ℓ : ℕ) : ℝ)) * b =
        ((11 : ℝ) * (k : ℝ)) * C + C := by
      dsimp [C]
      ring
    rw [hs]
    exact hu'

/-- **`k`-dependent block-approximation in the exponential flow (expanding block)**:
anchor `(11k)·C`, `C = (d−ℓ)·e^{t/(d−ℓ)}`. -/
theorem exists_largePoint_annulus_k_exp (ℓ : ℕ) (hℓd : ℓ < d)
    {t : ℝ} {u : ℝᵈ} (hu : u ∈ largeSpan (d := d) ℓ) (hu1 : ‖u‖ = 1) {k : ℕ} (hk : 1 ≤ k) :
    ∃ v : Submission.LargeBlockMinima.largeFlow (d := d)
        (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ,
      ‖(v : ℝᵈ) - (((11 : ℝ) * (k : ℝ)) * ((d - ℓ : ℕ) : ℝ) *
          Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) • u‖ ≤
        ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) ∧
      (((11 : ℝ) * (k : ℝ) - 1) * ((d - ℓ : ℕ) : ℝ)) *
          Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) ≤ ‖(v : ℝᵈ)‖ ∧
      ‖(v : ℝᵈ)‖ ≤ (((11 : ℝ) * (k : ℝ) + 1) * ((d - ℓ : ℕ) : ℝ)) *
          Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) := by
  rcases exists_largePoint_annulus_k (d := d) ℓ (le_of_lt hℓd)
    (a := Real.exp (-t / (ℓ : ℝ))) (b := Real.exp (t / ((d : ℝ) - (ℓ : ℝ))))
    (Real.exp_pos _) (u := u) hu hu1 hk with ⟨v, hd, hl, hu'⟩
  exact ⟨v, by simpa using hd, by simpa using hl, by simpa using hu'⟩

/-- **`k`-dependent block-approximation for a family of unit directions (expanding
block)**: for a family `u : Fin m → ℝᵈ` of unit vectors in `largeSpan ℓ` and `1 ≤ m`,
there are expanding block lattice points `v i`, each of norm in
`[(11m−1)·C, (11m+1)·C]` and within `C` of `(11m)·C·u i` on its line,
`C := (d−ℓ:ℝ)·b`. -/
theorem exists_largeFamily_annulus_k (ℓ : ℕ) (hℓd : ℓ ≤ d) {a b : ℝ} (hb0 : 0 < b)
    {m : ℕ} {u : Fin m → ℝᵈ} (hm : 1 ≤ m) (hu : ∀ i, u i ∈ largeSpan (d := d) ℓ)
    (hu1 : ∀ i, ‖u i‖ = 1) :
    ∃ v : Fin m → Submission.LargeBlockMinima.largeFlow (d := d) a b ℓ,
      ∀ i, ‖(v i : ℝᵈ) - (((11 : ℝ) * (m : ℝ)) * ((d - ℓ : ℕ) : ℝ) * b) • u i‖ ≤
            ((d - ℓ : ℕ) : ℝ) * b ∧
        (((11 : ℝ) * (m : ℝ) - 1) * ((d - ℓ : ℕ) : ℝ)) * b ≤ ‖(v i : ℝᵈ)‖ ∧
        ‖(v i : ℝᵈ)‖ ≤ (((11 : ℝ) * (m : ℝ) + 1) * ((d - ℓ : ℕ) : ℝ)) * b := by
  classical
  refine ⟨fun i => Classical.choose (exists_largePoint_annulus_k (d := d) ℓ hℓd
    (a := a) (b := b) hb0 (u := u i) (hu i) (hu1 i) hm), ?_⟩
  intro i
  exact Classical.choose_spec (exists_largePoint_annulus_k (d := d) ℓ hℓd
    (a := a) (b := b) hb0 (u := u i) (hu i) (hu1 i) hm)

/-- **`k`-dependent family, exponential flow (expanding block)**: anchor `(11m)·C`,
`C = (d−ℓ)·e^{t/(d−ℓ)}`. -/
theorem exists_largeFamily_annulus_k_exp (ℓ : ℕ) (hℓd : ℓ < d)
    {t : ℝ} {m : ℕ} {u : Fin m → ℝᵈ} (hm : 1 ≤ m) (hu : ∀ i, u i ∈ largeSpan (d := d) ℓ)
    (hu1 : ∀ i, ‖u i‖ = 1) :
    ∃ v : Fin m → Submission.LargeBlockMinima.largeFlow (d := d)
        (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ,
      ∀ i, ‖(v i : ℝᵈ) - (((11 : ℝ) * (m : ℝ)) * ((d - ℓ : ℕ) : ℝ) *
            Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) • u i‖ ≤
            ((d - ℓ : ℕ) : ℝ) * Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) ∧
        (((11 : ℝ) * (m : ℝ) - 1) * ((d - ℓ : ℕ) : ℝ)) *
            Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) ≤ ‖(v i : ℝᵈ)‖ ∧
        ‖(v i : ℝᵈ)‖ ≤ (((11 : ℝ) * (m : ℝ) + 1) * ((d - ℓ : ℕ) : ℝ)) *
            Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) := by
  classical
  refine ⟨fun i => Classical.choose (exists_largePoint_annulus_k_exp (d := d) ℓ hℓd
    (u := u i) (hu i) (hu1 i) hm), ?_⟩
  intro i
  exact Classical.choose_spec (exists_largePoint_annulus_k_exp (d := d) ℓ hℓd
    (u := u i) (hu i) (hu1 i) hm)


end Submission.LargeBlockCovering
