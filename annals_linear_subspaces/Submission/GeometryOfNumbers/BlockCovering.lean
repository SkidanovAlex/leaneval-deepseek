import Mathlib
import Submission.GeometryOfNumbers.BlockMinima
import Submission.GeometryOfNumbers.FlowLatticeMinimaLower

/-!
# Covering radius of the contracting block and lattice points near unit directions

For the two-scale flow with scale `a > 0` on the first `ℓ` coordinates, the contracting
block `smallFlow a b ℓ` (the `ℤ`-span of `a e_j`, `j.val < ℓ`) acts on its real span
`blockSpan ℓ = Span {(B d) j | j.val < ℓ}` (the coordinate subspace).  Its successive
minima are all exactly `a` (`BlockMinima.successiveMinimum_smallFlow_eq`), and here we
prove the metric core of the paper §3 Prop-5 "approach unit directions with block-lattice
vectors of controlled size in an annulus" step, **without** any full-rank `IsZLattice`
instance:

* `covering_radius_block`: every `x ∈ blockSpan ℓ` is within `(ℓ:ℝ)·a` of a point of
  `smallFlow` — an *exact* bound with no slack; the proof is direct floor-rounding of the
  block coordinates: write `x = Σ c_j • e_j` (block coordinates in the unit basis), take
  `v = Σ ⌊c_j/a⌋ • (a e_j) ∈ smallFlow`; each rounding error is `≤ a`, so
  `‖x − v‖ ≤ Σ |c_j − a·⌊c_j/a⌋| ≤ ℓ·a` (no successive-minima machinery needed);
* `exists_blockPoint_near_direction`: for a unit vector `u ∈ blockSpan ℓ` and `M ≥ 0`, there
  is a block lattice point `v` with `‖v − M·u‖ ≤ (ℓ:ℝ)·a` and
  `‖v‖ ∈ [M − (ℓ:ℝ)a, M + (ℓ:ℝ)a]` (triangle inequality around `M·u`);
* **`exists_blockPoint_annulus`** — the model Prop-5 block-approximation step: with the
  anchor `M = 11·(ℓ:ℝ)a`, one obtains `v ∈ smallFlow` of norm in
  `[10·(ℓ:ℝ)a, 12·(ℓ:ℝ)a]` within `(ℓ:ℝ)a` of the point `11·(ℓ:ℝ)a·u` (hence of the line
  `ℝ·u`); `exists_blockFamily_annulus` is the same for a family of unit directions.

All of the above come in two-scale form (parameters `a b`) and in exponential-flow form
(`a = exp(-t/ℓ)`, `b = exp(t/(d-ℓ))` — suffix `_exp`), the model instance of the paper §3
lattice `a_t ℤᵈ` with contracting directions of scale `exp(-t/ℓ)`.

All results are Mathlib-only.
-/

noncomputable section

open Set Filter Metric MeasureTheory Module Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open LinearSubspaces
open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.FlowLattice

namespace Submission.BlockCovering

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)


/-- The standard basis vectors of the block (unit, pairwise orthogonal), indexed by the
coordinates below `ℓ`. -/
abbrev blockAmb (ℓ : ℕ) (j : {j : Fin d // j.val < ℓ}) : ℝᵈ := (B d) j.1

/-- The real span of the block: the coordinate subspace `Span {(B d) j | j.val < ℓ}`. -/
abbrev blockSpan (ℓ : ℕ) : Submodule ℝ ℝᵈ :=
  Submodule.span ℝ (Set.range (blockAmb (d := d) ℓ))

/-- The flow image of a standard basis vector of the block. -/
abbrev blockVec (a b : ℝ) (ℓ : ℕ) (j : {j : Fin d // j.val < ℓ}) : ℝᵈ :=
  scaleMap (twoScale a b ℓ) ((B d) j.1)

/-- Each block generator is the `a`-multiple of the ambient basis vector `blockAmb`
(because `j.val < ℓ`, the two-scale flow coefficient at `j` is `a`). -/
lemma blockVec_eq_smul {a b : ℝ} (ℓ : ℕ) (j : {j : Fin d // j.val < ℓ}) :
    blockVec (d := d) a b ℓ j = a • blockAmb (d := d) (ℓ := ℓ) j := by
  unfold blockVec blockAmb
  rw [scaleMap_basis, twoScale_apply]
  simp [j.2]

/-- The ambient norm of a block basis vector is `1`. -/
lemma blockAmb_norm (ℓ : ℕ) (j : {j : Fin d // j.val < ℓ}) : ‖blockAmb (d := d) (ℓ := ℓ) j‖ = 1 := by
  simp [blockAmb]

/-- The real span of the block coincides with the real span of the flowed generators
(`a ≠ 0` makes the scaling by `a` invertible). -/
lemma blockSpan_eq_flowSpan {a b : ℝ} (ℓ : ℕ) (ha : a ≠ 0) :
    blockSpan (d := d) ℓ =
      Submodule.span ℝ (Set.range (fun j : {j : Fin d // j.val < ℓ} => blockVec (d := d) a b ℓ j)) := by
  classical
  apply le_antisymm
  · -- amb span ⊆ flowVec span : amb j = a⁻¹ • blockVec j
    rw [blockSpan]
    refine Submodule.span_le.mpr ?_
    intro v hv
    rcases hv with ⟨j, rfl⟩
    change blockAmb (d := d) (ℓ := ℓ) j ∈ Submodule.span ℝ
      (Set.range (fun j : {j : Fin d // j.val < ℓ} => blockVec (d := d) a b ℓ j))
    have hbv : blockVec (d := d) a b ℓ j ∈ Submodule.span ℝ
        (Set.range (fun j : {j : Fin d // j.val < ℓ} => blockVec (d := d) a b ℓ j)) :=
      Submodule.subset_span ⟨j, rfl⟩
    have heq : a⁻¹ • blockVec (d := d) a b ℓ j = blockAmb (d := d) (ℓ := ℓ) j := by
      calc
        a⁻¹ • blockVec (d := d) a b ℓ j
            = a⁻¹ • (a • blockAmb (d := d) (ℓ := ℓ) j) := by
                rw [blockVec_eq_smul (d := d) (a := a) (b := b) ℓ j]
        _ = (a⁻¹ * a) • blockAmb (d := d) (ℓ := ℓ) j := by
                rw [← mul_smul]
        _ = blockAmb (d := d) (ℓ := ℓ) j := by
                rw [inv_mul_cancel₀ ha, one_smul]
    rw [← heq]
    exact Submodule.smul_mem _ (a⁻¹) hbv
  · -- flowVec span ⊆ amb span : blockVec j = a • amb j ∈ span amb
    refine Submodule.span_le.mpr ?_
    intro v hv
    rcases hv with ⟨j, rfl⟩
    change blockVec (d := d) a b ℓ j ∈ (blockSpan (d := d) ℓ : Submodule ℝ ℝᵈ)
    rw [blockSpan, blockVec_eq_smul (d := d) (a := a) (b := b) ℓ j]
    exact Submodule.smul_mem _ a (Submodule.subset_span ⟨j, rfl⟩)

/-- A ℤ-combination of the block generators is a member of the small block (the block is by
definition their ℤ-span). -/
lemma blockComb_mem_smallFlow {a b : ℝ} (ℓ : ℕ) (hℓd : ℓ ≤ d) (n : {j : Fin d // j.val < ℓ} → ℤ) :
    (∑ j : {j : Fin d // j.val < ℓ}, (n j : ℤ) • blockVec (d := d) a b ℓ j) ∈
      Submission.FlowLatticeMinimaLower.smallFlow (d := d) a b ℓ hℓd := by
  unfold Submission.FlowLatticeMinimaLower.smallFlow
  exact Submodule.sum_mem _ (by
    intro j hj
    exact Submodule.smul_mem _ (n j) (Submodule.subset_span ⟨j, rfl⟩))

end Submission.BlockCovering

namespace Submission.BlockCovering

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- **Covering radius of the contracting block**: for `0 < a`, every point
`x ∈ blockSpan ℓ` (the coordinate subspace spanned by the block) is within distance
`(ℓ:ℝ)·a` of a point of `smallFlow a b ℓ` (no slack: the block generators have norm exactly
`a`, so the rounding is exact).  Proof: write `x = Σ c_j • e_j` (block coordinates), round
each `c_j / a` to the integer `n_j = ⌊c_j/a⌋`, and let `v = Σ n_j • (a e_j) ∈ smallFlow`;
then `‖x − v‖ ≤ Σ |c_j − a n_j| ≤ ℓ·a`. -/
theorem covering_radius_block (ℓ : ℕ) (hℓd : ℓ ≤ d) {a b : ℝ} (ha0 : 0 < a)
    {x : ℝᵈ} (hx : x ∈ blockSpan (d := d) ℓ) :
    ∃ v : Submission.FlowLatticeMinimaLower.smallFlow (d := d) a b ℓ hℓd,
      ‖x - (v : ℝᵈ)‖ ≤ (ℓ : ℝ) * a := by
  classical
  let S : Submodule ℤ ℝᵈ := Submission.FlowLatticeMinimaLower.smallFlow (d := d) a b ℓ hℓd
  have hx' : x ∈ Submodule.span ℝ (Set.range (blockAmb (d := d) ℓ)) := by
    simpa [blockSpan] using hx
  rcases (Submodule.mem_span_range_iff_exists_fun (R := ℝ)).mp hx' with ⟨c, hc⟩
  let n : {j : Fin d // j.val < ℓ} → ℤ := fun j => Int.floor (c j / a)
  let v : S := ⟨∑ j : {j : Fin d // j.val < ℓ}, (n j : ℤ) • blockVec (d := d) a b ℓ j, by
    exact blockComb_mem_smallFlow (d := d) (a := a) (b := b) ℓ hℓd n⟩
  have hv_eq : ((v : S) : ℝᵈ) = ∑ j : {j : Fin d // j.val < ℓ},
      (((n j : ℤ) : ℝ) * a) • blockAmb (d := d) (ℓ := ℓ) j := by
    calc
      ((v : S) : ℝᵈ) = ∑ j : {j : Fin d // j.val < ℓ}, (n j : ℤ) • blockVec (d := d) a b ℓ j := by
        rfl
      _ = ∑ j : {j : Fin d // j.val < ℓ}, (((n j : ℤ) : ℝ) • blockVec (d := d) a b ℓ j) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (Int.cast_smul_eq_zsmul ℝ (n j) (blockVec (d := d) a b ℓ j)).symm
      _ = ∑ j : {j : Fin d // j.val < ℓ}, (((n j : ℤ) : ℝ) * a) • blockAmb (d := d) (ℓ := ℓ) j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [blockVec_eq_smul (d := d) (a := a) (b := b) ℓ j]
        rw [mul_smul]
  have hδ0 : ∀ j : {j : Fin d // j.val < ℓ}, 0 ≤ c j - ((n j : ℤ) : ℝ) * a := by
    intro j
    have hfl : ((n j : ℤ) : ℝ) ≤ c j / a := by
      dsimp [n]
      exact Int.floor_le (c j / a)
    have hfl' : ((n j : ℤ) : ℝ) * a ≤ c j := by
      have hm := mul_le_mul_of_nonneg_right hfl (le_of_lt ha0)
      rwa [div_mul_cancel₀ (c j) (ne_of_gt ha0)] at hm
    linarith
  have hδa : ∀ j : {j : Fin d // j.val < ℓ}, c j - ((n j : ℤ) : ℝ) * a ≤ a := by
    intro j
    have hlt : c j / a < ((n j : ℤ) : ℝ) + 1 := by
      dsimp [n]
      exact Int.lt_floor_add_one (c j / a)
    have hlt' : c j < ((n j : ℤ) : ℝ) * a + a := by
      have hm := mul_lt_mul_of_pos_right hlt ha0
      rwa [div_mul_cancel₀ (c j) (ne_of_gt ha0), add_mul, one_mul] at hm
    linarith
  refine ⟨v, ?_⟩
  have hdiff : x - ((v : S) : ℝᵈ) = ∑ j : {j : Fin d // j.val < ℓ},
      (c j - ((n j : ℤ) : ℝ) * a) • blockAmb (d := d) (ℓ := ℓ) j := by
    calc
      x - ((v : S) : ℝᵈ)
          = (∑ j : {j : Fin d // j.val < ℓ}, c j • blockAmb (d := d) (ℓ := ℓ) j) -
              (∑ j : {j : Fin d // j.val < ℓ}, (((n j : ℤ) : ℝ) * a) • blockAmb (d := d) (ℓ := ℓ) j) := by
              rw [← hc, hv_eq]
      _ = ∑ j : {j : Fin d // j.val < ℓ},
              (c j • blockAmb (d := d) (ℓ := ℓ) j -
                (((n j : ℤ) : ℝ) * a) • blockAmb (d := d) (ℓ := ℓ) j) := by
              rw [← Finset.sum_sub_distrib]
      _ = ∑ j : {j : Fin d // j.val < ℓ},
              (c j - ((n j : ℤ) : ℝ) * a) • blockAmb (d := d) (ℓ := ℓ) j := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [← sub_smul]
  calc
    ‖x - ((v : S) : ℝᵈ)‖
        = ‖∑ j : {j : Fin d // j.val < ℓ},
            (c j - ((n j : ℤ) : ℝ) * a) • blockAmb (d := d) (ℓ := ℓ) j‖ := by rw [hdiff]
    _ ≤ ∑ j : {j : Fin d // j.val < ℓ},
            ‖((c j - ((n j : ℤ) : ℝ) * a) • blockAmb (d := d) (ℓ := ℓ) j)‖ := norm_sum_le _ _
    _ ≤ ∑ j : {j : Fin d // j.val < ℓ}, a := by
        apply Finset.sum_le_sum
        intro j hj
        calc
          ‖((c j - ((n j : ℤ) : ℝ) * a) • blockAmb (d := d) (ℓ := ℓ) j)‖
              = |c j - ((n j : ℤ) : ℝ) * a| * ‖blockAmb (d := d) (ℓ := ℓ) j‖ := by
                  rw [norm_smul, Real.norm_eq_abs]
          _ = |c j - ((n j : ℤ) : ℝ) * a| := by rw [blockAmb_norm (d := d) ℓ j, mul_one]
          _ = c j - ((n j : ℤ) : ℝ) * a := abs_of_nonneg (hδ0 j)
          _ ≤ a := hδa j
    _ = (Fintype.card {j : Fin d // j.val < ℓ} : ℝ) * a := by simp
    _ = (ℓ : ℝ) * a := by rw [Submission.FlowLatticeMinimaLower.card_smallFlow_index (d := d) ℓ hℓd]

/-- **Block lattice point near a prescribed unit direction, with controlled size**: for
`0 < a`, a unit vector `u ∈ blockSpan ℓ` and `M ≥ 0`, there is a block lattice point `v`
within distance `(ℓ:ℝ)·a` of `M·u`, whose norm lies in the interval
`[M − (ℓ:ℝ)a, M + (ℓ:ℝ)a]`.  (Metric core of paper §3 Prop 5: taking `M := 11C` with
`C := (ℓ:ℝ)a` places `‖v‖` in `[10C, 12C]` at distance `≤ C` from the line `ℝ·u`.) -/
theorem exists_blockPoint_near_direction (ℓ : ℕ) (hℓd : ℓ ≤ d) {a b : ℝ} (ha0 : 0 < a)
    {u : ℝᵈ} (hu : u ∈ blockSpan (d := d) ℓ) (hu1 : ‖u‖ = 1)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ v : Submission.FlowLatticeMinimaLower.smallFlow (d := d) a b ℓ hℓd,
      ‖(v : ℝᵈ) - M • u‖ ≤ (ℓ : ℝ) * a ∧
      M - (ℓ : ℝ) * a ≤ ‖(v : ℝᵈ)‖ ∧
      ‖(v : ℝᵈ)‖ ≤ M + (ℓ : ℝ) * a := by
  classical
  let C : ℝ := (ℓ : ℝ) * a
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (Nat.cast_nonneg ℓ) (le_of_lt ha0)
  have hMmem : M • u ∈ blockSpan (d := d) ℓ := Submodule.smul_mem _ M hu
  obtain ⟨v, hv⟩ := covering_radius_block (d := d) ℓ hℓd (a := a) (b := b) ha0 (x := M • u) hMmem
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

end Submission.BlockCovering

namespace Submission.BlockCovering

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- **Covering radius of the contracting block in the exponential flow**: every
`x ∈ blockSpan ℓ` is within `(ℓ:ℝ)·exp(-t/ℓ)` of a point of the contracting block of
`a_t ℤᵈ` (`a = exp(-t/ℓ)`, `b = exp(t/(d-ℓ))`) — the model instance of the paper §3
lattice `a_t ℤᵈ`. -/
theorem covering_radius_block_exp (ℓ : ℕ) (hℓd : ℓ < d)
    {t : ℝ} {x : ℝᵈ} (hx : x ∈ blockSpan (d := d) ℓ) :
    ∃ v : Submission.FlowLatticeMinimaLower.smallFlow (d := d)
        (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ (le_of_lt hℓd),
      ‖x - (v : ℝᵈ)‖ ≤ (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ)) := by
  rcases covering_radius_block (d := d) ℓ (le_of_lt hℓd)
    (a := Real.exp (-t / (ℓ : ℝ))) (b := Real.exp (t / ((d : ℝ) - (ℓ : ℝ))))
    (Real.exp_pos _) (x := x) hx with ⟨v, hv⟩
  exact ⟨v, by simpa using hv⟩

/-- **Block lattice point near a prescribed unit direction in the exponential flow**: a unit
`u ∈ blockSpan ℓ` and `M ≥ 0`, there is a point `v` of the contracting block of `a_t ℤᵈ`
within `(ℓ:ℝ)·exp(-t/ℓ)` of `M·u`, of norm in
`[M − (ℓ:ℝ)exp(-t/ℓ), M + (ℓ:ℝ)exp(-t/ℓ)]`. -/
theorem exists_blockPoint_near_direction_exp (ℓ : ℕ) (hℓd : ℓ < d)
    {t : ℝ} {u : ℝᵈ} (hu : u ∈ blockSpan (d := d) ℓ) (hu1 : ‖u‖ = 1)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ v : Submission.FlowLatticeMinimaLower.smallFlow (d := d)
        (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ (le_of_lt hℓd),
      ‖(v : ℝᵈ) - M • u‖ ≤ (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ)) ∧
      M - (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ)) ≤ ‖(v : ℝᵈ)‖ ∧
      ‖(v : ℝᵈ)‖ ≤ M + (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ)) := by
  rcases exists_blockPoint_near_direction (d := d) ℓ (le_of_lt hℓd)
    (a := Real.exp (-t / (ℓ : ℝ))) (b := Real.exp (t / ((d : ℝ) - (ℓ : ℝ))))
    (Real.exp_pos _) (u := u) hu hu1 (M := M) hM with ⟨v, hd, hl, hu'⟩
  exact ⟨v, by simpa using hd, by simpa using hl, by simpa using hu'⟩

end Submission.BlockCovering

namespace Submission.BlockCovering

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- **Prop-5 block-approximation, contracting block**: for a unit direction
`u ∈ blockSpan ℓ` (the real span of the block) and `0 < a`, there is a block lattice point
`v` of norm in `[10·(ℓ:ℝ)a, 12·(ℓ:ℝ)a]` whose distance to the point `11·(ℓ:ℝ)a · u` (hence
to the line `ℝ·u`) is at most `(ℓ:ℝ)a`.  This is the paper §3 Prop 5 metric step in the
coordinate model: "vectors in `a_t V_{j_s}(ℤ)` of norm in `[10Cλ, 12Cλ]` with
`d(v_i, ℝu_i) ≤ Cλ`", here with `λ = a` and `C = (ℓ:ℝ)`. -/
theorem exists_blockPoint_annulus (ℓ : ℕ) (hℓd : ℓ ≤ d) {a b : ℝ} (ha0 : 0 < a)
    {u : ℝᵈ} (hu : u ∈ blockSpan (d := d) ℓ) (hu1 : ‖u‖ = 1) :
    ∃ v : Submission.FlowLatticeMinimaLower.smallFlow (d := d) a b ℓ hℓd,
      ‖(v : ℝᵈ) - ((11 : ℝ) * (ℓ : ℝ) * a) • u‖ ≤ (ℓ : ℝ) * a ∧
      (10 : ℝ) * (ℓ : ℝ) * a ≤ ‖(v : ℝᵈ)‖ ∧
      ‖(v : ℝᵈ)‖ ≤ (12 : ℝ) * (ℓ : ℝ) * a := by
  classical
  have hpos : 0 ≤ (ℓ : ℝ) * a := mul_nonneg (Nat.cast_nonneg ℓ) (le_of_lt ha0)
  rcases exists_blockPoint_near_direction (d := d) ℓ hℓd (a := a) (b := b) ha0
    (u := u) hu hu1 (M := 11 * ((ℓ : ℝ) * a))
    (by exact mul_nonneg (by norm_num) hpos) with ⟨v, hd, hl, hu'⟩
  refine ⟨v, ?_, ?_, ?_⟩
  · -- distance: align the anchor `((11:ℝ)*(ℓ:ℝ))*a` with the hypothesis' `11*((ℓ:ℝ)a)`
    have hs : ((11 : ℝ) * (ℓ : ℝ)) * a = 11 * ((ℓ : ℝ) * a) := by ring
    rw [hs]
    exact hd
  · -- lower annulus: `((10:ℝ)*(ℓ:ℝ))*a = 11C − C` with `C = (ℓ:ℝ)a`
    have hs : ((10 : ℝ) * (ℓ : ℝ)) * a = 11 * ((ℓ : ℝ) * a) - (ℓ : ℝ) * a := by ring
    rw [hs]
    exact hl
  · -- upper annulus: `((12:ℝ)*(ℓ:ℝ))*a = 11C + C` with `C = (ℓ:ℝ)a`
    have hs : ((12 : ℝ) * (ℓ : ℝ)) * a = 11 * ((ℓ : ℝ) * a) + (ℓ : ℝ) * a := by ring
    rw [hs]
    exact hu'

/-- **Prop-5 block-approximation in the exponential flow**: for a unit
`u ∈ blockSpan ℓ`, there is a point `v` of the contracting block of `a_t ℤᵈ` of norm in
`[10·(ℓ:ℝ)e^{-t/ℓ}, 12·(ℓ:ℝ)e^{-t/ℓ}]` within `(ℓ:ℝ)e^{-t/ℓ}` of the point
`11·(ℓ:ℝ)e^{-t/ℓ}·u` (hence of the line `ℝ·u`). -/
theorem exists_blockPoint_annulus_exp (ℓ : ℕ) (hℓd : ℓ < d)
    {t : ℝ} {u : ℝᵈ} (hu : u ∈ blockSpan (d := d) ℓ) (hu1 : ‖u‖ = 1) :
    ∃ v : Submission.FlowLatticeMinimaLower.smallFlow (d := d)
        (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ (le_of_lt hℓd),
      ‖(v : ℝᵈ) - ((11 : ℝ) * (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ))) • u‖ ≤
        (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ)) ∧
      (10 : ℝ) * (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ)) ≤ ‖(v : ℝᵈ)‖ ∧
      ‖(v : ℝᵈ)‖ ≤ (12 : ℝ) * (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ)) := by
  rcases exists_blockPoint_annulus (d := d) ℓ (le_of_lt hℓd)
    (a := Real.exp (-t / (ℓ : ℝ))) (b := Real.exp (t / ((d : ℝ) - (ℓ : ℝ))))
    (Real.exp_pos _) (u := u) hu hu1 with ⟨v, hd, hl, hu'⟩
  exact ⟨v, by simpa using hd, by simpa using hl, by simpa using hu'⟩

/-- **Prop-5 block-approximation for a family of unit directions**: for a family
`u : Fin m → ℝᵈ` of unit vectors in `blockSpan ℓ` and `0 < a`, there are block lattice
points `v i` (one per direction), each of norm in `[10·(ℓ:ℝ)a, 12·(ℓ:ℝ)a]` and within
`(ℓ:ℝ)a` of the point `11·(ℓ:ℝ)a·u i` on its line. -/
theorem exists_blockFamily_annulus (ℓ : ℕ) (hℓd : ℓ ≤ d) {a b : ℝ} (ha0 : 0 < a)
    {m : ℕ} {u : Fin m → ℝᵈ} (hu : ∀ i, u i ∈ blockSpan (d := d) ℓ)
    (hu1 : ∀ i, ‖u i‖ = 1) :
    ∃ v : Fin m → Submission.FlowLatticeMinimaLower.smallFlow (d := d) a b ℓ hℓd,
      ∀ i, ‖(v i : ℝᵈ) - ((11 : ℝ) * (ℓ : ℝ) * a) • u i‖ ≤ (ℓ : ℝ) * a ∧
        (10 : ℝ) * (ℓ : ℝ) * a ≤ ‖(v i : ℝᵈ)‖ ∧
        ‖(v i : ℝᵈ)‖ ≤ (12 : ℝ) * (ℓ : ℝ) * a := by
  classical
  refine ⟨fun i => Classical.choose (exists_blockPoint_annulus (d := d) ℓ hℓd (a := a)
    (b := b) ha0 (u := u i) (hu i) (hu1 i)), ?_⟩
  intro i
  exact Classical.choose_spec (exists_blockPoint_annulus (d := d) ℓ hℓd (a := a)
    (b := b) ha0 (u := u i) (hu i) (hu1 i))

/-- **Prop-5 block-approximation for a family of unit directions in the exponential flow**:
for unit `u i ∈ blockSpan ℓ`, there are points `v i` of the contracting block of `a_t ℤᵈ`,
each of norm in `[10·(ℓ:ℝ)e^{-t/ℓ}, 12·(ℓ:ℝ)e^{-t/ℓ}]` and within `(ℓ:ℝ)e^{-t/ℓ}` of
`11·(ℓ:ℝ)e^{-t/ℓ}·u i`. -/
theorem exists_blockFamily_annulus_exp (ℓ : ℕ) (hℓd : ℓ < d)
    {t : ℝ} {m : ℕ} {u : Fin m → ℝᵈ} (hu : ∀ i, u i ∈ blockSpan (d := d) ℓ)
    (hu1 : ∀ i, ‖u i‖ = 1) :
    ∃ v : Fin m → Submission.FlowLatticeMinimaLower.smallFlow (d := d)
        (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ (le_of_lt hℓd),
      ∀ i, ‖(v i : ℝᵈ) - ((11 : ℝ) * (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ))) • u i‖ ≤
            (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ)) ∧
        (10 : ℝ) * (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ)) ≤ ‖(v i : ℝᵈ)‖ ∧
        ‖(v i : ℝᵈ)‖ ≤ (12 : ℝ) * (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ)) := by
  classical
  refine ⟨fun i => Classical.choose (exists_blockPoint_annulus_exp (d := d) ℓ hℓd
    (u := u i) (hu i) (hu1 i)), ?_⟩
  intro i
  exact Classical.choose_spec (exists_blockPoint_annulus_exp (d := d) ℓ hℓd
    (u := u i) (hu i) (hu1 i))


/-! ### General-`k` annulus (contracting block, `(11k)`-anchor)

The fixed-constant annuli above (`anchor 11C`, bounds `[10C, 12C]`, direction error `1/5`)
are the `k = 1` case of the general-`k` annuli with `anchor (11k)·C`, bounds
`[(11k−1)·C, (11k+1)·C]` and direction error `2/(11k−1) ≤ 1/5` — which stay valid for
arbitrary block rank `k ≤ ℓ` (the per-direction error shrinks like `1/k`). -/

/-- **`k`-dependent block-approximation, contracting block**: for a unit direction
`u ∈ blockSpan ℓ` and `1 ≤ k`, there is a contracting block lattice point `v` of norm in
`[(11k−1)·C, (11k+1)·C]` whose distance to `(11k)·C·u` (hence to the line `ℝ·u`) is at most
`C`, `C := (ℓ:ℝ)·a`. -/
theorem exists_blockPoint_annulus_k (ℓ : ℕ) (hℓd : ℓ ≤ d) {a b : ℝ} (ha0 : 0 < a)
    {u : ℝᵈ} (hu : u ∈ blockSpan (d := d) ℓ) (hu1 : ‖u‖ = 1) {k : ℕ} (_hk : 1 ≤ k) :
    ∃ v : Submission.FlowLatticeMinimaLower.smallFlow (d := d) a b ℓ hℓd,
      ‖(v : ℝᵈ) - (((11 : ℝ) * (k : ℝ)) * (ℓ : ℝ) * a) • u‖ ≤ (ℓ : ℝ) * a ∧
      (((11 : ℝ) * (k : ℝ) - 1) * (ℓ : ℝ)) * a ≤ ‖(v : ℝᵈ)‖ ∧
      ‖(v : ℝᵈ)‖ ≤ (((11 : ℝ) * (k : ℝ) + 1) * (ℓ : ℝ)) * a := by
  classical
  let C : ℝ := (ℓ : ℝ) * a
  have hpos : 0 ≤ C := mul_nonneg (Nat.cast_nonneg ℓ) (le_of_lt ha0)
  have hkR0 : 0 ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
  have hMpos : 0 ≤ ((11 : ℝ) * (k : ℝ)) * C := by
    exact mul_nonneg (mul_nonneg (by norm_num) hkR0) hpos
  rcases exists_blockPoint_near_direction (d := d) ℓ hℓd (a := a) (b := b) ha0
    (u := u) hu hu1 (M := ((11 : ℝ) * (k : ℝ)) * C) hMpos with ⟨v, hd, hl, hu'⟩
  refine ⟨v, ?_, ?_, ?_⟩
  · have hs : ((11 : ℝ) * (k : ℝ)) * (ℓ : ℝ) * a = ((11 : ℝ) * (k : ℝ)) * C := by
      dsimp [C]
      ring
    rw [hs]
    exact hd
  · have hs : (((11 : ℝ) * (k : ℝ) - 1) * (ℓ : ℝ)) * a = ((11 : ℝ) * (k : ℝ)) * C - C := by
      dsimp [C]
      ring
    rw [hs]
    exact hl
  · have hs : (((11 : ℝ) * (k : ℝ) + 1) * (ℓ : ℝ)) * a = ((11 : ℝ) * (k : ℝ)) * C + C := by
      dsimp [C]
      ring
    rw [hs]
    exact hu'

/-- **`k`-dependent block-approximation in the exponential flow (contracting block)**:
anchor `(11k)·C`, `C = (ℓ:ℝ)·e^{−t/ℓ}`. -/
theorem exists_blockPoint_annulus_k_exp (ℓ : ℕ) (hℓd : ℓ < d)
    {t : ℝ} {u : ℝᵈ} (hu : u ∈ blockSpan (d := d) ℓ) (hu1 : ‖u‖ = 1) {k : ℕ} (hk : 1 ≤ k) :
    ∃ v : Submission.FlowLatticeMinimaLower.smallFlow (d := d)
        (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ (le_of_lt hℓd),
      ‖(v : ℝᵈ) - (((11 : ℝ) * (k : ℝ)) * (ℓ : ℝ) *
          Real.exp (-t / (ℓ : ℝ))) • u‖ ≤ (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ)) ∧
      (((11 : ℝ) * (k : ℝ) - 1) * (ℓ : ℝ)) *
          Real.exp (-t / (ℓ : ℝ)) ≤ ‖(v : ℝᵈ)‖ ∧
      ‖(v : ℝᵈ)‖ ≤ (((11 : ℝ) * (k : ℝ) + 1) * (ℓ : ℝ)) *
          Real.exp (-t / (ℓ : ℝ)) := by
  rcases exists_blockPoint_annulus_k (d := d) ℓ (le_of_lt hℓd)
    (a := Real.exp (-t / (ℓ : ℝ))) (b := Real.exp (t / ((d : ℝ) - (ℓ : ℝ))))
    (Real.exp_pos _) (u := u) hu hu1 hk with ⟨v, hd, hl, hu'⟩
  exact ⟨v, by simpa using hd, by simpa using hl, by simpa using hu'⟩

/-- **`k`-dependent block-approximation for a family of unit directions (contracting
block)**: for a family `u : Fin m → ℝᵈ` of unit vectors in `blockSpan ℓ` and `1 ≤ m`,
there are contracting block lattice points `v i`, each of norm in
`[(11m−1)·C, (11m+1)·C]` and within `C` of `(11m)·C·u i` on its line,
`C := (ℓ:ℝ)·a`. -/
theorem exists_blockFamily_annulus_k (ℓ : ℕ) (hℓd : ℓ ≤ d) {a b : ℝ} (ha0 : 0 < a)
    {m : ℕ} {u : Fin m → ℝᵈ} (hm : 1 ≤ m) (hu : ∀ i, u i ∈ blockSpan (d := d) ℓ)
    (hu1 : ∀ i, ‖u i‖ = 1) :
    ∃ v : Fin m → Submission.FlowLatticeMinimaLower.smallFlow (d := d) a b ℓ hℓd,
      ∀ i, ‖(v i : ℝᵈ) - (((11 : ℝ) * (m : ℝ)) * (ℓ : ℝ) * a) • u i‖ ≤ (ℓ : ℝ) * a ∧
        (((11 : ℝ) * (m : ℝ) - 1) * (ℓ : ℝ)) * a ≤ ‖(v i : ℝᵈ)‖ ∧
        ‖(v i : ℝᵈ)‖ ≤ (((11 : ℝ) * (m : ℝ) + 1) * (ℓ : ℝ)) * a := by
  classical
  refine ⟨fun i => Classical.choose (exists_blockPoint_annulus_k (d := d) ℓ hℓd
    (a := a) (b := b) ha0 (u := u i) (hu i) (hu1 i) hm), ?_⟩
  intro i
  exact Classical.choose_spec (exists_blockPoint_annulus_k (d := d) ℓ hℓd
    (a := a) (b := b) ha0 (u := u i) (hu i) (hu1 i) hm)

/-- **`k`-dependent family, exponential flow (contracting block)**: anchor `(11m)·C`,
`C = (ℓ:ℝ)·e^{−t/ℓ}`. -/
theorem exists_blockFamily_annulus_k_exp (ℓ : ℕ) (hℓd : ℓ < d)
    {t : ℝ} {m : ℕ} {u : Fin m → ℝᵈ} (hm : 1 ≤ m) (hu : ∀ i, u i ∈ blockSpan (d := d) ℓ)
    (hu1 : ∀ i, ‖u i‖ = 1) :
    ∃ v : Fin m → Submission.FlowLatticeMinimaLower.smallFlow (d := d)
        (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ (le_of_lt hℓd),
      ∀ i, ‖(v i : ℝᵈ) - (((11 : ℝ) * (m : ℝ)) * (ℓ : ℝ) *
            Real.exp (-t / (ℓ : ℝ))) • u i‖ ≤
            (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ)) ∧
        (((11 : ℝ) * (m : ℝ) - 1) * (ℓ : ℝ)) *
            Real.exp (-t / (ℓ : ℝ)) ≤ ‖(v i : ℝᵈ)‖ ∧
        ‖(v i : ℝᵈ)‖ ≤ (((11 : ℝ) * (m : ℝ) + 1) * (ℓ : ℝ)) *
            Real.exp (-t / (ℓ : ℝ)) := by
  classical
  refine ⟨fun i => Classical.choose (exists_blockPoint_annulus_k_exp (d := d) ℓ hℓd
    (u := u i) (hu i) (hu1 i) hm), ?_⟩
  intro i
  exact Classical.choose_spec (exists_blockPoint_annulus_k_exp (d := d) ℓ hℓd
    (u := u i) (hu i) (hu1 i) hm)

end Submission.BlockCovering
