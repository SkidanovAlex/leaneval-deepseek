import Mathlib
import Submission.Work.Lattice.AngularTightness
import Submission.Work.Lattice.Prop42General
import Submission.Work.Lattice.UniformBddBelow
import Submission.Work.Lattice.IntrinsicIndex
import Submission.Work.Polygon.ConvexRankEquation

/-!
# Prop 4(2) UPPER bound: the prefix sums of `log λᵢ(Λ)` are pinned by the Grayson polygon

For a full-rank lattice `Λ ≤ ℝᵈ` with Grayson polygon `c = polygon Λ`, the second half of
paper Prop 4(2) is the upper bound on the prefix sums of the logarithmic successive minima

    `Σ_{i≤j} log λᵢ(Λ) ≤ c(j) + K_d`.

Proof strategy (no Harder–Narasimhan flag needed):

* **At the angular ranks** `j = blockStart d c s` (`1 ≤ s < numBlocks`), angular
  data-tightness (`AngularTightness.exists_subgroup_polygon_at_angular`) provides a
  subgroup `W ≤ Λ` of rank `j` with `log covol(W) = c(j)`.  Presenting `W` by its
  `ℤ`-basis family `u`, the **sublattice minima comparison**
  (`SublatticeGe.successiveMinimum_ge_of_le_span`, `λᵢ(Λ) ≤ λᵢ(W)`) and
  **Minkowski's second theorem (upper) on the family span**
  (`UniformBddBelow.covol_span_rank_lower_bound`) give

      `unitBallVol(j) · ∏_{i≤j} λᵢ(Λ) ≤ 2^{2j} · covol(W)`,

  hence (logarithms) `Σ_{i≤j} log λᵢ(Λ) ≤ c(j) + (2j·log 2 − log unitBallVol(j))`.
  The same computation at `j = d` uses `W = Λ` itself.

* **Away from the angular ranks** the prefix sum `j ↦ Σ_{i≤j} log λᵢ(Λ)` is a
  **discrete-convex** sequence (its increments `log λ_{j+1}` are nondecreasing), while `c`
  is **affine on each block**; a convex sequence lies below its chord, so the boundary
  bounds extend to every `j ≤ d` with the same constant `K_d`.

Combined with the *lower* bound `Prop42General.polygon_le_sum_log_general`
(`c(j) ≤ Σ_{i≤j} log λᵢ(Λ)`), this yields the per-index form of Prop 4(2):

    `|log λⱼ(Λ) − (c(j) − c(j−1))| ≤ K_d`   (`1 ≤ j ≤ d`),

recorded as `abs_log_successiveMinimum_sub_dslope_le`.

All declarations are Mathlib + Submission (AngularTightness, Prop42General,
UniformBddBelow, IntrinsicIndex, ConvexRankEquation).
-/

noncomputable section

open Set Module Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000

namespace Submission.Prop42Upper

open Submission.GraysonData
open Submission.GraysonLattice
open Submission.LatticePolygon
open Submission.Polygon
open Submission.AngularRanks
open Submission.AngularTightness
open Submission.UniformBddBelow
open Submission.IntrinsicIndex
open Commons.Lattice.SuccessiveMinima

/-- The prefix sum of the logarithms of the successive minima of `Λ`. -/
noncomputable def prSum {d : ℕ} (Λ : Submodule ℤ (E d)) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range j, Real.log (successiveMinimum Λ (i + 1))

/-- The increment of `prSum` is `log λ_{i+1}`. -/
lemma dslope_prSum {d : ℕ} (Λ : Submodule ℤ (E d)) (i : ℕ) :
    Submission.Polygon.dslope (prSum Λ) i = Real.log (successiveMinimum Λ (i + 1)) := by
  unfold Submission.Polygon.dslope prSum
  rw [Finset.sum_range_succ]
  ring

/-- Every successive minimum of the indices `1 ≤ i ≤ d` is strictly positive. -/
lemma prSum_lambda_pos {d : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) {i : ℕ} (hi0 : 0 < i) (hid : i ≤ d) :
    0 < successiveMinimum Λ i :=
  positive Λ i hi0 (by rw [hΛfin]; exact hid)

/-- `prSum` is discrete-convex on `{0,…,d}`: its increments `log λ_{i+1}` are
nondecreasing. -/
lemma prSum_convex {d : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hΛfin : Module.finrank ℤ Λ = d) : DiscreteConvexOn (prSum Λ) d := by
  intro i hi
  rw [dslope_prSum, dslope_prSum, show i + 1 + 1 = (i + 1) + 1 from rfl]
  apply Real.log_le_log
  · exact prSum_lambda_pos Λ hΛfin (by omega) (by omega)
  · exact successiveMinimum_mono Λ (by omega) (by rw [hΛfin]; omega)

/-- **A discrete-convex sequence lies below its chord**: for `m ≤ j ≤ n ≤ d`,

`(n − m) · c j ≤ (n − j) · c m + (j − m) · c n`. -/
lemma chord_le_of_discreteConvex {c : ℕ → ℝ} {d : ℕ} (hcvx : DiscreteConvexOn c d)
    {m j n : ℕ} (hmj : m ≤ j) (hjn : j ≤ n) (hnd : n ≤ d) :
    ((n - m : ℕ) : ℝ) * c j ≤ ((n - j : ℕ) : ℝ) * c m + ((j - m : ℕ) : ℝ) * c n := by
  by_cases hjm : j = m
  · subst hjm
    rw [Nat.sub_self, Nat.cast_zero, zero_mul, add_zero]
  by_cases hjne : j = n
  · subst hjne
    rw [Nat.sub_self, Nat.cast_zero, zero_mul, zero_add]
  have hjm' : m < j := lt_of_le_of_ne hmj (Ne.symm hjm)
  have hjn' : j < n := lt_of_le_of_ne hjn hjne
  -- telescope both sides in terms of the block slope `dslope c (j-1)`
  have hshift₁ := telescope_shift c m (j - m)
  have hshift₂ := telescope_shift c j (n - j)
  rw [show m + (j - m) = j from by omega] at hshift₁
  rw [show j + (n - j) = n from by omega] at hshift₂
  have hsum₁ : ((j - m : ℕ) : ℝ) * dslope c (j - 1) =
      ∑ _i ∈ Finset.range (j - m), dslope c (j - 1) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hsum₂ : ((n - j : ℕ) : ℝ) * dslope c (j - 1) =
      ∑ _i ∈ Finset.range (n - j), dslope c (j - 1) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hbound₁ : c j - c m ≤ ((j - m : ℕ) : ℝ) * dslope c (j - 1) := by
    rw [← hshift₁, hsum₁]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' : i < j - m := Finset.mem_range.mp hi
    have h1 : m + i ≤ j - 1 := by omega
    have h2 : (j - 1) + 1 ≤ d := by omega
    exact dslope_mono hcvx h1 h2
  have hbound₂ : ((n - j : ℕ) : ℝ) * dslope c (j - 1) ≤ c n - c j := by
    rw [← hshift₂, hsum₂]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' : i < n - j := Finset.mem_range.mp hi
    have h1 : j - 1 ≤ j + i := by omega
    have h2 : (j + i) + 1 ≤ d := by omega
    exact dslope_mono hcvx h1 h2
  have hlen : ((n - m : ℕ) : ℝ) = ((n - j : ℕ) : ℝ) + ((j - m : ℕ) : ℝ) := by
    have : n - m = (n - j) + (j - m) := by omega
    rw [this, Nat.cast_add]
  have ha : (0 : ℝ) ≤ ((n - j : ℕ) : ℝ) := Nat.cast_nonneg _
  have hb : (0 : ℝ) ≤ ((j - m : ℕ) : ℝ) := Nat.cast_nonneg _
  have e1 : ((n - j : ℕ) : ℝ) * c j ≤ ((n - j : ℕ) : ℝ) * c m +
      ((n - j : ℕ) : ℝ) * (((j - m : ℕ) : ℝ) * dslope c (j - 1)) := by
    have h := mul_le_mul_of_nonneg_left hbound₁ ha
    nlinarith [h]
  have e2 : ((n - j : ℕ) : ℝ) * (((j - m : ℕ) : ℝ) * dslope c (j - 1)) ≤
      ((j - m : ℕ) : ℝ) * c n - ((j - m : ℕ) : ℝ) * c j := by
    have h := mul_le_mul_of_nonneg_left hbound₂ hb
    nlinarith [h]
  have step : ((n - j : ℕ) : ℝ) * c j + ((j - m : ℕ) : ℝ) * c j ≤
      ((n - j : ℕ) : ℝ) * c m + ((j - m : ℕ) : ℝ) * c n := by
    linarith only [e1, e2]
  calc ((n - m : ℕ) : ℝ) * c j
      = (((n - j : ℕ) : ℝ) + ((j - m : ℕ) : ℝ)) * c j := by rw [hlen]
    _ = ((n - j : ℕ) : ℝ) * c j + ((j - m : ℕ) : ℝ) * c j := by ring
    _ ≤ ((n - j : ℕ) : ℝ) * c m + ((j - m : ℕ) : ℝ) * c n := step


/-- **Chord step**: combining the chord inequality for `prSum` with the boundary bounds and
the (`K`-slack of the) endpoints gives the multiplied bound
`(A+B)·prSum ≤ (A+B)·(polygon + K)`. -/
lemma chord_step {A B P Q R U K : ℝ} (h1 : (A + B) * P ≤ A * Q + B * R)
    (h2 : A * Q ≤ A * U + A * K) (h3 : B * R ≤ B * U + B * K) :
    (A + B) * P ≤ (A + B) * (U + K) := by
  nlinarith [h1, h2, h3]

/-- The rank-only error constant of the prefix-sum upper bound. -/
noncomputable def Kconst (d : ℕ) : ℝ :=
  (∑ b ∈ Finset.range (d + 1),
      max (Real.log ((2 : ℝ) ^ (2 * b)) - Real.log (unitBallVol b)) 0) + 1

/-- The per-rank constants are dominated by `Kconst d`. -/
lemma le_Kconst {b d : ℕ} (hbd : b ≤ d) :
    Real.log ((2 : ℝ) ^ (2 * b)) - Real.log (unitBallVol b) ≤ Kconst d := by
  have hmem : b ∈ Finset.range (d + 1) := Finset.mem_range.mpr (by omega)
  have h1 : max (Real.log ((2 : ℝ) ^ (2 * b)) - Real.log (unitBallVol b)) 0 ≤
      ∑ c ∈ Finset.range (d + 1),
        max (Real.log ((2 : ℝ) ^ (2 * c)) - Real.log (unitBallVol c)) 0 :=
    Finset.single_le_sum (f := fun c : ℕ =>
      max (Real.log ((2 : ℝ) ^ (2 * c)) - Real.log (unitBallVol c)) 0)
      (fun c _ => le_max_right _ _) hmem
  have h2 : Real.log ((2 : ℝ) ^ (2 * b)) - Real.log (unitBallVol b) ≤
      max (Real.log ((2 : ℝ) ^ (2 * b)) - Real.log (unitBallVol b)) 0 := le_max_left _ _
  dsimp [Kconst]
  linarith

/-- `Kconst` is positive. -/
lemma Kconst_pos (d : ℕ) : 0 < Kconst d := by
  dsimp [Kconst]
  linarith [Finset.sum_nonneg (s := Finset.range (d + 1))
    (f := fun c : ℕ => max (Real.log ((2 : ℝ) ^ (2 * c)) - Real.log (unitBallVol c)) 0)
    (fun c _ => le_max_right _ 0)]

/-- **The prefix-sum upper bound at a realiser**: if a subgroup `W ≤ Λ` of rank `b`
realises the polygon value at `b`, then the first `b` log-successive-minima of `Λ`
are bounded by `polygon Λ b` up to the rank-only constant. -/
theorem prSum_le_polygon_at_realiser {d b : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) (hb0 : 0 < b) (hbd : b ≤ d)
    (W : Submodule ℤ (E d)) (hWle : W ≤ Λ) (hWdim : subDim W = b)
    (hWcov : Real.log (latticeCovol W) = polygon Λ b) :
    prSum Λ b ≤ polygon Λ b +
      (Real.log ((2 : ℝ) ^ (2 * b)) - Real.log (unitBallVol b)) := by
  classical
  subst hWdim
  have hW0 : W ≠ ⊥ := by
    intro hz
    have hz0 : subDim W = 0 := (subDim_eq_zero_iff_bot W).mpr hz
    omega
  rcases exists_basis_family_int_of_le_lattice (d := d) Λ hΛfin W hWle hW0 with
    ⟨cW, hliW, _hzliW, hmemW, hspanW⟩
  have hM := covol_span_rank_lower_bound (d := d) (r := subDim W) hb0 Λ hΛfin hbd cW hmemW hliW
  have hcovspan : latticeCovol (Submodule.span ℤ (Set.range cW)) = latticeCovol W :=
    (congrArg latticeCovol hspanW).symm
  have hcovpos : 0 < latticeCovol W := latticeCovol_pos Λ W hWle hW0
  have hposV : 0 < unitBallVol (subDim W) := unitBallVol_pos hb0
  have hposprod : 0 < ∏ i : Fin (subDim W), successiveMinimum Λ (i.val + 1) :=
    Finset.prod_pos fun i _ => prSum_lambda_pos Λ hΛfin (by omega) (by omega)
  have hposL : 0 < unitBallVol (subDim W) *
      ∏ i : Fin (subDim W), successiveMinimum Λ (i.val + 1) := mul_pos hposV hposprod
  have hposR : 0 < (2 : ℝ) ^ (2 * subDim W) * latticeCovol W :=
    mul_pos (by positivity) hcovpos
  have hbridge : unitBallVol (subDim W) * (∏ i : Fin (subDim W), successiveMinimum Λ (i.val + 1)) ≤
      (2 : ℝ) ^ (2 * subDim W) * latticeCovol W := by
    simpa only [hcovspan] using hM
  have hlog := Real.log_le_log hposL hbridge
  rw [Real.log_mul hposV.ne' hposprod.ne', Real.log_mul (by positivity) hcovpos.ne',
    Real.log_prod (fun i _ => (prSum_lambda_pos Λ hΛfin (by omega) (by omega)).ne')] at hlog
  have hpr : prSum Λ (subDim W) = ∑ i : Fin (subDim W),
      Real.log (successiveMinimum Λ (i.val + 1)) := by
    rw [prSum]
    exact (Fin.sum_univ_eq_sum_range
      (fun i : ℕ => Real.log (successiveMinimum Λ (i + 1))) (subDim W)).symm
  rw [hpr]
  linarith [hlog, hWcov]


/-- **Affinity of the Grayson polygon on a block**: between consecutive block boundaries
`b₁ = blockStart s`, `b₂ = blockStart (s+1)` the polygon is affine:
`(b₂−b₁)·polygon Λ j = (b₂−j)·polygon Λ b₁ + (j−b₁)·polygon Λ b₂`. -/
lemma polygon_block_affine {d : ℕ} (Λ : Submodule ℤ (E d)) {s j : ℕ}
    (h1 : blockStart d (polygon Λ) s ≤ j) (h2 : j ≤ blockStart d (polygon Λ) (s + 1)) :
    ((blockStart d (polygon Λ) (s + 1) - blockStart d (polygon Λ) s : ℕ) : ℝ) * polygon Λ j =
      ((blockStart d (polygon Λ) (s + 1) - j : ℕ) : ℝ) * polygon Λ (blockStart d (polygon Λ) s) +
        ((j - blockStart d (polygon Λ) s : ℕ) : ℝ) *
          polygon Λ (blockStart d (polygon Λ) (s + 1)) := by
  classical
  have htel : ∀ {a b : ℕ}, blockStart d (polygon Λ) s ≤ a → a ≤ b →
      b ≤ blockStart d (polygon Λ) (s + 1) →
      polygon Λ b - polygon Λ a =
        ((b - a : ℕ) : ℝ) * Submission.Polygon.dslope (polygon Λ) (blockStart d (polygon Λ) s) := by
    intro a b ha hab hb
    have hsub := Finset.sum_Ico_eq_sub (f := Submission.Polygon.dslope (polygon Λ)) hab
    rw [Submission.Polygon.telescope, Submission.Polygon.telescope] at hsub
    have hcongr : (∑ i ∈ Finset.Ico a b, Submission.Polygon.dslope (polygon Λ) i) =
        ∑ _i ∈ Finset.Ico a b,
          Submission.Polygon.dslope (polygon Λ) (blockStart d (polygon Λ) s) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_Ico.mp hi
      exact dslope_eq_on_block (polygon Λ) d s (le_trans ha hi'.1) (lt_of_lt_of_le hi'.2 hb)
    rw [hcongr, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at hsub
    linarith [hsub]
  rcases eq_or_lt_of_le h1 with h1' | h1'
  · rw [← h1', Nat.sub_self, Nat.cast_zero, zero_mul, add_zero]
  rcases eq_or_lt_of_le h2 with h2' | h2'
  · rw [h2', Nat.sub_self, Nat.cast_zero, zero_mul, zero_add]
  have hb2 := htel le_rfl (le_of_lt h1') h2
  have hb1 := htel h1 (le_of_lt h2') le_rfl
  have hlen : ((blockStart d (polygon Λ) (s + 1) - blockStart d (polygon Λ) s : ℕ) : ℝ) =
      ((blockStart d (polygon Λ) (s + 1) - j : ℕ) : ℝ) +
        ((j - blockStart d (polygon Λ) s : ℕ) : ℝ) := by
    have heq : blockStart d (polygon Λ) (s + 1) - blockStart d (polygon Λ) s =
        (blockStart d (polygon Λ) (s + 1) - j) + (j - blockStart d (polygon Λ) s) := by omega
    rw [heq, Nat.cast_add]
  have e1 : polygon Λ (blockStart d (polygon Λ) s) = polygon Λ j -
      ((j - blockStart d (polygon Λ) s : ℕ) : ℝ) *
        Submission.Polygon.dslope (polygon Λ) (blockStart d (polygon Λ) s) := by linarith [hb2]
  have e2 : polygon Λ (blockStart d (polygon Λ) (s + 1)) = polygon Λ j +
      ((blockStart d (polygon Λ) (s + 1) - j : ℕ) : ℝ) *
        Submission.Polygon.dslope (polygon Λ) (blockStart d (polygon Λ) s) := by linarith [hb1]
  rw [e1, e2, hlen]
  ring

/-- **The prefix-sum upper bound at every block boundary.** -/
lemma prSum_le_polygon_at_boundary {d : ℕ} (hd : 0 < d) (Λ : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) (s : ℕ)
    (hs : s ≤ numBlocks d (polygon Λ)) :
    prSum Λ (blockStart d (polygon Λ) s) ≤
      polygon Λ (blockStart d (polygon Λ) s) + Kconst d := by
  classical
  rcases Nat.eq_zero_or_pos s with hs0 | hs1
  · subst hs0
    rw [blockStart_zero, prSum, Finset.range_zero, Finset.sum_empty, polygon_zero]
    linarith [Kconst_pos d]
  by_cases hsd : blockStart d (polygon Λ) s = d
  · have h := prSum_le_polygon_at_realiser (d := d) (b := d) Λ hΛfin hd le_rfl Λ le_rfl
      (subDim_full (d := d) Λ) ((polygon_eq_logCovol_full (d := d) Λ hΛfin).symm)
    rw [hsd]
    exact le_trans h (by linarith [le_Kconst (b := d) (d := d) le_rfl])
  · have hsN : s < numBlocks d (polygon Λ) := by
      by_contra hcon
      have hge : numBlocks d (polygon Λ) ≤ s := not_lt.mp hcon
      rw [blockStart_eq_d_of_ge_numBlocks d (polygon Λ) hge] at hsd
      exact hsd rfl
    have hnumle : numBlocks d (polygon Λ) ≤ d := numBlocks_le (polygon Λ)
    have hsle : s ≤ d := le_trans (le_of_lt hsN) hnumle
    have hb0 : 0 < blockStart d (polygon Λ) s := by
      have h₁ : s ≤ blockStart d (polygon Λ) s := blockStart_n_ge d (polygon Λ) s hsle
      omega
    have hbd : blockStart d (polygon Λ) s ≤ d := blockStart_le_d d (polygon Λ) s
    rcases exists_subgroup_polygon_at_angular (d := d) Λ hΛfin hs1 hsN with ⟨W, hWle, hWdim, hWcov⟩
    have h := prSum_le_polygon_at_realiser (d := d) (b := blockStart d (polygon Λ) s) Λ hΛfin
      hb0 hbd W hWle hWdim hWcov
    exact le_trans h (by linarith [le_Kconst (b := blockStart d (polygon Λ) s) (d := d) hbd])

/-- **Prop 4(2), upper bound (prefix-sum form)**: for every full-rank lattice `Λ ≤ ℝᵈ`
and every `j ≤ d`, the prefix sum of the log-successive-minima is at most the Grayson
polygon value plus the rank-only constant `Kconst d`. -/
theorem prSum_le_polygon_add_Kconst {d : ℕ} (hd : 0 < d) (Λ : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) {j : ℕ}
    (hjd : j ≤ d) : prSum Λ j ≤ polygon Λ j + Kconst d := by
  classical
  rcases eq_or_lt_of_le hjd with hjd' | hjd'
  · have h := prSum_le_polygon_at_boundary hd Λ hΛfin (numBlocks d (polygon Λ)) le_rfl
    rw [blockStart_numBlocks] at h
    rwa [hjd']
  rcases exists_blockStart_containing (polygon Λ) d hjd' with ⟨s, hsN, hb1, hb2⟩
  by_cases hje : j = blockStart d (polygon Λ) s
  · rw [hje]
    exact prSum_le_polygon_at_boundary hd Λ hΛfin s (le_of_lt hsN)
  have hb1' : blockStart d (polygon Λ) s < j := lt_of_le_of_ne hb1 (Ne.symm hje)
  have hb2le : blockStart d (polygon Λ) (s + 1) ≤ d := blockStart_le_d d (polygon Λ) (s + 1)
  have hb1d : blockStart d (polygon Λ) s < d := lt_of_lt_of_le hb1' (le_of_lt hjd')
  have hstrict : blockStart d (polygon Λ) s < blockStart d (polygon Λ) (s + 1) :=
    blockStart_strict d (polygon Λ) hb1d
  have hchord := chord_le_of_discreteConvex (prSum_convex Λ hΛfin) hb1 (le_of_lt hb2) hb2le
  have hstep1 := mul_le_mul_of_nonneg_left
    (prSum_le_polygon_at_boundary hd Λ hΛfin s (le_of_lt hsN)) (Nat.cast_nonneg _ :
      (0 : ℝ) ≤ ((blockStart d (polygon Λ) (s + 1) - j : ℕ) : ℝ))
  have hstep2 := mul_le_mul_of_nonneg_left
    (prSum_le_polygon_at_boundary hd Λ hΛfin (s + 1) (by omega)) (Nat.cast_nonneg _ :
      (0 : ℝ) ≤ ((j - blockStart d (polygon Λ) s : ℕ) : ℝ))
  have haff := polygon_block_affine Λ hb1 (le_of_lt hb2)
  have hlen : ((blockStart d (polygon Λ) (s + 1) - blockStart d (polygon Λ) s : ℕ) : ℝ) =
      ((blockStart d (polygon Λ) (s + 1) - j : ℕ) : ℝ) +
        ((j - blockStart d (polygon Λ) s : ℕ) : ℝ) := by
    have heq : blockStart d (polygon Λ) (s + 1) - blockStart d (polygon Λ) s =
        (blockStart d (polygon Λ) (s + 1) - j) + (j - blockStart d (polygon Λ) s) := by omega
    rw [heq, Nat.cast_add]
  have hposm : (0 : ℝ) <
      ((blockStart d (polygon Λ) (s + 1) - blockStart d (polygon Λ) s : ℕ) : ℝ) :=
    by exact_mod_cast Nat.sub_pos_of_lt hstrict
  have hkey : ((blockStart d (polygon Λ) (s + 1) - blockStart d (polygon Λ) s : ℕ) : ℝ) *
        (prSum Λ j) ≤
      ((blockStart d (polygon Λ) (s + 1) - blockStart d (polygon Λ) s : ℕ) : ℝ) *
        (polygon Λ j + Kconst d) := by
    rw [hlen] at hchord haff
    rw [hlen]
    nlinarith [hchord, hstep1, hstep2, haff]
  exact le_of_mul_le_mul_left hkey hposm

/-- **Prop 4(2), per-index form**: for a full-rank lattice `Λ ≤ ℝᵈ` (`0 < d`) and every
`1 ≤ i ≤ d`,

`|log λᵢ(Λ) − (c(i) − c(i−1))| ≤ Kconst d`,  `c = polygon Λ`,

i.e. `log λᵢ(Λ) = c(i) − c(i−1) + O(1)` with a constant depending only on the dimension.
This combines the two-sided prefix-sum bounds: the lower bound
(`Prop42General.polygon_le_sum_log_general`) and the upper bound proved above. -/
theorem abs_log_successiveMinimum_sub_dslope_le {d : ℕ} (hd : 0 < d)
    (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hΛfin : Module.finrank ℤ Λ = d) {i : ℕ} (hi1 : 1 ≤ i) (hid : i ≤ d) :
    |Real.log (successiveMinimum Λ i) - Submission.Polygon.dslope (polygon Λ) (i - 1)| ≤
      Kconst d := by
  classical
  have hbdd : ∀ r : ℕ, r ≤ d → BddBelow (rankDataSet Λ r) :=
    fun r hr => rankData_bddBelow_of_lattice Λ hΛfin r hr
  have hpr : ∀ j : ℕ, prSum Λ j =
      ∑ x : Fin j, Real.log (successiveMinimum Λ (x.val + 1)) := by
    intro j
    rw [prSum]
    exact (Fin.sum_univ_eq_sum_range
      (fun n : ℕ => Real.log (successiveMinimum Λ (n + 1))) j).symm
  have hub_i : prSum Λ i ≤ polygon Λ i + Kconst d := prSum_le_polygon_add_Kconst hd Λ hΛfin hid
  have hlw_i : polygon Λ i ≤ prSum Λ i := by
    have h := Prop42General.polygon_le_sum_log_general (d := d) (j := i) Λ hΛfin hbdd hi1 hid
    rwa [← hpr i] at h
  have hub_im1 : prSum Λ (i - 1) ≤ polygon Λ (i - 1) + Kconst d :=
    prSum_le_polygon_add_Kconst hd Λ hΛfin (by omega)
  have hlw_im1 : polygon Λ (i - 1) ≤ prSum Λ (i - 1) := by
    rcases Nat.eq_zero_or_pos (i - 1) with h0 | hpos
    · rw [h0, prSum, Finset.range_zero, Finset.sum_empty, polygon_zero]
    · have h := Prop42General.polygon_le_sum_log_general (d := d) (j := i - 1) Λ hΛfin hbdd hpos
        (by omega)
      rwa [← hpr (i - 1)] at h
  have hA : prSum Λ i = prSum Λ (i - 1) + Real.log (successiveMinimum Λ i) := by
    conv_lhs => rw [show i = (i - 1) + 1 from by omega]
    rw [prSum, Finset.sum_range_succ, show (i - 1) + 1 = i from by omega, prSum]
  have hA' : Real.log (successiveMinimum Λ i) = prSum Λ i - prSum Λ (i - 1) := by linarith [hA]
  have hB : Submission.Polygon.dslope (polygon Λ) (i - 1) = polygon Λ i - polygon Λ (i - 1) := by
    unfold Submission.Polygon.dslope
    rw [show i - 1 + 1 = i from by omega]
  have hgoal : |(prSum Λ i - prSum Λ (i - 1)) - (polygon Λ i - polygon Λ (i - 1))| ≤
      Kconst d := by
    rw [abs_le]
    constructor <;> linarith
  rw [hA', hB]
  exact hgoal

end Submission.Prop42Upper
