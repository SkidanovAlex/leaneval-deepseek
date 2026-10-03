import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.envelopeDefs
import Submission.Work.ORHughesFree.NaturalExtension.envelopeToeplitz
import Submission.Work.ORHughesFree.NaturalExtension.toeplitzT_rank
import Submission.Work.ORHughesFree.MatrixBlocks.exists_sylvesterRank_matrix
import Submission.Work.ORHughesFree.RankAPI.rk_reindex
import Submission.Work.ORHughesFree.NaturalExtension.blim_of_tendsto
import Submission.Work.ORHughesFree.NaturalExtension.blim_congr

namespace Work.ORHughesFree.NaturalExtension

open Matrix

/-! ## `blimRank` of a `1 × 1` matrix of blocks

The truncated matrices `toeplitz (n+1) t` live in `W U = ∏_n M_{n+1}(U)`, and `blimRank` of a
`1 × 1` matrix over `W U` is by construction the ultralimit of the normalized ranks of the
`n`-th coordinates.  Here we record that the (redundant) block flattening of a `1 × 1` matrix of
blocks is just its single entry, so that `blimRank` of `oneByOne C` is the ultralimit of the
normalized ranks of the matrices `C n`. -/

/-- Definitional unfolding of `blimRank` as an ultralimit of normalized flattened ranks. -/
theorem blimRank_apply {U : Type} [Ring U] (ω : Ultrafilter ℕ) (rk : SylvesterRank U)
    (k m : ℕ) (A : Matrix (Fin k) (Fin m) (W U)) :
    blimRank ω rk k m A =
      blim ω (fun n => rk.rk (k * (n+1)) (m * (n+1)) (flatW k m A n) / ((n+1 : ℕ) : ℝ)) :=
  rfl

/-- The `n`-th block flattening of the `1 × 1` matrix of blocks with entry `C` is the `n`-th
coordinate of `C`, up to the raw identification of `Fin (1 * (n+1))` with `Fin (n+1)`. -/
theorem flatW_oneByOne {U : Type} [Ring U] (C : W U) (n : ℕ) :
    flatW 1 1 (oneByOne C) n =
      Matrix.reindex ((finCongr (Nat.one_mul (n+1))).symm)
        ((finCongr (Nat.one_mul (n+1))).symm) (C n) := by
  rw [show flatW 1 1 (oneByOne C) n = flattenBlocks (oneByOne (C n)) from rfl,
    Work.ORHughesFree.MatrixBlocks.flattenBlocks_oneByOne]

/-- The rank of the `n`-th flattening of a `1 × 1` matrix of blocks is the rank of its `n`-th
coordinate. -/
theorem rk_flatW_oneByOne {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    (rk : SylvesterRank U) (C : W U) (n : ℕ) :
    rk.rk (1 * (n+1)) (1 * (n+1)) (flatW 1 1 (oneByOne C) n) = rk.rk (n+1) (n+1) (C n) := by
  rw [flatW_oneByOne, Work.ORHughesFree.RankAPI.rk_reindex]

/-- `blimRank` of a `1 × 1` matrix of blocks is the ultralimit of the normalized ranks of the
coordinates of the block. -/
theorem blimRank_oneByOne {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    (ω : Ultrafilter ℕ) (rk : SylvesterRank U) (C : W U) :
    blimRank ω rk 1 1 (oneByOne C) =
      blim ω (fun n => rk.rk (n+1) (n+1) (C n) / ((n+1 : ℕ) : ℝ)) := by
  rw [blimRank_apply]
  apply congrArg (blim ω)
  funext n
  rw [rk_flatW_oneByOne]

/-! ## The two elementary limits -/

/-- `1 - 1/(n+1) → 1`. -/
theorem blim_one_sub_div_eq_one (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.atTop) :
    blim ω (fun n : ℕ => 1 - 1 / (((n+1 : ℕ) : ℝ))) = 1 := by
  refine blim_of_tendsto ω hω (f := fun n : ℕ => 1 - 1 / (((n+1 : ℕ) : ℝ))) (l := 1) (M := 1)
    ?_ ?_
  · intro n
    have hpos : (0:ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
    have hone : (1:ℝ) ≤ ((n+1 : ℕ) : ℝ) := Nat.one_le_cast.mpr (Nat.succ_le_succ (Nat.zero_le n))
    have hle : 1 / (((n+1 : ℕ) : ℝ)) ≤ 1 := (div_le_one hpos).mpr hone
    have hge : (0:ℝ) ≤ 1 / (((n+1 : ℕ) : ℝ)) := by positivity
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  · have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h' : Filter.Tendsto (fun n : ℕ => 1 / (((n+1 : ℕ) : ℝ))) Filter.atTop (nhds 0) := by
      simpa [Nat.cast_add, Nat.cast_one] using h
    have h1 : Filter.Tendsto (fun _ : ℕ => (1:ℝ)) Filter.atTop (nhds 1) := tendsto_const_nhds
    simpa using h1.sub h'

/-- `1/(n+1) → 0`. -/
theorem blim_one_div_eq_zero (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.atTop) :
    blim ω (fun n : ℕ => 1 / (((n+1 : ℕ) : ℝ))) = 0 := by
  refine blim_of_tendsto ω hω (f := fun n : ℕ => 1 / (((n+1 : ℕ) : ℝ))) (l := 0) (M := 1) ?_ ?_
  · intro n
    have hpos : (0:ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
    have hone : (1:ℝ) ≤ ((n+1 : ℕ) : ℝ) := Nat.one_le_cast.mpr (Nat.succ_le_succ (Nat.zero_le n))
    have hle : 1 / (((n+1 : ℕ) : ℝ)) ≤ 1 := (div_le_one hpos).mpr hone
    rw [abs_of_pos (by positivity)]
    exact hle
  · have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa [Nat.cast_add, Nat.cast_one] using h

/-- The `(n+1)`-st coordinate of the block family `1 - A * star A`. -/
theorem sub_star_apply {U : Type} [Ring U] [StarRing U] [MulSemiringAction (Multiplicative ℤ) U]
    (n : ℕ) :
    (1 - toeplitzFamily (skewLaurentT : SkewL U) *
        star (toeplitzFamily (skewLaurentT : SkewL U))) n =
      1 - toeplitz (n+1) (skewLaurentT : SkewL U) *
        star (toeplitz (n+1) (skewLaurentT : SkewL U)) := by
  rw [Pi.sub_apply, Pi.one_apply, Pi.mul_apply, Pi.star_apply]
  rfl

/-! ## The main theorem -/

theorem blimRank_toeplitzT {U : Type} [Ring U] [StarRing U] [MulSemiringAction (Multiplicative ℤ) U]
    (rk : SylvesterRank U) (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.atTop) :
    blimRank ω rk 1 1 (oneByOne (toeplitzFamily (skewLaurentT : SkewMonoidAlgebra U (Multiplicative ℤ)))) = 1 ∧
    blimRank ω rk 1 1 (oneByOne (1 - toeplitzFamily (skewLaurentT : SkewMonoidAlgebra U (Multiplicative ℤ)) *
      star (toeplitzFamily (skewLaurentT : SkewMonoidAlgebra U (Multiplicative ℤ))))) = 0 := by
  constructor
  · rw [blimRank_oneByOne]
    have hseq : (fun n => rk.rk (n+1) (n+1)
          (toeplitzFamily (skewLaurentT : SkewL U) n) / ((n+1 : ℕ) : ℝ))
        = fun n : ℕ => 1 - 1 / (((n+1 : ℕ) : ℝ)) := by
      funext n
      rw [show toeplitzFamily (skewLaurentT : SkewL U) n
            = toeplitz (n+1) (skewLaurentT : SkewL U) from rfl,
          (toeplitzT_rank rk).1 (n+1) (Nat.succ_pos n)]
      have hne : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
      rw [sub_div, div_self hne]
    rw [hseq]
    exact blim_one_sub_div_eq_one ω hω
  · rw [blimRank_oneByOne]
    have hseq : (fun n => rk.rk (n+1) (n+1)
          ((1 - toeplitzFamily (skewLaurentT : SkewL U) *
            star (toeplitzFamily (skewLaurentT : SkewL U))) n) / ((n+1 : ℕ) : ℝ))
        = fun n : ℕ => 1 / (((n+1 : ℕ) : ℝ)) := by
      funext n
      rw [sub_star_apply, (toeplitzT_rank rk).2 (n+1) (Nat.succ_pos n)]
    rw [hseq]
    exact blim_one_div_eq_zero ω hω

end Work.ORHughesFree.NaturalExtension
