import Mathlib
import Submission.Work.LinnikAreas.FarBoundOfJutilaMontgomery
import Submission.Work.LinnikAreas.JMAux.QuarterPowMulRpow
import Submission.Work.LinnikAreas.JMAux.GeomTailLe
import Submission.Work.LinnikAreas.JMAux.RpowTwoSubTwoLeThreeQuarters
import Submission.Work.LinnikAreas.JMAux.PowSubTwoPowClogLe
import Submission.Work.LinnikAreas.JMAux.CellLayerEqClogIcc

namespace Work.LinnikAreas.JMAux

/-- The `k`-sum of the weight `(1/4)^k · cellLayer R m k · (q·2^k)^θ` is bounded by
`4 q^θ R^{-9/10}`:  the layer indicator is `1` exactly for `k ≥ clog 2 (max R m)`, so the sum is
a geometric tail with ratio `2^(θ-2) ≤ 3/4`, whose leading term `(2^(θ-2))^j` is at most
`R^{-9/10}` because `2^j ≥ R` and `θ - 2 ≤ -9/10`. -/
lemma CellLayerKsum (q R N m : ℕ) (hR : 1 ≤ R) (hq : 0 ≤ q) {θ : ℝ} (hθ : θ ≤ 11/10) :
    ∑ k ∈ Finset.range N, (1/4:ℝ)^k * Work.LinnikAreas.cellLayer R m k * ((q:ℝ)*(2:ℝ)^k)^θ
      ≤ 4 * (q:ℝ)^θ * (R:ℝ)^(-(9/10:ℝ)) := by
  classical
  have h2 : (1:ℕ) < 2 := by norm_num
  have hq0 : (0:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  set j : ℕ := Nat.clog 2 (max R m) with hj
  have hRj : (R:ℝ) ≤ (2:ℝ)^j := by
    rw [hj]
    have hc : max R m ≤ 2 ^ Nat.clog 2 (max R m) := Nat.le_pow_clog h2 (max R m)
    have hRc : R ≤ max R m := le_max_left _ _
    have h3 : R ≤ 2 ^ Nat.clog 2 (max R m) := le_trans hRc hc
    calc (R:ℝ) ≤ ((2 ^ Nat.clog 2 (max R m) : ℕ) : ℝ) := by exact_mod_cast h3
      _ = (2:ℝ) ^ Nat.clog 2 (max R m) := by push_cast; ring
  have hcell : ∀ k, Work.LinnikAreas.cellLayer R m k = (if j ≤ k then (1:ℝ) else 0) := by
    intro k
    rw [hj]
    exact CellLayerEqClogIcc R m k
  have hqm : ∀ k, (1/4:ℝ)^k * Work.LinnikAreas.cellLayer R m k * ((q:ℝ)*(2:ℝ)^k)^θ
      = (if j ≤ k then (1:ℝ) else 0) * ((q:ℝ)^θ * ((2:ℝ)^(θ-2))^k) := by
    intro k
    rw [hcell k]
    by_cases h : j ≤ k
    · rw [if_pos h, one_mul, mul_one]
      exact QuarterPowMulRpow q k θ
    · rw [if_neg h]
      ring
  have hsum : ∑ k ∈ Finset.range N, (1/4:ℝ)^k * Work.LinnikAreas.cellLayer R m k
        * ((q:ℝ)*(2:ℝ)^k)^θ
      = (q:ℝ)^θ * ∑ k ∈ Finset.range N, (if j ≤ k then (1:ℝ) else 0) * ((2:ℝ)^(θ-2))^k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hqm k]
    ring
  have hqnn : (0:ℝ) ≤ (q:ℝ)^θ := Real.rpow_nonneg hq0 θ
  have hr0 : 0 ≤ (2:ℝ)^(θ-2) := Real.rpow_nonneg (by norm_num) _
  have hgeo : ∑ k ∈ Finset.range N, (if j ≤ k then (1:ℝ) else 0) * ((2:ℝ)^(θ-2))^k
      ≤ 4 * ((2:ℝ)^(θ-2))^j := GeomTailLe _ hr0 (RpowTwoSubTwoLeThreeQuarters hθ) N j
  have hbound : ((2:ℝ)^(θ-2))^j ≤ (R:ℝ)^(-(9/10:ℝ)) := PowSubTwoPowClogLe R j hR hRj hθ
  calc ∑ k ∈ Finset.range N, (1/4:ℝ)^k * Work.LinnikAreas.cellLayer R m k * ((q:ℝ)*(2:ℝ)^k)^θ
      = (q:ℝ)^θ * ∑ k ∈ Finset.range N, (if j ≤ k then (1:ℝ) else 0) * ((2:ℝ)^(θ-2))^k :=
        hsum
    _ ≤ (q:ℝ)^θ * (4 * ((2:ℝ)^(θ-2))^j) := mul_le_mul_of_nonneg_left hgeo hqnn
    _ ≤ (q:ℝ)^θ * (4 * (R:ℝ)^(-(9/10:ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbound (by norm_num)) hqnn
    _ = 4 * (q:ℝ)^θ * (R:ℝ)^(-(9/10:ℝ)) := by ring

end Work.LinnikAreas.JMAux
