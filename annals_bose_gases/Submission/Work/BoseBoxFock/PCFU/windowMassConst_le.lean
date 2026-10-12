import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.windowMassConst_le`

Pure-real bookkeeping for the window constants, with the FS monomials
`ℓ = a·(μa³)^{−163/323}`, `d = (μa³)^{6/323}`, `s = (μa³)^{1/323}` and the
diluteness bound `μa³ ≤ 1`.

Writing `t := μa³` (so `0 < t ≤ 1`) and `σ := s = t^{1/323}` we have
`t = σ^{323}`, `s = σ`, `d = σ⁶`, `ℓ = a/σ^{163}`, hence

* `(2(sℓ))^{-1}² = σ^{324}/(4a²)`,
* `(2(dsℓ))^{-1}² = σ^{312}/(4a²)`,
* `(M/ℓ)² = M²σ^{326}/a²`,
* `μ²aℓ³ = σ^{157}/a²`,

and the claim reduces (after multiplying by `a²/4 > 0`) to

`((1−εT)σ^{324} + εT σ^{312})·chiP² + 6M²σ^{326} ≤ (chiP² + 6M²)·σ^{157}`,

which holds term by term because `0 < σ ≤ 1` and `157 ≤ 312, 324 ≤ 326`.
-/

namespace Work.BoseBoxFock.PCFU

theorem windowMassConst_le {a μ ℓ d s εT M chiP : ℝ}
    (ha : 0 < a) (hμ : 0 < μ) (hℓ : 0 < ℓ) (hd : 0 < d) (hs : 0 < s)
    (hεT0 : 0 ≤ εT) (hεT1 : εT ≤ 1) (hM0 : 0 ≤ M) (hchiP0 : 0 ≤ chiP)
    (hℓeq : ℓ = a * (μ * a ^ 3) ^ (-(163 / 323) : ℝ))
    (hdeq : d = (μ * a ^ 3) ^ (6 / 323 : ℝ))
    (hseq : s = (μ * a ^ 3) ^ (1 / 323 : ℝ))
    (ht1 : μ * a ^ 3 ≤ 1) :
    16 * ((1 - εT) * ((2 * (s * ℓ))⁻¹) ^ 2 + εT * ((2 * (d * s * ℓ))⁻¹) ^ 2) * chiP ^ 2
        + 24 * (M / ℓ) ^ 2
      ≤ (4 * chiP ^ 2 + 24 * M ^ 2) * (μ ^ 2 * a * ℓ ^ 3) := by
  -- the positivity hypotheses of the interface (`ℓ, d > 0`, `M, chiP ≥ 0`)
  have _ : 0 < ℓ := hℓ
  have _ : 0 < d := hd
  have _ : 0 ≤ M := hM0
  have _ : 0 ≤ chiP := hchiP0
  have ht0 : 0 < μ * a ^ 3 := by positivity
  -- `s = t^{1/323}` has `0 < s ≤ 1` and `s ^ 323 = t`
  have hs0 : 0 < s := by rw [hseq]; positivity
  have hs1 : s ≤ 1 := by rw [hseq]; exact Real.rpow_le_one ht0.le ht1 (by norm_num)
  have hs323 : s ^ 323 = μ * a ^ 3 := by
    rw [hseq]
    rw [← Real.rpow_natCast ((μ * a ^ 3) ^ ((1 : ℝ) / 323)) 323, ← Real.rpow_mul ht0.le]
    rw [show ((1 : ℝ) / 323) * ((323 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
  have hμ' : μ = s ^ 323 / a ^ 3 := by rw [hs323]; field_simp; try ring
  -- `ℓ = a/s ^ 163` and `d = s ^ 6`
  have hℓ' : ℓ = a / s ^ 163 := by
    rw [hℓeq, hseq]
    rw [show (-(163 / 323) : ℝ) = ((1 : ℝ) / 323) * (-163) by norm_num, Real.rpow_mul ht0.le]
    rw [Real.rpow_neg (Real.rpow_nonneg ht0.le _)]
    rw [show (163 : ℝ) = ((163 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  have hd' : d = s ^ 6 := by
    rw [hdeq, hseq]
    rw [show (6 / 323 : ℝ) = ((1 : ℝ) / 323) * 6 by norm_num, Real.rpow_mul ht0.le]
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  -- the four reductions of the goal's subterms
  have h_t1 : ((2 * (s * ℓ))⁻¹) ^ 2 = s ^ 324 / (4 * a ^ 2) := by
    rw [hℓ']; field_simp; try ring
  have h_t2 : ((2 * (d * s * ℓ))⁻¹) ^ 2 = s ^ 312 / (4 * a ^ 2) := by
    rw [hℓ', hd']; field_simp; try ring
  have h_M : (M / ℓ) ^ 2 = M ^ 2 * s ^ 326 / a ^ 2 := by
    rw [hℓ']; field_simp; try ring
  have h_rhs : μ ^ 2 * a * ℓ ^ 3 = s ^ 157 / a ^ 2 := by
    rw [hℓ', hμ']; field_simp; try ring
  -- monotonicity of the powers of `s ∈ (0,1]`
  have hcomp : s ^ 324 ≤ s ^ 157 := pow_le_pow_of_le_one hs0.le hs1 (by norm_num)
  have hcomp2 : s ^ 312 ≤ s ^ 157 := pow_le_pow_of_le_one hs0.le hs1 (by norm_num)
  have hcomp3 : s ^ 326 ≤ s ^ 157 := pow_le_pow_of_le_one hs0.le hs1 (by norm_num)
  rw [h_t1, h_t2, h_M, h_rhs]
  -- factor out `4/a²`
  have hleft : 16 * ((1 - εT) * (s ^ 324 / (4 * a ^ 2)) + εT * (s ^ 312 / (4 * a ^ 2))) * chiP ^ 2
        + 24 * (M ^ 2 * s ^ 326 / a ^ 2)
      = (4 / a ^ 2) * (((1 - εT) * s ^ 324 + εT * s ^ 312) * chiP ^ 2 + 6 * M ^ 2 * s ^ 326) := by
    field_simp; ring
  have hright : (4 * chiP ^ 2 + 24 * M ^ 2) * (s ^ 157 / a ^ 2)
      = (4 / a ^ 2) * ((chiP ^ 2 + 6 * M ^ 2) * s ^ 157) := by
    field_simp; ring
  rw [hleft, hright]
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ 4 / a ^ 2)
  -- the remaining scalar inequality
  have hA : (1 - εT) * s ^ 324 + εT * s ^ 312 ≤ s ^ 157 := by
    have h1 := mul_le_mul_of_nonneg_left hcomp (by linarith : (0 : ℝ) ≤ 1 - εT)
    have h2 := mul_le_mul_of_nonneg_left hcomp2 hεT0
    have h3 : (1 - εT) * s ^ 157 + εT * s ^ 157 = s ^ 157 := by ring
    linarith
  have hB : 6 * M ^ 2 * s ^ 326 ≤ 6 * M ^ 2 * s ^ 157 :=
    mul_le_mul_of_nonneg_left hcomp3 (by positivity)
  have hA' := mul_le_mul_of_nonneg_right hA (sq_nonneg chiP)
  nlinarith [hA', hB]

end Work.BoseBoxFock.PCFU
