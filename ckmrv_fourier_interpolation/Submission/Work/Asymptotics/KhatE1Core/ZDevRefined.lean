import Mathlib
import Submission.Work.Asymptotics.KhatE1.ZAtomsSecondOrder
import Submission.Work.Asymptotics.Compact.kminus_tail_core
import Submission.Work.Asymptotics.KhatE1.SecondOrderAtomIdentities

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane
open Work.Residues (Ept)

noncomputable section

/-!
# Refined cusp deviations of the `z`-atoms (leading coefficients)

The *named* deviations of the `d = 24` analysis (`Compact.dW`, `Compact.dD2`, `Compact.dE14`,
`Compact.dE10`, `Compact.dE8`, `Compact.dDelta`, `Compact.dSinv`, `Compact.dSh`) are only
bounded in the workspace up to their order (`KMFDShapes`, `cusp_W_second`, …), which is enough
for *weight* estimates but not for the `E(z)^k`-coefficient identities of the sharp bracket
bound, where the *leading coefficient* of each deviation must be known.

This module records those leading coefficients:

* `dW z = W(z) - (1 - 8E + 24E²) = -32E³ + 24E⁴ - 48E⁵ + O(‖E‖⁶)`,
* `dD2 z = (U²-V²)(z) - (1 + 16E - 144E²) = 448E³ - 912E⁴ + 2016E⁵ + O(‖E‖⁶)`

with `E = Ept z`, as `O(‖E‖⁴)`-statements (the higher terms being dominated by `‖E‖⁴` on
`‖E‖ ≤ 1`).  The sixth-order expansions themselves are the *proved* `WfunSixthH` and
`UVSqSixthH` of `KhatE1.ZAtomsSecondOrder`.
-/

/-- `Compact.dW z = -32 Ept z³ + O(‖Ept z‖⁴)`. -/
theorem dW_eq_leading :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
      ‖Work.Asymptotics.Compact.dW z + 32 * Ept z ^ 3‖ ≤ C * ‖Ept z‖ ^ 4 := by
  obtain ⟨C, hC, hW⟩ := Work.Asymptotics.KhatE1.WfunSixthH.mono (k := 6) (l := 4) (by norm_num)
  refine ⟨C + 48 + 24, by positivity, fun z hz => ?_⟩
  have hkey : Work.Asymptotics.Compact.dW z + 32 * Ept z ^ 3
      = (Work.Kernels.WFun z - (1 - 8 * Ept z + 24 * (Ept z) ^ 2 - 32 * (Ept z) ^ 3
            + 24 * (Ept z) ^ 4 - 48 * (Ept z) ^ 5))
        + (24 * Ept z ^ 4 - 48 * Ept z ^ 5) := by
    rw [Work.Asymptotics.Compact.dW, Work.Asymptotics.Compact.Wref]; ring
  rw [hkey]
  refine le_trans (norm_add_le _ _) ?_
  have h1 : ‖24 * Ept z ^ 4 - 48 * Ept z ^ 5‖ ≤ 24 * ‖Ept z‖ ^ 4 + 48 * ‖Ept z‖ ^ 5 := by
    calc ‖24 * Ept z ^ 4 - 48 * Ept z ^ 5‖
        ≤ ‖24 * Ept z ^ 4‖ + ‖48 * Ept z ^ 5‖ := norm_sub_le _ _
      _ = 24 * ‖Ept z‖ ^ 4 + 48 * ‖Ept z‖ ^ 5 := by
          rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_ofNat, Complex.norm_ofNat]
  have h2 : ‖Ept z‖ ^ 5 ≤ ‖Ept z‖ ^ 4 :=
    pow_le_pow_of_le_one (norm_nonneg _) (le_of_lt (Work.Residues.norm_Ept_lt_one z)) (by norm_num)
  have h3 : ‖Ept z‖ ^ 6 ≤ ‖Ept z‖ ^ 4 :=
    pow_le_pow_of_le_one (norm_nonneg _) (le_of_lt (Work.Residues.norm_Ept_lt_one z)) (by norm_num)
  have hw := hW z hz
  have h4 : ‖Ept z‖ ^ 4 ≤ ‖Ept z‖ ^ 4 := le_rfl
  nlinarith [hw, h1, h2, h3, h4, hC.le, pow_nonneg (norm_nonneg (Ept z)) 4]

/-- `Compact.dD2 z = 448 Ept z³ + O(‖Ept z‖⁴)`. -/
theorem dD2_eq_leading :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
      ‖Work.Asymptotics.Compact.dD2 z - 448 * Ept z ^ 3‖ ≤ C * ‖Ept z‖ ^ 4 := by
  obtain ⟨C, hC, hU⟩ := Work.Asymptotics.KhatE1.UVSqSixthH.mono (k := 6) (l := 4) (by norm_num)
  refine ⟨C + 2016 + 912, by positivity, fun z hz => ?_⟩
  have hkey : Work.Asymptotics.Compact.dD2 z - 448 * Ept z ^ 3
      = ((Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2)
            - (1 + 16 * Ept z - 144 * (Ept z) ^ 2 + 448 * (Ept z) ^ 3
                - 912 * (Ept z) ^ 4 + 2016 * (Ept z) ^ 5))
        + (-912 * Ept z ^ 4 + 2016 * Ept z ^ 5) := by
    rw [Work.Asymptotics.Compact.dD2, Work.Asymptotics.Compact.D2ref]; ring
  rw [hkey]
  refine le_trans (norm_add_le _ _) ?_
  have h1 : ‖-912 * Ept z ^ 4 + 2016 * Ept z ^ 5‖ ≤ 912 * ‖Ept z‖ ^ 4 + 2016 * ‖Ept z‖ ^ 5 := by
    calc ‖-912 * Ept z ^ 4 + 2016 * Ept z ^ 5‖
        ≤ ‖-912 * Ept z ^ 4‖ + ‖2016 * Ept z ^ 5‖ := norm_add_le _ _
      _ = 912 * ‖Ept z‖ ^ 4 + 2016 * ‖Ept z‖ ^ 5 := by
          rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_neg, Complex.norm_ofNat,
            Complex.norm_ofNat]
  have h2 : ‖Ept z‖ ^ 5 ≤ ‖Ept z‖ ^ 4 :=
    pow_le_pow_of_le_one (norm_nonneg _) (le_of_lt (Work.Residues.norm_Ept_lt_one z)) (by norm_num)
  have h3 : ‖Ept z‖ ^ 6 ≤ ‖Ept z‖ ^ 4 :=
    pow_le_pow_of_le_one (norm_nonneg _) (le_of_lt (Work.Residues.norm_Ept_lt_one z)) (by norm_num)
  have hu := hU z hz
  nlinarith [hu, h1, h2, h3, hC.le, pow_nonneg (norm_nonneg (Ept z)) 4]

/-- `Compact.dE6 z = -16632 q(z)² + O(‖q(z)‖³)`. -/
theorem dE6_eq_leading :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
      ‖Work.Asymptotics.Compact.dE6 z + 16632 * Work.Kernels.qParamFun z ^ 2‖
        ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.KhatE1.E6ThirdOrder
  refine ⟨C, hC, fun z hz => ?_⟩
  have hkey : Work.Asymptotics.Compact.dE6 z + 16632 * Work.Kernels.qParamFun z ^ 2
      = Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z
        + 16632 * Work.Kernels.qParamFun z ^ 2 := by
    rw [Work.Asymptotics.Compact.dE6, Work.Asymptotics.Compact.E6ref,
      Work.Asymptotics.Small.qParamFun_eq_Ept_sq]; ring
  rw [hkey]
  exact h z hz

/-- `Compact.dE8 z = 61920 q(z)² + O(‖q(z)‖³)`. -/
theorem dE8_eq_leading :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
      ‖Work.Asymptotics.Compact.dE8 z - 61920 * Work.Kernels.qParamFun z ^ 2‖
        ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.KhatE1.E4sqThirdOrder
  refine ⟨C, hC, fun z hz => ?_⟩
  have hkey : Work.Asymptotics.Compact.dE8 z - 61920 * Work.Kernels.qParamFun z ^ 2
      = Work.Kernels.E4Fun z ^ 2 - 1 - 480 * Work.Kernels.qParamFun z
        - 61920 * Work.Kernels.qParamFun z ^ 2 := by
    rw [Work.Asymptotics.Compact.dE8, Work.Asymptotics.Compact.E8ref,
      Work.Kernels.E8Fun, Work.Asymptotics.Small.qParamFun_eq_Ept_sq]; ring
  rw [hkey]
  exact h z hz

/-- `Compact.dE10 z = -135432 q(z)² + O(‖q(z)‖³)`. -/
theorem dE10_eq_leading :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
      ‖Work.Asymptotics.Compact.dE10 z + 135432 * Work.Kernels.qParamFun z ^ 2‖
        ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.KhatE1.E4E6ThirdOrder
  refine ⟨C, hC, fun z hz => ?_⟩
  have hkey : Work.Asymptotics.Compact.dE10 z + 135432 * Work.Kernels.qParamFun z ^ 2
      = Work.Kernels.E4Fun z * Work.Kernels.E6Fun z - 1 + 264 * Work.Kernels.qParamFun z
        + 135432 * Work.Kernels.qParamFun z ^ 2 := by
    rw [Work.Asymptotics.Compact.dE10, Work.Asymptotics.Compact.E10ref,
      Work.Kernels.E10Fun, Work.Asymptotics.Small.qParamFun_eq_Ept_sq]; ring
  rw [hkey]
  exact h z hz

end

end Work.Asymptotics.KhatE1Core
