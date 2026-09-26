import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.Bracket24XtruncDefs
import Submission.Work.Asymptotics.KhatE1Core.DSm1RowBound
import Submission.Work.Asymptotics.KhatE1.ZAtomsSecondOrder

namespace Work.Asymptotics.KhatE1Core.XtruncDev

open UpperHalfPlane

noncomputable section

/-!
# `D2T` is the sixth-order truncation of `U² - V²`

`D2T` (`Bracket24XtruncDefs.D2T`) is the truncated version of the `z`-atom `U(z)² - V(z)²`
used in the materialised `d = 24` bracket `Xtrunc`:

  `D2T z = 1 + 16 E - 144 E² + 448 E³ - 912 E⁴ + 2016 E⁵`,  `E = Ept z = e^{πiz}`,

and the atom expansion `Work.Asymptotics.KhatE1.UVSqSixthH` of `KhatE1.ZAtomsSecondOrder`
states exactly that the remainder is `O(‖E‖⁶) = O(‖q‖³)` on the half-plane `1 ≤ Im z`:

  `IsSmH 6 (fun z => (U(z)² - V(z)²) - (1 + 16E - 144E² + 448E³ - 912E⁴ + 2016E⁵))`.

Since `D2T z` *is* that polynomial in `E = Ept z` (`D2T` is defined through the abbrev
`Te = Ept`), the transfer to the two-exponent funnel calculus `Bound2` at the exponents
`(n, k) = (0, 3)` is immediate: `‖Ept z‖⁶ = (‖Ept z‖²)³ = ‖qParamFun z‖³`, and
`‖qParamFun τ‖⁰ = (scale τ)⁰ = (1 + t)⁰ = 1`.

This is the `d = 24` companion of `E10Tdev` (`E₁₀ - E10T = O(‖q‖³)`) and of `WTdev`
(`W - WT = O(‖q‖³)`, both `WT` and `WfunSixthH` being the analogous truncation of `W = θ₀₁⁴`).
-/

/-- `q(z) = E(z)²`, so `‖q(z)‖ = ‖E(z)‖²`. -/
private lemma qParamFun_eq_Ept_sq' (z : ℍ) :
    Work.Kernels.qParamFun z = Work.Residues.Ept z ^ 2 := by
  rw [Work.Residues.Ept, Work.Kernels.qParamFun, sq, ← Complex.exp_add]
  congr 1
  ring

/-- `‖q(z)‖³ = ‖E(z)‖⁶`. -/
private lemma norm_qParamFun_pow_three (z : ℍ) :
    ‖Work.Kernels.qParamFun z‖ ^ (3 : ℤ) = ‖Work.Residues.Ept z‖ ^ 6 := by
  rw [qParamFun_eq_Ept_sq' z, norm_pow, zpow_ofNat]
  ring

/-- **`D2T` is the `‖q(z)‖³`-truncation of `U(z)² - V(z)²`.** -/
theorem D2Tdev :
    Work.Asymptotics.KhatE1Core.Bound2
      (fun (_ : UpperHalfPlane) (z : UpperHalfPlane) =>
        (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2)
          - Work.Asymptotics.KhatE1Core.D2T z) 0 3 := by
  obtain ⟨C, hC, hb⟩ := Work.Asymptotics.KhatE1.UVSqSixthH
  refine ⟨C, 0, 0, hC, le_rfl, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have hzi : (1 : ℝ) ≤ z.im := by
    have h1 := Work.Asymptotics.Funnel.im_one hF
    rw [hzim]; linarith
  have h := hb z hzi
  rw [norm_qParamFun_pow_three z]
  simp only [Work.Asymptotics.KhatE1Core.D2T, Work.Asymptotics.KhatE1Core.Te, zpow_zero,
    Real.rpow_zero, one_mul, mul_one]
  exact h

end

end Work.Asymptotics.KhatE1Core.XtruncDev
