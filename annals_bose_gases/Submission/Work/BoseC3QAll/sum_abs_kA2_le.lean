import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseC3QAll.estQ3fourADefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseC3QAll.sum_abs_kA2_le`

The second of the four coefficient bounds of the `Q₃⁽⁴⁾` estimate
(`Work.BoseC3QAll.estQ3fourA`).  Recall (FS `eq:1Q-integral`)

```
kA2 s = f_L(s) χ̂²(s) [ ρ_z ℓ³ Ŵ₁ω(0) − Σ_{k∈P_H} Ŵ₁(k) α_k ] ,
```

so `kA2` is `f_L χ̂²` times the `lem:EstimateIntegral` remainder.  FS's node
`N-INT` (`Q3KernelFSAll.intOne`) bounds exactly that remainder:

```
| ρ_z Ŵ₁ω(0) − ℓ⁻³ Σ_{k∈P_H} Ŵ₁(k) α_k | ≤ K₀ ρ_z a K_H⁻¹ .
```

Multiplying by `ℓ³` (using `ℓ³ · ℓ⁻³ = 1`) bounds the bracket by
`ℓ³ · K₀ ρ_z a K_H⁻¹`, and `|f_L| ≤ 1`, together with the lattice count
`Σ_s |χ̂²(s)| ≤ K₀` (`Q3KernelFSAll.sum_hatChiSq`), produces the claimed bound
`K₀² ρ_z a K_H⁻¹ ℓ³`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseC3QAll

open Work.BoseB7

theorem sum_abs_kA2_le (K₀ : ℝ)
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseC3QAll.TildeData F) (E : Work.BoseB7.Q3Env Mode)
    (hK : Work.BoseC3QAll.Q3KernelFSAll K₀ F T E) (hv : Work.BoseB7.FSParamsView E) :
    ∑ s ∈ Work.BoseB7.excited Mode, |Work.BoseC3QAll.kA2 F E s|
      ≤ K₀ ^ 2 * E.rho * E.aScat * E.KH⁻¹ * E.ell ^ 3 := by
  have hell : 0 < E.ell := Work.BoseB7.ell_pos E hv
  -- the `lem:EstimateIntegral` remainder is nonnegative (it dominates an absolute value)
  have hBnn : 0 ≤ K₀ * E.rho * E.aScat * E.KH⁻¹ := le_trans (abs_nonneg _) hK.intOne
  have hellBnn : 0 ≤ E.ell ^ 3 * (K₀ * E.rho * E.aScat * E.KH⁻¹) :=
    mul_nonneg (pow_pos hell 3).le hBnn
  -- `ρ_z ℓ³ Ŵ₁ω(0) − Σ_k Ŵ₁(k)α_k = ℓ³ (ρ_z Ŵ₁ω(0) − ℓ⁻³ Σ_k Ŵ₁(k)α_k)`
  have habs : |E.rho * E.ell ^ 3 * E.W1omega0 - ∑ k ∈ F.PHset E, E.W1 k * E.alpha k|
      ≤ E.ell ^ 3 * (K₀ * E.rho * E.aScat * E.KH⁻¹) := by
    have hC : E.rho * E.ell ^ 3 * E.W1omega0 - ∑ k ∈ F.PHset E, E.W1 k * E.alpha k
        = E.ell ^ 3 * (E.rho * E.W1omega0
            - E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, E.W1 k * E.alpha k) := by
      have hinv : E.ell ^ 3 * E.ell ^ (-(3 : ℝ)) = 1 := by
        rw [← Real.rpow_natCast E.ell 3, ← Real.rpow_add hell]
        norm_num
      rw [mul_sub]
      rw [show E.ell ^ 3 * (E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, E.W1 k * E.alpha k)
            = (E.ell ^ 3 * E.ell ^ (-(3 : ℝ))) * ∑ k ∈ F.PHset E, E.W1 k * E.alpha k
          from by ring]
      rw [hinv, one_mul]
      ring
    rw [hC, abs_mul, abs_of_pos (pow_pos hell 3)]
    exact mul_le_mul_of_nonneg_left hK.intOne (pow_pos hell 3).le
  calc ∑ s ∈ Work.BoseB7.excited Mode, |Work.BoseC3QAll.kA2 F E s|
      ≤ ∑ s ∈ Work.BoseB7.excited Mode,
          |E.hatChiSq s| * (E.ell ^ 3 * (K₀ * E.rho * E.aScat * E.KH⁻¹)) :=
        Finset.sum_le_sum fun s _ => by
          have hfL : |E.fL s| ≤ 1 := by
            rw [abs_of_nonneg (hK.fL_nonneg s)]
            exact hK.fL_le_one s
          calc |kA2 F E s|
              = |E.fL s| * |E.hatChiSq s|
                  * |E.rho * E.ell ^ 3 * E.W1omega0
                      - ∑ k ∈ F.PHset E, E.W1 k * E.alpha k| := by
                rw [kA2, abs_mul, abs_mul]
            _ ≤ |E.hatChiSq s| * (E.ell ^ 3 * (K₀ * E.rho * E.aScat * E.KH⁻¹)) := by
                calc |E.fL s| * |E.hatChiSq s|
                        * |E.rho * E.ell ^ 3 * E.W1omega0
                            - ∑ k ∈ F.PHset E, E.W1 k * E.alpha k|
                    ≤ (1 * |E.hatChiSq s|) * (E.ell ^ 3 * (K₀ * E.rho * E.aScat * E.KH⁻¹)) :=
                      mul_le_mul (mul_le_mul_of_nonneg_right hfL (abs_nonneg _)) habs
                        (abs_nonneg _) (mul_nonneg zero_le_one (abs_nonneg _))
                  _ = |E.hatChiSq s| * (E.ell ^ 3 * (K₀ * E.rho * E.aScat * E.KH⁻¹)) := by
                      ring
    _ = (∑ s ∈ Work.BoseB7.excited Mode, |E.hatChiSq s|)
          * (E.ell ^ 3 * (K₀ * E.rho * E.aScat * E.KH⁻¹)) := by
        rw [Finset.sum_mul]
    _ ≤ K₀ * (E.ell ^ 3 * (K₀ * E.rho * E.aScat * E.KH⁻¹)) :=
        mul_le_mul_of_nonneg_right hK.sum_hatChiSq hellBnn
    _ = K₀ ^ 2 * E.rho * E.aScat * E.KH⁻¹ * E.ell ^ 3 := by ring

end Work.BoseC3QAll
