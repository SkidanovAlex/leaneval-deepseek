/-
# The angular Cauchy–Schwarz for the `∫⁻_θ |K A B|` block

`inner_lintegral_le` is the elementary ingredient every `rl¹`/`gg`-row of `N` uses when a
piece of the nonlinearity is dominated pointwise by `K θ · A(z,θ) · B(z,θ)` with `A` bounded
by a constant `M` and `B` only known through the *square* bound `∫⁻_θ B(z,θ)² ≤ Φz`:

```
∫⁻_θ |K θ · A z θ · B z θ| ≤ ofReal (3 M √(π/2)) · (ofReal Φz)^(1/2) .
```

The proof is the honest one: `|K θ| ≤ 3` (so `K` is bounded and drops out with a constant),
`|A| ≤ M` a.e., and the remaining `∫⁻_θ 3 M |B|` is Cauchy–Schwarz in `L²(Iθ)` against the
constant function `1`, whose `L²`-norm is `√(volume Iθ) = √(π/2)`.  The constant `3√(π/2)`
is therefore exactly the one produced by `K ≤ 3` together with `μ Iθ = π/2` (the sharp
constant `(∫K²)^{1/2} = 3√(π/32)` is a factor `4` smaller, but no application needs it).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools

/-- `K` is bounded by `3` on all of `ℝ` (and on `Iθ` it is nonnegative and `≤ 3`). -/
theorem abs_K_le_three_aux (θ : ℝ) : |Work.Spaces.K θ| ≤ 3 := by
  rw [Work.Spaces.K]
  have h1 : |Real.sin θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
  have h2 : |Real.cos θ ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [Real.neg_one_le_cos θ, Real.cos_le_one θ]
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
  calc 3 * |Real.sin θ| * |Real.cos θ ^ 2| ≤ 3 * 1 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2 (abs_nonneg _) (by norm_num)
    _ = 3 := by norm_num

theorem inner_lintegral_le {A B : ℝ → ℝ → ℝ} {M Φz z : ℝ}
    (hM : 0 ≤ M) (hΦz : 0 ≤ Φz)
    (hAmeas : MeasureTheory.AEStronglyMeasurable (fun θ => A z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hBmeas : MeasureTheory.AEStronglyMeasurable (fun θ => B z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hAb : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), |A z θ| ≤ M)
    (hB : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((B z θ) ^ 2)) ≤ ENNReal.ofReal Φz) :
    (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * A z θ * B z θ|)
      ≤ ENNReal.ofReal (3 * M * Real.sqrt (Real.pi / 2)) *
          (ENNReal.ofReal Φz) ^ (1 / 2 : ℝ) := by
  have h3M : (0 : ℝ) ≤ 3 * M := mul_nonneg (by norm_num) hM
  -- the pointwise a.e. domination by `3 M |B|`
  have hbd : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |Work.Spaces.K θ * A z θ * B z θ| ≤ 3 * M * |B z θ| := by
    filter_upwards [hAb] with θ hθ
    have hK := abs_K_le_three_aux θ
    have h1 : |Work.Spaces.K θ| * |A z θ| ≤ 3 * M :=
      mul_le_mul hK hθ (abs_nonneg _) (by norm_num)
    calc |Work.Spaces.K θ * A z θ * B z θ|
        = |Work.Spaces.K θ| * |A z θ| * |B z θ| := by rw [abs_mul, abs_mul]
      _ ≤ 3 * M * |B z θ| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  -- pull the constant `3 M` out of the integral
  have hstep1 : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * A z θ * B z θ|)
      ≤ ENNReal.ofReal (3 * M) * ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |B z θ| := by
    calc (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * A z θ * B z θ|)
        ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (3 * M * |B z θ|) :=
          MeasureTheory.lintegral_mono_ae
            (hbd.mono fun θ hθ => ENNReal.ofReal_le_ofReal hθ)
      _ = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (3 * M) * ENNReal.ofReal |B z θ| := by
          rw [MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)]
          exact ENNReal.ofReal_mul h3M
      _ = ENNReal.ofReal (3 * M) * ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |B z θ| :=
          MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  -- Cauchy–Schwarz against the constant function `1` on `Iθ`
  have hcs : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |B z θ|)
      ≤ ENNReal.ofReal (Real.sqrt (Real.pi / 2)) * (ENNReal.ofReal Φz) ^ (1 / 2 : ℝ) := by
    have hg : AEMeasurable (fun θ => ENNReal.ofReal |B z θ|)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (hBmeas.aemeasurable.abs).ennreal_ofReal
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (p := 2) (q := 2) Real.HolderConjugate.two_two
      (f := fun _ : ℝ => (1 : ENNReal)) (g := fun θ => ENNReal.ofReal |B z θ|)
      aemeasurable_const hg
    have h1 : (∫⁻ a : ℝ, ((fun _ : ℝ => (1 : ENNReal)) * (fun θ => ENNReal.ofReal |B z θ|)) a
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |B z θ| := by
      simp [Pi.mul_apply]
    have h1' : (∫⁻ a : ℝ, (1 : ENNReal) ^ (2 : ℝ)
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) = ENNReal.ofReal (Real.pi / 2) := by
      simp only [ENNReal.one_rpow]
      rw [MeasureTheory.setLIntegral_const, one_mul, Work.Spaces.Iθ, Real.volume_Icc]
      norm_num
    have h2 : (∫⁻ a : ℝ, (fun θ => ENNReal.ofReal |B z θ|) a ^ (2 : ℝ)
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((B z θ) ^ 2) := by
      rw [MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)]
      show ENNReal.ofReal |B z θ| ^ (2 : ℝ) = ENNReal.ofReal (B z θ ^ 2)
      rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_two, sq_abs]
    have hsqrt : (ENNReal.ofReal (Real.pi / 2)) ^ (1 / 2 : ℝ)
        = ENNReal.ofReal (Real.sqrt (Real.pi / 2)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num : (0 : ℝ) ≤ 1 / 2),
        ← Real.sqrt_eq_rpow]
    rw [h1, h1', h2] at hH
    calc (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |B z θ|)
        ≤ (ENNReal.ofReal (Real.pi / 2)) ^ (1 / 2 : ℝ)
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((B z θ) ^ 2)) ^ (1 / 2 : ℝ) := hH
      _ ≤ (ENNReal.ofReal (Real.pi / 2)) ^ (1 / 2 : ℝ) * (ENNReal.ofReal Φz) ^ (1 / 2 : ℝ) :=
          mul_le_mul_right (ENNReal.rpow_le_rpow hB (by norm_num)) _
      _ = ENNReal.ofReal (Real.sqrt (Real.pi / 2)) * (ENNReal.ofReal Φz) ^ (1 / 2 : ℝ) := by
          rw [hsqrt]
  calc (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * A z θ * B z θ|)
      ≤ ENNReal.ofReal (3 * M) * ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |B z θ| := hstep1
    _ ≤ ENNReal.ofReal (3 * M)
          * (ENNReal.ofReal (Real.sqrt (Real.pi / 2)) * (ENNReal.ofReal Φz) ^ (1 / 2 : ℝ)) :=
        mul_le_mul_right hcs _
    _ = ENNReal.ofReal (3 * M * Real.sqrt (Real.pi / 2))
          * (ENNReal.ofReal Φz) ^ (1 / 2 : ℝ) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul h3M]

end Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools
