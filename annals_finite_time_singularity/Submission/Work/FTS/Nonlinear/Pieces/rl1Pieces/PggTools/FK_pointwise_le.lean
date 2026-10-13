import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.NormNum.RealSqrt
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Blocks.IMC.cs_integral_mul_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The pointwise `L²(θ)`-bound for the angular moment `FK`

`FK g z = ∫_θ g z θ · K θ` with `K θ = 3 sin θ cos²θ` and `Iθ = [0,π/2]`.  Since
`0 ≤ K θ ≤ 3` on `Iθ` and `|Iθ| = π/2`, Cauchy–Schwarz gives

  `|FK g z| ≤ ‖g z ·‖_{L²(Iθ)} · ‖K‖_{L²(Iθ)} ≤ 3√(π/2) · √(∫_θ (g z θ)²)`,

which is the claimed inequality.  Concretely: `‖∫f‖ ≤ ∫‖f‖`, `|g z θ · K θ| = |g z θ| · K θ` on
`Iθ` (as `K ≥ 0` there), the `L²`-pairing step `|∫ f g| ≤ √(∫f²)·√(∫g²)` is the workspace lemma
`Work.Blocks.IMC.cs_integral_mul_le`, and the kernel factor is bounded by `9·(π/2)` for `∫K²`:
`K² ≤ 9` pointwise on `Iθ` and `∫_{Iθ} 1 = π/2`.

The only measurability input needed for Cauchy–Schwarz is `AEStronglyMeasurable (g z ·)`, and it
does *not* follow from square-integrability alone for a general real function; what follows is
`AEStronglyMeasurable (|g z ·|)`, because `|g z θ| = √((g z θ)²)` is a continuous function of
the square-integrable `(g z ·)²`.  That is enough, since `∫ |g z| · K = ∫ |g z · K|`.

The hypothesis `hint` (integrability of `θ ↦ g z θ · K θ`) is not needed for the estimate itself
— `‖∫f‖ ≤ ∫‖f‖` is unconditional — but it is what makes the statement meaningful: it guarantees
that `FK g z` is the genuine Bochner integral of `g z · K` rather than the junk value `0` of a
non-integrable integral.
-/

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools

-- The integrability hypothesis `hint` of `FK_pointwise_le` is part of the requested statement but
-- is not needed for the estimate itself (see the file docstring), whence the linter option.
set_option linter.unusedVariables false

/-- `K(θ) = 3 sin θ cos²θ ≥ 0` on `Iθ`. -/
theorem K_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Spaces.K θ := by
  rw [Work.Spaces.K]
  have h1 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  positivity

/-- `K(θ) = 3 sin θ cos²θ ≤ 3` for every `θ` (hence on `Iθ`). -/
theorem K_le_three (θ : ℝ) : Work.Spaces.K θ ≤ 3 := by
  rw [Work.Spaces.K]
  have h1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have h2 : Real.cos θ ^ 2 ≤ 1 := Real.cos_sq_le_one θ
  have h3 : Real.sin θ * Real.cos θ ^ 2 ≤ 1 := by
    simpa using mul_le_mul h1 h2 (sq_nonneg (Real.cos θ)) (by norm_num : (0 : ℝ) ≤ 1)
  calc 3 * Real.sin θ * Real.cos θ ^ 2 = 3 * (Real.sin θ * Real.cos θ ^ 2) := by ring
    _ ≤ 3 * 1 := mul_le_mul_of_nonneg_left h3 (by norm_num)
    _ = 3 := by ring

/-- `K` is continuous. -/
theorem continuous_K : Continuous fun θ : ℝ => Work.Spaces.K θ := by
  unfold Work.Spaces.K
  fun_prop

/-- `θ ↦ K θ ^ 2` is integrable on `Iθ` (it is continuous and bounded by `9` there, and `Iθ`
has finite measure). -/
theorem integrableOn_K_sq :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (Work.Spaces.K θ) ^ 2) Work.Spaces.Iθ := by
  refine MeasureTheory.Integrable.mono' (g := fun _ : ℝ => (9 : ℝ))
    (MeasureTheory.integrableOn_const (by rw [Work.Spaces.Iθ, Real.volume_Icc]; simp))
    (continuous_K.pow 2).aestronglyMeasurable ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [K_le_three θ, K_nonneg_of_mem_Iθ hθ]

/-- `∫_{Iθ} K² ≤ 9·(π/2)`: pointwise `K² ≤ 9` on `Iθ`, and `|Iθ| = π/2`. -/
theorem integral_K_sq_le :
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ) ^ 2) ≤ 9 * (Real.pi / 2) := by
  have hvol : MeasureTheory.volume.real Work.Spaces.Iθ = Real.pi / 2 := by
    rw [MeasureTheory.measureReal_def, Work.Spaces.Iθ, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  have h9 : (∫ θ in Work.Spaces.Iθ, (9 : ℝ)) = 9 * (Real.pi / 2) := by
    rw [MeasureTheory.setIntegral_const, hvol, smul_eq_mul]
    ring
  rw [← h9]
  refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _)
    (MeasureTheory.integrableOn_const (by rw [Work.Spaces.Iθ, Real.volume_Icc]; simp)) ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
  nlinarith [K_le_three θ, K_nonneg_of_mem_Iθ hθ]

/-- `√(∫_{Iθ} K²) ≤ 3√(π/2)`, the `L²`-norm of the kernel. -/
theorem sqrt_integral_K_sq_le :
    Real.sqrt (∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ) ^ 2)
      ≤ 3 * Real.sqrt (Real.pi / 2) := by
  calc Real.sqrt (∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ) ^ 2)
      ≤ Real.sqrt (9 * (Real.pi / 2)) := Real.sqrt_le_sqrt integral_K_sq_le
    _ = 3 * Real.sqrt (Real.pi / 2) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9)]
        norm_num

theorem FK_pointwise_le {g : ℝ → ℝ → ℝ} {z : ℝ}
    (hint : MeasureTheory.IntegrableOn (fun θ => g z θ * Work.Spaces.K θ) Work.Spaces.Iθ)
    (h2 : MeasureTheory.IntegrableOn (fun θ => (g z θ) ^ 2) Work.Spaces.Iθ) :
    |Work.Construction.FK g z|
      ≤ 3 * Real.sqrt (Real.pi / 2) * Real.sqrt (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2) := by
  have hIθae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ∈ Work.Spaces.Iθ :=
    MeasureTheory.self_mem_ae_restrict measurableSet_Icc
  -- `|g z ·|` is ae-strongly measurable, being `√(·)` of the square-integrable `(g z ·)²`
  have haesm_abs : MeasureTheory.AEStronglyMeasurable (fun θ => |g z θ|)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h : MeasureTheory.AEStronglyMeasurable (fun θ => (g z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := h2.aestronglyMeasurable
    refine (Real.continuous_sqrt.comp_aestronglyMeasurable h).congr
      (Eventually.of_forall fun θ => ?_)
    exact Real.sqrt_sq_eq_abs (g z θ)
  have habs_sq_int : MeasureTheory.Integrable (fun θ => |g z θ| ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have heq : (fun θ => |g z θ| ^ 2) = fun θ => (g z θ) ^ 2 := by
      funext θ
      exact sq_abs (g z θ)
    rw [heq]
    exact h2
  have hKsq_int : MeasureTheory.Integrable (fun θ => (Work.Spaces.K θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := integrableOn_K_sq
  -- Cauchy–Schwarz, `L²(Iθ)`
  have hcs := Work.Blocks.IMC.cs_integral_mul_le (MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (f := fun θ => |g z θ|) (g := fun θ => Work.Spaces.K θ)
    haesm_abs continuous_K.aestronglyMeasurable habs_sq_int hKsq_int
  have hsq_eq : (∫ θ in Work.Spaces.Iθ, |g z θ| ^ 2)
      = ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 := by
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun θ => ?_)
    exact sq_abs (g z θ)
  have hcs' : |∫ θ in Work.Spaces.Iθ, |g z θ| * Work.Spaces.K θ|
      ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ) ^ 2) := by
    simpa only [hsq_eq] using hcs
  -- drop the absolute value inside the integral, using `K ≥ 0` on `Iθ`
  have hstep1 : |∫ θ in Work.Spaces.Iθ, g z θ * Work.Spaces.K θ|
      ≤ ∫ θ in Work.Spaces.Iθ, |g z θ| * Work.Spaces.K θ := by
    have h := MeasureTheory.norm_integral_le_integral_norm
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun θ => g z θ * Work.Spaces.K θ)
    simp only [Real.norm_eq_abs] at h
    refine h.trans (le_of_eq ?_)
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hIθae] with θ hθ
    rw [abs_mul, abs_of_nonneg (K_nonneg_of_mem_Iθ hθ)]
  have hstep2 : |∫ θ in Work.Spaces.Iθ, |g z θ| * Work.Spaces.K θ|
      = ∫ θ in Work.Spaces.Iθ, |g z θ| * Work.Spaces.K θ := by
    rw [abs_of_nonneg (MeasureTheory.integral_nonneg_of_ae
      (hIθae.mono fun θ hθ => mul_nonneg (abs_nonneg _) (K_nonneg_of_mem_Iθ hθ)))]
  have hFK : Work.Construction.FK g z
      = ∫ θ in Work.Spaces.Iθ, g z θ * Work.Spaces.K θ := rfl
  rw [hFK]
  calc |∫ θ in Work.Spaces.Iθ, g z θ * Work.Spaces.K θ|
      ≤ ∫ θ in Work.Spaces.Iθ, |g z θ| * Work.Spaces.K θ := hstep1
    _ = |∫ θ in Work.Spaces.Iθ, |g z θ| * Work.Spaces.K θ| := hstep2.symm
    _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ) ^ 2) := hcs'
    _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2) * (3 * Real.sqrt (Real.pi / 2)) :=
        mul_le_mul_of_nonneg_left sqrt_integral_K_sq_le (Real.sqrt_nonneg _)
    _ = 3 * Real.sqrt (Real.pi / 2) * Real.sqrt (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2) := by
        ring

end Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools
