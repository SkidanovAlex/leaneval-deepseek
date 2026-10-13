import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.PoissonAux.Defs
import Submission.Work.FTS.PressureOn.PoissonAux.deriv_deriv_rhoProfile_support
import Submission.Work.FTS.PressureOn.PoissonAux.tendsto_integral_massKernel_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Topology

namespace Work.FTS.PressureOn.PoissonAux.KI

/-!
# Peaking of the mass kernel against a continuous test function

The mass kernel `massKernel 1` is (up to normalisation) the second radial derivative of the
cutoff profile `rhoProfile 1` divided by `4π‖x‖`; it vanishes off the *fixed* annulus
`1 ≤ ‖x‖ ≤ √2` (`massKernel_eq_zero_of_lt`) and is integrable (`integrable_massKernel`).
Consequently, for any *continuous* `Ψ`, the rescaled argument `ε • x` tends to `0` uniformly
on the (fixed, compact) support of `massKernel 1`, and

`∫ x, massKernel 1 x * Ψ (ε • x) → Ψ 0 * ∫ x, massKernel 1 x`  as `ε → 0`.

The proof below is the classical `ε`-`δ` estimate: write the difference of the two sides as
`∫ x, massKernel 1 x * (Ψ (ε • x) - Ψ 0)`, bound it by
`(∫ x, |massKernel 1 x|) · sup_{x ∈ supp} |Ψ (ε • x) - Ψ 0|`, and let `ε → 0`.
No `C¹`-regularity of `Ψ` is needed (compare `tendsto_integral_massKernel_mul`, where the
shrinking support forces a first-order Taylor bound), because the support of the kernel here
does not shrink with `ε`; this is exactly what makes `∫ massKernel 1 · Ψ (ε • ·)` peak at
`ε = 0`.
-/

/-- The two-sided (`ε → 0`) version of `massKernel_peak`: the mass kernel `massKernel 1`,
which lives on the fixed annulus `1 ≤ ‖x‖ ≤ √2`, peaks against every continuous `Ψ`. -/
theorem massKernel_peak_aux {Ψ : R3 → ℝ} (hΨ : Continuous Ψ) :
    Filter.Tendsto (fun ε : ℝ => ∫ x : R3, massKernel 1 x * Ψ (ε • x))
      (nhds (0 : ℝ)) (nhds (Ψ 0 * ∫ x : R3, massKernel 1 x)) := by
  have hgint : Integrable (fun x : R3 => massKernel 1 x) := integrable_massKernel 1 one_pos
  -- `massKernel 1` is supported in the fixed ball of radius `√2`
  have hsupp : ∀ x : R3, massKernel 1 x ≠ 0 → ‖x‖ ≤ Real.sqrt 2 := by
    intro x hx
    by_contra h
    rw [not_le] at h
    exact hx (massKernel_eq_zero_of_lt one_pos (by simpa using h))
  -- the total variation of the kernel
  set D : ℝ := ∫ x : R3, |massKernel 1 x| with hD
  have hDnn : 0 ≤ D := integral_nonneg fun x => abs_nonneg _
  have hD1 : 0 < D + 1 := by linarith
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  rw [Metric.tendsto_nhds]
  intro δ hδ
  -- continuity of `Ψ` at the origin, with the weight `(D + 1)⁻¹`
  have hcont : ContinuousAt Ψ 0 := hΨ.continuousAt
  obtain ⟨η, hηpos, hη⟩ :=
    Metric.continuousAt_iff.mp hcont (δ / (D + 1)) (by positivity)
  -- only `ε` with `|ε| √2 < η` matter
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (div_pos hηpos hsqrt)] with ε hε
  have hηε : |ε| * Real.sqrt 2 < η := by
    have h1 : |ε| < η / Real.sqrt 2 := by
      simpa [Metric.mem_ball, Real.dist_eq] using hε
    calc |ε| * Real.sqrt 2 < (η / Real.sqrt 2) * Real.sqrt 2 :=
          mul_lt_mul_of_pos_right h1 hsqrt
      _ = η := by rw [div_mul_cancel₀ _ (ne_of_gt hsqrt)]
  -- pointwise estimate: `|Ψ (ε • x) - Ψ 0|` is small wherever the kernel does not vanish
  have hpoint : ∀ x : R3,
      |massKernel 1 x * (Ψ (ε • x) - Ψ 0)| ≤ |massKernel 1 x| * (δ / (D + 1)) := by
    intro x
    by_cases hx : massKernel 1 x = 0
    · simp [hx]
    · have hxs : ‖x‖ ≤ Real.sqrt 2 := hsupp x hx
      have hnorm : ‖ε • x‖ < η := by
        rw [norm_smul, Real.norm_eq_abs]
        calc |ε| * ‖x‖ ≤ |ε| * Real.sqrt 2 := mul_le_mul_of_nonneg_left hxs (abs_nonneg ε)
          _ < η := hηε
      have hΨx : |Ψ (ε • x) - Ψ 0| ≤ δ / (D + 1) := le_of_lt (by
        have h := hη (x := ε • x) (by simpa [dist_eq_norm] using hnorm)
        rwa [Real.dist_eq] at h)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hΨx (abs_nonneg _)
  have hInt1 : Integrable (fun x : R3 => massKernel 1 x * Ψ (ε • x)) :=
    integrable_massKernel_mul 1 one_pos (hΨ.comp (continuous_const_smul ε))
  have hInt3 : Integrable (fun x : R3 => massKernel 1 x * (Ψ (ε • x) - Ψ 0)) :=
    integrable_massKernel_mul 1 one_pos
      ((hΨ.comp (continuous_const_smul ε)).sub continuous_const)
  -- split off the limit value `Ψ 0 * ∫ massKernel 1`
  have hsplit : ∫ x : R3, massKernel 1 x * (Ψ (ε • x) - Ψ 0)
      = (∫ x : R3, massKernel 1 x * Ψ (ε • x)) - Ψ 0 * ∫ x : R3, massKernel 1 x := by
    rw [show (∫ x : R3, massKernel 1 x * (Ψ (ε • x) - Ψ 0))
        = ∫ x : R3, (massKernel 1 x * Ψ (ε • x) - massKernel 1 x * Ψ 0) from
        integral_congr_ae (Eventually.of_forall fun x => by ring)]
    rw [integral_sub hInt1 (hgint.mul_const (Ψ 0)), integral_mul_const]
    ring
  have hbound : |∫ x : R3, massKernel 1 x * (Ψ (ε • x) - Ψ 0)| ≤ D * (δ / (D + 1)) := by
    have h1 : |∫ x : R3, massKernel 1 x * (Ψ (ε • x) - Ψ 0)|
        ≤ ∫ x : R3, |massKernel 1 x * (Ψ (ε • x) - Ψ 0)| := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun x : R3 => massKernel 1 x * (Ψ (ε • x) - Ψ 0))
    have h2 : ∫ x : R3, |massKernel 1 x * (Ψ (ε • x) - Ψ 0)|
        ≤ ∫ x : R3, |massKernel 1 x| * (δ / (D + 1)) :=
      integral_mono_ae hInt3.abs (hgint.abs.mul_const _) (Eventually.of_forall hpoint)
    have h3 : ∫ x : R3, |massKernel 1 x| * (δ / (D + 1)) = D * (δ / (D + 1)) := by
      rw [integral_mul_const, ← hD]
    linarith [h1, h2, h3]
  have hlt : D * (δ / (D + 1)) < δ := by
    have hratio : D / (D + 1) < 1 := (div_lt_one hD1).mpr (by linarith)
    calc D * (δ / (D + 1)) = δ * (D / (D + 1)) := by ring
      _ < δ * 1 := mul_lt_mul_of_pos_left hratio hδ
      _ = δ := by ring
  rw [Real.dist_eq, ← hsplit]
  exact lt_of_le_of_lt hbound hlt

theorem massKernel_peak {Ψ : R3 → ℝ} (hΨ : Continuous Ψ) :
    Filter.Tendsto (fun ε : ℝ => ∫ x : R3, massKernel 1 x * Ψ (ε • x))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (Ψ 0 * ∫ x : R3, massKernel 1 x)) := by
  exact (massKernel_peak_aux hΨ).mono_left nhdsWithin_le_nhds

end Work.FTS.PressureOn.PoissonAux.KI
