import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.EllipticEst.Core.derivIntegrableOfEnergy
import Submission.Work.FTS.EllipticEst.AngSecond.abs_setIntegral_le_sqrt_mul_sqrt
import Submission.Work.FTS.EllipticEst.Prop.TraceLeftPieces.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The two integrations by parts against the cutoff `χ`

`cutoff_ibp` produces the boundary term `F₀ L₀` and `cutoff_ibp_cross` moves the `χ'`-term onto
`χ''`.
-/

namespace Work.FTS.EllipticEst.Prop.TraceLeftCore

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

/-! ### The first integration by parts -/

theorem cutoff_ibp (f χ : ℝ → ℝ) {F₀ L₀ : ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hχ : ∀ θ : ℝ, HasDerivAt χ (deriv χ θ) θ)
    (hχ1 : ∀ θ : ℝ, θ ≤ Real.pi / 4 → χ θ = 1)
    (hχ0 : ∀ θ : ℝ, 3 * Real.pi / 8 ≤ θ → χ θ = 0)
    (hlim : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 F₀))
    (hlimL : Tendsto (deriv f) (𝓝[>] (0 : ℝ)) (𝓝 L₀))
    (hint : IntervalIntegrable (fun θ : ℝ => (deriv f θ) ^ 2 * χ θ + f θ * deriv χ θ * deriv f θ
      + f θ * χ θ * deriv (deriv f) θ) volume 0 (3 * Real.pi / 8)) :
    F₀ * L₀ = -(∫ θ in (0 : ℝ)..(3 * Real.pi / 8),
      ((deriv f θ) ^ 2 * χ θ + f θ * deriv χ θ * deriv f θ
        + f θ * χ θ * deriv (deriv f) θ)) := by
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) (3 * Real.pi / 8),
      HasDerivAt (fun θ : ℝ => f θ * χ θ * deriv f θ)
        ((deriv f x) ^ 2 * χ x + f x * deriv χ x * deriv f x
          + f x * χ x * deriv (deriv f) x) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
    have hmem : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 x := isOpen_Ioo.mem_nhds hx'
    have hfx : HasDerivAt f (deriv f x) x :=
      ((hf.of_le (by norm_num : ((1 : ℕ∞) : WithTop ℕ∞) ≤ 2)).differentiableOn_one).differentiableAt
        hmem |>.hasDerivAt
    have hdfx : HasDerivAt (deriv f) (deriv (deriv f) x) x :=
      ((hf.deriv_of_isOpen (m := 1) isOpen_Ioo (by norm_num)).differentiableOn_one).differentiableAt
        hmem |>.hasDerivAt
    have h := (hfx.mul (hχ x)).mul hdfx
    convert h using 1
    simp only [Pi.mul_apply]
    ring
  have ha : Tendsto (fun θ : ℝ => f θ * χ θ * deriv f θ) (𝓝[>] (0 : ℝ)) (𝓝 (F₀ * L₀)) := by
    have hev : (fun θ : ℝ => f θ * χ θ * deriv f θ) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun θ : ℝ => f θ * deriv f θ) := by
      filter_upwards [self_mem_nhdsWithin,
        Filter.le_def.mp nhdsWithin_le_nhds _ (Iio_mem_nhds (by positivity : (0:ℝ) < Real.pi/4))]
        with θ _ hθ4
      rw [hχ1 θ (le_of_lt hθ4)]
      ring
    exact (hlim.mul hlimL).congr' hev.symm
  have hb : Tendsto (fun θ : ℝ => f θ * χ θ * deriv f θ) (𝓝[<] (3 * Real.pi / 8)) (𝓝 0) := by
    have hmem : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 (3 * Real.pi / 8) :=
      isOpen_Ioo.mem_nhds three_eighths_mem
    have hcf : Tendsto f (𝓝 (3 * Real.pi / 8)) (𝓝 (f (3 * Real.pi / 8))) :=
      (hf.continuousOn.continuousAt hmem).tendsto
    have hcg : Tendsto (deriv f) (𝓝 (3 * Real.pi / 8)) (𝓝 (deriv f (3 * Real.pi / 8))) :=
      ((hf.deriv_of_isOpen (m := 1) isOpen_Ioo (by norm_num)).continuousOn.continuousAt
        hmem).tendsto
    have hcχ : Tendsto χ (𝓝 (3 * Real.pi / 8)) (𝓝 (χ (3 * Real.pi / 8))) :=
      (hχ (3 * Real.pi / 8)).continuousAt.tendsto
    have hprod : Tendsto (fun θ : ℝ => f θ * deriv f θ * χ θ) (𝓝[<] (3 * Real.pi / 8))
        (𝓝 (f (3 * Real.pi / 8) * deriv f (3 * Real.pi / 8) * χ (3 * Real.pi / 8))) :=
      ((hcf.mono_left nhdsWithin_le_nhds).mul
        (hcg.mono_left nhdsWithin_le_nhds)).mul (hcχ.mono_left nhdsWithin_le_nhds)
    rw [hχ0 _ le_rfl, mul_zero] at hprod
    exact hprod.congr' (Eventually.of_forall (fun θ : ℝ => by ring))
  have hmain : (∫ θ in (0 : ℝ)..(3 * Real.pi / 8),
      ((deriv f θ) ^ 2 * χ θ + f θ * deriv χ θ * deriv f θ + f θ * χ θ * deriv (deriv f) θ))
      = 0 - F₀ * L₀ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (by positivity) hderiv hint ha hb
  rw [hmain]
  ring

/-! ### The second integration by parts (the `χ'`-term) -/

theorem cutoff_ibp_cross (f χ : ℝ → ℝ)
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hχ2 : ∀ θ : ℝ, HasDerivAt (deriv χ) (deriv (deriv χ) θ) θ)
    (hχ1' : ∀ θ : ℝ, θ ≤ Real.pi / 4 → deriv χ θ = 0)
    (hχ0' : ∀ θ : ℝ, 3 * Real.pi / 8 ≤ θ → deriv χ θ = 0)
    (hint1 : IntervalIntegrable (fun θ : ℝ => f θ * deriv f θ * deriv χ θ) volume 0
      (3 * Real.pi / 8))
    (hint2 : IntervalIntegrable (fun θ : ℝ => (f θ) ^ 2 * deriv (deriv χ) θ) volume 0
      (3 * Real.pi / 8)) :
    (∫ θ in (0 : ℝ)..(3 * Real.pi / 8), f θ * deriv f θ * deriv χ θ)
      = -(1 / 2) * (∫ θ in (0 : ℝ)..(3 * Real.pi / 8),
          (f θ) ^ 2 * deriv (deriv χ) θ) := by
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) (3 * Real.pi / 8),
      HasDerivAt (fun θ : ℝ => (1 / 2) * (f θ) ^ 2 * deriv χ θ)
        (f x * deriv f x * deriv χ x + (1 / 2) * ((f x) ^ 2 * deriv (deriv χ) x)) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
    have hmem : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 x := isOpen_Ioo.mem_nhds hx'
    have hfx : HasDerivAt f (deriv f x) x :=
      ((hf.of_le (by norm_num : ((1 : ℕ∞) : WithTop ℕ∞) ≤ 2)).differentiableOn_one).differentiableAt
        hmem |>.hasDerivAt
    have h := ((hfx.pow 2).const_mul (1 / 2)).mul (hχ2 x)
    convert h using 1
    simp only [Pi.mul_apply, Pi.pow_apply]
    ring
  have ha : Tendsto (fun θ : ℝ => (1 / 2) * (f θ) ^ 2 * deriv χ θ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hev : (fun θ : ℝ => (1 / 2) * (f θ) ^ 2 * deriv χ θ)
        =ᶠ[𝓝[>] (0 : ℝ)] fun _ => (0 : ℝ) := by
      filter_upwards [self_mem_nhdsWithin,
        Filter.le_def.mp nhdsWithin_le_nhds _ (Iio_mem_nhds (by positivity : (0:ℝ) < Real.pi/4))]
        with θ _ hθ4
      rw [hχ1' θ (le_of_lt hθ4)]
      ring
    exact tendsto_const_nhds.congr' hev.symm
  have hb : Tendsto (fun θ : ℝ => (1 / 2) * (f θ) ^ 2 * deriv χ θ) (𝓝[<] (3 * Real.pi / 8))
      (𝓝 0) := by
    have hmem : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 (3 * Real.pi / 8) :=
      isOpen_Ioo.mem_nhds three_eighths_mem
    have hcf : Tendsto f (𝓝 (3 * Real.pi / 8)) (𝓝 (f (3 * Real.pi / 8))) :=
      (hf.continuousOn.continuousAt hmem).tendsto
    have hcg : Tendsto (deriv χ) (𝓝 (3 * Real.pi / 8)) (𝓝 (deriv χ (3 * Real.pi / 8))) :=
      (hχ2 (3 * Real.pi / 8)).continuousAt.tendsto
    have hprod : Tendsto (fun θ : ℝ => (1 / 2) * (f θ * f θ) * deriv χ θ)
        (𝓝[<] (3 * Real.pi / 8))
        (𝓝 ((1 / 2) * (f (3 * Real.pi / 8) * f (3 * Real.pi / 8))
          * deriv χ (3 * Real.pi / 8))) :=
      (((hcf.mul hcf).mono_left nhdsWithin_le_nhds).const_mul (1 / 2)).mul
        (hcg.mono_left nhdsWithin_le_nhds)
    have hval : (1 / 2) * (f (3 * Real.pi / 8) * f (3 * Real.pi / 8))
        * deriv χ (3 * Real.pi / 8) = (0 : ℝ) := by
      rw [hχ0' _ le_rfl, mul_zero]
    rw [hval] at hprod
    exact hprod.congr' (Eventually.of_forall (fun θ : ℝ => by ring))
  have hsum : IntervalIntegrable
      (fun θ : ℝ => f θ * deriv f θ * deriv χ θ + (1 / 2) * ((f θ) ^ 2 * deriv (deriv χ) θ))
      volume 0 (3 * Real.pi / 8) :=
    hint1.add (hint2.const_mul (1 / 2))
  have hmain : (∫ θ in (0 : ℝ)..(3 * Real.pi / 8),
      (f θ * deriv f θ * deriv χ θ + (1 / 2) * ((f θ) ^ 2 * deriv (deriv χ) θ))) = 0 - 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (by positivity) hderiv hsum ha hb
  have hsplit : (∫ θ in (0 : ℝ)..(3 * Real.pi / 8),
        (f θ * deriv f θ * deriv χ θ + (1 / 2) * ((f θ) ^ 2 * deriv (deriv χ) θ)))
      = (∫ θ in (0 : ℝ)..(3 * Real.pi / 8), f θ * deriv f θ * deriv χ θ)
        + (1 / 2) * (∫ θ in (0 : ℝ)..(3 * Real.pi / 8), (f θ) ^ 2 * deriv (deriv χ) θ) := by
    rw [intervalIntegral.integral_add hint1 (hint2.const_mul (1 / 2)),
      intervalIntegral.integral_const_mul]
  rw [hsplit] at hmain
  linarith

end

end Work.FTS.EllipticEst.Prop.TraceLeftCore
