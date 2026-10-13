/-
Copyright: work module for the Elgindi finite-time singularity project.

# Differentiation of the mode numerator `numW`

`numW m F z = ∫_{Iθ} F z θ · φ_m(θ) dθ` is differentiated under the integral sign at `z₀ > 0`:

  `deriv (numW m F) z₀ = pwF m F z₀ = ∫_{Iθ} ∂_zF(z₀,θ) · φ_m(θ) dθ`.

The hypotheses are exactly the ones produced for a source `C^∞` on the open quadrant and honest
in `ℋ²` by the auxiliary modules of `Zpz/Aux/`: the `θ`-slice integrability of `F`, `∂_zF` and
`φ_m·F`, the pointwise second-order slice bound
`|∂_z²F(τ,θ)| ≤ (2/τ²)√(HkIntegrand α 2 F τ θ)`, the `L¹`-ness of `τ ↦ ∫_θ √(HkIntegrand α 2 F τ θ)`
on compact intervals of positive radii, and Tonelli's theorem for `|∂_z²F|`.

The proof passes to the limit in the difference quotient: `slope_bound` bounds the slope at
`x` by `Cφ·(2/a²)·∫_{uIoc z₀ x} Hsq`, which tends to `0` by the fundamental theorem of calculus
for the primitive of the `L¹` function `Hsq α F` (`setIntegral_uIoc_eq_abs` converts the
`uIoc`-integral into the absolute value of an interval integral).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.PhiStar.Honesty.exists_bound_eFam_mul_cos
import Submission.Work.FTS.ClassCHon.Zpz.Defs
import Submission.Work.FTS.ClassCHon.Zpz.Slope

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.ClassCHon.Zpz

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **Derivative of `numW`.**  Under the slice integrability and the second-order slice bound
hypotheses, the derivative of the `m`-th mode numerator of `F` is the `θ`-integral of
`∂_zF · φ_m`. -/
theorem numW_hasDerivAt {α : ℝ} {F : ℝ → ℝ → ℝ} (m : ℕ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hphi : ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun θ : ℝ => F z θ * phiW m θ) Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.pz F z θ * phiW m θ)
        Work.Spaces.Iθ)
    (habs : ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun θ : ℝ => |F z θ|) Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ : ℝ => |Work.Spaces.pz F z θ|) Work.Spaces.Iθ)
    (hpt2 : ∀ τ θ : ℝ, 0 < τ → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      |Work.Spaces.pzIter 2 F τ θ|
        ≤ (2 / τ ^ 2) * Real.sqrt (Work.Spaces.HkIntegrand α 2 F τ θ))
    (hsl : ∀ τ : ℝ, 0 ≤ τ → MeasureTheory.IntegrableOn
      (fun θ : ℝ => Real.sqrt (Work.Spaces.HkIntegrand α 2 F τ θ)) Work.Spaces.Iθ)
    (hout : ∀ a b : ℝ, 0 < a → MeasureTheory.IntegrableOn
      (fun τ : ℝ => ∫ θ in Work.Spaces.Iθ,
        Real.sqrt (Work.Spaces.HkIntegrand α 2 F τ θ)) (Set.Icc a b))
    (hswap : ∀ {z x : ℝ}, 0 < z → 0 < x →
      MeasureTheory.Integrable (Function.uncurry (fun τ θ : ℝ => |Work.Spaces.pzIter 2 F τ θ|))
          ((MeasureTheory.volume.restrict (Set.uIoc z x)).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
        (∫ θ in Work.Spaces.Iθ, (∫ τ in Set.uIoc z x, |Work.Spaces.pzIter 2 F τ θ|))
          = ∫ τ in Set.uIoc z x,
              (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pzIter 2 F τ θ|))
    {z₀ : ℝ} (hz₀ : 0 < z₀) :
    HasDerivAt (numW m F) (pwF m F z₀) z₀ := by
  obtain ⟨Cφ, hCφnn, hCφ⟩ := Work.FTS.PhiStar.Honesty.exists_bound_eFam_mul_cos m
  have hCφ' : ∀ θ ∈ Work.Spaces.Iθ, |phiW m θ| ≤ Cφ := by
    intro θ hθ; simpa only [phiW] using hCφ θ hθ
  set a : ℝ := z₀ / 2 with ha
  have hapos : 0 < a := by rw [ha]; linarith
  have haz : a ≤ z₀ := by rw [ha]; linarith
  have hHsq_nn : ∀ τ : ℝ, 0 ≤ Hsq α F τ := fun τ =>
    MeasureTheory.integral_nonneg fun θ => Real.sqrt_nonneg _
  -- the punctured-neighbourhood slope bound
  have hbound : ∀ᶠ x in 𝓝[{z₀}ᶜ] z₀,
      |slope (numW m F) z₀ x - pwF m F z₀|
        ≤ Cφ * (2 / a ^ 2) * ∫ τ in Set.uIoc z₀ x, Hsq α F τ := by
    have hmem0 : z₀ ∈ Set.Ioo a (2 * z₀) := ⟨by rw [ha]; linarith, by linarith⟩
    have hmem : ∀ᶠ x in 𝓝[{z₀}ᶜ] z₀, x ∈ Set.Ioo a (2 * z₀) :=
      (show ∀ᶠ x in 𝓝 z₀, x ∈ Set.Ioo a (2 * z₀) from isOpen_Ioo.mem_nhds hmem0).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [hmem, self_mem_nhdsWithin] with x hx hxc
    have hne : x ≠ z₀ := by simpa using hxc
    exact slope_bound m hCφnn hCφ' hsm hphi habs hpt2 hsl hout hswap
      (a := a) (z₀ := z₀) (x := x) hapos haz hx.1.le hx.2.le hz₀
      (lt_trans hapos hx.1) hne
  -- the primitive of `Hsq` is continuous at `z₀`
  have hhalf : (0 : ℝ) < z₀ / 2 := by rw [← ha]; exact hapos
  have hsub : Set.uIcc (z₀ / 2) (2 * z₀) ⊆ Set.Ioi (0 : ℝ) := by
    intro t ht
    rcases Set.mem_uIcc.mp ht with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact lt_of_lt_of_le hhalf h1
    · exact lt_of_lt_of_le (by linarith) h1
  have hint : IntervalIntegrable (Hsq α F) MeasureTheory.volume (z₀ / 2) (2 * z₀) :=
    MeasureTheory.IntegrableOn.intervalIntegrable
      ((hout (z₀ / 2) (2 * z₀) hhalf).mono_set (fun t ht => by
        rwa [Set.uIcc_of_le (by linarith : z₀ / 2 ≤ 2 * z₀)] at ht))
  have hprim : Filter.Tendsto (fun x : ℝ => ∫ τ in z₀..x, Hsq α F τ) (𝓝 z₀) (𝓝 0) := by
    have hcw : ContinuousWithinAt (fun b : ℝ => ∫ s in z₀..b, Hsq α F s)
        (Set.Icc (z₀ / 2) (2 * z₀)) z₀ :=
      intervalIntegral.continuousWithinAt_primitive (μ := MeasureTheory.volume)
        (f := Hsq α F) (a := z₀) (b₀ := z₀) (b₁ := z₀ / 2) (b₂ := 2 * z₀)
        Real.volume_singleton (by
          rw [min_eq_right (by linarith), max_eq_right (by linarith)]
          exact hint)
    have hc : ContinuousAt (fun b : ℝ => ∫ s in z₀..b, Hsq α F s) z₀ :=
      hcw.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
    have h0 : (fun b : ℝ => ∫ s in z₀..b, Hsq α F s) z₀ = 0 := by simp
    rw [← h0]
    exact hc.tendsto
  -- replace the `uIoc`-integral by the absolute value of the interval integral
  have hUIoc : Filter.Tendsto (fun x : ℝ => ∫ τ in Set.uIoc z₀ x, Hsq α F τ)
      (𝓝 z₀) (𝓝 0) := by
    have hfun : (fun x : ℝ => ∫ τ in Set.uIoc z₀ x, Hsq α F τ)
        = fun x : ℝ => |∫ τ in z₀..x, Hsq α F τ| :=
      funext fun x => setIntegral_uIoc_eq_abs hHsq_nn z₀ x
    rw [hfun]
    simpa only [abs_zero] using hprim.abs
  have htend : Filter.Tendsto
      (fun x : ℝ => Cφ * (2 / a ^ 2) * ∫ τ in Set.uIoc z₀ x, Hsq α F τ)
      (𝓝[{z₀}ᶜ] z₀) (𝓝 0) := by
    have hmono : 𝓝[{z₀}ᶜ] z₀ ≤ 𝓝 z₀ := nhdsWithin_le_nhds
    have h := (Filter.Tendsto.mono_left hUIoc hmono).const_mul (Cφ * (2 / a ^ 2))
    simpa only [mul_zero] using h
  have hsq : Filter.Tendsto (fun x => |slope (numW m F) z₀ x - pwF m F z₀|)
      (𝓝[{z₀}ᶜ] z₀) (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun x => abs_nonneg _) hbound htend
  rw [hasDerivAt_iff_tendsto_slope, tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Real.norm_eq_abs] using hsq

end Work.FTS.ClassCHon.Zpz
