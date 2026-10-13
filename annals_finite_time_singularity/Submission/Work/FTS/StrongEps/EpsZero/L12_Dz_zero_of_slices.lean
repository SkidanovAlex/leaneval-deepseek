/-
# The zero mode of `D_z` from the *slicewise* hypotheses only

`Work.FTS.Apriori.ZeroMode.L12_Dz_zero` proves `L₁₂(D_z f)(0) = 0` under the hypotheses
`hdiff, hcont, hcont0, hdec, hvan, hint, hint2`, where `hcont` (continuity of the slices of
`∂_z f` on `[0,∞)`) and `hint2` (integrability of the density of `D_z f`) are part of the
requested interface but never used in the argument.  This file provides the version actually
consumed by the `StrongEps` (`ClassC`-based) chain, where the natural hypotheses are only the
*slice* statements: differentiability on `(0,∞)`, continuity of the slices of `f` on `[0,∞)`,
decay at `+∞`, vanishing at `0`, and the joint integrability of `K(θ)·∂_z f` on
`(0,∞) × Iθ`.

The argument is the one recorded at the head of `L12_Dz_zero`: for `s ≠ 0` the angular density
of `D_z f` is the `K`-average of `∂_z f`,

  `L₁₂dens (D_z f)(s) = ∫_{Iθ} K(θ) · ∂_z f(s,θ) dθ`,

so `L₁₂(D_z f)(0) = ∫_{s>0} ∫_{Iθ} K(θ) ∂_z f(s,θ)`, and for each `θ` the inner radial integral
vanishes by the FTC applied to `s ↦ K(θ)·f(s,θ)`, which is continuous on `[0,∞)`,
differentiable on `(0,∞)`, tends to `0` at `+∞`, and vanishes at `0`.  Fubini (legitimate by
`hint`) both swaps the two integrations and supplies the a.e. radial integrability of the
`θ`-slices needed by the FTC.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.Apriori.ZeroMode.L12_Dz_zero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongEps.EpsZero

theorem L12_Dz_zero_of_slices {f : ℝ → ℝ → ℝ}
    (hdiff : ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun s => f s θ) (Work.Spaces.pz f z θ) z)
    (hcont0 : ∀ θ ∈ Work.Spaces.Iθ, ContinuousOn (fun s => f s θ) (Set.Ici 0))
    (hdec : ∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun s => f s θ) Filter.atTop (nhds 0))
    (hvan : ∀ θ ∈ Work.Spaces.Iθ, f 0 θ = 0)
    (hint : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.pz f p.1 p.2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)) :
    Work.Construction.L12 (Work.Spaces.Dz f) 0 = 0 := by
  -- The angular density of `D_z f` is the `K`-average of `∂_z f`, for `s ≠ 0`.
  have hdens : ∀ s ∈ Set.Ioi (0 : ℝ),
      Work.Construction.L12dens (Work.Spaces.Dz f) s
        = ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.pz f s θ := by
    intro s hs
    have hsne : s ≠ 0 := ne_of_gt hs
    have hpt : ∀ θ : ℝ, Work.Spaces.K θ * Work.Spaces.Dz f s θ / s
        = Work.Spaces.K θ * Work.Spaces.pz f s θ := by
      intro θ
      simp only [Work.Spaces.Dz]
      rw [mul_div_assoc, mul_div_cancel_left₀ _ hsne]
    simp only [Work.Construction.L12dens, Work.FM.L12dens]
    exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => hpt θ)
  -- `L₁₂(D_z f)(0)` as the iterated integral `∫_s ∫_θ K(θ) ∂_z f(s,θ)`.
  have hstep : Work.Construction.L12 (Work.Spaces.Dz f) 0
      = ∫ s in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.K θ * Work.Spaces.pz f s θ := by
    rw [show Work.Construction.L12 (Work.Spaces.Dz f) 0
        = ∫ s in Set.Ioi (0 : ℝ), Work.Construction.L12dens (Work.Spaces.Dz f) s from rfl]
    exact setIntegral_congr_fun measurableSet_Ioi hdens
  have hsIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  -- Fubini: swap the two integrations (legitimate by `hint`).
  have hswap : (∫ s in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.K θ * Work.Spaces.pz f s θ)
      = ∫ θ in Work.Spaces.Iθ, ∫ s in Set.Ioi (0 : ℝ),
          Work.Spaces.K θ * Work.Spaces.pz f s θ := by
    refine integral_integral_swap (μ := volume.restrict (Set.Ioi (0 : ℝ)))
      (ν := volume.restrict Work.Spaces.Iθ)
      (f := fun s θ => Work.Spaces.K θ * Work.Spaces.pz f s θ) ?_
    rw [MeasureTheory.Measure.prod_restrict]
    exact hint
  -- For almost every `θ` the radial integral vanishes, by the FTC.
  have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ∫ s in Set.Ioi (0 : ℝ), Work.Spaces.K θ * Work.Spaces.pz f s θ = 0 := by
    -- Fubini also gives the a.e. radial integrability of the slices, the FTC's integrability
    -- hypothesis.
    have hslice : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        MeasureTheory.IntegrableOn (fun s => Work.Spaces.K θ * Work.Spaces.pz f s θ)
          (Set.Ioi 0) := by
      have hprod : MeasureTheory.Integrable
          (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.pz f p.1 p.2)
          ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict Work.Spaces.Iθ)) := by
        rw [MeasureTheory.Measure.prod_restrict]
        exact hint
      exact hprod.prod_left_ae
    filter_upwards [hslice, MeasureTheory.self_mem_ae_restrict (μ := volume) hsIθ]
      with θ hsl hmem
    have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun s => Work.Spaces.K θ * f s θ)
        (Work.Spaces.K θ * Work.Spaces.pz f x θ) x :=
      fun x hx => (hdiff θ hmem x hx).const_mul _
    have hcw : ContinuousWithinAt (fun s => Work.Spaces.K θ * f s θ) (Set.Ici 0) 0 :=
      ((hcont0 θ hmem).continuousWithinAt (by simp : (0 : ℝ) ∈ Set.Ici 0)).const_mul _
    have hlim : Filter.Tendsto (fun s => Work.Spaces.K θ * f s θ) Filter.atTop (nhds (0 : ℝ)) := by
      simpa using (hdec θ hmem).const_mul (Work.Spaces.K θ)
    have hftc := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcw hderiv hsl hlim
    rw [hvan θ hmem] at hftc
    simpa using hftc
  rw [hstep, hswap]
  calc ∫ θ in Work.Spaces.Iθ, (∫ s in Set.Ioi (0 : ℝ),
        Work.Spaces.K θ * Work.Spaces.pz f s θ)
      = ∫ θ in Work.Spaces.Iθ, (0 : ℝ) := integral_congr_ae hae
    _ = 0 := integral_zero ℝ ℝ

end Work.FTS.StrongEps.EpsZero
