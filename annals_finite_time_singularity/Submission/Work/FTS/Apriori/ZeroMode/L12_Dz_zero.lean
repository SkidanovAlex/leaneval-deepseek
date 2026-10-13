/-
# The zero mode of `D_z`: `L₁₂(D_z f)(0) = 0`

The zero mode of the paper's operator is `L₁₂(g)(0) = ∫₀^∞ ∫₀^{π/2} K(θ) g(s,θ)/s dθ ds`.
For `g = D_z f = z ∂_z f` the angular density (`Work.FM.L12dens`) is the `K`-average of
`∂_z f`, away from `s = 0`:

  `L₁₂dens (D_z f)(s) = ∫_{Iθ} K(θ) · ∂_z f(s,θ) dθ`   (`0 < s`),

because `D_z f s θ / s = ∂_z f s θ`.  Hence

  `L₁₂(D_z f)(0) = ∫₀^∞ ∫_{Iθ} K(θ) ∂_z f(s,θ) dθ ds`,

and the inner radial integral vanishes for each `θ` by the fundamental theorem of calculus
applied to `s ↦ K(θ)·f(s,θ)`: that function is continuous on `[0,∞)`, differentiable on
`(0,∞)` with derivative `K(θ)·∂_z f`, it has limit `0` at `+∞` and `K(θ)·f(0,θ) = 0`:

  `∫₀^∞ K(θ) ∂_z f(s,θ) ds = lim_{s→∞} K(θ) f(s,θ) − K(θ) f(0,θ) = 0`.

The product integrability `hint` enters twice: through Fubini (the swap of the two
integrations, `MeasureTheory.integral_integral_swap`) and through the a.e. radial
integrability of the `θ`-slices (`MeasureTheory.Integrable.prod_left_ae`), which is the
integrability hypothesis of the FTC.  Only these are needed: the remaining two hypotheses of
the statement, `hcont` and `hint2`, are not used below, and are kept because they are part of
the requested interface (and are recorded here so that the statement is not silently
weakened).

This is the `z = 0` case of `Work.Coercivity.CommutZ.L12f_Dz_eq`, the identity
`L₁₂(D_z f)(z) = -(f,K)_{L²_θ}(z)` used in the `L₁₂` zero-mode chapter
(design §4 L-N5.8) to see that `L₁₂(D_z f)(0) = 0` for profiles vanishing at `z = 0`.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.FTS.Apriori.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FM.Core

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.Apriori.ZeroMode

theorem L12_Dz_zero {f : ℝ → ℝ → ℝ}
    (hdiff : ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun s => f s θ) (Work.Spaces.pz f z θ) z)
    (hcont : ∀ θ ∈ Work.Spaces.Iθ, ContinuousOn (fun s => Work.Spaces.pz f s θ) (Set.Ici 0))
    (hcont0 : ∀ θ ∈ Work.Spaces.Iθ, ContinuousOn (fun s => f s θ) (Set.Ici 0))
    (hdec : ∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun s => f s θ) Filter.atTop (nhds 0))
    (hvan : ∀ θ ∈ Work.Spaces.Iθ, f 0 θ = 0)
    (hint : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.pz f p.1 p.2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ))
    (hint2 : MeasureTheory.IntegrableOn
      (fun z => Work.Construction.L12dens (Work.Spaces.Dz f) z) (Set.Ioi 0)) :
    Work.Construction.L12 (Work.Spaces.Dz f) 0 = 0 := by
  -- `hcont` and `hint2` are part of the requested interface but are not needed by the argument
  -- below; they are referenced here only to keep the statement intact without a linter notice.
  have _hcont := hcont
  have _hint2 := hint2
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

end Work.FTS.Apriori.ZeroMode
