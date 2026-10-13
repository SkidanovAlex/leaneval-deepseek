import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Stability.Defs
import Submission.Work.FM.Core

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Stability

/-- **The `F_*`-slice is integrable in `θ`.**  For `α > 0` the angular slice
`θ ↦ K(θ) F_*(s,θ)/s` of the reference profile is continuous on the compact interval
`Iθ = [0,π/2]` — `K` is a trigonometric polynomial and `F_* = α(Γ/c) F_{*,rad}(s)` with
`Γ(θ) = (sin θ cos²θ)^{α/3}`, whose exponent `α/3 > 0` makes the real power continuous at
the endpoints `θ = 0, π/2` where `sin θ cos²θ = 0` — hence integrable there.

This is what allows the angular slices of `g` to be recovered from those of the sum
`F_* + g`: it is the *only* place where the statement of `L12Add` uses `α > 0`. -/
theorem integrableOn_slice_Fstar (α : ℝ) (hα : 0 < α) (s : ℝ) :
    MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * Work.Construction.Fstar α s θ / s) Work.Spaces.Iθ := by
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  have hGam : ContinuousOn (fun θ => Work.Spaces.Gam α θ) Work.Spaces.Iθ := by
    unfold Work.Spaces.Gam
    intro θ _
    exact (Real.continuousAt_rpow_const _ _ (Or.inr (by positivity))).comp_continuousWithinAt
      (by fun_prop)
  have hF : ContinuousOn (fun θ => Work.Construction.Fstar α s θ) Work.Spaces.Iθ := by
    simp only [Work.Construction.Fstar]
    exact ((continuousOn_const.mul (hGam.div_const (Work.Spaces.c α))).mul continuousOn_const)
  have hK : ContinuousOn (fun θ => Work.Spaces.K θ) Work.Spaces.Iθ := by
    unfold Work.Spaces.K; fun_prop
  exact (hK.mul hF).div_const s

/-- **Linearity of `L₁₂` over `F = F_* + g`.**  The integral operator
`L₁₂(f)(z) = ∫_z^∞ ∫_0^{π/2} K(θ) f(s,θ)/s dθ ds` is additive, so
`L₁₂(F_* + g)(z) = L₁₂(F_*)(z) + L₁₂(g)(z)`, under the integrability of the two densities on
`(z,∞)` and of the angular slices of the sum.  (This is the `hL`-field of
`Work.Stability.GDerivData`.) -/
theorem L12Add (α : ℝ) (hα : 0 < α) {g : F2} {z : ℝ}
    (h1 : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K (Work.Construction.Fstar α))
      (Set.Ioi z))
    (h2 : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K g) (Set.Ioi z))
    (h3 : ∀ s ∈ Set.Ioi z, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * (Work.Construction.Fstar α s θ + g s θ) / s) Work.Spaces.Iθ) :
    Work.Construction.L12 (fun z θ => Work.Construction.Fstar α z θ + g z θ) z
      = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 g z := by
  -- The reference slice is integrable, so h3 (integrability of the *sum* slice) yields the
  -- integrability of the slice of `g` and `integral_add` applies at the angular level.
  have hdens : ∀ s ∈ Set.Ioi z,
      Work.FM.L12dens Work.Spaces.K (fun z θ => Work.Construction.Fstar α z θ + g z θ) s
        = Work.FM.L12dens Work.Spaces.K (Work.Construction.Fstar α) s
          + Work.FM.L12dens Work.Spaces.K g s := by
    intro s hs
    have hsum := h3 s hs
    have hF := integrableOn_slice_Fstar α hα s
    have hg : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * g s θ / s) Work.Spaces.Iθ := by
      have h := hsum.sub hF
      refine h.congr ?_
      filter_upwards with θ
      simp only [Pi.sub_apply]
      ring
    simp only [Work.FM.L12dens]
    have hcongr : (∫ θ in Set.Icc 0 (Real.pi / 2),
          Work.Spaces.K θ * (Work.Construction.Fstar α s θ + g s θ) / s)
        = ∫ θ in Set.Icc 0 (Real.pi / 2),
          (Work.Spaces.K θ * Work.Construction.Fstar α s θ / s
            + Work.Spaces.K θ * g s θ / s) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro θ _
      ring
    rw [hcongr]
    exact MeasureTheory.integral_add hF hg
  -- Additivity of the outer integral over `(z,∞)`, now that the densities are pointwise equal.
  have key : (∫ s in Set.Ioi z,
        Work.FM.L12dens Work.Spaces.K (fun z θ => Work.Construction.Fstar α z θ + g z θ) s)
      = (∫ s in Set.Ioi z, Work.FM.L12dens Work.Spaces.K (Work.Construction.Fstar α) s)
        + ∫ s in Set.Ioi z, Work.FM.L12dens Work.Spaces.K g s := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun s hs => hdens s hs)]
    exact MeasureTheory.integral_add h1 h2
  simpa only [Work.Construction.L12, Work.FM.L12] using key

end Work.Stability
