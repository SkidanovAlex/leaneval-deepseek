import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Construction.Defs
import Submission.Work.FTS.GalFields.RHS.SharpAux.Core
import Submission.Work.FTS.Nonlinear.FstarPkg.FK_Fstar

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalFields.Tail

open MeasureTheory

/-- **The `F_*`-slice of the angular moment is integrable on `Iθ`, for *every* `α`.**

`F_*(z,θ)·K(θ) = α·(Γ(θ)/c(α))·F_{*,rad}(z)·K(θ)`.  There are two cases:

* if the `Γ·K` slice is integrable on `Iθ`, then `F_*·K` is a constant multiple of it;
* otherwise `c(α) = ∫_θ Γ(θ)K(θ) dθ = 0` — the integral of a non-integrable function is `0` by
  the Bochner convention `MeasureTheory.integral_undef` — and then `Γ(θ)/c(α) = Γ(θ)/0 = 0`
  makes the slice of `F_*` identically zero.

This is why the statement of `FK_Fstar_add` needs no hypothesis `0 < α`: `F_*` is either a
multiple of an integrable function or it vanishes. -/
theorem integrableOn_Fstar_mul_K (α z : ℝ) :
    MeasureTheory.IntegrableOn
      (fun θ => Work.Construction.Fstar α z θ * Work.Spaces.K θ) Work.Spaces.Iθ := by
  by_cases hG : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.Gam α θ * Work.Spaces.K θ) Work.Spaces.Iθ
  · have h1 : MeasureTheory.IntegrableOn
        (fun θ => (α * Work.FM.Fstar z / Work.Spaces.c α)
          * (Work.Spaces.Gam α θ * Work.Spaces.K θ)) Work.Spaces.Iθ := hG.const_mul _
    exact h1.congr_fun (fun θ _ => by simp only [Work.Construction.Fstar]; ring) measurableSet_Icc
  · have hc0 : Work.Spaces.c α = 0 := by
      rw [Work.Spaces.c]
      exact MeasureTheory.integral_undef hG
    refine (integrableOn_zero (s := Work.Spaces.Iθ)).congr_fun ?_ measurableSet_Icc
    intro θ _
    simp [Work.Construction.Fstar, hc0]

/-- **Additivity of the angular moment `FK` in the profile**, for the split
`F = F_* + u` of the modulation.  Only the `θ`-slices of `u` are assumed integrable: the
`F_*`-slices are automatically integrable (`integrableOn_Fstar_mul_K`), with no hypothesis on
the sign of `α`.  Hence the two angular moments add. -/
theorem FK_Fstar_add {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hint : ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => u z θ * Work.Spaces.K θ) Work.Spaces.Iθ)
    {z : ℝ} (hz : 0 < z) :
    Work.Construction.FK (fun z θ => Work.Construction.Fstar α z θ + u z θ) z
      = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK u z := by
  have hstar := integrableOn_Fstar_mul_K α z
  have hu : MeasureTheory.IntegrableOn (fun θ => u z θ * Work.Spaces.K θ) Work.Spaces.Iθ :=
    hint z hz
  simp only [Work.Construction.FK]
  have hcongr : (∫ θ in Work.Spaces.Iθ,
        (Work.Construction.Fstar α z θ + u z θ) * Work.Spaces.K θ)
      = ∫ θ in Work.Spaces.Iθ,
          (Work.Construction.Fstar α z θ * Work.Spaces.K θ + u z θ * Work.Spaces.K θ) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
  rw [hcongr]
  exact MeasureTheory.integral_add hstar hu

end Work.FTS.GalFields.Tail
