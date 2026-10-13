import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.R1G.Defs
import Submission.Work.Stability.L12Add
import Submission.Work.Elliptic.L12densFacts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G

/-!
# Additivity of the angular density `L₁₂dens` over `F = F_* + g`

`Work.Construction.L12dens f r` is the *angular* density of the operator `L₁₂`, i.e. the integral

  `L₁₂dens f r = ∫_0^{π/2} K(θ)·f(r,θ)/r dθ`   (`K(θ) = 3 sinθ cos²θ`),

`Work.FM.L12dens Work.Spaces.K f r`.  Additivity in `f` is therefore additivity of the angular
integral, and it requires only that the two θ-slices be integrable on the compact interval
`Iθ = [0,π/2]`: for the reference profile this is `Work.Stability.integrableOn_slice_Fstar`
(`K` bounded, `Γ` continuous), and for the perturbation it follows from the smoothness
`ProfileData.hsmooth` of `g` on a neighbourhood of the closed quadrant.  The hypothesis `0 < r`
of the statement is then not needed for the algebra (only, through `g`'s slice continuity, the
weaker `-1 < r` entering `SmoothNbhd`).

This is the `hL`-splitting of the derivation bundle `GDerivData`/`GDerivDataQd`, read at a fixed
value of `z` (`z = r > 0`, where the `L₁₂`-operator is regular).
-/

variable {α : NNReal}

/-- **The θ-slice of `K·g/r` is continuous on `Iθ`** for a perturbation `g` smooth on a
neighbourhood of the closed quadrant and `r` in `(-1,∞)`: the slice `θ ↦ g r θ` is continuous by
`Work.Elliptic.continuousOn_slice_theta_Iθ`, the weight `K` is continuous. -/
theorem continuousOn_slice_K_mul_div (P : Work.ConstructionInstance.ProfileData α)
    {r : ℝ} (hr : -1 < r) :
    ContinuousOn (fun θ => Work.Spaces.K θ * P.g r θ / r) Work.Spaces.Iθ := by
  have hslice : ContinuousOn (fun θ => P.g r θ) Work.Spaces.Iθ :=
    Work.Elliptic.continuousOn_slice_theta_Iθ P.g P.hsmooth (by simpa using hr)
  have hK : Continuous fun θ : ℝ => Work.Spaces.K θ := by
    simp only [Work.Spaces.K]; fun_prop
  exact (hK.continuousOn.mul hslice).div_const r

/-- **Integrability of the θ-slice of `K·g/r` on `Iθ`** — continuity on the compact interval
`Iθ = [0,π/2]`. -/
theorem integrableOn_slice_K_mul_div (P : Work.ConstructionInstance.ProfileData α)
    {r : ℝ} (hr : -1 < r) :
    MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * P.g r θ / r) Work.Spaces.Iθ :=
  (continuousOn_slice_K_mul_div P hr).integrableOn_compact isCompact_Icc

/-- **Linearity of `L₁₂dens` over the full profile `F = F_* + P.g`**:

  `L₁₂dens (F_* + g) r = L₁₂dens F_* r + L₁₂dens g r`   for `r > 0`.

Both integrands are integrable on `Iθ` (`Work.Stability.integrableOn_slice_Fstar` for the
reference profile, `integrableOn_slice_K_mul_div` for the perturbation), so the angular integral
splits by `MeasureTheory.integral_add` after the pointwise identity
`K·(F_* + g)/r = K·F_*/r + K·g/r`. -/
theorem L12densFtot_add {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    {r : ℝ} (hr : 0 < r) :
    Work.Construction.L12dens
        (fun z θ => Work.Construction.Fstar (Work.ConstructionInstance.profExp α) z θ + P.g z θ) r
      = Work.Construction.L12dens (Work.Construction.Fstar (Work.ConstructionInstance.profExp α)) r
        + Work.Construction.L12dens P.g r := by
  have hp : 0 < Work.ConstructionInstance.profExp α :=
    Work.ConstructionInstance.profExp_pos P.hα
  have hF : MeasureTheory.IntegrableOn
      (fun θ =>
        Work.Spaces.K θ * Work.Construction.Fstar (Work.ConstructionInstance.profExp α) r θ / r)
      Work.Spaces.Iθ :=
    Work.Stability.integrableOn_slice_Fstar (Work.ConstructionInstance.profExp α) hp r
  have hg : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * P.g r θ / r)
      Work.Spaces.Iθ :=
    integrableOn_slice_K_mul_div P (by linarith)
  -- the two sides are the same angular integral of the pointwise sum
  have hsplit : (∫ θ in Set.Icc 0 (Real.pi / 2),
        Work.Spaces.K θ * (Work.Construction.Fstar (Work.ConstructionInstance.profExp α) r θ
          + P.g r θ) / r)
      = ∫ θ in Set.Icc 0 (Real.pi / 2),
          (Work.Spaces.K θ * Work.Construction.Fstar (Work.ConstructionInstance.profExp α) r θ / r
            + Work.Spaces.K θ * P.g r θ / r) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
  simp only [Work.Construction.L12dens, Work.FM.L12dens]
  rw [hsplit]
  exact MeasureTheory.integral_add hF hg

end Work.R1G
