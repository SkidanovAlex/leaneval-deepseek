/-
Copyright: work module for the Elgindi finite-time singularity project.

# `D_z 𝓛_Γ^T = D_z 𝓛̂ + Z₃ + Z₄ + Z₇` in the open class `SmoothOpen`

The open-quadrant (`Work.FTS.EllipticEst.SmoothOpen`, i.e. genuine `C^∞` on `(0,∞) × (0,π/2)`,
the class carried by a localised datum) twin of the frozen

  `Work.FTS.CoercivityFix.Coer1T.Dz_LGammaT_eq_Lhat_add_Zrest`,

which is stated for the strip class `Work.FTS.LocData.SmoothQuad` (`C^∞` on `z > -1`).

With `𝓛_Γ^T = 𝓛̂ + Corr` (`Work.FTS.CoercivityFix.LGammaT_eq_Lhat_add_Corr`), differentiating the
two slices in `z` at an interior point `z > 0`, `0 < θ < π/2` and reading off the three nonlocal
deflections `Z₃`, `Z₄`, `Z₇` gives

  `D_z(𝓛_Γ^T f) = D_z(𝓛̂ f) + Z₃ + Z₄ + Z₇`   (`Dz = z ∂_z`).

Nothing in the frozen proof uses the strip `z > -1`: the only smoothness inputs are the
`z`-slices `t ↦ f t θ`, `t ↦ ∂_z f t θ`, `t ↦ ∂_θ f t θ` being differentiable at `z`, and those
come from the *open-quadrant* smoothness (`SmoothOpen.curry_z`, `SmoothOpen.pz`,
`SmoothOpen.pth`) composed with the generic slice lemmas `Work.FTS.LocData.contDiffOn_slice_z`,
which are stated for an arbitrary product `s ×ˢ t`.  So the port only swaps
`Ioi (-1) ×ˢ Ioo 0 (π/2)` for `Q0 = Ioi 0 ×ˢ Ioo 0 (π/2)` and `SmoothQuad` for `SmoothOpen`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.CoercivityFix.Coer1T.slotDz_LGammaT
import Submission.Work.FTS.StrongPersist.H6Aux.LhatCommOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.OClass

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The pointwise decomposition of `D_z𝓛_Γ^T` in the interior class.**  With
`𝓛_Γ^T = 𝓛̂ + Corr` (`LGammaT_eq_Lhat_add_Corr`), the `z`-derivative splits as

  `D_z(𝓛_Γ^T f) = D_z(𝓛̂ f) + Z₃ + Z₄ + Z₇`,

where `Z₃, Z₄, Z₇` are the three nonlocal/projector terms of `Work.Coercivity.SumI`, in the
open-quadrant class `SmoothOpen` (the class of a localised datum). -/
theorem Dz_LGammaT_eq_Lhat_add_Zrest_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 10 ^ 14)
    {f : Work.FTS.Galerkin.Fn} (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hfH : Work.Coercivity.HardyHyp f) :
    ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Work.Spaces.Dz (Work.Coercivity.LGammaT α f) z θ
        = Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ
          + Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
          + Work.Coercivity.Z7 α f z θ := by
  have hα1' : α ≤ 1 := by linarith [hα1]
  intro z θ hz hθ
  have h1z : (1 : ℝ) + z ≠ 0 := by positivity
  have hc : Work.Spaces.c α ≠ 0 := Work.Coercivity.c_ne_zero hα hα1'
  have hcdPz : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pz f)) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    hso.pz
  have hcdPth : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pth f)) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    hso.pth
  have hdiffF : DifferentiableAt ℝ (fun t : ℝ => f t θ) z :=
    (((hso.curry_z hθ).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
      (isOpen_Ioi.mem_nhds hz))
  have hdiffPz : DifferentiableAt ℝ (fun t : ℝ => Work.Spaces.pz f t θ) z :=
    (((Work.FTS.LocData.contDiffOn_slice_z hcdPz hθ).differentiableOn
      Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt (isOpen_Ioi.mem_nhds hz))
  have hdiffPth : DifferentiableAt ℝ (fun t : ℝ => Work.Spaces.pth f t θ) z :=
    (((Work.FTS.LocData.contDiffOn_slice_z hcdPth hθ).differentiableOn
      Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt (isOpen_Ioi.mem_nhds hz))
  have hF : HasDerivAt (fun t : ℝ => f t θ) (Work.Spaces.pz f z θ) z := hdiffF.hasDerivAt
  have hPz : HasDerivAt (fun t : ℝ => Work.Spaces.pz f t θ)
      (Work.Spaces.pz (Work.Spaces.pz f) z θ) z := hdiffPz.hasDerivAt
  have hPth : HasDerivAt (fun t : ℝ => Work.Spaces.pth f t θ)
      (Work.Spaces.pz (Work.Spaces.pth f) z θ) z := hdiffPth.hasDerivAt
  have hden1 : HasDerivAt (fun t : ℝ => 1 + t) (1 : ℝ) z := (hasDerivAt_id z).const_add 1
  -- ## the derivative of the `𝓛̂`-slice
  have hDz : HasDerivAt (fun t : ℝ => t * Work.Spaces.pz f t θ)
      (1 * Work.Spaces.pz f z θ + z * Work.Spaces.pz (Work.Spaces.pz f) z θ) z :=
    (hasDerivAt_id z).mul hPz
  have hq3 : HasDerivAt (fun t : ℝ => 2 * f t θ / (1 + t))
      ((2 * Work.Spaces.pz f z θ * (1 + z) - 2 * f z θ * 1) / (1 + z) ^ 2) z :=
    (hF.const_mul 2).div hden1 h1z
  have hq4 : HasDerivAt (fun t : ℝ => 3 * Real.sin (2 * θ) * Work.Spaces.pth f t θ / (1 + t))
      ((3 * Real.sin (2 * θ) * Work.Spaces.pz (Work.Spaces.pth f) z θ * (1 + z)
        - 3 * Real.sin (2 * θ) * Work.Spaces.pth f z θ * 1) / (1 + z) ^ 2) z :=
    ((hPth.const_mul (3 * Real.sin (2 * θ))).div hden1 h1z)
  have hLhatSlice : HasDerivAt (fun t : ℝ => Work.FTS.CoercivityFix.Lhat f t θ)
      (Work.Spaces.pz f z θ
        + (1 * Work.Spaces.pz f z θ + z * Work.Spaces.pz (Work.Spaces.pz f) z θ)
        - (2 * Work.Spaces.pz f z θ * (1 + z) - 2 * f z θ * 1) / (1 + z) ^ 2
        - (3 * Real.sin (2 * θ) * Work.Spaces.pz (Work.Spaces.pth f) z θ * (1 + z)
            - 3 * Real.sin (2 * θ) * Work.Spaces.pth f z θ * 1) / (1 + z) ^ 2) z := by
    have hmain := ((hF.add hDz).sub hq3).sub hq4
    refine hmain.congr_of_eventuallyEq ?_
    filter_upwards with t
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [Work.FTS.CoercivityFix.Lhat_eq]
    simp only [Work.Spaces.Dz, Work.Spaces.Dth]
    ring
  -- ## the derivative of the `Corr`-slice
  have hL12 : HasDerivAt (fun t : ℝ => Work.Coercivity.L12f f t)
      (-(Work.Coercivity.Kavg f z / z)) z := Work.Coercivity.L12f_zDeriv f hfH hz
  have hsq : HasDerivAt (fun t : ℝ => (1 + t) ^ 2) (2 * (1 + z)) z := by
    have hraw := hden1.pow 2
    have hfun : ((fun t : ℝ => 1 + t) ^ 2) =ᶠ[𝓝 z] (fun t : ℝ => (1 + t) ^ 2) :=
      Filter.Eventually.of_forall (fun t => by simp)
    exact (hraw.congr_of_eventuallyEq hfun).congr_deriv (by simp)
  have hinv : HasDerivAt (fun t : ℝ => ((1 + t) ^ 2)⁻¹)
      (-(2 * (1 + z)) / ((1 + z) ^ 2) ^ 2) z := hsq.inv (by positivity)
  have hprod : HasDerivAt (fun t : ℝ => t * ((1 + t) ^ 2)⁻¹)
      (1 * ((1 + z) ^ 2)⁻¹ + z * (-(2 * (1 + z)) / ((1 + z) ^ 2) ^ 2)) z :=
    (hasDerivAt_id z).mul hinv
  have hg1 : HasDerivAt
      (fun t : ℝ => (-(2 * Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹)) * (t * ((1 + t) ^ 2)⁻¹)
        * Work.Coercivity.L12f f t)
      ((-(2 * Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹)) * (1 * ((1 + z) ^ 2)⁻¹
          + z * (-(2 * (1 + z)) / ((1 + z) ^ 2) ^ 2)) * Work.Coercivity.L12f f z
        + ((-(2 * Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹)) * (z * ((1 + z) ^ 2)⁻¹))
          * (-(Work.Coercivity.Kavg f z / z))) z :=
    (hprod.const_mul (-(2 * Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹))).mul hL12
  have hsq2 : HasDerivAt (fun t : ℝ => 2 * t ^ 2) (4 * z) z := by
    have hraw := ((hasDerivAt_id z).pow 2).const_mul 2
    have hfun : (fun y : ℝ => 2 * (id ^ 2) y) =ᶠ[𝓝 z] (fun t : ℝ => 2 * t ^ 2) :=
      Filter.Eventually.of_forall (fun t => by simp)
    exact (hraw.congr_of_eventuallyEq hfun).congr_deriv (by simp; ring)
  have hcube : HasDerivAt (fun t : ℝ => (1 + t) ^ 3) (3 * (1 + z) ^ 2) z := by
    have hraw := hden1.pow 3
    have hfun : ((fun t : ℝ => 1 + t) ^ 3) =ᶠ[𝓝 z] (fun t : ℝ => (1 + t) ^ 3) :=
      Filter.Eventually.of_forall (fun t => by simp)
    exact (hraw.congr_of_eventuallyEq hfun).congr_deriv (by simp)
  have hinv3 : HasDerivAt (fun t : ℝ => ((1 + t) ^ 3)⁻¹)
      (-(3 * (1 + z) ^ 2) / ((1 + z) ^ 3) ^ 2) z := hcube.inv (by positivity)
  have hinner : HasDerivAt (fun t : ℝ => 2 * t ^ 2 * ((1 + t) ^ 3)⁻¹)
      (4 * z * ((1 + z) ^ 3)⁻¹
        + 2 * z ^ 2 * (-(3 * (1 + z) ^ 2) / ((1 + z) ^ 3) ^ 2)) z :=
    hsq2.mul hinv3
  have hg2 : HasDerivAt
      (fun t : ℝ => (Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹ * Work.Coercivity.C0 f)
        * (2 * t ^ 2 * ((1 + t) ^ 3)⁻¹))
      ((Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹ * Work.Coercivity.C0 f)
        * (4 * z * ((1 + z) ^ 3)⁻¹
          + 2 * z ^ 2 * (-(3 * (1 + z) ^ 2) / ((1 + z) ^ 3) ^ 2))) z :=
    hinner.const_mul _
  have hCorrSlice : HasDerivAt (fun t : ℝ => Work.FTS.CoercivityFix.Corr α f t θ)
      ((-(2 * Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹)) * (1 * ((1 + z) ^ 2)⁻¹
          + z * (-(2 * (1 + z)) / ((1 + z) ^ 2) ^ 2)) * Work.Coercivity.L12f f z
        + ((-(2 * Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹)) * (z * ((1 + z) ^ 2)⁻¹))
          * (-(Work.Coercivity.Kavg f z / z))
        + (Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹ * Work.Coercivity.C0 f)
          * (4 * z * ((1 + z) ^ 3)⁻¹
            + 2 * z ^ 2 * (-(3 * (1 + z) ^ 2) / ((1 + z) ^ 3) ^ 2))) z := by
    have hmain := hg1.add hg2
    refine hmain.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioi.mem_nhds hz] with t ht
    have ht' : (0 : ℝ) < t := ht
    have h1t : (1 : ℝ) + t ≠ 0 := by linarith
    simp only [Pi.add_apply]
    rw [Work.FTS.CoercivityFix.Corr_eq, Work.Coercivity.C0]
    field_simp
  -- ## the sum
  have hsum : HasDerivAt (fun t : ℝ => Work.Coercivity.LGammaT α f t θ)
      ((Work.Spaces.pz f z θ
        + (1 * Work.Spaces.pz f z θ + z * Work.Spaces.pz (Work.Spaces.pz f) z θ)
        - (2 * Work.Spaces.pz f z θ * (1 + z) - 2 * f z θ * 1) / (1 + z) ^ 2
        - (3 * Real.sin (2 * θ) * Work.Spaces.pz (Work.Spaces.pth f) z θ * (1 + z)
            - 3 * Real.sin (2 * θ) * Work.Spaces.pth f z θ * 1) / (1 + z) ^ 2)
      + ((-(2 * Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹)) * (1 * ((1 + z) ^ 2)⁻¹
          + z * (-(2 * (1 + z)) / ((1 + z) ^ 2) ^ 2)) * Work.Coercivity.L12f f z
        + ((-(2 * Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹)) * (z * ((1 + z) ^ 2)⁻¹))
          * (-(Work.Coercivity.Kavg f z / z))
        + (Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹ * Work.Coercivity.C0 f)
          * (4 * z * ((1 + z) ^ 3)⁻¹
            + 2 * z ^ 2 * (-(3 * (1 + z) ^ 2) / ((1 + z) ^ 3) ^ 2)))) z := by
    have hmain := hLhatSlice.add hCorrSlice
    refine hmain.congr_of_eventuallyEq ?_
    filter_upwards with t
    rw [Work.FTS.CoercivityFix.LGammaT_eq_Lhat_add_Corr]
    rfl
  have hderiv := hsum.deriv
  -- ## conclusion
  show Work.Spaces.Dz (Work.Coercivity.LGammaT α f) z θ = _
  rw [show Work.Spaces.Dz (Work.Coercivity.LGammaT α f) z θ
      = z * deriv (fun t : ℝ => Work.Coercivity.LGammaT α f t θ) z from rfl, hderiv,
    show Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ
      = z * (Work.Spaces.pz f z θ
        + (1 * Work.Spaces.pz f z θ + z * Work.Spaces.pz (Work.Spaces.pz f) z θ)
        - (2 * Work.Spaces.pz f z θ * (1 + z) - 2 * f z θ * 1) / (1 + z) ^ 2
        - (3 * Real.sin (2 * θ) * Work.Spaces.pz (Work.Spaces.pth f) z θ * (1 + z)
            - 3 * Real.sin (2 * θ) * Work.Spaces.pth f z θ * 1) / (1 + z) ^ 2)
      from by
        rw [show Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ
            = z * deriv (fun t : ℝ => Work.FTS.CoercivityFix.Lhat f t θ) z from rfl,
          hLhatSlice.deriv]]
  simp only [Work.Coercivity.Z3, Work.Coercivity.Z4, Work.Coercivity.Z7]
  field_simp
  ring

end Work.FTS.StrongEps.EpsE4Thr.OClass
