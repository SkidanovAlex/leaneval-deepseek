import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.AngAWeak.Basic
import Submission.Work.FTS.EllipticEst.AeCrux.AeMixedAeMemOfCrux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux

/-!
## The endpoint values of the angular slices of `D_z u = z ∂_z u`

For every datum in `AeData` the Dirichlet conditions `u · 0 ≡ 0` and `u · (π/2) ≡ 0` are
imposed for *every* `z`, hence the radial derivative at the two endpoint angles also vanishes:
`z ∂_z u (z,0) = z ∂_z u (z,π/2) = 0`.  These two *values* are the ones the one-dimensional
slice machinery consumes (`slice_ibp_sigma_fts`, `hardy_slice_cos2`, `slice_sharp_bound`), and
they cost nothing — the expensive input there is the *closed-interval* smoothness
`ContDiffOn ℝ 2 (fun θ => z * pz u z θ) (Icc 0 (π/2))`, i.e. the trace of `D_z u`; see
`NOTES_aeMixedAe_mem_ROUTE3.md`.
-/

/-- `D_z u` vanishes at the angle `θ = 0`, as a value. -/
theorem dzSliceValue_left {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hAe : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (z : ℝ) :
    z * Work.Spaces.pz u z 0 = 0 := by
  rw [Work.Spaces.pz]
  have h : (fun z' : ℝ => u z' 0) = fun _ => (0 : ℝ) := by
    funext z'; exact hAe.dirZero z'
  rw [h, deriv_const]
  ring

/-- `D_z u` vanishes at the angle `θ = π/2`, as a value. -/
theorem dzSliceValue_right {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hAe : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (z : ℝ) :
    z * Work.Spaces.pz u z (Real.pi / 2) = 0 := by
  rw [Work.Spaces.pz]
  have h : (fun z' : ℝ => u z' (Real.pi / 2)) = fun _ => (0 : ℝ) := by
    funext z'; exact hAe.dirPi z'
  rw [h, deriv_const]
  ring

theorem aeMixedAe_mem : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) →
      (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        MeasureTheory.IntegrableOn
          (fun θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iz := by
  intro α u G hA hU
  exact Work.FTS.EllipticEst.AeCrux.AeMixedAeMemOfCrux hA hU
    (Work.FTS.EllipticEst.AeCrux.AeSliceHonV hA hU)
    (Work.FTS.EllipticEst.AeCrux.AeVGlobalFin2 hA hU)

end Work.FTS.EllipticEst.Cores.AeStep2Aux
