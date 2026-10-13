import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.Proj_L12f_zero
import Submission.Work.Spaces.Defs
import Submission.Work.Coercivity.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FM.Core
import Submission.Work.Spaces.CAux.integrableOn_GamK
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsZero.Bridge

open MeasureTheory

/-- The angular profile `K(θ)Γ(θ)/c` is integrable on `Iθ`.  (Used to transfer the
integrability of the transport density to its projection: the projection subtracts a
constant multiple of `K Γ/c` from every `θ`-slice.) -/
theorem integrableOn_KGam_div_c {α : ℝ} (hα : 0 < α) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ * Work.Spaces.Gam α θ / Work.Spaces.c α) Work.Spaces.Iθ := by
  refine MeasureTheory.IntegrableOn.congr_fun
    ((Work.Spaces.CAux.integrableOn_GamK α hα).const_mul (Work.Spaces.c α)⁻¹)
    (fun θ _ => ?_) measurableSet_Icc
  show (Work.Spaces.c α)⁻¹ * (Work.Spaces.Gam α θ * Work.Spaces.K θ)
      = Work.Spaces.K θ * Work.Spaces.Gam α θ / Work.Spaces.c α
  ring

/-- **The pointwise identity underlying `ProjTransport`.**  The angular slice density of the
projection is the slice density of `f` minus the constant `L₁₂(f)(0)·2s/(1+s)³` times
`K Γ/c`:

`K(θ)·𝕡(f)(s,θ)/s = K(θ)·f(s,θ)/s - (L₁₂(f)(0)·2s²/(1+s)³/s)·(K(θ)Γ(θ)/c)`.

(This is `Proj_eq` rearranged so that the `z`-dependent correction profile and the angular
profile `K Γ/c` are separated.) -/
theorem slice_Proj_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (s θ : ℝ) :
    Work.Spaces.K θ * Work.Coercivity.Proj α f s θ / s
      = Work.Spaces.K θ * f s θ / s
        - (Work.Coercivity.L12f f 0 * (2 * s ^ 2 / (1 + s) ^ 3) / s)
          * (Work.Spaces.K θ * Work.Spaces.Gam α θ / Work.Spaces.c α) := by
  simp only [Work.Coercivity.Proj_eq]
  ring

theorem ProjTransport {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hslice : ∀ s : ℝ, 0 < s → MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ * Work.Coercivity.Transport f s θ / s) Work.Spaces.Iθ)
    (hdens : MeasureTheory.IntegrableOn
      (Work.Construction.L12dens (Work.Coercivity.Transport f)) (Set.Ioi 0)) :
    (∀ s : ℝ, 0 < s → MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ * Work.Coercivity.Proj α (Work.Coercivity.Transport f) s θ / s)
      Work.Spaces.Iθ) ∧
    MeasureTheory.IntegrableOn
      (Work.Construction.L12dens (Work.Coercivity.Proj α (Work.Coercivity.Transport f)))
      (Set.Ioi 0) := by
  have hGK := integrableOn_KGam_div_c (α := α) hα
  refine ⟨?_, ?_⟩
  · -- the angular slices of the projection are the slices of `Transport f` minus a constant
    -- multiple of `K Γ/c`
    intro s hs
    have hcorr : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
            * (2 * s ^ 2 / (1 + s) ^ 3) / s)
          * (Work.Spaces.K θ * Work.Spaces.Gam α θ / Work.Spaces.c α)) Work.Spaces.Iθ :=
      hGK.const_mul _
    refine MeasureTheory.IntegrableOn.congr_fun ((hslice s hs).sub hcorr) (fun θ _ => ?_)
      measurableSet_Icc
    simp only [Pi.sub_apply]
    exact (slice_Proj_eq α (Work.Coercivity.Transport f) s θ).symm
  · -- the density of the projection is the density of `Transport f` minus an integrable
    -- correction profile
    have hproj := fun s (hs : s ∈ Set.Ioi (0:ℝ)) =>
      Work.Coercivity.Proj_L12dens α hα hα1 (Work.Coercivity.Transport f)
        (fun s hs => hslice s hs) hs
    have hcorr : MeasureTheory.IntegrableOn
        (fun s : ℝ => Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
          * (2 * s / (1 + s) ^ 3)) (Set.Ioi 0) :=
      Work.Coercivity.integrableOn_two_mul_div_cube.const_mul _
    refine MeasureTheory.IntegrableOn.congr_fun (hdens.sub hcorr) (fun s hs => ?_)
      measurableSet_Ioi
    simp only [Pi.sub_apply]
    rw [Work.Construction.L12dens, Work.Construction.L12dens, hproj s hs]

end Work.FTS.StrongEps.EpsZero.Bridge
