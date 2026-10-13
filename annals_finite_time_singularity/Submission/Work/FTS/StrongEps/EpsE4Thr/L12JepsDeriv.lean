/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Work.FTS.StrongEps.EpsE4Thr.L12JepsDeriv`

The fake-time derivative of the `L₁₂`-zero mode of the mollified family:

  `∂_τ L₁₂ (J_ε (slice g τ)) (0) = L₁₂ (J_ε (epsRHSP … g τ)) (0)`,

i.e. the `(j,i) = (0,0)` instance of the slot chain rule for the projected family
(`EpsE4Thr.hasDerivWithinAt_slice_JfamP` consumes it as its hypothesis `hL12`).

The proof is a *two-level* differentiation:

* **outer** (`r`-level): the target's `hintVal` (integrability of the value density), `hmeasDer`
  (a.e. strong measurability of the derivative density) and `hdom` (an `L¹`-majorant for it) are
  exactly the data of `hasDerivAt_integral_of_dominated_loc_of_deriv_le` for the integral
  `r ↦ L12dens K (J_ε (slice g ·)) r`;
* **inner** (`θ`-level, `L12JepsAux.hasDerivAt_L12dens_Jeps`): the derivative of the angular
  integral, whose pointwise-in-`θ` input is `Jeps_family_deriv` (the target's `hint` + `hbdU`).

The one genuinely non-elementary input is the **a.e. strong measurability in `θ`** of
`θ ↦ J_ε f r θ` for the value profile and for the right-hand-side profile.  It is *not* among the
hypotheses on their face (a Bochner integral of a merely `p`-integrable integrand need not be
measurable in `θ`); it is produced here from the all-`(r,θ)` integrability `hint`:

* `hint` (for all `θ ∈ (0,π/2)`) divides by the kernel on a ball where `Jker ρ ε > 0`, giving a.e.
  strong measurability of the slice `(z,θ) ↦ slice g s z θ` on the quadrant, transported to the log
  coordinates (`L12JepsAux.aesm_logPull_slice_of_hint`, via `aesm_of_integrable_mul_shift`);
* for the right-hand-side profile, strong measurability is inherited from the derivative
  `∂_s (logPull (slice g s))` (`L12JepsAux.aesm_logPull_epsRHSP`);
* finally `L12JepsAux.aesm_Jeps_slice_of_aesm_logPull` turns the log-coordinate measurability of a
  profile into the `θ`-measurability of its mollification.
-/
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.Jker_integral_eq_one
import Submission.Work.FTS.StrongEps.EpsE4Thr.hasDerivWithinAt_Jeps_slice_repair
import Submission.Work.FTS.StrongEps.EpsE4Thr.Repair.aestronglyMeasurable_Jker_mul_epsRHSP
import Submission.Work.FTS.StrongEps.EpsE4Thr.L12JepsAux.Basic
import Submission.Work.FTS.StrongEps.EpsE4Thr.L12JepsAux.Inner
import Submission.Work.FTS.StrongEps.EpsE4Thr.L12JepsAux.aesm_Jeps_slice_of_aesm_logPull
import Submission.Work.FTS.StrongEps.EpsE4Thr.L12JepsAux.aesm_logPull_epsRHSP

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

open MeasureTheory Set Filter
open scoped Topology
open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

theorem L12JepsDeriv {ρ : ℝ × ℝ → ℝ} {α T ε : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε)
    (hsol : Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g)
    (hint : ∀ r θ : ℝ, 0 < r → θ ∈ Set.Ioo 0 (Real.pi / 2) → ∀ s ∈ Set.Icc 0 T,
      MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p *
        (Work.FTS.Galerkin.slice g s) (Work.FTS.StrongEps.zShift r p.1)
          (Work.FTS.StrongEps.thShift θ p.2)) MeasureTheory.volume)
    (hbdU : ∀ r : ℝ, 0 < r → ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      ∀ p : ℝ × ℝ, ‖p‖ ≤ ε → ∀ s ∈ Set.Icc 0 T,
        |Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s (Work.FTS.StrongEps.zShift r p.1)
          (Work.FTS.StrongEps.thShift θ p.2)| ≤ C)
    (hsliceU : ∀ r : ℝ, 0 < r → ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      ∀ p : ℝ × ℝ, ‖p‖ ≤ ε → ∀ s ∈ Set.Icc 0 T,
        |Work.FTS.Galerkin.slice g s (Work.FTS.StrongEps.zShift r p.1)
          (Work.FTS.StrongEps.thShift θ p.2)| ≤ C)
    (hintVal : ∀ s ∈ Set.Icc 0 T, MeasureTheory.IntegrableOn
      (fun r : ℝ => Work.FM.L12dens Work.Spaces.K
        (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.Galerkin.slice g s)) r) (Set.Ioi 0))
    (hmeasDer : ∀ s ∈ Set.Icc 0 T, MeasureTheory.AEStronglyMeasurable
      (fun r : ℝ => Work.FM.L12dens Work.Spaces.K
        (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s)) r)
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hdom : ∃ G : ℝ → ℝ, MeasureTheory.IntegrableOn G (Set.Ioi 0) ∧
      ∀ r ∈ Set.Ioi 0, ∀ s ∈ Set.Icc 0 T,
        |Work.FM.L12dens Work.Spaces.K
          (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s)) r| ≤ G r)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo 0 T) :
    HasDerivWithinAt (fun s => Work.Construction.L12
        (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.Galerkin.slice g s)) 0)
      (Work.Construction.L12
        (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ)) 0)
      (Set.Icc 0 T) τ := by
  have hIoi : MeasurableSet (Set.Ioi (0 : ℝ)) := measurableSet_Ioi
  have hIcc : MeasurableSet (Set.Icc (0 : ℝ) (Real.pi / 2)) := measurableSet_Icc
  have hτm : τ ∈ Set.Icc (0 : ℝ) T := ⟨hτ.1.le, hτ.2.le⟩
  -- the log-coordinate strong measurability of the slices
  have hlogV : ∀ x ∈ Set.Icc 0 T, MeasureTheory.AEStronglyMeasurable
      (Work.FTS.StrongEps.logPull (slice g x)) MeasureTheory.volume :=
    L12JepsAux.aesm_logPull_slice_of_hint hρ.moll hε hint
  -- the inner (`θ`-level) derivative at every `r > 0` and every `x ∈ (0,T)`
  have hinner : ∀ r : ℝ, 0 < r → ∀ x ∈ Set.Ioo 0 T,
      HasDerivAt (fun y => Work.FM.L12dens Work.Spaces.K
          (Work.FTS.StrongEps.Jeps ρ ε (slice g y)) r)
        (Work.FM.L12dens Work.Spaces.K
          (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g x)) r) x := by
    intro r hr x hx
    have hxm : x ∈ Set.Icc (0 : ℝ) T := ⟨hx.1.le, hx.2.le⟩
    have hmk : Measurable (fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p) :=
      (Work.FTS.StrongEps.Jker_continuous hρ.moll ε).measurable
    -- strong measurability in `θ` of the value profile
    have hV : ∀ y ∈ Set.Ioo 0 T, MeasureTheory.AEStronglyMeasurable
        (fun θ : ℝ => Work.FTS.StrongEps.Jeps ρ ε (slice g y) r θ)
        (MeasureTheory.volume.restrict (Set.Icc 0 (Real.pi / 2))) := by
      intro y hy
      exact L12JepsAux.aesm_Jeps_slice_of_aesm_logPull hmk hr
        (hlogV y ⟨hy.1.le, hy.2.le⟩)
        (fun θ hθ => hint r θ hr hθ y ⟨hy.1.le, hy.2.le⟩)
    -- strong measurability in `θ` of the right-hand-side profile
    obtain ⟨Cd, hCd0, hCd⟩ := hbdU r hr
    have hD : MeasureTheory.AEStronglyMeasurable
        (fun θ : ℝ => Work.FTS.StrongEps.Jeps ρ ε
          (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g x) r θ)
        (MeasureTheory.volume.restrict (Set.Icc 0 (Real.pi / 2))) := by
      refine L12JepsAux.aesm_Jeps_slice_of_aesm_logPull hmk hr
        (L12JepsAux.aesm_logPull_epsRHSP hsol hlogV hx) ?_
      intro θ hθ
      exact L12JepsAux.integrable_Jker_mul_of_bound hρ.moll hε hCd0
        (fun θ' hθ' => Repair.aestronglyMeasurable_Jker_mul_epsRHSP hr hθ' hx hsol
          (fun s hs => hint r θ' hr hθ' s hs))
        (fun θ' hθ' p hp => hCd θ' hθ' p hp x hxm) θ hθ
    -- the sup bound for the value profile
    obtain ⟨Cv, hCv0, hCv⟩ := hsliceU r hr
    exact L12JepsAux.hasDerivAt_L12dens_Jeps hρ.moll hε hr hsol hx
      (fun θ hθ s hs => hint r θ hr hθ s hs) ⟨Cd, hCd0, hCd⟩
      ⟨Cv, hCv0, fun θ hθ p hp => hCv θ hθ p hp x hxm⟩ hV hD
  -- the outer (`r`-level) differentiation
  obtain ⟨G, hGint, hGbd⟩ := hdom
  have hs : Set.Ioo (0 : ℝ) T ∈ 𝓝 τ := isOpen_Ioo.mem_nhds hτ
  have hF_meas : ∀ᶠ x in 𝓝 τ, MeasureTheory.AEStronglyMeasurable
      (fun r : ℝ => Work.FM.L12dens Work.Spaces.K
        (Work.FTS.StrongEps.Jeps ρ ε (slice g x)) r)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    filter_upwards [hs] with x hx
    exact (hintVal x ⟨hx.1.le, hx.2.le⟩).aestronglyMeasurable
  have hF_int : MeasureTheory.Integrable
      (fun r : ℝ => Work.FM.L12dens Work.Spaces.K
        (Work.FTS.StrongEps.Jeps ρ ε (slice g τ)) r)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := hintVal τ hτm
  have hF'_meas : MeasureTheory.AEStronglyMeasurable
      (fun r : ℝ => Work.FM.L12dens Work.Spaces.K
        (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ)) r)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := hmeasDer τ hτm
  have h_bound : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ∀ x ∈ Set.Ioo (0 : ℝ) T,
        ‖Work.FM.L12dens Work.Spaces.K
          (Work.FTS.StrongEps.Jeps ρ ε
            (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g x)) r‖ ≤ G r := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict hIoi] with r hr x hx
    simpa only [Real.norm_eq_abs] using hGbd r hr x ⟨hx.1.le, hx.2.le⟩
  have h_diff : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ∀ x ∈ Set.Ioo (0 : ℝ) T,
        HasDerivAt (fun y => Work.FM.L12dens Work.Spaces.K
            (Work.FTS.StrongEps.Jeps ρ ε (slice g y)) r)
          (Work.FM.L12dens Work.Spaces.K
            (Work.FTS.StrongEps.Jeps ρ ε
              (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g x)) r) x := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict hIoi] with r hr
    exact hinner r hr
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := MeasureTheory.volume.restrict (Set.Ioi 0)) (𝕜 := ℝ) (E := ℝ)
    (F := fun x r => Work.FM.L12dens Work.Spaces.K
      (Work.FTS.StrongEps.Jeps ρ ε (slice g x)) r)
    (F' := fun x r => Work.FM.L12dens Work.Spaces.K
      (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g x)) r)
    (bound := G) (x₀ := τ) (s := Set.Ioo 0 T)
    hs hF_meas hF_int hF'_meas h_bound hGint h_diff
  simpa only [Work.Construction.L12, Work.FM.L12] using hmain.2.hasDerivWithinAt

end Work.FTS.StrongEps.EpsE4Thr
