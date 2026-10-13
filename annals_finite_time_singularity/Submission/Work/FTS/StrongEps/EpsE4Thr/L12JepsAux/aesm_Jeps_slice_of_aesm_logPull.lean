/-
Work module for the Elgindi finite-time singularity project (StrongEps / EpsE4Thr / L12).

`aesm_Jeps_slice_of_aesm_logPull`: the `θ`-slice `θ ↦ Jeps ρ ε f r θ` of the log-coordinate
mollifier is a.e.-strongly-measurable on `[0, π/2]`, given only that the log-pull `logPull f` is
a.e.-strongly-measurable.

The point is that on the open quadrant

  `Jeps ρ ε f r θ = ∫ p, Jker ρ ε p * logPull f (sOf r - p.1, zetaOf θ - p.2)`,

i.e. the `θ`-dependence is the *affine* map `p ↦ (sOf r - p.1, zetaOf θ - p.2)` applied to the
argument of `logPull f`.  That affine map of `ℝ × ℝ` is a reflection of the additive group, so it
preserves Lebesgue measure (hence the ideal of null sets); replacing `logPull f` by a measurable
representative `G` therefore changes the integral for no `θ`
(`L12JepsAux.ae_eq_comp_sub`), and `ζ ↦ ∫ p, Jker ρ ε p * G (sOf r - p.1, ζ - p.2)` is measurable
because the Bochner integral of a jointly measurable integrand is measurable, with no integrability
hypothesis (`L12JepsAux.measurable_integral_sub_conv`).
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.EpsE4Thr.L12JepsAux.ae_eq_comp_sub
import Submission.Work.FTS.StrongEps.EpsE4Thr.L12JepsAux.measurable_integral_sub_conv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.L12JepsAux

theorem aesm_Jeps_slice_of_aesm_logPull {ρ : ℝ × ℝ → ℝ} {ε r : ℝ} {f : ℝ → ℝ → ℝ}
    (hmk : Measurable (fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p))
    (hr : 0 < r)
    (hG : MeasureTheory.AEStronglyMeasurable (Work.FTS.StrongEps.logPull f) MeasureTheory.volume)
    (hint : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p *
        f (Work.FTS.StrongEps.zShift r p.1) (Work.FTS.StrongEps.thShift θ p.2))
      MeasureTheory.volume) :
    MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => Work.FTS.StrongEps.Jeps ρ ε f r θ)
      (MeasureTheory.volume.restrict (Set.Icc 0 (Real.pi / 2))) := by
  -- a measurable representative of `logPull f`
  obtain ⟨G, hGm, hGae⟩ : ∃ G : ℝ × ℝ → ℝ, Measurable G ∧ logPull f =ᵐ[volume] G :=
    ⟨hG.mk (logPull f), hG.stronglyMeasurable_mk.measurable, hG.ae_eq_mk⟩
  -- the parametric integral against the measurable representative is measurable in `ζ`
  have hHm : Measurable (fun ζ : ℝ => ∫ p : ℝ × ℝ, Jker ρ ε p * G (sOf r - p.1, ζ - p.2)) :=
    measurable_integral_sub_conv hmk hGm (sOf r)
  -- on the open quadrant `Jeps` is the integral against the representative `G`
  have hkey : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Jeps ρ ε f r θ = ∫ p : ℝ × ℝ, Jker ρ ε p * G (sOf r - p.1, zetaOf θ - p.2) := by
    intro θ hθ
    rw [Jeps_eq_integral ρ ε f hr hθ]
    trans ∫ p : ℝ × ℝ, Jker ρ ε p * logPull f (sOf r - p.1, zetaOf θ - p.2)
    · refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      exact congrArg (fun t => Jker ρ ε p * t) (logPull_shift f hr hθ).symm
    · refine integral_congr_ae ?_
      filter_upwards [ae_eq_comp_sub hGae (sOf r) (zetaOf θ)] with p hp
      rw [hp]
  -- `zetaOf` is measurable
  have htan : Measurable fun x : ℝ => Real.tan x := by
    rw [show (fun x : ℝ => Real.tan x) = fun x => Real.sin x / Real.cos x from
      funext fun x => Real.tan_eq_sin_div_cos x]
    exact Real.measurable_sin.div Real.measurable_cos
  have hzeta : Measurable zetaOf := Real.measurable_log.comp htan
  -- conclude: the two functions agree a.e. on `[0, π/2]`
  refine (hHm.comp hzeta).aestronglyMeasurable.congr ?_
  show ∀ᵐ θ ∂(volume.restrict (Set.Icc 0 (Real.pi / 2))),
      (fun ζ : ℝ => ∫ p : ℝ × ℝ, Jker ρ ε p * G (sOf r - p.1, ζ - p.2)) (zetaOf θ)
        = (fun θ : ℝ => Jeps ρ ε f r θ) θ
  rw [ae_restrict_iff' measurableSet_Icc]
  have h0 : ∀ᵐ θ ∂volume, θ ≠ (0 : ℝ) := by rw [ae_iff]; simp
  have hpi : ∀ᵐ θ ∂volume, θ ≠ Real.pi / 2 := by rw [ae_iff]; simp
  filter_upwards [h0, hpi] with θ hθ0 hθpi hmem
  exact (hkey θ ⟨lt_of_le_of_ne hmem.1 (Ne.symm hθ0), lt_of_le_of_ne hmem.2 hθpi⟩).symm

end Work.FTS.StrongEps.EpsE4Thr.L12JepsAux
