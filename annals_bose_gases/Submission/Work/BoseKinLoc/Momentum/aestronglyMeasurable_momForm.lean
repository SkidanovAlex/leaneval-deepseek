import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseKinLoc.Momentum.junkMomForm
import Submission.Work.BoseKinLoc.Momentum.maxAESMsupport
import Submission.Work.BoseKinLoc.Momentum.measurableBoxMeasure
import Submission.Work.BoseKinLoc.Momentum.momFormCongrAE
import Submission.Work.BoseKinLoc.Momentum.momFormIntegrandMeasurable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Momentum.aestronglyMeasurable_momForm`

Measurability in the moving-box parameter `u` of the large-momentum form
`momForm ℓ d u ψ = (2π)⁻³ ∫_p 1_{(d²ℓ)⁻¹<‖p‖}(p)·‖𝓕(1_{Λ(u)}·Q_uψ)(p)‖²`
(FS `eq:DefT`'s third kinetic piece, on the moving box `Λ(u) = ℓu + acube ℓ`), for an
**arbitrary** (not necessarily measurable) function `ψ : ℝ³ → ℝ`.

## Strategy

Mathlib's Bochner integral is `0` on functions that are not a.e. strongly measurable
(`MeasureTheory.integral_undef`), so the whole expression only "sees" the a.e. strongly measurable
part of `ψ`.  Concretely:

* `maxAESMsupport` provides a maximal (mod null) measurable set `M` on which `ψ` restricts to an
  a.e. strongly measurable function; write `G := 1_M · (a strongly measurable representative of
  1_M ψ)`.
* `aestronglyMeasurable_indicator_iff_sdiff_eq_zero` turns this into the criterion: for a
  measurable `S`, `1_S ψ` is a.e. strongly measurable iff `volume (S \ M) = 0`.
* On the (measurable, by `measurableBoxMeasure`) set `Au = {u | volume (Λ(u) \ M) = 0}` we have
  `ψ =ᵐ G` on the box `Λ(u)`, so `momForm` agrees there with the `G`-form
  (`momFormCongrAE`); off `Au` the integrand `1_{Λ(u)}ψ` is *not* a.e. strongly measurable and
  everything collapses to `0` (`junkMomForm`).
* Hence `u ↦ momForm ℓ d u ψ` is the pointwise product of the measurable indicator of `Au` with
  `u ↦ momForm ℓ d u G`, and the latter is a.e. strongly measurable because the `(u,p)`-integrand is
  strongly measurable (`momFormIntegrandMeasurable`) and integration in `p` preserves this
  (`MeasureTheory.StronglyMeasurable.integral_prod_right'`).
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Work.BoseKinLoc.Momentum

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Criterion for the maximal support.**  If `M` is a maximal (mod null) measurable set on which
`ψ` restricts to an a.e. strongly measurable function, then for a measurable set `S` the function
`1_S ψ` is a.e. strongly measurable exactly when `S ⊆ M` up to a null set. -/
theorem aestronglyMeasurable_indicator_iff_sdiff_eq_zero {ψ : E3 → ℝ} {M : Set E3}
    (hMaesm : AEStronglyMeasurable (M.indicator ψ) volume)
    (hMmax : ∀ N : Set E3, MeasurableSet N → AEStronglyMeasurable (N.indicator ψ) volume →
      (volume : Measure E3) (N \ M) = 0)
    {S : Set E3} (hS : MeasurableSet S) :
    AEStronglyMeasurable (S.indicator ψ) volume ↔ (volume : Measure E3) (S \ M) = 0 := by
  refine ⟨fun h => hMmax S hS h, fun h0 => ?_⟩
  have hnull : ∀ᵐ x ∂(volume : Measure E3), x ∉ S \ M :=
    (MeasureTheory.measure_eq_zero_iff_ae_notMem).mp h0
  have heq : S.indicator (M.indicator ψ) =ᵐ[volume] S.indicator ψ := by
    filter_upwards [hnull] with x hx
    by_cases hxS : x ∈ S
    · by_cases hxM : x ∈ M
      · rw [Set.indicator_of_mem hxS, Set.indicator_of_mem hxS, Set.indicator_of_mem hxM]
      · rw [Set.indicator_of_mem hxS, Set.indicator_of_mem hxS, Set.indicator_of_notMem hxM]
        exact absurd ⟨hxS, hxM⟩ hx
    · rw [Set.indicator_of_notMem hxS, Set.indicator_of_notMem hxS]
  exact (hMaesm.indicator hS).congr heq

theorem aestronglyMeasurable_momForm (ℓ d : ℝ) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) : MeasureTheory.AEStronglyMeasurable (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.momForm ℓ d u ψ) MeasureTheory.volume := by
  classical
  -- a maximal measurable set on which `ψ` restricts to an a.e. strongly measurable function
  obtain ⟨M, hM, hMaesm, hMmax⟩ := maxAESMsupport (μ := (volume : Measure E3)) inferInstance ψ
  -- its strongly measurable representative, made to vanish off `M`
  set G : E3 → ℝ := M.indicator (hMaesm.mk (M.indicator ψ)) with hGdef
  have hGmeas : Measurable G := hMaesm.measurable_mk.indicator hM
  have hcrit : ∀ S : Set E3, MeasurableSet S →
      (AEStronglyMeasurable (S.indicator ψ) volume ↔ (volume : Measure E3) (S \ M) = 0) :=
    fun S hS => aestronglyMeasurable_indicator_iff_sdiff_eq_zero hMaesm hMmax hS
  -- on `M`, `G` agrees with `ψ` a.e.
  have hkey : ∀ᵐ x ∂(volume : Measure E3), x ∈ M → G x = ψ x := by
    filter_upwards [hMaesm.ae_eq_mk] with x hx hxM
    have h1 : G x = hMaesm.mk (M.indicator ψ) x := by
      rw [hGdef, Set.indicator_of_mem hxM]
    rw [h1, ← hx, Set.indicator_of_mem hxM]
  have hbox_meas : ∀ u : E3, MeasurableSet (Work.BSKinetic.bsBox ℓ u) := fun u =>
    (Submission.BoseGases.acube_measurable ℓ).preimage (by fun_prop)
  -- the parameter set on which the box is a.e. contained in `M`
  set Au : Set E3 := {u : E3 | (volume : Measure E3) (Work.BSKinetic.bsBox ℓ u \ M) = 0} with hAudef
  have hAumeas : MeasurableSet Au :=
    (measurableBoxMeasure ℓ hM) (measurableSet_singleton 0)
  -- the `G`-form of `momForm` is a.e. strongly measurable in `u`
  have hGAESM : AEStronglyMeasurable (fun u : E3 => Work.BoseKinLoc.momForm ℓ d u G) volume := by
    have hS : StronglyMeasurable (fun u : E3 => ∫ p : E3, Work.BoseKinLoc.momProj ℓ d p *
        ‖Submission.BoseGases.kinFT (fun z : E3 =>
          ((Work.BoseKinLoc.indU ℓ u z : ℝ) : ℂ) * ((Work.BoseKinLoc.Qfree ℓ u G z : ℝ) : ℂ)) p‖ ^ 2) :=
      (momFormIntegrandMeasurable ℓ d hGmeas).integral_prod_right' (ν := (volume : Measure E3))
    have hfun : (fun u : E3 => Work.BoseKinLoc.momForm ℓ d u G) = fun u : E3 =>
        ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, Work.BoseKinLoc.momProj ℓ d p *
          ‖Submission.BoseGases.kinFT (fun z : E3 =>
            ((Work.BoseKinLoc.indU ℓ u z : ℝ) : ℂ) * ((Work.BoseKinLoc.Qfree ℓ u G z : ℝ) : ℂ)) p‖ ^ 2 :=
      rfl
    rw [hfun]
    exact (hS.const_mul _).aestronglyMeasurable
  -- pointwise reduction to the `G`-form
  have hpoint : ∀ u : E3, Work.BoseKinLoc.momForm ℓ d u ψ =
      Au.indicator (fun _ => (1 : ℝ)) u * Work.BoseKinLoc.momForm ℓ d u G := by
    intro u
    by_cases hu : u ∈ Au
    · -- the box is a.e. contained in `M`: `ψ` and `G` agree a.e. on the box
      rw [Set.indicator_of_mem hu, one_mul]
      refine momFormCongrAE ℓ d ?_
      filter_upwards [hkey,
        (MeasureTheory.measure_eq_zero_iff_ae_notMem).mp
          (show (volume : Measure E3) (Work.BSKinetic.bsBox ℓ u \ M) = 0 from hu)] with x hx hxne hxbox
      exact (hx (by by_contra hxM; exact hxne ⟨hxbox, hxM⟩)).symm
    · -- the box is not a.e. contained in `M`: everything collapses to `0`
      rw [Set.indicator_of_notMem hu, zero_mul]
      have hne : (volume : Measure E3) (Work.BSKinetic.bsBox ℓ u \ M) ≠ 0 := hu
      have hnot : ¬ AEStronglyMeasurable ((Work.BSKinetic.bsBox ℓ u).indicator ψ) volume :=
        fun h => hne ((hcrit (Work.BSKinetic.bsBox ℓ u) (hbox_meas u)).mp h)
      obtain ⟨-, hkin0⟩ := junkMomForm ℓ hnot
      rw [Work.BoseKinLoc.momForm]
      have hzero : (fun p : E3 => Work.BoseKinLoc.momProj ℓ d p *
          ‖Submission.BoseGases.kinFT (fun z : E3 =>
            ((Work.BoseKinLoc.indU ℓ u z : ℝ) : ℂ) * ((Work.BoseKinLoc.Qfree ℓ u ψ z : ℝ) : ℂ)) p‖ ^ 2)
          = fun _ => 0 := by
        funext p
        rw [hkin0 p]
        simp
      rw [hzero, integral_zero, mul_zero]
  rw [show (fun u : E3 => Work.BoseKinLoc.momForm ℓ d u ψ) =
      fun u : E3 => Au.indicator (fun _ => (1 : ℝ)) u * Work.BoseKinLoc.momForm ℓ d u G from
    funext hpoint]
  exact (StronglyMeasurable.indicator (stronglyMeasurable_const (b := (1 : ℝ))) hAumeas).aestronglyMeasurable.mul
    hGAESM

end Work.BoseKinLoc.Momentum
