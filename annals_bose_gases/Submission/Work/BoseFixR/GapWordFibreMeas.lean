import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseKinLoc.Sector.aemeasurable_gapWord_zero_fibre
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.GapWordFibreMeas`

The FS `eq:DefT` gap word `gapWord ℓ b 0 ψ` evaluated on the slot-`i` fibre
`Kinetic.genFibre i Φ r : z ↦ Φ (kcInsN i (z,r))` of a merely **continuous** `(m+1)`-particle
state `Φ` is a.e. measurable in the configuration variable `r : X m`.

This is the continuity-only strengthening of
`Work.BoseKinLoc.Sector.aemeasurable_gapWord_zero_fibre`, whose proof actually only ever uses
continuity of `Φ` (the `ContDiff`/support hypotheses of that statement are unused, as its own
documentation points out).  We reproduce the argument with the hypothesis weakened:

* `(r,z) ↦ Φ (kcInsN i (z,r))` is continuous, hence strongly measurable
  (`Kinetic.continuous_kcInsN_pair` composed with `Φ`);
* integrating in `z` against `volume.restrict (acube ℓ)` (`StronglyMeasurable.integral_prod_right'`)
  makes the box mean `r ↦ m₀(genFibre i Φ r)` strongly measurable;
* the squared mean-free integrand is strongly measurable, and one more
  `integral_prod_right'` yields the strong measurability of `r ↦ gapBare ℓ 0 (genFibre i Φ r)`;
* `gapWord ℓ b 0 ψ = bℓ⁻² · gapBare ℓ 0 ψ` is a constant multiple;
* strong measurability implies a.e. measurability.

No positivity of `ℓ` and no support hypothesis is needed: the fibre family is defined for every
`Φ`, and the anchored box `Λ(0) = acube ℓ = bsBox ℓ 0` makes sense for every `ℓ : ℝ`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixR

open Submission.BoseGases

set_option linter.unusedVariables false

/-- **Strong measurability of the anchored mean-free box mass along the fibre family**, for a
merely continuous state.

For a continuous `(n+1)`-particle state `Φ` and a slot `i`, the map
`r ↦ gapBare ℓ 0 (Kinetic.genFibre i Φ r)` is strongly measurable.  Since strong measurability is
measure-free this is stronger than the a.e. statement needed below (and it is exactly what the
"slice at `u = 0`" of a joint statement cannot provide). -/
theorem stronglyMeasurable_gapBare_genFibre_zero_of_continuous {ℓ : ℝ} {n : ℕ}
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : Continuous Φ) (i : Fin (n + 1)) :
    StronglyMeasurable (fun r : Submission.BoseGases.X n =>
      Work.BoseKinLoc.gapBare ℓ 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r)) := by
  -- the fibre `(r,z) ↦ Φ (kcInsN n i (z,r))` is continuous
  have hJ1 : StronglyMeasurable (fun p : Submission.BoseGases.X n × ℝ³ =>
      Φ (Submission.BoseGases.kcInsN n i (p.2, p.1))) :=
    (hΦ.comp ((Work.BoseKinLoc.Kinetic.continuous_kcInsN_pair i).comp
      (continuous_snd.prodMk continuous_fst))).stronglyMeasurable
  -- the anchored box mean, written on the fixed cube `acube ℓ`
  have hH : StronglyMeasurable (fun p : Submission.BoseGases.X n × ℝ³ =>
      (Φ (Submission.BoseGases.kcInsN n i (p.2, p.1))
        - (ℓ ^ 3)⁻¹ * (∫ z in Submission.BoseGases.acube ℓ,
            Φ (Submission.BoseGases.kcInsN n i (z, p.1)))) ^ 2) := by
    have hM : StronglyMeasurable (fun r : Submission.BoseGases.X n =>
        (ℓ ^ 3)⁻¹ * ∫ z in Submission.BoseGases.acube ℓ,
          Φ (Submission.BoseGases.kcInsN n i (z, r))) := by
      have h : StronglyMeasurable (fun r : Submission.BoseGases.X n =>
          ∫ z, Φ (Submission.BoseGases.kcInsN n i (z, r))
            ∂(MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ))) :=
        hJ1.integral_prod_right'
      exact h.const_mul ((ℓ ^ 3)⁻¹)
    exact (hJ1.sub (hM.comp_measurable measurable_fst)).pow 2
  -- integrate the squared mean-free integrand over the fixed cube
  have hInt : StronglyMeasurable (fun r : Submission.BoseGases.X n =>
      ∫ z in Submission.BoseGases.acube ℓ,
        (Φ (Submission.BoseGases.kcInsN n i (z, r))
          - (ℓ ^ 3)⁻¹ * (∫ z in Submission.BoseGases.acube ℓ,
              Φ (Submission.BoseGases.kcInsN n i (z, r)))) ^ 2) :=
    hH.integral_prod_right'
  -- identify the two functions
  have hpoint : (fun r : Submission.BoseGases.X n =>
        Work.BoseKinLoc.gapBare ℓ 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r))
      = fun r : Submission.BoseGases.X n =>
      ∫ z in Submission.BoseGases.acube ℓ,
        (Φ (Submission.BoseGases.kcInsN n i (z, r))
          - (ℓ ^ 3)⁻¹ * (∫ z in Submission.BoseGases.acube ℓ,
              Φ (Submission.BoseGases.kcInsN n i (z, r)))) ^ 2 := by
    funext r
    have h1 : Work.BoseKinLoc.gapBare ℓ 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r)
        = ∫ z in Work.BoseKinLoc.lamBox ℓ 0,
            (Work.BSKinetic.bsQ ℓ 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r) z) ^ 2 := rfl
    rw [h1]
    have h2 : Work.BoseKinLoc.lamBox ℓ (0 : ℝ³) = Submission.BoseGases.acube ℓ := by
      ext x
      simp [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox]
    rw [h2]
    simp only [Work.BSKinetic.bsQ, Work.BSKinetic.bsMean, Work.BoseKinLoc.Kinetic.genFibre,
      smul_zero, zero_add]
  rw [hpoint]
  exact hInt

theorem GapWordFibreMeas {m : ℕ} {ℓ b : ℝ}
    {Φ : Submission.BoseGases.X (m + 1) → ℝ} (hΦ : Continuous Φ) (i : Fin (m + 1)) :
    AEMeasurable (fun r : Submission.BoseGases.X m =>
      Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r))
      MeasureTheory.volume := by
  have hbare := stronglyMeasurable_gapBare_genFibre_zero_of_continuous (ℓ := ℓ) (Φ := Φ) hΦ i
  have hword : StronglyMeasurable (fun r : Submission.BoseGases.X m =>
      Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r)) := by
    have heq : (fun r : Submission.BoseGases.X m =>
          Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r))
        = fun r : Submission.BoseGases.X m =>
          (b * ℓ ^ (-2 : ℤ)) * Work.BoseKinLoc.gapBare ℓ 0
            (Work.BoseKinLoc.Kinetic.genFibre i Φ r) := by
      funext r
      rfl
    rw [heq]
    exact hbare.const_mul _
  exact hword.aemeasurable

end Work.BoseFixR
