import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseKinLoc.Kinetic.fibre_lift_general
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Sector.aemeasurable_gapWord_zero_fibre`

FS `eq:DefT`'s second kinetic piece, the large-box Neumann gap `gapWord ℓ b u ψ`, evaluated on
the *fibre* `Kinetic.genFibre i Ψ r : z ↦ Ψ (kcInsN i (z,r))` of a smooth, box-supported
`(n+1)`-particle state, at the *anchored* box `u = 0`, is a.e. strongly measurable in the
configuration variable `r : X n`.

## Route

`Work.BoseKinLoc.Kinetic.gapBare_fibre_aemeasurable` gives the *joint* (in `(u,r)`)
a.e. strong measurability of `(u,r) ↦ gapBare ℓ u (Φ ∘ kcInsN i (·,r))`; that is not enough
here, because the requested statement lives on the slice `u = 0`, which is a `volume`-null
subset of `ℝ³` — an a.e. statement on the product gives no information on a null slice.
We therefore prove the **strong** (not a.e.) measurability of the fibre at the anchored box
directly:

  `gapBare ℓ 0 ψ = ∫_{Λ(0)} (ψ − m₀(ψ))² = ∫_{acube ℓ} (ψ − m₀(ψ))²` (`Λ(0) = acube ℓ`),

with the box mean `m₀(ψ) = (ℓ³)⁻¹ ∫_{acube ℓ} ψ` (`bsMean` is *defined* on the fixed cube).
Both ingredients are handled on the fixed cube `acube ℓ`, so no moving-box bookkeeping is
needed:

* `(r,z) ↦ Ψ (kcInsN i (z,r))` is continuous, hence strongly measurable
  (`Kinetic.continuous_kcInsN_pair` composed with `Ψ`);
* integrating it in `z` against `volume.restrict (acube ℓ)`
  (`StronglyMeasurable.integral_prod_right'`) gives the strong measurability of the box mean
  `r ↦ m₀(genFibre i Ψ r)`;
* the squared mean-free integrand `(r,z) ↦ (Ψ (kcInsN i (z,r)) − m₀(genFibre i Ψ r))²` is
  strongly measurable, and one more `integral_prod_right'` produces the mass
  `r ↦ gapBare ℓ 0 (genFibre i Ψ r)`;
* finally `gapWord ℓ b 0 ψ = bℓ⁻² · gapBare ℓ 0 ψ` is a constant multiple.

None of the hypotheses `hℓ`, `hL`, `hsupp` is needed: the fibre family is defined for every
`Ψ`, and the anchored box is `acube ℓ` whether or not `ℓ > 0`.  (They are part of the
interface requested by the consumer and are kept verbatim.)
-/

noncomputable section

open MeasureTheory

namespace Work.BoseKinLoc.Sector

open Submission.BoseGases

set_option linter.unusedVariables false

/-- **Strong measurability of the anchored mean-free box mass along the fibre family.**

For a smooth `(n+1)`-particle state `Φ` and a slot `i`, the map
`r ↦ gapBare ℓ 0 (Kinetic.genFibre i Φ r)` is strongly measurable.  Since strong measurability
is measure-free, this is stronger than the a.e. statement needed below (and it is exactly what
the "slice at `u = 0`" of the joint statement cannot provide). -/
theorem stronglyMeasurable_gapBare_genFibre_zero {ℓ : ℝ} {n : ℕ}
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (i : Fin (n + 1)) :
    StronglyMeasurable (fun r : Submission.BoseGases.X n =>
      Work.BoseKinLoc.gapBare ℓ 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r)) := by
  -- the fibre `(r,z) ↦ Φ (kcInsN n i (z,r))` is continuous
  have hJ1 : StronglyMeasurable (fun p : Submission.BoseGases.X n × ℝ³ =>
      Φ (Submission.BoseGases.kcInsN n i (p.2, p.1))) :=
    (hΦ.continuous.comp ((Work.BoseKinLoc.Kinetic.continuous_kcInsN_pair i).comp
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

theorem aemeasurable_gapWord_zero_fibre {ℓ b L : ℝ} (hℓ : 0 < ℓ) (hL : 0 ≤ L)
    {n : ℕ} {Ψ : Submission.BoseGases.X (n + 1) → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ)
    (hsupp : tsupport Ψ ⊆ Submission.BoseGases.abox (n + 1) L) (i : Fin (n + 1)) :
    MeasureTheory.AEStronglyMeasurable
      (fun r : Submission.BoseGases.X n =>
        Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ r))
      MeasureTheory.volume := by
  have h := stronglyMeasurable_gapBare_genFibre_zero (ℓ := ℓ) (Φ := Ψ) hΨ i
  have hword : StronglyMeasurable (fun r : Submission.BoseGases.X n =>
      Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ r)) := by
    have heq : (fun r : Submission.BoseGases.X n =>
          Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ r))
        = fun r : Submission.BoseGases.X n =>
          (b * ℓ ^ (-2 : ℤ)) * Work.BoseKinLoc.gapBare ℓ 0
            (Work.BoseKinLoc.Kinetic.genFibre i Ψ r) := by
      funext r
      rfl
    rw [heq]
    exact h.const_mul _
  exact hword.aestronglyMeasurable

end Work.BoseKinLoc.Sector
