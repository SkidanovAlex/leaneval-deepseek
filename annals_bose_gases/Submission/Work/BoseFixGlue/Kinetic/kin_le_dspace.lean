import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Kinetic.fibre_lift
import Submission.Work.BoseKinLoc.Kinetic.fibre_lift_general
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixGlue.Kinetic.kin_le_dspace`

The `N`-body kinetic localisation bound at a **general** state box `abox N L` (`L ≥ 0`),
with the localisation scale `ℓ` of the kinetic word `kinForm N ℓ d s εT b` unrelated to `L`:
the `u`-average of the localised kinetic word is dominated by the total kinetic energy

    `∫_u kinForm N ℓ d s εT b u Φ ≤ Σ_i ∫_x Σ_k (∂_{i,k} Φ)²`.

This is exactly the general-box-radius lifting of FS `lem:LocKinEn`; it is proved in
`Work.BoseKinLoc.Kinetic.fibre_lift_general` (whose support hypothesis is `abox N L` for
`0 ≤ L`, rather than the `abox N ℓ` of the earlier `Kinetic/fibre_lift.lean`).  We restate it
here at the interface used by the comparison-glue layer and forward to the general form.
-/

namespace Work.BoseFixGlue.Kinetic

theorem kin_le_dspace {c₀ : ℝ} (hKin : Work.BoseKinLoc.KineticLocalisation c₀) {N : ℕ}
    {ℓ L d s εT b : ℝ} (hreg : Work.BoseKinLoc.KinRegime c₀ ℓ d s εT b) (hL : 0 ≤ L)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox N L)
    (hint : MeasureTheory.Integrable
      (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.kinForm N ℓ d s εT b u Φ)) :
    (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.kinForm N ℓ d s εT b u Φ)
      ≤ ∑ i : Fin N, ∫ x : Submission.BoseGases.X N, ∑ k : Fin 3,
          (fderiv ℝ Φ x (Submission.BoseGases.kcDir N i k)) ^ 2 :=
  Work.BoseKinLoc.Kinetic.fibre_lift_general hKin hreg hL hΦ hsupp hint

end Work.BoseFixGlue.Kinetic
