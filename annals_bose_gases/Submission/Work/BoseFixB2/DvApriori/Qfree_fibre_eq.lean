import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.DvApriori.BandDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Qfree_fibre_eq` — the mean-free box projection commutes with taking a fibre

For an `n`-body state `Ψ` and a slot `j : Fin n`, the slot-`j` fibre of the `j`-th
complement projection `aQ ℓ j Ψ` is the mean-free projection `Qfree ℓ 0` of the
slot-`j` fibre of `Ψ`:

    `Q_{Λ}((j ↦ Ψ(x_{j←·}))) = (j ↦ (Q_jΨ)(x_{j←·}))`   (`Λ` anchored, `u = 0`).

Reason: `aQ ℓ j Ψ y = Ψ y − aP ℓ j Ψ y` with `aP ℓ j Ψ y = 1/ℓ³ ∫_{acube ℓ} Ψ(y_{j←y'}) dy'`,
while `bsMean ℓ 0 ψ = (ℓ³)⁻¹ ∫_{acube ℓ} ψ(ℓ·0 + y') dy' = (ℓ³)⁻¹ ∫_{acube ℓ} ψ y' dy'`.
The two inner integrals agree because `(x_{j←z})_{j←y'} = x_{j←y'}`, and `1/ℓ³ = (ℓ³)⁻¹`.
The positivity of `ℓ` is not needed for this identity (the scalar factor is
definitionally the same inverse, and no `ℓ = 0` case is reached); it is part of the
interface's parameter regime.

This is the anchored (`u = 0`) version of `Work.BoseFixB3.HighMass.fibre_aQ_eq_bsQ`,
stated with the localisation-module names `Qfree`/`fibre` used by the `DvApriori` layer.
-/

namespace Work.BoseFixB2.DvApriori

open Submission.BoseGases

theorem Qfree_fibre_eq {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n) {Ψ : Submission.BoseGases.X n → ℝ}
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (x : Submission.BoseGases.X n) :
    Work.BoseKinLoc.Qfree ℓ 0 (Work.BoseKinLoc.fibre n j Ψ x)
      = Work.BoseKinLoc.fibre n j (Submission.BoseGases.aQ ℓ j Ψ) x := by
  funext z
  simp only [Work.BoseKinLoc.Qfree, Work.BoseKinLoc.fibre, Work.BSKinetic.bsQ,
    Work.BSKinetic.bsMean, Submission.BoseGases.aQ, Submission.BoseGases.aP,
    Function.update_idem, smul_zero, zero_add, one_div]

end Work.BoseFixB2.DvApriori
