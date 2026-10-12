import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.DvApriori.MomBilDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.DvApriori.boxState_fibre_eq`

The complexified anchored box state `boxState ℓ 0` of the slot-`j` fibre of a joint
sector projection is the indicator of the box times that fibre, with **no** box mean
subtracted:

`boxState ℓ 0 (fibre_j (E_S Φ) x) = fun z ↦ 1_{Λ}(z) · fibre_j (E_S Φ) x z`   (`j ∈ S`).

Reason: `boxState ℓ 0 ψ = 1_{Λ} · Q_{Λ}ψ` with `Q_{Λ}` the anchored mean-free projection
`Qfree ℓ 0 = bsQ ℓ 0`, and

* the anchored mean-free projection of a slot-`j` fibre is the fibre of the slot-`j`
  complement projection `aQ ℓ j` (`Qfree ℓ 0 (fibre_j Ψ x) = fibre_j (aQ ℓ j Ψ) x`);
* for `(j : ℕ) ∈ S` the joint sector projection `E_S = jointProj ℓ S Φ` is annihilated by
  the slot-`j` mean `aP ℓ j` (`Sector.jointProj_aP_eq_zero`), hence fixed by
  `aQ ℓ j = 1 − aP ℓ j`.

So the mean-free projection acts as the identity on the fibre, which is exactly the
statement: the `momBil`/`momForm` integrands built from `boxState ℓ 0` on a sector fibre
may be read as built from the *raw* fibre (the only slot-dependence entering is the
indicator `1_{Λ}(z)`).

Both auxiliary steps are proved here (under local names) so that this module stays a
leaf of the import graph.
-/

noncomputable section

namespace Work.BoseFixB2.DvApriori

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The anchored mean-free projection commutes with taking a fibre**:
`Qfree ℓ 0 (fibre_j Ψ x) = fibre_j (aQ ℓ j Ψ) x`.

Both sides are `Ψ(x_{j←z}) − |Λ|⁻¹∫_{Λ}Ψ(x_{j←z'}) dz'`, the first because
`bsMean ℓ 0 ψ = (ℓ³)⁻¹∫_{acube ℓ}ψ` and the second because
`aP ℓ j Ψ y = (1/ℓ³)∫_{acube ℓ}Ψ(y_{j←z'}) dz'`. -/
lemma boxState_Qfree_fibre {ℓ : ℝ} {n : ℕ} (j : Fin n) {Ψ : Submission.BoseGases.X n → ℝ}
    (x : Submission.BoseGases.X n) :
    Work.BoseKinLoc.Qfree ℓ 0 (Work.BoseKinLoc.fibre n j Ψ x)
      = Work.BoseKinLoc.fibre n j (Submission.BoseGases.aQ ℓ j Ψ) x := by
  funext z
  simp only [Work.BoseKinLoc.Qfree, Work.BoseKinLoc.fibre, Work.BSKinetic.bsQ,
    Work.BSKinetic.bsMean, Submission.BoseGases.aQ, Submission.BoseGases.aP,
    Function.update_idem, smul_zero, zero_add, one_div]

/-- **The complement projection `Q_m` fixes a joint sector containing the slot `m`**:
`aQ ℓ m (E_S Ψ) = E_S Ψ` for `(m : ℕ) ∈ S`, `m < n`.  Indeed `aP ℓ m (E_S Ψ) = 0`
(`Sector.jointProj_aP_eq_zero`), so `Q_m = 1 − P_m` acts as the identity. -/
lemma boxState_aQ_jointProj_eq_self {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {S : Finset ℕ} {m : ℕ}
    (hmS : m ∈ S) (hmn : m < n) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    Submission.BoseGases.aQ ℓ ⟨m, hmn⟩ (Work.BoseFixB2.jointProj ℓ S Φ)
      = Work.BoseFixB2.jointProj ℓ S Φ := by
  have h := Work.BoseFixB2.Sector.jointProj_aP_eq_zero (ℓ := ℓ) hℓ hmS hmn hΦ
  funext x
  simp only [Submission.BoseGases.aQ, h, Pi.zero_apply, sub_zero]

theorem boxState_fibre_eq {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n)
    {S : Finset ℕ} (hjS : (j : ℕ) ∈ S) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (x : Submission.BoseGases.X n) :
    Work.BoseKinLoc.Kinetic.boxState ℓ 0
        (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ) x)
      = fun z => ((Work.BoseKinLoc.indU ℓ 0 z : ℝ) : ℂ) *
          ((Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ) x z : ℝ) : ℂ) := by
  have hQ : Work.BoseKinLoc.Qfree ℓ 0
        (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ) x)
      = Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ) x := by
    rw [boxState_Qfree_fibre j x,
      boxState_aQ_jointProj_eq_self hℓ hjS j.isLt hΦ]
  funext z
  simp only [Work.BoseKinLoc.Kinetic.boxState, hQ]

end Work.BoseFixB2.DvApriori
