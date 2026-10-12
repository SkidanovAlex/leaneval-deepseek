import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Compare.neuFrac_fibre_aemeasurable_v2
import Submission.Work.BoseKinLoc.Kinetic.gapBare_fibre_aemeasurable
import Submission.Work.BoseKinLoc.Kinetic.mainWord_fibre_aemeasurable
import Submission.Work.BoseKinLoc.Kinetic.momForm_fibre_aemeasurable
import Submission.Work.BoseKinLoc.Kinetic.neuFrac_zero_a2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBox.fsT_fibre_aemeasurable`

**The localised kinetic word `fsT` (FS `eq:DefT`) is a.e. strongly measurable along the
slot-`i` fibre of a smooth, compactly supported `(n+1)`-body state** — with **no support
condition** on `Ψ` beyond compact support.

This is the `HasCompactSupport` variant of
`Work.BoseKinLoc.Kinetic.aestronglyMeasurable_fsT_genFibre` (which assumes the stronger
`tsupport Φ ⊆ abox (n+1) L`).  The statement is

`q ↦ fsT ℓ d s εT b q.1 ψ_q`,   `ψ_q(z) = Ψ (kcInsN n i (z, q.2))`,

a.e. strongly measurable on the product of the Lebesgue measure on the box position
`u = q.1` and the volume measure on the remaining configuration `q.2`.

## Proof

`fsT = neuWord + gapWord + momWord + mainWord` (`Work.BoseKinLoc.fsT_eq_sum`); the four
pieces are handled separately and assembled with `AEStronglyMeasurable.add`.

* `gapWord` — `gapBare_fibre_aemeasurable` times the constant `b ℓ⁻²`.
* `momWord` — `momForm_fibre_aemeasurable` times the constant `b εT (dℓ)⁻²`.
* `mainWord` — `mainWord_fibre_aemeasurable`.
* `neuWord` — `neuWord ℓ d εT u ψ = ½εT(dℓ)⁻² · neuFrac ℓ (dℓ)⁻² u (Q_uψ)`.  `neuFrac` is an
  `sInf` of variational trial values, not an integral, so measurability is obtained by a case
  split on the coefficient `a² = (dℓ)⁻²`:

  * `a² = 0` (`d = 0`): `neuFrac ℓ 0 u φ = ∫_{Λ(u)} φ²` (`neuFrac_zero_a2`), and at `φ = Q_uψ_q`
    this is exactly `gapBare ℓ u ψ_q`, so `gapBare_fibre_aemeasurable` applies.
  * `a² > 0`: the box mean may be removed from the fibre,
    `neuFrac ℓ a² u (Q_uψ_q) = neuFrac ℓ a² u ψ_q` (`neuFrac_add_const_of_integrableOn_sq`,
    which needs only measurability and square-integrability of the fibre on the box — supplied
    by continuity of the slice `z ↦ Ψ (kcInsN n i (z, q.2))`, integrability on the compact
    `lamBox ℓ q.1`).  Measurability of `q ↦ neuFrac ℓ a² q.1 ψ_q` for a *compactly supported*
    smooth `Ψ` is `Work.BoseKinLoc.Compare.neuFrac_fibre_aemeasurable_v2` (continuity of
    `neuFrac` in `(u, q₂)`, via the Lipschitz estimate in the state and the continuity of the
    squared fibre difference).
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBox

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-- The product measure on `(box position, remaining configuration)`. -/
private abbrev fsTVol (n : ℕ) :
    MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) :=
  (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
    (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n))

/-- The insertion `z ↦ kcInsN n i (z, r)` of a single coordinate is continuous. -/
private lemma kcInsN_slice_continuous {n : ℕ} (i : Fin (n + 1)) (r : Submission.BoseGases.X n) :
    Continuous (fun z : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.kcInsN n i (z, r)) := by
  have h1 : (fun z : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.kcInsN n i (z, r))
      = Function.update (Submission.BoseGases.kcInsN n i (0, r)) i := by
    funext z
    exact Submission.BoseGases.kcInsN_update_zero i z r
  rw [h1]
  have hupd : ContDiff ℝ (⊤ : ℕ∞)
      (Function.update (Submission.BoseGases.kcInsN n i (0, r)) i) :=
    contDiff_update (⊤ : ℕ∞) (Submission.BoseGases.kcInsN n i (0, r)) i
  exact hupd.continuous

/-- The slot-`i` fibre `z ↦ Ψ (kcInsN n i (z, r))` is continuous. -/
private lemma fibre_continuous {n : ℕ} {Ψ : Submission.BoseGases.X (n + 1) → ℝ}
    (hΨ : Continuous Ψ) (i : Fin (n + 1)) (r : Submission.BoseGases.X n) :
    Continuous (fun z : EuclideanSpace ℝ (Fin 3) => Ψ (Submission.BoseGases.kcInsN n i (z, r))) := by
  exact Continuous.comp (g := Ψ) hΨ (kcInsN_slice_continuous i r)

/-- The square of the slot-`i` fibre is integrable on the moving box `Λ(u)` (the box is compact
and the fibre is continuous). -/
private lemma fibre_sq_integrableOn {n : ℕ} {ℓ : ℝ} {Ψ : Submission.BoseGases.X (n + 1) → ℝ}
    (hΨ : Continuous Ψ) (i : Fin (n + 1)) (r : Submission.BoseGases.X n)
    (u : EuclideanSpace ℝ (Fin 3)) :
    IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) =>
      (Ψ (Submission.BoseGases.kcInsN n i (z, r))) ^ 2) (Work.BoseKinLoc.lamBox ℓ u) := by
  exact ContinuousOn.integrableOn_compact (Work.BoseKinLoc.NeuFrac.lamBox_isCompact ℓ u)
    ((fibre_continuous hΨ i r).pow 2).continuousOn

theorem fsT_fibre_aemeasurable {ℓ d s eT b : ℝ} (hℓ : 0 < ℓ) {n : ℕ}
    {Ψ : Submission.BoseGases.X (n + 1) → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hcs : HasCompactSupport Ψ) (i : Fin (n + 1)) :
    MeasureTheory.AEStronglyMeasurable
      (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        Work.BoseKinLoc.fsT ℓ d s eT b q.1
          (fun z : EuclideanSpace ℝ (Fin 3) => Ψ (Submission.BoseGases.kcInsN n i (z, q.2))))
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n))) := by
  have hcont : Continuous Ψ := hΨ.continuous
  -- the coefficient `a² = (dℓ)⁻²` of the Neumann word is nonnegative (a reciprocal square)
  have ha2nn : (0 : ℝ) ≤ (d * ℓ) ^ (-2 : ℤ) := by
    rw [zpow_neg]
    exact inv_nonneg.mpr (by positivity)
  -- ## the Neumann word
  have hbase : MeasureTheory.AEStronglyMeasurable
      (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) q.1
          (Work.BoseKinLoc.Qfree ℓ q.1
            (fun z : EuclideanSpace ℝ (Fin 3) => Ψ (Submission.BoseGases.kcInsN n i (z, q.2)))))
      (fsTVol n) := by
    by_cases hz : (d * ℓ) ^ (-2 : ℤ) = 0
    · -- `a² = 0`: `neuFrac` collapses onto the mean-free box mass
      have hfun : (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
          Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) q.1
            (Work.BoseKinLoc.Qfree ℓ q.1
              (fun z : EuclideanSpace ℝ (Fin 3) => Ψ (Submission.BoseGases.kcInsN n i (z, q.2)))))
          = (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
              Work.BoseKinLoc.gapBare ℓ q.1
                (fun z : EuclideanSpace ℝ (Fin 3) => Ψ (Submission.BoseGases.kcInsN n i (z, q.2)))) := by
        funext q
        rw [hz, Work.BoseKinLoc.Kinetic.neuFrac_zero_a2]
        rfl
      rw [hfun]
      exact Work.BoseKinLoc.Kinetic.gapBare_fibre_aemeasurable hΨ i
    · -- `a² > 0`: strip the box mean, then use continuity of `neuFrac` in `(u, q₂)`
      have hpos : 0 < (d * ℓ) ^ (-2 : ℤ) := lt_of_le_of_ne ha2nn (Ne.symm hz)
      have hcongr : (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
          Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) q.1
            (Work.BoseKinLoc.Qfree ℓ q.1
              (fun z : EuclideanSpace ℝ (Fin 3) => Ψ (Submission.BoseGases.kcInsN n i (z, q.2)))))
          = (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
              Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) q.1
                (fun z : EuclideanSpace ℝ (Fin 3) => Ψ (Submission.BoseGases.kcInsN n i (z, q.2)))) := by
        funext q
        have hshift : Work.BoseKinLoc.Qfree ℓ q.1
              (fun z : EuclideanSpace ℝ (Fin 3) => Ψ (Submission.BoseGases.kcInsN n i (z, q.2)))
            = fun z : EuclideanSpace ℝ (Fin 3) =>
                Ψ (Submission.BoseGases.kcInsN n i (z, q.2))
                  + (-(Work.BoseKinLoc.meanU ℓ q.1
                      (fun z : EuclideanSpace ℝ (Fin 3) =>
                        Ψ (Submission.BoseGases.kcInsN n i (z, q.2))))) := by
          funext z
          simp only [Work.BoseKinLoc.Qfree, Work.BSKinetic.bsQ, Work.BoseKinLoc.meanU,
            sub_eq_add_neg]
        rw [hshift]
        exact Work.BoseKinLoc.NeuFrac.neuFrac_add_const_of_integrableOn_sq hpos q.1
          (fun z : EuclideanSpace ℝ (Fin 3) => Ψ (Submission.BoseGases.kcInsN n i (z, q.2)))
          (-(Work.BoseKinLoc.meanU ℓ q.1
              (fun z : EuclideanSpace ℝ (Fin 3) =>
                Ψ (Submission.BoseGases.kcInsN n i (z, q.2)))))
          (fibre_continuous hcont i q.2).measurable (fibre_sq_integrableOn hcont i q.2 q.1)
      rw [hcongr]
      exact Work.BoseKinLoc.Compare.neuFrac_fibre_aemeasurable_v2 (ℓ := ℓ)
        (a2 := (d * ℓ) ^ (-2 : ℤ)) hℓ hpos hΨ hcs i
  have hneu : MeasureTheory.AEStronglyMeasurable
      (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        Work.BoseKinLoc.neuWord ℓ d eT q.1
          (fun z : EuclideanSpace ℝ (Fin 3) => Ψ (Submission.BoseGases.kcInsN n i (z, q.2))))
      (fsTVol n) := by
    exact hbase.const_mul ((1 / 2) * eT * (d * ℓ) ^ (-2 : ℤ))
  -- ## the mean-free mass word
  have hgap : MeasureTheory.AEStronglyMeasurable
      (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        Work.BoseKinLoc.gapWord ℓ b q.1
          (fun z : EuclideanSpace ℝ (Fin 3) => Ψ (Submission.BoseGases.kcInsN n i (z, q.2))))
      (fsTVol n) := by
    exact (Work.BoseKinLoc.Kinetic.gapBare_fibre_aemeasurable hΨ i).const_mul (b * ℓ ^ (-2 : ℤ))
  -- ## the large-momentum word
  have hmom : MeasureTheory.AEStronglyMeasurable
      (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        Work.BoseKinLoc.momWord ℓ d eT b q.1
          (fun z : EuclideanSpace ℝ (Fin 3) => Ψ (Submission.BoseGases.kcInsN n i (z, q.2))))
      (fsTVol n) := by
    exact (Work.BoseKinLoc.Kinetic.momForm_fibre_aemeasurable hΨ i).const_mul
      (b * eT * (d * ℓ) ^ (-2 : ℤ))
  -- ## the windowed kinetic word
  have hmain : MeasureTheory.AEStronglyMeasurable
      (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        Work.BoseKinLoc.mainWord ℓ d s eT q.1
          (fun z : EuclideanSpace ℝ (Fin 3) => Ψ (Submission.BoseGases.kcInsN n i (z, q.2))))
      (fsTVol n) := by
    exact Work.BoseKinLoc.Kinetic.mainWord_fibre_aemeasurable hΨ i
  -- ## assembly
  have hsum : MeasureTheory.AEStronglyMeasurable
      (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        Work.BoseKinLoc.neuWord ℓ d eT q.1
            (fun z : EuclideanSpace ℝ (Fin 3) => Ψ (Submission.BoseGases.kcInsN n i (z, q.2)))
          + Work.BoseKinLoc.gapWord ℓ b q.1
            (fun z : EuclideanSpace ℝ (Fin 3) => Ψ (Submission.BoseGases.kcInsN n i (z, q.2)))
          + Work.BoseKinLoc.momWord ℓ d eT b q.1
            (fun z : EuclideanSpace ℝ (Fin 3) => Ψ (Submission.BoseGases.kcInsN n i (z, q.2)))
          + Work.BoseKinLoc.mainWord ℓ d s eT q.1
            (fun z : EuclideanSpace ℝ (Fin 3) => Ψ (Submission.BoseGases.kcInsN n i (z, q.2))))
      (fsTVol n) := by
    exact ((hneu.add hgap).add hmom).add hmain
  have hfs : (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        Work.BoseKinLoc.fsT ℓ d s eT b q.1
          (fun z : EuclideanSpace ℝ (Fin 3) => Ψ (Submission.BoseGases.kcInsN n i (z, q.2))))
      = (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        Work.BoseKinLoc.neuWord ℓ d eT q.1
            (fun z : EuclideanSpace ℝ (Fin 3) => Ψ (Submission.BoseGases.kcInsN n i (z, q.2)))
          + Work.BoseKinLoc.gapWord ℓ b q.1
            (fun z : EuclideanSpace ℝ (Fin 3) => Ψ (Submission.BoseGases.kcInsN n i (z, q.2)))
          + Work.BoseKinLoc.momWord ℓ d eT b q.1
            (fun z : EuclideanSpace ℝ (Fin 3) => Ψ (Submission.BoseGases.kcInsN n i (z, q.2)))
          + Work.BoseKinLoc.mainWord ℓ d s eT q.1
            (fun z : EuclideanSpace ℝ (Fin 3) => Ψ (Submission.BoseGases.kcInsN n i (z, q.2)))) := by
    funext q
    rfl
  rw [hfs]
  exact hsum

end Work.BoseBox
