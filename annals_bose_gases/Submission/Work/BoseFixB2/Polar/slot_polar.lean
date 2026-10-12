import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB2.Polar

/-- **The slot-`i` polarisation identity** for the localised kinetic word: the
slot-`i` `indU`-weighted box integral of the polarised word `fsTbil` is the polarisation of the
slot-`i` box integrals.

Since `fsTbil` is *defined* as the polarisation `(fsT(f+g) − fsT(f−g))/4`, the content is:

* the slot fibre is additive in the state — `fibre n i (Φ+Ψ) x` is the pointwise sum of
  `fibre n i Φ x` and `fibre n i Ψ x`, and likewise for the difference (this is `rfl`, `fibre`
  being evaluation at `Function.update x i ·`);
* the two slot integrands of the sum and the difference are integrable on the box
  (`Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth`, applied to the smooth states `Φ ± Ψ`),
  so the box integral is additive;
* the constant `4` may be pulled out of the integral. -/
theorem slot_polar {n : ℕ} {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) (i : Fin n) {Φ Ψ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) : ((∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x i) * Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre n i (fun y => Φ y + Ψ y) x)) - (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x i) * Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre n i (fun y => Φ y - Ψ y) x))) / 4 = ∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x i) * Work.BoseFixB2.fsTbil ℓ d s εT b 0 (Work.BoseKinLoc.fibre n i Φ x) (Work.BoseKinLoc.fibre n i Ψ x) := by
  -- the slot fibre is additive / subtractive in the state
  have hFibAdd : ∀ x : Submission.BoseGases.X n,
      Work.BoseKinLoc.fibre n i (fun y => Φ y + Ψ y) x
        = fun z => Work.BoseKinLoc.fibre n i Φ x z + Work.BoseKinLoc.fibre n i Ψ x z :=
    fun x => by funext z; rfl
  have hFibSub : ∀ x : Submission.BoseGases.X n,
      Work.BoseKinLoc.fibre n i (fun y => Φ y - Ψ y) x
        = fun z => Work.BoseKinLoc.fibre n i Φ x z - Work.BoseKinLoc.fibre n i Ψ x z :=
    fun x => by funext z; rfl
  -- the two slot integrands are integrable on the box
  have hInt1 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      Work.BoseKinLoc.indU ℓ 0 (x i) * Work.BoseKinLoc.fsT ℓ d s εT b 0
        (Work.BoseKinLoc.fibre n i (fun y => Φ y + Ψ y) x)) (Submission.BoseGases.abox n ℓ) :=
    Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth (d := d) (s := s) (εT := εT) (b := b)
      hℓ i (hΦ.add hΨ)
  have hInt2 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      Work.BoseKinLoc.indU ℓ 0 (x i) * Work.BoseKinLoc.fsT ℓ d s εT b 0
        (Work.BoseKinLoc.fibre n i (fun y => Φ y - Ψ y) x)) (Submission.BoseGases.abox n ℓ) :=
    Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth (d := d) (s := s) (εT := εT) (b := b)
      hℓ i (hΦ.sub hΨ)
  -- pull the difference and the constant out of the box integral
  have key : (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x i) * Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre n i (fun y => Φ y + Ψ y) x))
      - (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x i) * Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre n i (fun y => Φ y - Ψ y) x))
      = 4 * (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x i) * Work.BoseFixB2.fsTbil ℓ d s εT b 0 (Work.BoseKinLoc.fibre n i Φ x) (Work.BoseKinLoc.fibre n i Ψ x)) := by
    rw [← MeasureTheory.integral_sub hInt1 hInt2]
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable n ℓ)
    intro x _
    simp only []
    rw [hFibAdd x, hFibSub x]
    unfold Work.BoseFixB2.fsTbil
    ring
  rw [key]
  ring

end Work.BoseFixB2.Polar
