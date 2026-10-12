import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.XSpow_aeStronglyMeasurable_ae_bounded
import Submission.Work.BoseBoxFock.modeProd_XS_pairing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.BoseBoxFock

/-- **The `j`-fold pairing of the mode product against the iterated sector count.**
For an a.e. strongly measurable, a.e. bounded function `g` on `Fin d → Ω`, the slot means expand
`Σ_i aPC_i M_α = (α 0)·M_α` on the box, so each application of `XS ℓ univ` (whose `j`-fold iterate
is `XSpow`) multiplies the pairing `∫ conj(M_α)·g` by the number `d − α 0` of slots not carrying
the condensate mode. Iterating the one-step box identity `Work.BoseBoxFock.modeProd_XS_pairing`
(whose `IntegrableOn g (abox d ℓ)` hypothesis is supplied by `hgmeas` + `hg` and the finite measure
of the box) gives the `j`-fold statement. The integrability of the intermediate iterates
`XSpow ℓ univ i g` follows from `hgmeas` + `hg`, because each slot mean
`aPC ℓ i Ψ x = ℓ⁻³ ∫_{acube ℓ} Ψ (x[i ↦ y]) dy` is bounded on the box by an a.e. bound of `Ψ`
(the hypothesis `hgmeas` is genuinely needed: an a.e. bound alone gives no `IntegrableOn`).
⚠ the file must NOT import `Submission.Work.BoseBoxFock.slotSum_sectorPointwise` (a `update_pairCoord` clash). -/
theorem XSpow_modeProd_pairing {m : ℕ} [NeZero m]
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (he : ∀ l l', (∫ x : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (e l x) * e l' x)
      = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hc : ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      (∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
        e 0 x = c * Work.BoseK15.corpusBox.thetaFun ℓ x))
    (d : ℕ) (α : Fin m →₀ ℕ) (j : ℕ) {g : (Fin d → EuclideanSpace ℝ (Fin 3)) → ℂ} {Cg : ℝ}
    (hgmeas : MeasureTheory.AEStronglyMeasurable g
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → EuclideanSpace ℝ (Fin 3))))
    (hg : ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure
      (Fin d → EuclideanSpace ℝ (Fin 3))), ‖g u‖ ≤ Cg) :
    (∫ u in Submission.BoseGases.abox d ℓ,
        (starRingEnd ℂ) (Work.BoseDict.modeProd e d α u)
          * Work.BoseBoxFock.XSpow ℓ (Finset.univ : Finset (Fin d)) j g u)
      = (((d - α 0 : ℕ) : ℂ)) ^ j
        * ∫ u in Submission.BoseGases.abox d ℓ,
            (starRingEnd ℂ) (Work.BoseDict.modeProd e d α u) * g u := by
  classical
  -- the box has finite measure, so a.e. boundedness plus a.e. strong measurability give
  -- integrability on it
  haveI : MeasureTheory.IsFiniteMeasure
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X d)).restrict
        (Submission.BoseGases.abox d ℓ)) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ]
        exact Submission.BoseGases.abox_lt_top d ℓ hℓ.le⟩
  -- every iterate `XSpow ℓ univ i g` is integrable on the box
  have hInt : ∀ i : ℕ, MeasureTheory.IntegrableOn
      (Work.BoseBoxFock.XSpow ℓ (Finset.univ : Finset (Fin d)) i g)
      (Submission.BoseGases.abox d ℓ) := by
    intro i
    obtain ⟨hmeas, C, hC⟩ := Work.BoseBoxFock.XSpow_aeStronglyMeasurable_ae_bounded ℓ hℓ
      (Finset.univ : Finset (Fin d)) hgmeas ⟨Cg, hg⟩ i
    exact MeasureTheory.Integrable.of_bound hmeas.restrict C
      (MeasureTheory.ae_mono MeasureTheory.Measure.restrict_le_self hC)
  have key : ∀ j : ℕ,
      (∫ u in Submission.BoseGases.abox d ℓ,
          (starRingEnd ℂ) (Work.BoseDict.modeProd e d α u)
            * Work.BoseBoxFock.XSpow ℓ (Finset.univ : Finset (Fin d)) j g u)
        = (((d - α 0 : ℕ) : ℂ)) ^ j
          * ∫ u in Submission.BoseGases.abox d ℓ,
              (starRingEnd ℂ) (Work.BoseDict.modeProd e d α u) * g u := by
    intro j
    induction j with
    | zero =>
        rw [show Work.BoseBoxFock.XSpow ℓ (Finset.univ : Finset (Fin d)) 0 g = g from rfl,
          pow_zero, one_mul]
    | succ j ih =>
        have hstep := Work.BoseBoxFock.modeProd_XS_pairing ℓ hℓ he hbdd hsupp hc α
          (Work.BoseBoxFock.XSpow ℓ (Finset.univ : Finset (Fin d)) j g) (hInt j)
        rw [show Work.BoseBoxFock.XSpow ℓ (Finset.univ : Finset (Fin d)) (j + 1) g
              = Work.BoseBoxFock.XS ℓ (Finset.univ : Finset (Fin d))
                  (Work.BoseBoxFock.XSpow ℓ (Finset.univ : Finset (Fin d)) j g) from rfl,
          hstep, ih, pow_succ]
        ring
  exact key j

end Work.BoseBoxFock
