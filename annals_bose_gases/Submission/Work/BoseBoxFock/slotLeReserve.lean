import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.bf3a_kin
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.slotLeReserve` — the slot-`i` reserve inequality

Per slot `i` and per configuration `x`, the smoothed `τ̃`-one-body word is dominated by the
`eq:T'u` kinetic row of `fsT` (`bf3a_fibre`), while the Neumann word is nonnegative
(`neuWord_nonneg_of_continuous`).  Since `fsT = neuWord + gapWord + momWord + mainWord`, the
*windowed* `τ̃`-slot integral is therefore dominated by the `fsT`-slot integral, with the gap and
momentum rows *unhalved* (they appear on both sides and cancel): that is precisely the statement
below.

The proof is the fibre-wise `integral_mono_of_nonneg` with the dominating integrand
`1_Λ(x_i)·(fsT − gapWord − momWord)`, exactly as in `bf3a_kin`'s per-slot step but without the
`½`-reserve on the gap and momentum rows.
-/

namespace Work.BoseBoxFock

open scoped Real Topology BigOperators
open MeasureTheory Metric Filter
open _root_.BoseGases Submission.BoseGases
open Work.BoseKinLoc Work.BSKinetic

set_option maxHeartbeats 2000000

theorem slotLeReserve {ℓ d s eT b : ℝ} (hℓ : 0 < ℓ) (hs : 0 < s) (hd : 0 < d)
    (heT0 : 0 ≤ eT) (heT1 : eT ≤ 1) (hb : 0 ≤ b)
    {n : ℕ} (i : Fin n) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x i)
          * Work.BSKinetic.bsOneBody ℓ (Work.BoseBoxFock.tauSmRad eT s d ℓ) 0
              (Work.BoseKinLoc.fibre n i Φ x))
      + (∫ x in Submission.BoseGases.abox n ℓ,
          Work.BoseKinLoc.indU ℓ 0 (x i)
            * Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.fibre n i Φ x))
      + (∫ x in Submission.BoseGases.abox n ℓ,
          Work.BoseKinLoc.indU ℓ 0 (x i)
            * Work.BoseKinLoc.momWord ℓ d eT b 0 (Work.BoseKinLoc.fibre n i Φ x))
    ≤ ∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x i)
          * Work.BoseKinLoc.fsT ℓ d s eT b 0 (Work.BoseKinLoc.fibre n i Φ x) := by
  have hfib : ∀ x : Submission.BoseGases.X n, ContDiff ℝ (⊤ : ℕ∞) (fibre n i Φ x) :=
    fun x => hΦ.comp (contDiff_update (⊤ : ℕ∞) x i)
  obtain ⟨hIgap, hImom, hImain, hIneu⟩ :=
    Work.BoseFixB2.DvApriori.KinOffdiag.pieces_integrableOn_fibre (ℓ := ℓ) (d := d) (s := s)
      (εT := eT) (b := b) hℓ i hΦ
  have hIfs :=
    Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth (ℓ := ℓ) (d := d) (s := s)
      (εT := eT) (b := b) hℓ i hΦ
  -- integrability of the dominating "difference" integrand
  have hDint : Integrable (fun x : Submission.BoseGases.X n =>
      indU ℓ 0 (x i) * (fsT ℓ d s eT b 0 (fibre n i Φ x) - gapWord ℓ b 0 (fibre n i Φ x)
        - momWord ℓ d eT b 0 (fibre n i Φ x))) (volume.restrict (abox n ℓ)) := by
    refine ((hIfs.sub hIgap).sub hImom).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  -- the `τ̃`-row is dominated by the difference integrand
  have hmono : (∫ x in abox n ℓ,
        indU ℓ 0 (x i) * bsOneBody ℓ (tauSmRad eT s d ℓ) 0 (fibre n i Φ x))
      ≤ ∫ x in abox n ℓ, indU ℓ 0 (x i) *
          (fsT ℓ d s eT b 0 (fibre n i Φ x) - gapWord ℓ b 0 (fibre n i Φ x)
            - momWord ℓ d eT b 0 (fibre n i Φ x)) := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ hDint ?_
    · filter_upwards with x
      simp only [Pi.zero_apply]
      exact mul_nonneg (Word.kinFormB_indU_nonneg ℓ 0 (x i))
        (bsOneBody_nonneg (fun r => tauSmRad_nonneg heT0 heT1 r) 0 (fibre n i Φ x))
    · filter_upwards with x
      have hnd : 0 ≤ indU ℓ 0 (x i) := Word.kinFormB_indU_nonneg ℓ 0 (x i)
      have hK := bf3a_fibre hℓ hs hd heT0 heT1 (fibre n i Φ x) (hfib x)
      have hneu := neuWord_nonneg_of_continuous hℓ hd heT0 (hfib x).continuous
      have hcore' : bsOneBody ℓ (tauSmRad eT s d ℓ) 0 (fibre n i Φ x)
          ≤ fsT ℓ d s eT b 0 (fibre n i Φ x) - gapWord ℓ b 0 (fibre n i Φ x)
            - momWord ℓ d eT b 0 (fibre n i Φ x) := by
        rw [fsT_eq_sum]
        linarith
      exact mul_le_mul_of_nonneg_left hcore' hnd
  -- the difference integral linearises
  have hsub1 : (∫ x in abox n ℓ,
        (indU ℓ 0 (x i) * fsT ℓ d s eT b 0 (fibre n i Φ x)
          - indU ℓ 0 (x i) * gapWord ℓ b 0 (fibre n i Φ x)))
      = (∫ x in abox n ℓ, indU ℓ 0 (x i) * fsT ℓ d s eT b 0 (fibre n i Φ x))
        - (∫ x in abox n ℓ, indU ℓ 0 (x i) * gapWord ℓ b 0 (fibre n i Φ x)) :=
    MeasureTheory.integral_sub hIfs hIgap
  have hsub2 : (∫ x in abox n ℓ,
        (indU ℓ 0 (x i) * fsT ℓ d s eT b 0 (fibre n i Φ x)
          - indU ℓ 0 (x i) * gapWord ℓ b 0 (fibre n i Φ x)
          - indU ℓ 0 (x i) * momWord ℓ d eT b 0 (fibre n i Φ x)))
      = (∫ x in abox n ℓ,
          (indU ℓ 0 (x i) * fsT ℓ d s eT b 0 (fibre n i Φ x)
            - indU ℓ 0 (x i) * gapWord ℓ b 0 (fibre n i Φ x)))
        - (∫ x in abox n ℓ, indU ℓ 0 (x i) * momWord ℓ d eT b 0 (fibre n i Φ x)) :=
    MeasureTheory.integral_sub (hIfs.sub hIgap) hImom
  have hcongr : (∫ x in abox n ℓ, indU ℓ 0 (x i) *
        (fsT ℓ d s eT b 0 (fibre n i Φ x) - gapWord ℓ b 0 (fibre n i Φ x)
          - momWord ℓ d eT b 0 (fibre n i Φ x)))
      = ∫ x in abox n ℓ,
          (indU ℓ 0 (x i) * fsT ℓ d s eT b 0 (fibre n i Φ x)
            - indU ℓ 0 (x i) * gapWord ℓ b 0 (fibre n i Φ x)
            - indU ℓ 0 (x i) * momWord ℓ d eT b 0 (fibre n i Φ x)) :=
    MeasureTheory.integral_congr_ae (Eventually.of_forall fun x => by ring)
  have hlin : (∫ x in abox n ℓ, indU ℓ 0 (x i) *
        (fsT ℓ d s eT b 0 (fibre n i Φ x) - gapWord ℓ b 0 (fibre n i Φ x)
          - momWord ℓ d eT b 0 (fibre n i Φ x)))
      = (∫ x in abox n ℓ, indU ℓ 0 (x i) * fsT ℓ d s eT b 0 (fibre n i Φ x))
        - (∫ x in abox n ℓ, indU ℓ 0 (x i) * gapWord ℓ b 0 (fibre n i Φ x))
        - (∫ x in abox n ℓ, indU ℓ 0 (x i) * momWord ℓ d eT b 0 (fibre n i Φ x)) :=
    hcongr.trans (hsub2.trans (congrArg₂ (· - ·) hsub1 rfl))
  linarith [hmono, hlin]

end Work.BoseBoxFock
