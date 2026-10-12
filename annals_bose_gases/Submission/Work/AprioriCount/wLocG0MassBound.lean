import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.AprioriCount.chemMassLeChiMass
import Submission.Work.AprioriCount.conv3_pos_of_norm_lt
import Submission.Work.AprioriCount.fibMass_le_chiCount
import Submission.Work.AprioriCount.flatLeChi
import Submission.Work.BoseBox.aprioriCoreWindowBook
import Submission.Work.BoseBox.aprioriWindows
import Submission.Work.BoseFixB1.WB.kb_window
import Submission.Work.BoseFixB1B.PerBoxSectorResidual
import Submission.Work.BoseFixB1B.bornGap
import Submission.Work.BoseFixB1B.integrableOn_oneBody_wPair
import Submission.Work.BoseFixB1B.integrableOn_pair_wPair
import Submission.Work.BoseFixB1B.pairPartB_boxConstant
import Submission.Work.BoseFixB1B.slotKIntegrable
import Submission.Work.BoseFixB1B.slotKIntegral
import Submission.Work.BoseFixB1B.wLocOffCubeZero
import Submission.Work.BoseFixB1S.windowOfCrudePairBound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AprioriCount

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators

/-- The uniform fibre bound `|∫_y wLoc ℓ (g₀) 0 x y| ≤ K` and the resulting one-body mass
bound `∫ Φ² Σᵢ ∫_y wLoc ≤ K·n·∫Φ²`, both in the kernel regime `R ≤ ℓ·chiR0`.

Route (all inputs proved): `wLoc ℓ (g0 v h) 0 x y = wPair ℓ (g0 v h) x y` pointwise
(`simp [wLoc, wPair, chiU, chiScale]`), then `Submission.BoseGases.fibre_integral_abs_le`
(`|∫_y wPair ℓ hh x y| ≤ chiSup²·2·∫|hh|`, needing `0 < ℓ`, `0 ≤ R`, `R ≤ ℓ·chiR0`,
`Integrable hh`, `∀z, R ≤ ‖z‖ → hh z = 0`) with `hh := g0 v h` (`g0_integrable`,
`g0_zero_of_norm_ge`), giving the first conjunct with `K := chiSup²·2·∫|g0 v h| + 1 > 0`.
For the second conjunct: pointwise `Σᵢ ∫_y wLoc ≤ n·K`, multiply by `Φ² ≥ 0`, then either
`MeasureTheory.integral_mono` with the integrability of `x ↦ Φ x ^ 2 * (n * K)` on the compact
`abox n ℓ` (`ContinuousOn.integrableOn_compact`, `abox_compact`), or a `by_cases` on
`IntegrableOn` plus `MeasureTheory.integral_undef` in the non-integrable case. -/
theorem wLocG0MassBound {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) :
    ∃ K : ℝ, 0 < K ∧
      (∀ (ℓ : ℝ) (x : EuclideanSpace ℝ (Fin 3)), 0 < ℓ →
        R ≤ ℓ * Submission.BoseGases.chiR0 →
        |∫ y : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 x y| ≤ K) ∧
      (∀ (n : ℕ) (ℓ : ℝ) (Φ : Submission.BoseGases.X n → ℝ), 0 < ℓ →
        R ≤ ℓ * Submission.BoseGases.chiR0 → Continuous Φ →
        (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
            (∑ i : Fin n, ∫ y : EuclideanSpace ℝ (Fin 3),
              Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y))
          ≤ K * (n : ℝ) * ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)
:= by
  have hg0int : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR hv_supp h
  have hg0supp : ∀ z : EuclideanSpace ℝ (Fin 3), R ≤ ‖z‖ → Submission.BoseGases.g0 v h z = 0 :=
    fun z hz => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h
  -- the uniform fibre constant
  set K : ℝ := Submission.BoseGases.chiSup ^ 2 * 2
      * (∫ z : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.g0 v h z|) + 1 with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]
    have h1 : 0 ≤ Submission.BoseGases.chiSup ^ 2 * 2
        * (∫ z : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.g0 v h z|) :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (by norm_num))
        (integral_nonneg fun z => abs_nonneg (Submission.BoseGases.g0 v h z))
    linarith
  -- ## the uniform fibre bound, in the regime `R ≤ ℓ·chiR0`
  have hfiball : ∀ (ℓ : ℝ) (x : EuclideanSpace ℝ (Fin 3)), 0 < ℓ →
      R ≤ ℓ * Submission.BoseGases.chiR0 →
      |∫ y : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 x y| ≤ K := by
    intro ℓ x hℓ hRℓ
    have hwlp : ∀ y : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 x y
          = Submission.BoseGases.wPair ℓ (Submission.BoseGases.g0 v h) x y := fun y => by
      simp [Submission.BoseGases.wLoc, Submission.BoseGases.wPair, Submission.BoseGases.chiU,
        Submission.BoseGases.chiScale]
    rw [show (∫ y : EuclideanSpace ℝ (Fin 3),
            Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 x y)
          = ∫ y : EuclideanSpace ℝ (Fin 3),
            Submission.BoseGases.wPair ℓ (Submission.BoseGases.g0 v h) x y from
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hwlp)]
    have hb := Submission.BoseGases.fibre_integral_abs_le hℓ (le_of_lt hR) hRℓ hg0int hg0supp x
    rw [hKdef]
    linarith
  refine ⟨K, hKpos, hfiball, ?_⟩
  -- ## the one-body mass bound
  intro n ℓ Φ hℓ hRℓ hΦc
  by_cases hint : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
      (∑ i : Fin n, ∫ y : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y))
      (Submission.BoseGases.abox n ℓ)
  · have hmaj : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
        (Φ x) ^ 2 * ((n : ℝ) * K)) (Submission.BoseGases.abox n ℓ) :=
      ContinuousOn.integrableOn_compact (Submission.BoseGases.abox_compact n hℓ)
        ((hΦc.pow 2).mul_const ((n : ℝ) * K)).continuousOn
    have hmono := MeasureTheory.integral_mono hint hmaj (fun x => by
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      calc (∑ i : Fin n, ∫ y : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.wLoc ℓ
              (Submission.BoseGases.g0 v h) 0 (x i) y)
          ≤ ∑ _i : Fin n, K :=
            Finset.sum_le_sum fun i _ => le_trans (le_abs_self _) (hfiball ℓ (x i) hℓ hRℓ)
        _ = (n : ℝ) * K := by simp [Finset.sum_const, nsmul_eq_mul])
    calc (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
            (∑ i : Fin n, ∫ y : EuclideanSpace ℝ (Fin 3),
              Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y))
        ≤ ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 * ((n : ℝ) * K) := hmono
      _ = ((n : ℝ) * K) * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) := by
            rw [← MeasureTheory.integral_const_mul]
            exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
      _ = K * (n : ℝ) * ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 := by ring
  · rw [MeasureTheory.integral_undef hint]
    refine mul_nonneg (mul_nonneg hKpos.le (Nat.cast_nonneg n)) ?_
    exact integral_nonneg fun x => sq_nonneg _

end Work.AprioriCount
