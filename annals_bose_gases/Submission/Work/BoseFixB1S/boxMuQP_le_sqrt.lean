import ChallengeDeps
import Submission.Work.BoseFixB1S.boxPQBoundsFix
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.boxMuQP_le_sqrt`

The `PQ`-cross line of the box `μ`-weight: the pairing of the excited projection `Q_{B(u),i}` with
the mean-free box projection `P_{B(u),i}` in the slot-`i` fibre weight
`fib(z) = ∫_{acube ℓ} w_{1,B(u)}(z,y) dy` obeys Cauchy–Schwarz,

  `Σᵢ boxMuQP_i ≤ √(Σᵢ boxMuQ_i) · √(Σᵢ boxMuP_i)` .

This is the triangle inequality applied to the already machine-checked abstract bound
`Work.BoseFixB1S.pqCrossCS` (Cauchy–Schwarz on the box `abox N ℓ` in each slot, plus
Cauchy–Schwarz over the finite index set), at the localised fibre `fib`, whose two required
pointwise facts are the corpus's sharp-regime inputs:

* `0 ≤ fib` (`Work.BoseFixB1S.boxFibLine_fibre_nonneg`),
* `fib ≤ Kfib M = KfibConst M · a(v)` (`Work.BoseFixB1.q1cw1_w1Fibre_abs_le`),

together with the a.e. strong measurability of `fib` on `acube ℓ`
(`Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre`, using the integrability of `g₀`).
-/

namespace Work.BoseFixB1S

theorem boxMuQP_le_sqrt {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : Work.UBB.ScatSol v) {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∑ i : Fin N, Work.BoseFixB1S.boxMuQP (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
        (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ i)
      ≤ Real.sqrt (∑ i : Fin N, Work.BoseFixB1S.boxMuQ (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
            (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ i)
        * Real.sqrt (∑ i : Fin N, Work.BoseFixB1S.boxMuP (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
            (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ i) := by
  classical
  -- ## the localised fibre: sign, size and a.e. strong measurability
  have hfib0 : ∀ z : EuclideanSpace ℝ (Fin 3),
      0 ≤ Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z :=
    fun z => boxFibLine_fibre_nonneg hR0 hv hvrad hv_supp h u z
  have hfibK : ∀ z : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z
        ≤ Work.BoseFixB1.Kfib (v := v) M :=
    fun z => le_trans (le_abs_self _)
      (Work.BoseFixB1.q1cw1_w1Fibre_abs_le (v := v) (R0 := R0) hv_supp hR0 hv hvrad hv1 h hM
        hℓ hd hR hRχ u z)
  have hfibm : MeasureTheory.AEStronglyMeasurable
      (fun z : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
        (Submission.BoseGases.acube ℓ)) := by
    have hg0 : AEMeasurable (Submission.BoseGases.g0 v h)
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) :=
      (Submission.BoseGases.g0_integrable (R := R0) hR0 hv_supp h).aemeasurable
    have hh := Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre (ℓ := ℓ) (d := d) M u hg0
    simpa only [Submission.BoseGases.wSmall1Pair, Submission.BoseGases.w1Fibre] using hh
  -- ## the box data of the sliding box
  have hAmeas : MeasurableSet (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hvolA : Work.SmallBoxSliding.boxMass ℓ d u
      = (MeasureTheory.volume (Submission.BoseGases.dlBox ℓ d u)).toReal := by
    rw [Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
  have hAc : Submission.BoseGases.dlBox ℓ d u ⊆ Submission.BoseGases.acube ℓ :=
    Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  -- ## Cauchy–Schwarz
  have hCS := pqCrossCS (N := N) (ℓ := ℓ) (volA := Work.SmallBoxSliding.boxMass ℓ d u)
    (A := Submission.BoseGases.dlBox ℓ d u) hℓ hvol hAmeas hvolA hAc hΦc
    (ψ := Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u))
    hfib0 (K := Work.BoseFixB1.Kfib (v := v) M) hfibK hfibm
  simp only [boxMuQP, boxMuQ, boxMuP]
  exact (le_abs_self _).trans hCS

end Work.BoseFixB1S
