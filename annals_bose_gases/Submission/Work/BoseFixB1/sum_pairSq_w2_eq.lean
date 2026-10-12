import ChallengeDeps
import Submission.Work.BoseFixB1.boxQ0SlackIntegrable
import Submission.Work.BoseFixB1S.BoxQIndCore
import Submission.Work.BoseFixB1S.boxPairValue
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

theorem sum_pairSq_w2_eq {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3))
    (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∑ p ∈ Submission.BoseGases.pairSet N,
        ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) p.1
              (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) p.2 Φ) x) ^ 2
            * (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)
                (x p.1) (x p.2)))
      = (Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h))
          / (Work.SmallBoxSliding.boxMass ℓ d u) ^ 2)
        * Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
            (Submission.BoseGases.dlBox ℓ d u) Φ := by
  -- The numerator `g₂ = v(1−w₀)(1+w₀)` is integrable and vanishes outside `ball 0 R₀`.
  have hfint : MeasureTheory.Integrable (Submission.BoseGases.g2 v h) :=
    Submission.BoseGases.g2_integrable (R := R0) hR0 hv hvrad hv_supp h
  have hfsupp : ∀ z : EuclideanSpace ℝ (Fin 3), R0 ≤ ‖z‖ → Submission.BoseGases.g2 v h z = 0 :=
    fun z hz => Submission.BoseGases.g2_zero_of_norm_ge hv_supp hz h
  -- Integrability of the localised pair kernel over the small box `B(u) × B(u)`, obtained from
  -- the big-box statement `integrableOn_wSmallPair_cube` by restriction (`B(u) ⊆ acube ℓ`).
  have hcube : MeasureTheory.IntegrableOn
      (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) q.1 q.2)
      (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ) :=
    Work.BoseFixB1.integrableOn_wSmallPair_cube (f := Submission.BoseGases.g2 v h)
      hfint hfsupp hM hℓ hd hR hRχ u
  have hint : MeasureTheory.IntegrableOn
      (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) q.1 q.2)
      (Submission.BoseGases.dlBox ℓ d u ×ˢ Submission.BoseGases.dlBox ℓ d u) :=
    hcube.mono_set (Set.prod_mono (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u)
      (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u))
  -- The collapsing identity: every pair integral collapses onto the product of the `B×B`-mass
  -- and the unweighted pair-condensate integral.
  rw [Work.BoseFixB1S.boxPairValue (n := N) (ℓ := ℓ) (d := d)
    (f := Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h))
    hℓ u Φ hint]
  simp only [Work.BoseFixB1S.boxM2, Work.BoseFixB1S.boxPairCount, div_eq_mul_inv]
  ring

end Work.BoseFixB1
