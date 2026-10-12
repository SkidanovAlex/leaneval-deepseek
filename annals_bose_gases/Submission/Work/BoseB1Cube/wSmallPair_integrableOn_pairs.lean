import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.integrableOn_slot_wSmallPair
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube

open MeasureTheory

/-- **Integrability of each pair-slot of the localised two-body kernel over the centred box.**

For every ordered pair `p` of distinct particle indices, the function
`x ↦ wSmallPair M ℓ d u v (x p.1) (x p.2)` is integrable on `abox n ℓ`.

This is the `S ≡ 1` instance of the (weighted) slot-integrability lemma
`Work.BoseFixB1.integrableOn_slot_wSmallPair`: the kernel is dominated by
`|v (x p.1 − x p.2)|` (the `abs_wSmallPair_le` bound, the two cutoff factors being bounded by
`chiSupAbs · chiSmallDecay M`), while `x ↦ v (x i − x j)` is integrable over the box because
the two-slot difference of a box configuration averages the translate of `v`
(`integrableOn_pair_sub_abox`). -/
theorem wSmallPair_integrableOn_pairs {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hv1 : MeasureTheory.MemLp v 1) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR16 : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0) {u : EuclideanSpace ℝ (Fin 3)}
    {n : ℕ} :
    ∀ p ∈ Submission.BoseGases.pairSet n,
      MeasureTheory.IntegrableOn
        (fun x : Submission.BoseGases.X n =>
          Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2))
        (Submission.BoseGases.abox n ℓ) := by
  have hvint : MeasureTheory.Integrable v :=
    MeasureTheory.memLp_one_iff_integrable.mp hv1
  have hvsupp : ∀ z : EuclideanSpace ℝ (Fin 3), R ≤ ‖z‖ → v z = 0 :=
    fun z hz => Work.SmallBoxSliding.eq_zero_of_tsupport_subset_ball hv_supp hz
  intro p hp
  have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
  have h1 := Work.BoseFixB1.integrableOn_slot_wSmallPair (N := n) (ℓ := ℓ) (d := d) (R := R)
    hℓ hd hvint hvsupp hM hR16 hRχ u hne
    (S := fun _ : Submission.BoseGases.X n => (1 : ℝ))
    MeasureTheory.aestronglyMeasurable_const (B := 1) zero_le_one
    (Filter.Eventually.of_forall (fun _ => by simp))
  simpa using h1

end Work.BoseB1Cube
