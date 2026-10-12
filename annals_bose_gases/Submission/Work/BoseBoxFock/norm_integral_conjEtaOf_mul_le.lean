import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.MB.SlotWeakBase
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory

/-- **The supported-pairing bound.**  If every mode `e l` is supported in the box `boxL ℓ`, the
state function `η_v = Σ_l v_l e_l` is supported there too, and it is bounded by `B` while the
test function `F` is bounded by `C`; then the pairing `∫ conj(η_v)·F` is bounded by
`B · max C 0 · vol (boxL ℓ)`.

The point of the estimate is that the bound is *supported*: the volume factor is the volume of
the box, not of the whole space, and no measurability of `F` (nor of the underlying one-particle
vectors `e l`, which enter only through their zero sets) is assumed —
`norm_integral_le_of_norm_le` applied to the (integrable) majorant `B·max C 0·1_{boxL ℓ}` gives
the claim for arbitrary integrands. -/
theorem norm_integral_conjEtaOf_mul_le {m : ℕ} {ℓ : ℝ} {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (v : Fin m → ℝ) {B : ℝ} (hB : ∀ z, ‖Work.BoseDict.etaOf e v z‖ ≤ B)
    {F : EuclideanSpace ℝ (Fin 3) → ℂ} {C : ℝ} (hF : ∀ z, ‖F z‖ ≤ C) :
    ‖∫ z : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (Work.BoseDict.etaOf e v z) * F z‖
      ≤ B * max C 0
        * (MeasureTheory.volume (Work.BoseK15.corpusBox.boxL ℓ)).toReal := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg (Work.BoseDict.etaOf e v 0)) (hB 0)
  have hsuppη : Function.support (Work.BoseDict.etaOf e v)
      ⊆ Work.BoseK15.corpusBox.boxL ℓ := by
    intro z hz
    rw [Function.mem_support] at hz
    by_contra h
    refine hz ?_
    rw [Work.BoseDict.etaOf]
    refine Finset.sum_eq_zero fun l _ => ?_
    have hz0 : e l z = 0 := by
      by_contra hne
      exact h (hsupp l (Function.mem_support.mpr hne))
    simp [hz0]
  have hpt : ∀ z : EuclideanSpace ℝ (Fin 3),
      ‖(starRingEnd ℂ) (Work.BoseDict.etaOf e v z) * F z‖ ≤ B * max C 0 := by
    intro z
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hB z) (le_trans (hF z) (le_max_left C 0)) (norm_nonneg _) hB0
  have hvol : MeasureTheory.volume (Work.BoseK15.corpusBox.boxL ℓ) < ⊤ :=
    (Work.BoseK15.corpusBox.boxL_compact ℓ).measure_lt_top
  have hind : Integrable
      (Set.indicator (Work.BoseK15.corpusBox.boxL ℓ)
        (fun _ : EuclideanSpace ℝ (Fin 3) => (1 : ℝ))) :=
    (integrable_indicator_iff (Work.BoseK15.corpusBox.boxL_measurableSet ℓ)).mpr
      (MeasureTheory.integrableOn_const (C := (1 : ℝ)) hvol.ne (by simp))
  have hgint : Integrable (fun z : EuclideanSpace ℝ (Fin 3) =>
      B * max C 0
        * Set.indicator (Work.BoseK15.corpusBox.boxL ℓ)
            (fun _ : EuclideanSpace ℝ (Fin 3) => (1 : ℝ)) z) := by
    simpa only [smul_eq_mul] using hind.const_mul (B * max C 0)
  have hae : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
      ‖(starRingEnd ℂ) (Work.BoseDict.etaOf e v z) * F z‖
        ≤ B * max C 0
          * Set.indicator (Work.BoseK15.corpusBox.boxL ℓ)
              (fun _ : EuclideanSpace ℝ (Fin 3) => (1 : ℝ)) z := by
    filter_upwards with z
    by_cases hz : z ∈ Work.BoseK15.corpusBox.boxL ℓ
    · rw [Set.indicator_of_mem hz, mul_one]
      exact hpt z
    · have h0 : Work.BoseDict.etaOf e v z = 0 :=
        Function.notMem_support.mp (fun h => hz (hsuppη h))
      rw [Set.indicator_of_notMem hz, mul_zero, h0]
      simp
  calc ‖∫ z : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (Work.BoseDict.etaOf e v z) * F z‖
      ≤ ∫ z : EuclideanSpace ℝ (Fin 3), B * max C 0
          * Set.indicator (Work.BoseK15.corpusBox.boxL ℓ)
              (fun _ : EuclideanSpace ℝ (Fin 3) => (1 : ℝ)) z :=
        MeasureTheory.norm_integral_le_of_norm_le hgint hae
    _ = B * max C 0 * (MeasureTheory.volume (Work.BoseK15.corpusBox.boxL ℓ)).toReal := by
        rw [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_indicator_const (s := Work.BoseK15.corpusBox.boxL ℓ) (1 : ℝ)
            (Work.BoseK15.corpusBox.boxL_measurableSet ℓ)]
        simp [MeasureTheory.Measure.real_def]

end Work.BoseBoxFock
