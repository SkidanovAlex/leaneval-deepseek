import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1S.BoxPIndFlat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

-- Bounded slot factor times an integrable fibre pulled back along one coordinate is integrable on
-- the box.  Route: `MeasureTheory.integrable_indicator_iff` turns `IntegrableOn fib A` into
-- `Integrable (A.indicator fib) volume`; the pull-back `x ↦ (A.indicator fib) (x i)` is integrable on
-- `abox N ℓ` (peel with `Submission.BoseGases.abox_peel_mp` + `MeasurePreserving.integrable_comp`,
-- then `MeasureTheory.Integrable.mul_prod` — the template is the proof of
-- `Submission.BoseGases.abox_integral_peel`), and the bounded measurable factor is handled with
-- `MeasureTheory.Integrable.mono'`/`Integrable.mul_bdd`.  The case `N = 0` is vacuous (`i : Fin 0`).
theorem integrableOn_coord_fib {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {F : Submission.BoseGases.X N → ℝ}
    (hFm : MeasureTheory.AEStronglyMeasurable F
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)))
    {C : ℝ} (hFb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |F x| ≤ C)
    {fib : EuclideanSpace ℝ (Fin 3) → ℝ} (hfib : MeasureTheory.IntegrableOn fib A) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N => F x * A.indicator fib (x i))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
  -- The slot factor `A.indicator fib` is globally integrable.
  have hg : MeasureTheory.Integrable (A.indicator fib)
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) :=
    (MeasureTheory.integrable_indicator_iff hA).mpr hfib
  -- It is supported on `A ⊆ acube ℓ`, hence also integrable against the restriction to the cube.
  have hsupp_eq : (Submission.BoseGases.acube ℓ).indicator (A.indicator fib) = A.indicator fib := by
    funext y
    by_cases hy : y ∈ Submission.BoseGases.acube ℓ
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem]
      intro hyA
      exact hy (hAc hyA)
  have hgA : MeasureTheory.IntegrableOn (A.indicator fib) (Submission.BoseGases.acube ℓ)
      MeasureTheory.volume :=
    (MeasureTheory.integrable_indicator_iff (Submission.BoseGases.acube_measurable ℓ)).mp
      (by rw [hsupp_eq]; exact hg)
  rcases N with _ | n
  · exact i.elim0
  -- The remaining box is a finite measure, so the pull-back of `A.indicator fib` to the pair
  -- `(y, r) ↦ A.indicator fib y` is integrable on the product.
  have hνfin : MeasureTheory.IsFiniteMeasure
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)) := by
    rw [MeasureTheory.isFiniteMeasure_restrict, Submission.BoseGases.abox_volume n ℓ hℓ.le]
    exact ENNReal.ofReal_ne_top
  have hpull : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n => A.indicator fib p.1)
      (((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube ℓ)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ))) :=
    MeasureTheory.Integrable.comp_fst hgA _
  -- Peel the slot `i`: the pull-back of that fibre along the coordinate `i` is integrable on the box.
  have hcomp := (Submission.BoseGases.abox_peel_mp (n := n) ℓ i).integrable_comp_of_integrable hpull
  have hgint : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X (n + 1) => A.indicator fib (x i))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) ℓ)) := hcomp
  -- The bounded measurable slot factor is absorbed by `Integrable.bdd_mul`.
  have hbound : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) ℓ)),
      ‖F x‖ ≤ max C 0 := by
    rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable (n + 1) ℓ)]
    filter_upwards with x hx
    rw [Real.norm_eq_abs]
    exact le_trans (hFb x hx) (le_max_left _ _)
  exact hgint.bdd_mul hFm hbound

end Work.BoseFixB1S
