import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.blockIIDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.box_pair_flat_integral` — the two iterated pair forms of a box-integrable kernel

Both sides of each conjunct are the integral of the same three-variable integrand over the box
`(Λ(ℓ))² × Λ(ℓ)^p`; the content is Fubini--Tonelli, honest because the hypotheses give
measurability plus a uniform bound `C` on `acube ℓ × acube ℓ × abox p ℓ` and the boxes have
finite volume.

Route (both conjuncts share it):

* for fixed `r2`, the double integral over `y, u ∈ acube ℓ` is the integral over the *product*
  `Λ(ℓ) × Λ(ℓ)` (`MeasureTheory.setIntegral_prod`), fed by `IntegrableOn.of_bound`
  (`|w| ≤ C` on the box, box of finite volume);
* the second conjunct's inner integrand is the transposed one, and `setIntegral_prod_swap`
  (which needs no integrability input) identifies the two pair integrals;
* the remaining swap of the `r2`-integral with the pair integral is `setIntegral_prod` /
  `setIntegral_prod_swap` between `volume` on `X p` and `(volume × volume)` on `E3 × E3`, again
  with `IntegrableOn.of_bound` for the hypothesis;
* finally `Measure.prod_restrict` identifies the nested restricted-product measure of the
  right-hand side with the restriction of the product volume to
  `(Λ(ℓ) × Λ(ℓ)) × Λ(ℓ)^p`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem box_pair_flat_integral {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {w : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → Submission.BoseGases.X p → ℝ}
    (hwm : Measurable (Function.uncurry (Function.uncurry w))) {C : ℝ}
    (hwb : ∀ a b r, a ∈ Submission.BoseGases.acube ℓ → b ∈ Submission.BoseGases.acube ℓ →
        r ∈ Submission.BoseGases.abox p ℓ → |w a b r| ≤ C) :
    ((∫ r2 in Submission.BoseGases.abox p ℓ,
          ∫ y in Submission.BoseGases.acube ℓ,
            ∫ u in Submission.BoseGases.acube ℓ, w y u r2)
        = ∫ q : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × Submission.BoseGases.X p,
            w q.1.1 q.1.2 q.2
            ∂(((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
                  (Submission.BoseGases.acube ℓ)).prod
                ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
                  (Submission.BoseGases.acube ℓ))).prod
              ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X p)).restrict
                (Submission.BoseGases.abox p ℓ)))
    ∧ ((∫ r2 in Submission.BoseGases.abox p ℓ,
          ∫ z in Submission.BoseGases.acube ℓ,
            ∫ y in Submission.BoseGases.acube ℓ, w y z r2)
        = ∫ q : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × Submission.BoseGases.X p,
            w q.1.1 q.1.2 q.2
            ∂(((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
                  (Submission.BoseGases.acube ℓ)).prod
                ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
                  (Submission.BoseGases.acube ℓ))).prod
              ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X p)).restrict
                (Submission.BoseGases.abox p ℓ))) := by
  -- the one-body double integral as a pair integral (identity of the first conjunct)
  have hpair : ∀ r2 ∈ Submission.BoseGases.abox p ℓ,
      (∫ y in Submission.BoseGases.acube ℓ, ∫ u in Submission.BoseGases.acube ℓ, w y u r2)
        = ∫ q2 in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ, w q2.1 q2.2 r2
            ∂((volume : Measure E3).prod (volume : Measure E3)) := by
    intro r2 hr2
    have hgm : Measurable (fun q2 : E3 × E3 => w q2.1 q2.2 r2) :=
      hwm.comp ((measurable_fst.prodMk measurable_snd).prodMk measurable_const)
    refine (setIntegral_prod (fun q2 : E3 × E3 => w q2.1 q2.2 r2) ?_).symm
    refine IntegrableOn.of_bound ?_ hgm.aestronglyMeasurable C ?_
    · rw [Measure.prod_prod, Submission.BoseGases.acube_volume ℓ hℓ.le]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
    · filter_upwards [self_mem_ae_restrict ((Submission.BoseGases.acube_measurable ℓ).prod
        (Submission.BoseGases.acube_measurable ℓ))] with x hx
      rw [Real.norm_eq_abs]
      exact hwb x.1 x.2 r2 hx.1 hx.2 hr2
  -- the transposed double integral gives the same pair integral (identity of the second conjunct)
  have hpair2 : ∀ r2 ∈ Submission.BoseGases.abox p ℓ,
      (∫ z in Submission.BoseGases.acube ℓ, ∫ y in Submission.BoseGases.acube ℓ, w y z r2)
        = ∫ q2 in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ, w q2.1 q2.2 r2
            ∂((volume : Measure E3).prod (volume : Measure E3)) := by
    intro r2 hr2
    have hgm : Measurable (fun q2 : E3 × E3 => w q2.2 q2.1 r2) :=
      hwm.comp ((measurable_snd.prodMk measurable_fst).prodMk measurable_const)
    have hint : IntegrableOn (fun q2 : E3 × E3 => w q2.2 q2.1 r2)
        (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ)
        ((volume : Measure E3).prod (volume : Measure E3)) := by
      refine IntegrableOn.of_bound ?_ hgm.aestronglyMeasurable C ?_
      · rw [Measure.prod_prod, Submission.BoseGases.acube_volume ℓ hℓ.le]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
      · filter_upwards [self_mem_ae_restrict ((Submission.BoseGases.acube_measurable ℓ).prod
          (Submission.BoseGases.acube_measurable ℓ))] with x hx
        rw [Real.norm_eq_abs]
        exact hwb x.2 x.1 r2 hx.2 hx.1 hr2
    have h1 : (∫ z in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ, w z.2 z.1 r2
          ∂((volume : Measure E3).prod (volume : Measure E3)))
        = ∫ z in Submission.BoseGases.acube ℓ, ∫ y in Submission.BoseGases.acube ℓ, w y z r2 :=
      setIntegral_prod (μ := (volume : Measure E3)) (ν := (volume : Measure E3))
        (s := Submission.BoseGases.acube ℓ) (t := Submission.BoseGases.acube ℓ)
        (fun q2 : E3 × E3 => w q2.2 q2.1 r2) hint
    have h2 : (∫ z in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ, w z.2 z.1 r2
          ∂((volume : Measure E3).prod (volume : Measure E3)))
        = ∫ z in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ, w z.1 z.2 r2
            ∂((volume : Measure E3).prod (volume : Measure E3)) :=
      setIntegral_prod_swap (μ := (volume : Measure E3)) (ν := (volume : Measure E3))
        (Submission.BoseGases.acube ℓ) (Submission.BoseGases.acube ℓ)
        (fun q2 : E3 × E3 => w q2.1 q2.2 r2)
    exact h1.symm.trans h2
  have hL1 : (∫ r2 in Submission.BoseGases.abox p ℓ,
          ∫ y in Submission.BoseGases.acube ℓ,
            ∫ u in Submission.BoseGases.acube ℓ, w y u r2)
      = ∫ r2 in Submission.BoseGases.abox p ℓ,
          ∫ q2 in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ, w q2.1 q2.2 r2
            ∂((volume : Measure E3).prod (volume : Measure E3)) := by
    refine setIntegral_congr_fun (Submission.BoseGases.abox_measurable p ℓ) ?_
    intro r2 hr2
    exact hpair r2 hr2
  have hL2 : (∫ r2 in Submission.BoseGases.abox p ℓ,
          ∫ z in Submission.BoseGases.acube ℓ,
            ∫ y in Submission.BoseGases.acube ℓ, w y z r2)
      = ∫ r2 in Submission.BoseGases.abox p ℓ,
          ∫ q2 in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ, w q2.1 q2.2 r2
            ∂((volume : Measure E3).prod (volume : Measure E3)) := by
    refine setIntegral_congr_fun (Submission.BoseGases.abox_measurable p ℓ) ?_
    intro r2 hr2
    exact hpair2 r2 hr2
  -- Fubini between the box variable on `X p` and the pair variable on `E3 × E3`
  have hswap : (∫ r2 in Submission.BoseGases.abox p ℓ,
          ∫ q2 in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ, w q2.1 q2.2 r2
            ∂((volume : Measure E3).prod (volume : Measure E3)))
      = ∫ q in (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ) ×ˢ
            Submission.BoseGases.abox p ℓ,
          w q.1.1 q.1.2 q.2
          ∂(((volume : Measure E3).prod (volume : Measure E3)).prod
              (volume : Measure (Submission.BoseGases.X p))) := by
    have hgm : Measurable (fun z : Submission.BoseGases.X p × (E3 × E3) => w z.2.1 z.2.2 z.1) :=
      hwm.comp (((measurable_fst.comp measurable_snd).prodMk
        (measurable_snd.comp measurable_snd)).prodMk measurable_fst)
    have hint : IntegrableOn (fun z : Submission.BoseGases.X p × (E3 × E3) => w z.2.1 z.2.2 z.1)
        (Submission.BoseGases.abox p ℓ ×ˢ (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ))
        ((volume : Measure (Submission.BoseGases.X p)).prod
          ((volume : Measure E3).prod (volume : Measure E3))) := by
      refine IntegrableOn.of_bound ?_ hgm.aestronglyMeasurable C ?_
      · rw [Measure.prod_prod, Measure.prod_prod, Submission.BoseGases.abox_volume p ℓ hℓ.le,
          Submission.BoseGases.acube_volume ℓ hℓ.le]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
      · filter_upwards [self_mem_ae_restrict ((Submission.BoseGases.abox_measurable p ℓ).prod
          ((Submission.BoseGases.acube_measurable ℓ).prod
            (Submission.BoseGases.acube_measurable ℓ)))] with x hx
        rw [Real.norm_eq_abs]
        exact hwb x.2.1 x.2.2 x.1 hx.2.1 hx.2.2 hx.1
    have h1 := setIntegral_prod (μ := (volume : Measure (Submission.BoseGases.X p)))
        (ν := (volume : Measure E3).prod (volume : Measure E3))
        (s := Submission.BoseGases.abox p ℓ)
        (t := Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ)
        (f := fun z : Submission.BoseGases.X p × (E3 × E3) => w z.2.1 z.2.2 z.1) hint
    have h2 := setIntegral_prod_swap (μ := (volume : Measure E3).prod (volume : Measure E3))
        (ν := (volume : Measure (Submission.BoseGases.X p)))
        (s := Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ)
        (t := Submission.BoseGases.abox p ℓ)
        (f := fun q : (E3 × E3) × Submission.BoseGases.X p => w q.1.1 q.1.2 q.2)
    exact h1.symm.trans h2
  -- the nested restricted-product measure is the product volume restricted to the triple box
  have hRHS : (∫ q : (E3 × E3) × Submission.BoseGases.X p,
            w q.1.1 q.1.2 q.2
            ∂(((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)).prod
                ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))).prod
              ((volume : Measure (Submission.BoseGases.X p)).restrict
                (Submission.BoseGases.abox p ℓ)))
      = ∫ q in (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ) ×ˢ
            Submission.BoseGases.abox p ℓ,
          w q.1.1 q.1.2 q.2
          ∂(((volume : Measure E3).prod (volume : Measure E3)).prod
              (volume : Measure (Submission.BoseGases.X p))) := by
    rw [Measure.prod_restrict, Measure.prod_restrict]
  exact ⟨hL1.trans (hswap.trans hRHS.symm), hL2.trans (hswap.trans hRHS.symm)⟩

end Work.BoseBoxFock
