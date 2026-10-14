import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif

/-- The level-6 weight `rho6`, as a function of the point `(z,θ)`, is Borel measurable. -/
private theorem measurable_rho6 (α : ℝ) (i : ℕ) :
    Measurable (fun p : ℝ × ℝ => rho6 α i p.1 p.2) := by
  have hsin : Measurable (fun θ : ℝ => Real.sin (2 * θ)) :=
    Real.measurable_sin.comp (measurable_const.mul measurable_id)
  have hw : Measurable (fun z : ℝ => Work.Spaces.w z) := by
    rw [show Work.Spaces.w = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 from rfl]
    exact ((measurable_const.add measurable_id).pow_const 2).div (measurable_id.pow_const 2)
  by_cases hi : i = 0
  · have hρ : (fun p : ℝ × ℝ => rho6 α i p.1 p.2)
        = fun p : ℝ × ℝ =>
            Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2) := by
      funext p
      simp only [rho6, hi, ite_true]
    rw [hρ]
    exact (hw.comp measurable_fst).div ((hsin.comp measurable_snd).pow_const _)
  · have hρ : (fun p : ℝ × ℝ => rho6 α i p.1 p.2)
        = fun p : ℝ × ℝ =>
            Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
      funext p
      simp only [rho6, hi, ite_false, Work.Spaces.Wt, Work.Spaces.wTheta]
    rw [hρ]
    exact (hw.comp measurable_fst).mul ((hsin.comp measurable_snd).pow_const _)

theorem aemeasurable_ofReal_level6 {α : ℝ} {g : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hslots : ∀ (j i : ℕ), ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.mixed j i g p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc c d))
    (ha : 0 < a) (hc : 0 < c) (hd : d < Real.pi / 2) :
    AEMeasurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal (Work.FTS.StrongEps.LocUnif.level6Z α g p.1 p.2))
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) ∧
      AEMeasurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal (Work.FTS.StrongEps.LocUnif.level6T α g p.1 p.2))
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) := by
  -- The three positivity hypotheses are not needed for measurability itself: they are what
  -- places the rectangle inside the open quadrant (where the weights are positive and the
  -- slots are continuous in the applications of this lemma).
  have hquad : ∀ (z θ : ℝ), z ∈ Set.Icc a b → θ ∈ Set.Icc c d →
      0 < z ∧ 0 < θ ∧ θ < Real.pi / 2 := by
    intro z θ hz hθ
    exact ⟨by linarith [hz.1, ha], by linarith [hθ.1, hc], by linarith [hθ.2, hd]⟩
  have hs : MeasurableSet (Set.Icc a b ×ˢ Set.Icc c d : Set (ℝ × ℝ)) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hslot : ∀ j i : ℕ, AEMeasurable (fun p : ℝ × ℝ => Work.Spaces.mixed j i g p.1 p.2)
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
    fun j i => (hslots j i).aemeasurable hs
  have hρ : ∀ i : ℕ, AEMeasurable (fun p : ℝ × ℝ => rho6 α i p.1 p.2)
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
    fun i => (measurable_rho6 α i).aemeasurable
  have hZ : AEMeasurable (fun p : ℝ × ℝ => level6Z α g p.1 p.2)
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) := by
    have hsum : AEMeasurable (∑ i ∈ Finset.range 6, fun p : ℝ × ℝ =>
        (Work.Spaces.mixed (6 - i) i g p.1 p.2 * rho6 α i p.1 p.2) ^ 2)
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
      Finset.aemeasurable_sum _ (fun i _ => ((hslot (6 - i) i).mul (hρ i)).pow_const 2)
    refine hsum.congr ?_
    filter_upwards with p
    simp only [Finset.sum_apply, level6Z]
  have hT : AEMeasurable (fun p : ℝ × ℝ => level6T α g p.1 p.2)
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) := by
    have hprod : AEMeasurable (fun p : ℝ × ℝ =>
        (Work.Spaces.mixed 0 6 g p.1 p.2 * rho6 α 6 p.1 p.2) ^ 2)
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
      ((hslot 0 6).mul (hρ 6)).pow_const 2
    refine hprod.congr ?_
    filter_upwards with p
    simp only [level6T]
  exact ⟨hZ.ennreal_ofReal, hT.ennreal_ofReal⟩

end Work.FTS.StrongEps.LocUnif
