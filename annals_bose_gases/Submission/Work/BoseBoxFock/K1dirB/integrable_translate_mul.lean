import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseBoxFock.K1dirBDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.K1dirB

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-!
# Integrability of the translated, box-supported pairing kernel

This file proves `Work.BoseBoxFock.K1dirB.integrable_translate_mul`: for an `L¹` function `W`,
a bounded, a.e. strongly measurable kernel `H` whose (pointwise) support lies in
`boxL ℓ × boxL ℓ`, and any lattice vector `m`, the product
`(w,y) ↦ W (w - y - ℓ • latVec m) · H w y` is integrable for the product of Lebesgue measures.

The mathematics is elementary: the box `boxL ℓ` has finite measure, `‖H‖` is bounded, and for
every fixed `w` the function `y ↦ ‖W (w - y - ℓ • latVec m)‖` has the same integral as `‖W‖`
(the map `y ↦ w - y - ℓ • latVec m` is a measure preserving involution of `ℝ³`).  The only
non-trivial bookkeeping is the a.e. strong measurability of `w ↦ W (w - y - ℓ • latVec m)`, which
follows because the shear `(w,y) ↦ w - y - a` is quasi-measure-preserving: it maps the null sets
of the product measure to null sets (Fubini + translation invariance).

## Main results

* `shear_map_sub_neg` : the map `y ↦ v - y` preserves Lebesgue measure;
* `shear_quasiMeasurePreserving` : the shear `(w,y) ↦ w - y - a` is quasi-measure-preserving;
* `integrable_translate_mul` : the target.
-/

/-- The map `y ↦ v - y` preserves Lebesgue measure on `ℝ³`. -/
lemma shear_map_sub_neg (v : E3) : Measure.map (fun y : E3 => v - y) volume = volume := by
  have h1 : (fun y : E3 => v - y)
      = ((fun z : E3 => z + v) ∘ (Neg.neg : E3 → E3)) := by
    funext y
    simp [sub_eq_add_neg, add_comm]
  rw [h1, ← Measure.map_map (by fun_prop : Measurable fun z : E3 => z + v)
    (by fun_prop : Measurable (Neg.neg : E3 → E3))]
  rw [Measure.map_neg_eq_self volume]
  exact (measurePreserving_add_right volume v).map_eq

/-- The map `y ↦ v - y` is measure preserving. -/
lemma shear_measurePreserving (v : E3) :
    MeasurePreserving (fun y : E3 => v - y) volume volume :=
  ⟨by fun_prop, shear_map_sub_neg v⟩

/-- The map `y ↦ v - y` as a measurable equivalence (it is an involution). -/
noncomputable def shearEquiv (v : E3) : E3 ≃ᵐ E3 where
  toFun := fun y => v - y
  invFun := fun y => v - y
  left_inv := by intro y; simp only [sub_eq_add_neg]; abel
  right_inv := by intro y; simp only [sub_eq_add_neg]; abel
  measurable_toFun := measurable_const.sub measurable_id
  measurable_invFun := measurable_const.sub measurable_id

/-- Change of variables for the reflection `y ↦ v - y`. -/
lemma shear_integral_sub_neg (v : E3) (g : E3 → ℝ) :
    ∫ y, g (v - y) ∂volume = ∫ u, g u ∂volume :=
  MeasurePreserving.integral_comp' (f := shearEquiv v)
    (⟨(shearEquiv v).measurable, shear_map_sub_neg v⟩) g

/-- Integrability is preserved by the reflection `y ↦ v - y`. -/
lemma shear_integrable_sub_neg (v : E3) {g : E3 → ℝ} (hg : Integrable g volume) :
    Integrable (fun y : E3 => g (v - y)) volume := by
  have h := (shear_measurePreserving v).integrable_comp (g := g) hg.aestronglyMeasurable
  simpa [Function.comp_def] using h.2 hg

/-- The composed reflection `y ↦ v - y - a` (integrability form). -/
lemma shear_integrable (a v : E3) {g : E3 → ℝ} (hg : Integrable g volume) :
    Integrable (fun y : E3 => g (v - y - a)) volume := by
  have hfun : (fun y : E3 => g (v - y - a)) = (fun y : E3 => g ((v - a) - y)) := by
    funext y; rw [sub_right_comm]
  rw [hfun]
  exact shear_integrable_sub_neg (v - a) hg

/-- The composed reflection `y ↦ v - y - a` (change of variables form). -/
lemma shear_integral (a v : E3) (g : E3 → ℝ) :
    ∫ y, g (v - y - a) ∂volume = ∫ u, g u ∂volume := by
  have hfun : (fun y : E3 => g (v - y - a)) = (fun y : E3 => g ((v - a) - y)) := by
    funext y; rw [sub_right_comm]
  rw [hfun]
  exact shear_integral_sub_neg (v - a) g

/-- The shear `(w,y) ↦ w - y - a` on `ℝ³ × ℝ³` is quasi-measure-preserving: it maps null sets
of the product of Lebesgue measures to null sets. -/
lemma shear_quasiMeasurePreserving (a : E3) :
    Measure.QuasiMeasurePreserving (fun p : E3 × E3 => p.1 - p.2 - a) (volume.prod volume) volume := by
  have hφ : Measurable (fun p : E3 × E3 => p.1 - p.2 - a) := by fun_prop
  refine ⟨hφ, Measure.AbsolutelyContinuous.mk ?_⟩
  intro S hS hS0
  have hpre : MeasurableSet ((fun p : E3 × E3 => p.1 - p.2 - a) ⁻¹' S) := hS.preimage hφ
  rw [Measure.map_apply hφ hS, Measure.prod_apply hpre]
  have hzero : ∀ w : E3,
      volume (Prod.mk w ⁻¹' ((fun p : E3 × E3 => p.1 - p.2 - a) ⁻¹' S)) = 0 := by
    intro w
    have hset : Prod.mk w ⁻¹' ((fun p : E3 × E3 => p.1 - p.2 - a) ⁻¹' S)
        = (fun y : E3 => w - y - a) ⁻¹' S := rfl
    rw [hset]
    have hfun : (fun y : E3 => w - y - a) = (fun y : E3 => (w - a) - y) := by
      funext y; rw [sub_right_comm]
    rw [hfun, ← Measure.map_apply (by fun_prop : Measurable fun y : E3 => (w - a) - y) hS,
      shear_map_sub_neg (w - a)]
    exact hS0
  simp only [hzero, lintegral_zero]

/-- `W (·.1 - ·.2 - a)` is a.e. strongly measurable on the product of Lebesgue measures whenever
`W` is. -/
lemma shear_aestronglyMeasurable {W : E3 → ℝ} (hW : AEStronglyMeasurable W volume) (a : E3) :
    AEStronglyMeasurable (fun p : E3 × E3 => W (p.1 - p.2 - a)) (volume.prod volume) :=
  hW.comp_quasiMeasurePreserving (shear_quasiMeasurePreserving a)

theorem integrable_translate_mul {ℓ : ℝ} (hℓ : 0 < ℓ)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hW : MeasureTheory.Integrable W) (m : Fin 3 → ℤ)
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hHm : MeasureTheory.AEStronglyMeasurable (Function.uncurry H)
      (MeasureTheory.volume.prod MeasureTheory.volume))
    (hHb : ∃ C : ℝ, ∀ w y, ‖H w y‖ ≤ C)
    (hHs : ∀ w y, H w y ≠ 0 →
      w ∈ Work.BoseK15.corpusBox.boxL ℓ ∧ y ∈ Work.BoseK15.corpusBox.boxL ℓ) :
    MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        ((W (p.1 - p.2 - ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ) * H p.1 p.2)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  obtain ⟨C, hC⟩ := hHb
  set Ast : Set E3 := Work.BoseK15.corpusBox.boxL ℓ with hAstdef
  set aa : E3 := ℓ • Work.BoseBoxFock.latVec m with haadef
  set K : ℝ := max C 0 * ∫ u : E3, ‖W u‖ ∂volume with hKdef
  have hAstm : MeasurableSet Ast := Work.BoseK15.corpusBox.boxL_measurableSet ℓ
  have hAstfin : volume Ast < ⊤ := (Work.BoseK15.corpusBox.boxL_compact ℓ).measure_lt_top
  have hHm' : AEStronglyMeasurable (fun p : E3 × E3 => H p.1 p.2) (volume.prod volume) := hHm
  -- pointwise bound `‖H w y‖ ≤ max C 0`
  have hbound : ∀ w y : E3, ‖H w y‖ ≤ max C 0 := fun w y =>
    le_trans (hC w y) (le_max_left C 0)
  have hf : AEStronglyMeasurable
      (fun p : E3 × E3 => ((W (p.1 - p.2 - aa) : ℝ) : ℂ) * H p.1 p.2)
      (volume.prod volume) :=
    (Complex.continuous_ofReal.comp_aestronglyMeasurable
      (shear_aestronglyMeasurable hW.aestronglyMeasurable aa)).mul hHm'
  refine (integrable_prod_iff hf).2 ⟨?_, ?_⟩
  · filter_upwards [hf.prodMk_left] with w hw
    have hmaj : Integrable (fun y : E3 => max C 0 * ‖W (w - y - aa)‖) volume :=
      shear_integrable aa w ((hW.norm).const_mul (max C 0))
    refine hmaj.mono' hw ?_
    filter_upwards with y
    have h1 : ‖H w y‖ ≤ max C 0 := hbound w y
    rw [norm_mul, Complex.norm_real]
    calc ‖W (w - y - aa)‖ * ‖H w y‖ ≤ ‖W (w - y - aa)‖ * max C 0 :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = max C 0 * ‖W (w - y - aa)‖ := mul_comm _ _
  · have hmeas2 : AEStronglyMeasurable
        (fun w : E3 => ∫ y : E3, ‖((W (w - y - aa) : ℝ) : ℂ) * H w y‖ ∂volume) volume :=
      hf.norm.integral_prod_right'
    have hAind : Integrable (Ast.indicator (fun _ : E3 => (1 : ℝ))) volume :=
      (integrable_indicator_iff hAstm).2
        (IntegrableOn.of_bound hAstfin aestronglyMeasurable_const 1
          (by filter_upwards with x; simp))
    refine (hAind.const_mul K).mono' hmeas2 ?_
    filter_upwards [hf.prodMk_left] with w hw
    have hmaj : Integrable (fun y : E3 => max C 0 * ‖W (w - y - aa)‖) volume :=
      shear_integrable aa w ((hW.norm).const_mul (max C 0))
    have hslice : Integrable (fun y : E3 => ((W (w - y - aa) : ℝ) : ℂ) * H w y) volume := by
      refine hmaj.mono' hw ?_
      filter_upwards with y
      have h1 : ‖H w y‖ ≤ max C 0 := hbound w y
      rw [norm_mul, Complex.norm_real]
      calc ‖W (w - y - aa)‖ * ‖H w y‖ ≤ ‖W (w - y - aa)‖ * max C 0 :=
            mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ = max C 0 * ‖W (w - y - aa)‖ := mul_comm _ _
    have hnorms : Integrable (fun y : E3 => ‖((W (w - y - aa) : ℝ) : ℂ) * H w y‖) volume :=
      hslice.norm
    by_cases hwAst : w ∈ Ast
    · rw [Set.indicator_of_mem hwAst, mul_one]
      have hb1 : (∫ y : E3, ‖((W (w - y - aa) : ℝ) : ℂ) * H w y‖ ∂volume)
          ≤ ∫ y : E3, max C 0 * ‖W (w - y - aa)‖ ∂volume := by
        refine integral_mono hnorms hmaj fun y => ?_
        have h1 : ‖H w y‖ ≤ max C 0 := hbound w y
        rw [norm_mul, Complex.norm_real]
        calc ‖W (w - y - aa)‖ * ‖H w y‖ ≤ ‖W (w - y - aa)‖ * max C 0 :=
              mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
          _ = max C 0 * ‖W (w - y - aa)‖ := mul_comm _ _
      have hb2 : (∫ y : E3, max C 0 * ‖W (w - y - aa)‖ ∂volume) = K := by
        rw [hKdef, integral_const_mul]
        congr 1
        exact shear_integral aa w (fun u => ‖W u‖)
      calc ‖∫ y : E3, ‖((W (w - y - aa) : ℝ) : ℂ) * H w y‖ ∂volume‖
          ≤ ∫ y : E3, ‖‖((W (w - y - aa) : ℝ) : ℂ) * H w y‖‖ ∂volume :=
            norm_integral_le_integral_norm _
        _ = ∫ y : E3, ‖((W (w - y - aa) : ℝ) : ℂ) * H w y‖ ∂volume := by simp
        _ ≤ K := le_trans hb1 (le_of_eq hb2)
    · rw [Set.indicator_of_notMem hwAst]
      have hzero : ∀ y : E3, H w y = 0 := by
        intro y
        by_contra hne
        exact hwAst (hHs w y hne).1
      have hz : (∫ y : E3, ‖((W (w - y - aa) : ℝ) : ℂ) * H w y‖ ∂volume) = 0 := by
        rw [show (fun y : E3 => ‖((W (w - y - aa) : ℝ) : ℂ) * H w y‖) = fun _ => (0 : ℝ) from by
          funext y; rw [hzero y, mul_zero, norm_zero]]
        simp
      rw [hz]
      simp

end Work.BoseBoxFock.K1dirB
