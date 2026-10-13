/-
Copyright: work module for the Elgindi finite-time singularity project.

# Swapping the order of integration and translating the radial variable

This file proves `Work.FTS.EllipticEst.DzAmgm.LintegralSwapTranslate`: the iterated
`lintegral` of `(z,θ) ↦ ENNReal.ofReal ((∂_z²V(z,θ) · wth θ)²)` over the rectangle
`(z₀, z₀+δ) × (0, π/2)`, written with the radial variable translated (`z = z₀ + t`,
`t ∈ (0,δ]`), agrees with the same iterated `lintegral` with the radial variable first.

The proof splits into two independent ingredients:

* `aem_uncurry_translate` — a.e. measurability of the uncurried integrand w.r.t. the
  product of the restricted Lebesgue measures.  This is where `ContDiffOn ℝ 2` is used:
  the second `z`-partial `∂_z²V` is jointly continuous on the quadrant
  (`ContinuousOnUncurryPzIterTwo`), and `wth` is measurable;
* `lintegralSwapTranslate_of_aem` — the measure-theoretic part, which is unconditional
  once measurability is available: Tonelli's theorem, translation invariance of Lebesgue
  measure (`z = z₀ + t`), and the passage from `Ioc` to `Ioo` (a null endpoint).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.DzAmgm.ContinuousOnUncurryPzIterTwo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real ENNReal
open MeasureTheory Set

namespace Work.FTS.EllipticEst.DzAmgm

set_option autoImplicit false

/-- **The measure-theoretic core.**  Once the uncurried integrand is a.e. measurable for
the product of the two restricted Lebesgue measures, the iterated integral written with the
translated radial variable `z = z₀ + t` equals the iterated integral with the radial variable
first.  No hypothesis on `V` or `wth` is needed here. -/
theorem lintegralSwapTranslate_of_aem (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ)
    {z₀ δ : ℝ} (hAEM : AEMeasurable
      (Function.uncurry (fun θ t => ENNReal.ofReal ((Work.Spaces.pzIter 2 V (z₀ + t) θ * wth θ) ^ 2)))
      ((MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))).prod
        (MeasureTheory.volume.restrict (Set.Ioo 0 δ)))) :
    (∫⁻ θ in Set.Ioo 0 (Real.pi / 2),
        ∫⁻ t in Set.Ioc 0 δ,
          ENNReal.ofReal ((Work.Spaces.pzIter 2 V (z₀ + t) θ * wth θ) ^ 2))
      = ∫⁻ z in Set.Ioo z₀ (z₀ + δ),
          ∫⁻ θ in Set.Ioo 0 (Real.pi / 2),
            ENNReal.ofReal ((Work.Spaces.pzIter 2 V z θ * wth θ) ^ 2) := by
  -- `Ioc 0 δ` and `Ioo 0 δ` differ by the null set `{δ}`.
  have hIoc : (MeasureTheory.volume.restrict (Set.Ioc 0 δ))
      = MeasureTheory.volume.restrict (Set.Ioo 0 δ) :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc.symm
  rw [hIoc]
  -- Tonelli: interchange the two integrals.
  rw [MeasureTheory.lintegral_lintegral_swap hAEM]
  -- Translation invariance of Lebesgue measure: `t ↦ z₀ + t` maps `Ioo 0 δ` onto `Ioo z₀ (z₀+δ)`.
  have hpre : (fun t : ℝ => z₀ + t) ⁻¹' (Set.Ioo z₀ (z₀ + δ)) = Set.Ioo 0 δ := by
    ext t
    simp only [Set.mem_preimage, Set.mem_Ioo]
    constructor <;> intro h <;> constructor <;> linarith
  have key := (MeasureTheory.measurePreserving_add_left MeasureTheory.volume z₀).setLIntegral_comp_preimage_emb
    ((Homeomorph.addLeft z₀).isClosedEmbedding.measurableEmbedding)
    (fun z => ∫⁻ θ in Set.Ioo 0 (Real.pi / 2),
      ENNReal.ofReal ((Work.Spaces.pzIter 2 V z θ * wth θ) ^ 2))
    (Set.Ioo z₀ (z₀ + δ))
  rw [hpre] at key
  exact key

/-- **Measurability of the uncurried integrand.**  Using that the second `z`-partial of `V`
is jointly continuous on the quadrant, and that `wth` is measurable, the integrand
`(θ,t) ↦ ofReal ((∂_z²V (z₀+t) θ · wth θ)²)` is a.e. measurable for the product of the
restricted Lebesgue measures on `(0,π/2)` and `(0,δ)`. -/
theorem aem_uncurry_translate (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ) (hwthmeas : Measurable wth)
    (hcont : ContinuousOn (Function.uncurry (Work.Spaces.pzIter 2 V))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {z₀ δ : ℝ} (hz₀ : 0 < z₀) (hδ : 0 < δ) :
    AEMeasurable
      (Function.uncurry (fun θ t => ENNReal.ofReal ((Work.Spaces.pzIter 2 V (z₀ + t) θ * wth θ) ^ 2)))
      ((MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))).prod
        (MeasureTheory.volume.restrict (Set.Ioo 0 δ))) := by
  -- View the product of restricted measures as a restriction of the product measure.
  rw [MeasureTheory.Measure.prod_restrict]
  have hAB : MeasurableSet (Set.Ioo (0 : ℝ) (Real.pi / 2) ×ˢ Set.Ioo (0 : ℝ) δ) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  -- The affine map `(θ,t) ↦ (z₀+t, θ)` sends the box into the quadrant.
  have hmaps : MapsTo (fun p : ℝ × ℝ => (z₀ + p.2, p.1))
      (Set.Ioo (0 : ℝ) (Real.pi / 2) ×ˢ Set.Ioo (0 : ℝ) δ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    rintro ⟨θ, t⟩ ⟨hθ, ht⟩
    simp only [Set.mem_prod, Set.mem_Ioo, Set.mem_Ioi] at hθ ht ⊢
    exact ⟨by linarith, ⟨hθ.1, hθ.2⟩⟩
  have hcont' : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 V (z₀ + p.2) p.1)
      (Set.Ioo (0 : ℝ) (Real.pi / 2) ×ˢ Set.Ioo (0 : ℝ) δ) :=
    (hcont.comp (((continuous_const.add continuous_snd).prodMk continuous_fst).continuousOn)
      hmaps).congr (fun p _ => rfl)
  have h1 : AEMeasurable (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 V (z₀ + p.2) p.1)
      ((MeasureTheory.volume.prod MeasureTheory.volume).restrict
        (Set.Ioo (0 : ℝ) (Real.pi / 2) ×ˢ Set.Ioo (0 : ℝ) δ)) :=
    hcont'.aemeasurable hAB
  have h2 : AEMeasurable (fun p : ℝ × ℝ => wth p.1)
      ((MeasureTheory.volume.prod MeasureTheory.volume).restrict
        (Set.Ioo (0 : ℝ) (Real.pi / 2) ×ˢ Set.Ioo (0 : ℝ) δ)) :=
    (hwthmeas.comp measurable_fst).aemeasurable
  have h3 : AEMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 V (z₀ + p.2) p.1 * wth p.1)
      ((MeasureTheory.volume.prod MeasureTheory.volume).restrict
        (Set.Ioo (0 : ℝ) (Real.pi / 2) ×ˢ Set.Ioo (0 : ℝ) δ)) :=
    h1.mul h2
  have h4 : AEMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.pzIter 2 V (z₀ + p.2) p.1 * wth p.1) ^ 2)
      ((MeasureTheory.volume.prod MeasureTheory.volume).restrict
        (Set.Ioo (0 : ℝ) (Real.pi / 2) ×ˢ Set.Ioo (0 : ℝ) δ)) :=
    (h3.mul h3).congr (Filter.Eventually.of_forall fun p => by simp [Pi.mul_apply, pow_two])
  refine ((ENNReal.measurable_ofReal.comp_aemeasurable h4)).congr ?_
  filter_upwards with p
  simp only [Function.uncurry, Function.comp_apply]

/-- The second `z`-partial of a `C²` function on the quadrant is jointly continuous there,
so the integrand of `LintegralSwapTranslate` is a.e. measurable. -/
theorem aem_uncurry_pzIter_two (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ) (hwthmeas : Measurable wth)
    (hV : ContDiffOn ℝ 2 (Function.uncurry V) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {z₀ δ : ℝ} (hz₀ : 0 < z₀) (hδ : 0 < δ) :
    AEMeasurable
      (Function.uncurry (fun θ t => ENNReal.ofReal ((Work.Spaces.pzIter 2 V (z₀ + t) θ * wth θ) ^ 2)))
      ((MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))).prod
        (MeasureTheory.volume.restrict (Set.Ioo 0 δ))) :=
  aem_uncurry_translate V wth hwthmeas
    (ContinuousOnUncurryPzIterTwo (isOpen_Ioi.prod isOpen_Ioo) hV) hz₀ hδ

theorem LintegralSwapTranslate (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ) (hwthmeas : Measurable wth)
    (hV : ContDiffOn ℝ 2 (Function.uncurry V) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {z₀ δ : ℝ} (hz₀ : 0 < z₀) (hδ : 0 < δ) :
    (∫⁻ θ in Set.Ioo 0 (Real.pi / 2),
        ∫⁻ t in Set.Ioc 0 δ,
          ENNReal.ofReal ((Work.Spaces.pzIter 2 V (z₀ + t) θ * wth θ) ^ 2))
      = ∫⁻ z in Set.Ioo z₀ (z₀ + δ),
          ∫⁻ θ in Set.Ioo 0 (Real.pi / 2),
            ENNReal.ofReal ((Work.Spaces.pzIter 2 V z θ * wth θ) ^ 2) :=
  lintegralSwapTranslate_of_aem V wth (aem_uncurry_pzIter_two V wth hwthmeas hV hz₀ hδ)

end Work.FTS.EllipticEst.DzAmgm
