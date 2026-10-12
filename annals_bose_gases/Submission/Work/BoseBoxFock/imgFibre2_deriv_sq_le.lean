import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.imgFibre2Aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.imgFibre2_deriv_sq_le` — the Cauchy–Schwarz step for the mirror fibre

This module proves the Cauchy–Schwarz estimate for the `p.1`-slot derivative of the *mirror*
position-space fibre

    imgFibre₂ ℓ p F₁ G u v = ℓ⁻³ ∫_{x'} ∫_{s ∈ boxL} F₁ (ins p u s x') · G (ins p u v x')

under the hypothesis that `F₁` is independent of the slot `p.1`:

    (∂_{u,j} imgFibre₂ ℓ p F₁ G · v)² ≤ ℓ⁻⁶ · (∫_{x'}∫_s F₁(ins p u s x')²)
                                            · (∫_{x'}∫_s (∂_{p.1,j} G (ins p u v x'))²).

Two ingredients:

* the derivative formula `Work.BoseBoxFock.fderiv_imgFibre₂_fst_apply` (in `imgFibre2Aux`), which
  evaluates the `u`-derivative as `ℓ⁻³` times the double integral of the (`u`-independent!)
  `F₁`-factor against the `p.1`-slot derivative of `G`;
* the two-variable Cauchy–Schwarz inequality for the iterated box integral
  `boxPi_cauchy_schwarz`: for continuous `f`, `g` on the box,
  `(∫_{x'}∫_s f·g)² ≤ (∫_{x'}∫_s f²)·(∫_{x'}∫_s g²)`.  It is proved by applying the `L²`
  Cauchy–Schwarz inequality `Work.BoseFixB1S.integral_mul_sq_le_of_memLp` to the *product* measure
  `(volume.restrict boxPiSet).prod (volume.restrict boxL)`, using Fubini
  (`MeasureTheory.integral_integral`) to identify the iterated integral with the product integral;
  the `L²`-memberships come from continuity plus compactness of the box
  (`MeasureTheory.memLp_two_iff_integrable_sq_norm` + `ContinuousOn.integrableOn_compact`).

Everything here is `sorry`-free.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "boxL" => Work.BoseK15.corpusBox.boxL

/-- **Cauchy–Schwarz for the iterated integral over the fibre box.**

For continuous `f`, `g : (ι → E3) → E3 → ℝ` on the compact box
`boxPiSet ι ℓ × boxL ℓ`,

    (∫_{x' ∈ boxPiSet ι ℓ} ∫_{s ∈ boxL ℓ} f x' s · g x' s)²
      ≤ (∫_{x' ∈ boxPiSet ι ℓ} ∫_{s ∈ boxL ℓ} f x' s ²) · (∫_{x' ∈ boxPiSet ι ℓ} ∫_{s ∈ boxL ℓ} g x' s ²).

The two-fold integral is the integral against the product measure
`(volume.restrict (boxPiSet ι ℓ)).prod (volume.restrict (boxL ℓ))`, which is the restriction of
the volume of the product to the compact box `boxPiSet ι ℓ ×ˢ boxL ℓ`; on that compact set
continuity gives both `L²`-memberships, and the `L²` Cauchy–Schwarz inequality
`Work.BoseFixB1S.integral_mul_sq_le_of_memLp` closes. -/
theorem boxPi_cauchy_schwarz {ι : Type*} [Fintype ι] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {f g : (ι → E3) → E3 → ℝ}
    (hf : Continuous (Function.uncurry f)) (hg : Continuous (Function.uncurry g)) :
    (∫ x' in boxPiSet ι ℓ, ∫ s in boxL ℓ, f x' s * g x' s) ^ 2
      ≤ (∫ x' in boxPiSet ι ℓ, ∫ s in boxL ℓ, (f x' s) ^ 2)
        * (∫ x' in boxPiSet ι ℓ, ∫ s in boxL ℓ, (g x' s) ^ 2) := by
  have hK : IsCompact (boxPiSet ι ℓ ×ˢ boxL ℓ) :=
    (isCompact_boxPiSet hℓ).prod (isCompact_boxL2 hℓ)
  -- the product of the two restricted box measures is the volume restricted to the product box
  have hprod : ((volume : Measure (ι → E3)).restrict (boxPiSet ι ℓ)).prod
        ((volume : Measure E3).restrict (boxL ℓ))
      = (volume : Measure ((ι → E3) × E3)).restrict (boxPiSet ι ℓ ×ˢ boxL ℓ) := by
    rw [MeasureTheory.Measure.prod_restrict,
      MeasureTheory.Measure.volume_eq_prod (ι → E3) E3]
  have hInt : Integrable (fun z : (ι → E3) × E3 => f z.1 z.2 * g z.1 z.2)
      (((volume : Measure (ι → E3)).restrict (boxPiSet ι ℓ)).prod
        ((volume : Measure E3).restrict (boxL ℓ))) := by
    rw [hprod]
    exact (hf.mul hg).continuousOn.integrableOn_compact hK
  have hfm : MemLp (fun z : (ι → E3) × E3 => f z.1 z.2) 2
      (((volume : Measure (ι → E3)).restrict (boxPiSet ι ℓ)).prod
        ((volume : Measure E3).restrict (boxL ℓ))) := by
    refine (MeasureTheory.memLp_two_iff_integrable_sq_norm ?_).mpr ?_
    · exact hf.aestronglyMeasurable
    · rw [hprod]
      exact ((hf.norm.pow 2).continuousOn).integrableOn_compact hK
  have hgm : MemLp (fun z : (ι → E3) × E3 => g z.1 z.2) 2
      (((volume : Measure (ι → E3)).restrict (boxPiSet ι ℓ)).prod
        ((volume : Measure E3).restrict (boxL ℓ))) := by
    refine (MeasureTheory.memLp_two_iff_integrable_sq_norm ?_).mpr ?_
    · exact hg.aestronglyMeasurable
    · rw [hprod]
      exact ((hg.norm.pow 2).continuousOn).integrableOn_compact hK
  have hCS := Work.BoseFixB1S.integral_mul_sq_le_of_memLp hfm hgm
  have hIntF : Integrable (fun z : (ι → E3) × E3 => (f z.1 z.2) ^ 2)
      (((volume : Measure (ι → E3)).restrict (boxPiSet ι ℓ)).prod
        ((volume : Measure E3).restrict (boxL ℓ))) := by
    rw [hprod]
    exact ((hf.pow 2).continuousOn).integrableOn_compact hK
  have hIntG : Integrable (fun z : (ι → E3) × E3 => (g z.1 z.2) ^ 2)
      (((volume : Measure (ι → E3)).restrict (boxPiSet ι ℓ)).prod
        ((volume : Measure E3).restrict (boxL ℓ))) := by
    rw [hprod]
    exact ((hg.pow 2).continuousOn).integrableOn_compact hK
  -- Fubini: the iterated integrals are the product-measure integrals
  have e1 := MeasureTheory.integral_integral (f := fun x' s => f x' s * g x' s) hInt
  have e2 := MeasureTheory.integral_integral (f := fun x' s => (f x' s) ^ 2) hIntF
  have e3 := MeasureTheory.integral_integral (f := fun x' s => (g x' s) ^ 2) hIntG
  rw [e1, e2, e3]
  exact hCS

theorem imgFibre2_deriv_sq_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    {F₁ G : Submission.BoseGases.X n → ℝ} (hF₁ : ContDiff ℝ (⊤ : ℕ∞) F₁)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hF₁ind : ∀ (x : Submission.BoseGases.X n) (t : EuclideanSpace ℝ (Fin 3)),
      F₁ (Function.update x p.1 t) = F₁ x)
    (v u : EuclideanSpace ℝ (Fin 3)) (j : Fin 3) :
    (fderiv ℝ (fun u' : EuclideanSpace ℝ (Fin 3) => Work.BoseBoxFock.imgFibre₂ ℓ p F₁ G u' v) u
        (EuclideanSpace.single j (1 : ℝ))) ^ 2
      ≤ ((ℓ ^ 3)⁻¹) ^ 2
        * (∫ x' in Work.BoseBoxFock.boxPiSet (Work.BoseBoxFock.pairFib2 n p) ℓ,
            ∫ s in Work.BoseK15.corpusBox.boxL ℓ,
              (F₁ (Work.BoseBoxFock.insertCoord2 p u s x')) ^ 2)
        * (∫ x' in Work.BoseBoxFock.boxPiSet (Work.BoseBoxFock.pairFib2 n p) ℓ,
            ∫ s in Work.BoseK15.corpusBox.boxL ℓ,
              (fderiv ℝ G (Work.BoseBoxFock.insertCoord2 p u v x')
                (Work.BoseBoxFock.slotDirVec p.1 j)) ^ 2) := by
  -- the derivative formula: the `u`-derivative falls on `G` alone, `F₁` being `p.1`-independent
  rw [Work.BoseBoxFock.fderiv_imgFibre₂_fst_apply hℓ p hF₁ hG hF₁ind v u j]
  -- continuity of the two integrands on the product box
  have hf : Continuous (Function.uncurry (fun (x' : pairFib2 n p → E3) (s : E3) =>
      F₁ (Work.BoseBoxFock.insertCoord2 p 0 s x'))) :=
    hF₁.continuous.comp (Work.BoseBoxFock.contDiff_insertCoord2_comp p
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
        (fun _ : (pairFib2 n p → E3) × E3 => (0 : E3)))
      contDiff_snd contDiff_fst).continuous
  have hg : Continuous (Function.uncurry (fun (x' : pairFib2 n p → E3) (_ : E3) =>
      (fderiv ℝ G (Work.BoseBoxFock.insertCoord2 p u v x'))
        (Work.BoseBoxFock.slotDirVec p.1 j))) := by
    have hins1 : Continuous (fun z : (pairFib2 n p → E3) × E3 =>
        Work.BoseBoxFock.insertCoord2 p u v z.1) :=
      (Work.BoseBoxFock.contDiff_insertCoord2_comp p
        (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
          (fun _ : (pairFib2 n p → E3) × E3 => u))
        (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
          (fun _ : (pairFib2 n p → E3) × E3 => v))
        contDiff_fst).continuous
    have hfd : Continuous (fun z : (pairFib2 n p → E3) × E3 =>
        fderiv ℝ G (Work.BoseBoxFock.insertCoord2 p u v z.1)) :=
      (hG.continuous_fderiv (by simp)).comp hins1
    exact hfd.clm_apply continuous_const
  -- the Cauchy–Schwarz inequality for the box integral
  have hcs : (∫ x' in boxPiSet (pairFib2 n p) ℓ, ∫ s in boxL ℓ,
        F₁ (Work.BoseBoxFock.insertCoord2 p 0 s x') *
          (fderiv ℝ G (Work.BoseBoxFock.insertCoord2 p u v x'))
            (Work.BoseBoxFock.slotDirVec p.1 j)) ^ 2
      ≤ (∫ x' in boxPiSet (pairFib2 n p) ℓ, ∫ s in boxL ℓ,
          (F₁ (Work.BoseBoxFock.insertCoord2 p 0 s x')) ^ 2)
        * (∫ x' in boxPiSet (pairFib2 n p) ℓ, ∫ s in boxL ℓ,
            ((fderiv ℝ G (Work.BoseBoxFock.insertCoord2 p u v x'))
              (Work.BoseBoxFock.slotDirVec p.1 j)) ^ 2) :=
    boxPi_cauchy_schwarz hℓ hf hg
  -- the `F₁`-factor is `u`-independent, so the second moment of the target is the one above
  have hAeq : (∫ x' in boxPiSet (pairFib2 n p) ℓ, ∫ s in boxL ℓ,
        (F₁ (Work.BoseBoxFock.insertCoord2 p u s x')) ^ 2)
      = (∫ x' in boxPiSet (pairFib2 n p) ℓ, ∫ s in boxL ℓ,
          (F₁ (Work.BoseBoxFock.insertCoord2 p 0 s x')) ^ 2) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x' => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [Work.BoseBoxFock.insertCoord2_indep_fst p hF₁ind s x' u 0]
  rw [hAeq, mul_pow, mul_assoc]
  exact mul_le_mul_of_nonneg_left hcs (sq_nonneg _)

end Work.BoseBoxFock
