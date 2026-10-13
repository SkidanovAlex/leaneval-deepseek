/-
Copyright: work module for the Elgindi finite-time singularity project (area `FTS.EllSol`).

# `dthBound` — the angular Hardy transfer for `NiceFlat` data

`Work.FTS.EllSol.FlatFT.dthBound`: if the *second* angular derivative of a `NiceFlat` datum is
in the weighted space `L²(Iθ, sin(2θ)^{-η} dθ)`, then so are the *first* derivative and the datum
itself.

The point is that the weight `sin(2θ)^{-η}`, `η = 99/100`, is *integrable* at both endpoints
(`η < 1`), so no boundary conditions on the slices are needed: for each `z` the slice
`θ ↦ g z θ` is `C²` on `(0,π/2)`, and for a fixed interior reference angle `θ₁`

`(∂_θg(z,θ) - ∂_θg(z,θ₁))² ≤ (∫_{θ₁}^{θ} sin(2t)^{η} dt)·(∫_{θ₁}^{θ}(∂_θ²g(z,t))² sin(2t)^{-η} dt)
 ≤ (π/2)·∫_{Iθ}(∂_θ²g(z,t))² sin(2t)^{-η} dt`

by Cauchy–Schwarz (the first factor is `≤ π/2` because `sin(2t)^{η} ≤ 1`).  The reference value
`∂_θg(z,θ₁)` is a *continuous, compactly supported* function of `z` (compact support comes from
the uniform compact support of `g` in `t`), hence in `L²`; the same applies to `g(z,θ₁)`.  The
two pointwise slice bounds are then integrated in `z` against the (integrable) slice integral of
`(∂_θ²g)²sin(2θ)^{-η}` using Tonelli for the product measure `volume.prod (volume.restrict Iθ)`,
and the two conclusions follow.

The slice inequalities are the siblings `slicePthBound`, `sliceFunBound`; the `L²`-in-`z`
statement about the two reference values is `niceFlatSliceL2`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.FTS.EllipticEst.RegQ.pthU_slot_alg
import Submission.Work.FTS.EllSol.FlatFT.Defs
import Submission.Work.FTS.EllSol.FlatFT.slicePthBound
import Submission.Work.FTS.EllSol.FlatFT.sliceFunBound
import Submission.Work.FTS.EllSol.FlatFT.niceFlatSliceL2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.FlatFT

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false

/-- The strip `ℝ × (0,π/2)` on which `NiceFlat` data are smooth. -/
private abbrev strip : Set (ℝ × ℝ) := Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)

private lemma isOpen_strip : IsOpen strip := isOpen_univ.prod isOpen_Ioo

private lemma measurableSet_strip : MeasurableSet strip :=
  MeasurableSet.univ.prod measurableSet_Ioo

private lemma sin_two_pos_of_mem_strip {p : ℝ × ℝ} (hp : p ∈ strip) :
    0 < Real.sin (2 * p.2) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2, Real.pi_pos])

private lemma sin_two_nonneg_of_mem_Icc {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The angular weight `sin(2θ)^{-η}` is nonnegative on `Iθ`. -/
private lemma wE_nonneg_of_mem_Icc {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
  Real.rpow_nonneg (sin_two_nonneg_of_mem_Icc hθ) _

/-- An (uncurried) function continuous on the strip has its square times `sin(2θ)^{-η}`
strongly measurable for the product of Lebesgue measure with the restriction to `Iθ`. -/
private lemma aesm_joint {f : ℝ → ℝ → ℝ} (hf : ContinuousOn (Function.uncurry f) strip) :
    AEStronglyMeasurable (fun p : ℝ × ℝ =>
        (f p.1 p.2) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      ((volume : Measure ℝ).prod (volume.restrict Work.Spaces.Iθ)) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      (f p.1 p.2) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) strip :=
    (hf.pow 2).mul
      (((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
        (fun p hp => Or.inl (ne_of_gt (sin_two_pos_of_mem_strip hp))))
  have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (f p.1 p.2) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      ((volume.prod volume).restrict strip) :=
    hcont.aestronglyMeasurable measurableSet_strip
  have hvol : (volume : Measure (ℝ × ℝ)) = Measure.prod (volume : Measure ℝ) volume := rfl
  have hstrip : ((volume : Measure (ℝ × ℝ)).restrict strip)
      = (volume : Measure ℝ).prod (volume.restrict Work.Spaces.Iθ) := by
    rw [hvol, ← Measure.prod_restrict, Measure.restrict_univ]
    congr 1
    exact Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
  rw [← hstrip]
  exact h1

theorem dthBound : ∀ (g : ℝ → ℝ → ℝ), Work.FTS.EllSol.FlatFT.NiceFlat g →
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pth (Work.Spaces.pth g) p.1 p.2) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) (Set.univ ×ˢ Work.Spaces.Iθ) →
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pth g p.1 p.2) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) (Set.univ ×ˢ Work.Spaces.Iθ) ∧
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (g p.1 p.2) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) (Set.univ ×ˢ Work.Spaces.Iθ) := by
  intro g hg h2
  set ν : Measure ℝ := volume.restrict Work.Spaces.Iθ with hν
  have hθ₁ : (Real.pi / 4) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  -- the hypothesis in product form
  have h2' : Integrable (fun p : ℝ × ℝ =>
      (Work.Spaces.pth (Work.Spaces.pth g) p.1 p.2) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      ((volume : Measure ℝ).prod ν) := by
    have hvol : (volume : Measure (ℝ × ℝ)) = Measure.prod (volume : Measure ℝ) volume := rfl
    rw [IntegrableOn, hvol, ← Measure.prod_restrict, Measure.restrict_univ] at h2
    rw [hν]
    exact h2
  -- a.e. slice integrability of the second-derivative slot, and its `z`-integral
  have h2slice : ∀ᵐ z ∂(volume : Measure ℝ), Integrable (fun θ : ℝ =>
      (Work.Spaces.pth (Work.Spaces.pth g) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ν := h2'.prod_right_ae
  have hNint : Integrable (fun z : ℝ => ∫ θ, (Work.Spaces.pth (Work.Spaces.pth g) z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ∂ν) volume := by
    have h := h2'.integral_norm_prod_left
    refine h.congr (Filter.Eventually.of_forall (fun z => ?_))
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (wE_nonneg_of_mem_Icc hθ))
  -- strong measurability of the two joint integrands
  have hsmP1 : ContinuousOn (Function.uncurry (Work.Spaces.pth g)) strip :=
    (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_pth_fin isOpen_strip hg.1).continuousOn
  have hsmP0 : ContinuousOn (Function.uncurry g) strip := hg.1.continuousOn
  have haesm1 : AEStronglyMeasurable (fun p : ℝ × ℝ => (Work.Spaces.pth g p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      ((volume : Measure ℝ).prod ν) := by
    rw [hν]
    exact aesm_joint hsmP1
  have haesm0 : AEStronglyMeasurable (fun p : ℝ × ℝ => (g p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      ((volume : Measure ℝ).prod ν) := by
    rw [hν]
    exact aesm_joint hsmP0
  -- the reference values at the fixed interior angle are in `L²(dz)`
  obtain ⟨hc0, hc1⟩ := niceFlatSliceL2 g hg hθ₁
  -- ===== first half: the first derivative =====
  have hF1slice : ∀ᵐ z ∂(volume : Measure ℝ), Integrable (fun θ : ℝ =>
      (Work.Spaces.pth g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ν := by
    filter_upwards [h2slice] with z hz
    exact (slicePthBound g hg.1 hθ₁ hz).1
  have hF1bound : ∀ᵐ z ∂(volume : Measure ℝ),
      (∫ θ, (Work.Spaces.pth g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ∂ν)
        ≤ (2 * (Real.pi / 2) * (∫ θ, (Work.Spaces.pth (Work.Spaces.pth g) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ∂ν)
            + 2 * (Work.Spaces.pth g z (Real.pi / 4)) ^ 2)
          * (∫ θ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ∂ν) := by
    filter_upwards [h2slice] with z hz
    exact (slicePthBound g hg.1 hθ₁ hz).2
  have hAESMout1 : AEStronglyMeasurable (fun z : ℝ =>
      ∫ θ, (Work.Spaces.pth g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ∂ν)
      (volume : Measure ℝ) := haesm1.integral_prod_right'
  have hSconst : Integrable (fun z : ℝ =>
      2 * (Real.pi / 2) * (∫ θ, (Work.Spaces.pth (Work.Spaces.pth g) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ∂ν)
        + 2 * (Work.Spaces.pth g z (Real.pi / 4)) ^ 2) volume :=
    (hNint.const_mul (2 * (Real.pi / 2))).add (hc1.const_mul 2)
  have hB : Integrable (fun z : ℝ => |(2 * (Real.pi / 2) *
        (∫ θ, (Work.Spaces.pth (Work.Spaces.pth g) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ∂ν)
        + 2 * (Work.Spaces.pth g z (Real.pi / 4)) ^ 2)
      * (∫ θ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ∂ν)|) volume :=
    (hSconst.mul_const (∫ θ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ∂ν)).abs
  have hF1out : Integrable (fun z : ℝ =>
      ∫ θ, (Work.Spaces.pth g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ∂ν)
      volume := by
    refine Integrable.mono' hB hAESMout1 ?_
    filter_upwards [hF1bound] with z hz
    rw [Real.norm_of_nonneg (integral_nonneg_of_ae ?_)]
    · exact le_trans hz (le_abs_self _)
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (sq_nonneg _) (wE_nonneg_of_mem_Icc hθ)
  have hF1 : Integrable (fun p : ℝ × ℝ => (Work.Spaces.pth g p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      ((volume : Measure ℝ).prod ν) := by
    rw [integrable_prod_iff haesm1]
    refine ⟨hF1slice, ?_⟩
    refine hF1out.congr (Filter.Eventually.of_forall (fun z => ?_))
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact (Real.norm_of_nonneg (mul_nonneg (sq_nonneg _)
      (wE_nonneg_of_mem_Icc hθ))).symm
  have hF1on : IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pth g p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) (Set.univ ×ˢ Work.Spaces.Iθ) := by
    have hvol : (volume : Measure (ℝ × ℝ)) = Measure.prod (volume : Measure ℝ) volume := rfl
    rw [IntegrableOn, hvol, ← Measure.prod_restrict, Measure.restrict_univ, ← hν]
    exact hF1
  -- ===== second half: the datum itself =====
  have hN1int : Integrable (fun z : ℝ => ∫ θ, (Work.Spaces.pth g z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ∂ν) volume := hF1out
  have hF0slice : ∀ᵐ z ∂(volume : Measure ℝ), Integrable (fun θ : ℝ =>
      (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ν := by
    filter_upwards [hF1slice] with z hz
    exact (sliceFunBound g hg.1 hθ₁ hz).1
  have hF0bound : ∀ᵐ z ∂(volume : Measure ℝ),
      (∫ θ, (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ∂ν)
        ≤ (2 * (Real.pi / 2) * (∫ θ, (Work.Spaces.pth g z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ∂ν)
            + 2 * (g z (Real.pi / 4)) ^ 2)
          * (∫ θ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ∂ν) := by
    filter_upwards [hF1slice] with z hz
    exact (sliceFunBound g hg.1 hθ₁ hz).2
  have hAESMout0 : AEStronglyMeasurable (fun z : ℝ =>
      ∫ θ, (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ∂ν)
      (volume : Measure ℝ) := haesm0.integral_prod_right'
  have hB0 : Integrable (fun z : ℝ => |(2 * (Real.pi / 2) *
        (∫ θ, (Work.Spaces.pth g z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ∂ν)
        + 2 * (g z (Real.pi / 4)) ^ 2)
      * (∫ θ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ∂ν)|) volume :=
    (((hN1int.const_mul (2 * (Real.pi / 2))).add (hc0.const_mul 2)).mul_const
      (∫ θ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ∂ν)).abs
  have hF0out : Integrable (fun z : ℝ =>
      ∫ θ, (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ∂ν) volume := by
    refine Integrable.mono' hB0 hAESMout0 ?_
    filter_upwards [hF0bound] with z hz
    rw [Real.norm_of_nonneg (integral_nonneg_of_ae ?_)]
    · exact le_trans hz (le_abs_self _)
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (sq_nonneg _) (wE_nonneg_of_mem_Icc hθ)
  have hF0 : Integrable (fun p : ℝ × ℝ => (g p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      ((volume : Measure ℝ).prod ν) := by
    rw [integrable_prod_iff haesm0]
    refine ⟨hF0slice, ?_⟩
    refine hF0out.congr (Filter.Eventually.of_forall (fun z => ?_))
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact (Real.norm_of_nonneg (mul_nonneg (sq_nonneg _)
      (wE_nonneg_of_mem_Icc hθ))).symm
  have hF0on : IntegrableOn (fun p : ℝ × ℝ => (g p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) (Set.univ ×ˢ Work.Spaces.Iθ) := by
    have hvol : (volume : Measure (ℝ × ℝ)) = Measure.prod (volume : Measure ℝ) volume := rfl
    rw [IntegrableOn, hvol, ← Measure.prod_restrict, Measure.restrict_univ, ← hν]
    exact hF0
  exact ⟨hF1on, hF0on⟩

end

end Work.FTS.EllSol.FlatFT
