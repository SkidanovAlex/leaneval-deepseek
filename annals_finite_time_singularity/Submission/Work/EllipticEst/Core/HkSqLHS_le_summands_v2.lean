import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.EllipticEst.Core.Defs
import Submission.Work.EllipticEst.Core.integral_finset_sum_le
import Submission.Work.EllipticEst.Core.HkSqLHSv2Pointwise
import Submission.Work.EllipticEst.Core.HkSqLHSv2Meas
import Submission.Work.EllipticEst.Core.HkSqLHSv2Slice
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.DzDthIterCommOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The summand decomposition of `HkSq` of `α • D_z∂_θV`

`HkSq α k (α D_z∂_θV)` is, by definition, the iterated Bochner integral of the sum of squares
`HkIntegrand`; the summands of that sum are the quantities `mixIntS (D_z^r V)`,
`mixedIntS α i j V` of the deformation estimate.  This module proves the value-wise reduction

`HkSq α k (α • D_z∂_θV) ≤ α² ∑_r ∫_z mixIntS(D_z^rV) + α² ∑_{1≤i, i+j≤k} ∫_z mixedIntS α i j V`,

with constant `1`, *under the hypothesis that the majorant* (the same sum without the
integrals in `z`) *is integrable on `[0,∞)`*.  The hypothesis is exactly what the junk-value
convention of the Bochner integral needs: without it the summand-wise integrals throw away a
finite contribution that the left-hand side keeps (see the sibling
`NOTES_HkSqLHS_le_summands.md`), while with it the two sides agree.

The proof is assembled from the pieces of `Submission/Work/EllipticEst/Core/`:

* `v2_aesm_slice`, `v2_aesm_integral` : measurability of the summands in `θ` and in `z`;
* `v2_zBlock_ae`, `v2_mixedBlock_ae` : the a.e. identification of the two blocks of
  `HkIntegrand α k (α • D_z∂_θV)` with the summands (via `pth`-`D_z` and `D_θ`-`D_z`
  commutation on the open quadrant);
* `v2_slice_le` : the reduction of the inner (`θ`) integral, using
  `integral_finset_sum_le`/`integral_add_le_nonneg`;
* the outer (`z`) integral is treated with the same subadditivity lemmas and the integrability
  of the majorant.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Core

set_option autoImplicit false

theorem HkSqLHS_le_summands_v2 (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (V : ℝ → ℝ → ℝ), 0 < α →
      Work.FTS.EllipticEst.SmoothOpen V →
      MeasureTheory.IntegrableOn (fun z : ℝ =>
          α ^ 2 * (∑ r ∈ Finset.range (k + 1),
              Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
          + α ^ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              if 1 ≤ i ∧ i + j ≤ k then
                Work.EllipticEst.Core.mixedIntS α i j V z
              else 0)) Work.Spaces.Iz →
      Work.Spaces.HkSq α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ)
        ≤ C * (α ^ 2 * (∑ r ∈ Finset.range (k + 1),
                  ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
            + α ^ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k then
                  ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixedIntS α i j V z
                else 0)) := by
  refine ⟨1, one_pos, ?_⟩
  intro α V hα hV hInt
  -- ## Pointwise nonnegativity of the two families, and measurability in `z`
  have hAnnP : ∀ r : ℕ, ∀ z : ℝ, 0 ≤ mixIntS (Work.Spaces.DzIter r V) z := by
    intro r z
    rw [mixIntS]
    refine mul_nonneg (sq_nonneg _) (MeasureTheory.integral_nonneg_of_ae
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _)
          (Work.FTS.EllipticEst.thEta_nonneg hθ))))
  have hBnnP : ∀ i j : ℕ, ∀ z : ℝ, 0 ≤ mixedIntS α i j V z := by
    intro i j z
    rw [mixedIntS]
    refine mul_nonneg (sq_nonneg _) (MeasureTheory.integral_nonneg_of_ae
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _)
          (Work.FTS.EllipticEst.thGam_nonneg hθ))))
  have hAesm : ∀ r : ℕ, AEMeasurable (fun z : ℝ => mixIntS (Work.Spaces.DzIter r V) z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    intro r
    have h := v2_aesm_integral ((hV.DzIter r).pth.Dz) (-(Work.Spaces.eta))
    simpa only [mixIntS, Work.FTS.EllipticEst.thEta] using h
  have hBesm : ∀ i j : ℕ, AEMeasurable (fun z : ℝ => mixedIntS α i j V z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    intro i j
    have h := v2_aesm_integral ((hV.pth).mixed (j + 1) i) (-(Work.Spaces.gam α))
    simpa only [mixedIntS, Work.FTS.EllipticEst.thGam] using h
  -- ## Integrability of the majorant, from the hypothesis
  have hInt' : MeasureTheory.IntegrableOn (fun z : ℝ =>
      α ^ 2 * ((∑ r ∈ Finset.range (k + 1), mixIntS (Work.Spaces.DzIter r V) z)
        + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            if 1 ≤ i ∧ i + j ≤ k then mixedIntS α i j V z else 0)))
      Work.Spaces.Iz :=
    hInt.congr_fun (fun z _ => by ring) measurableSet_Ici
  -- ## The `HkSq`-side bound: the slice inequality integrated in `z`
  have hSq : Work.Spaces.HkSq α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ)
      ≤ ∫ z in Work.Spaces.Iz, α ^ 2 *
          ((∑ r ∈ Finset.range (k + 1), mixIntS (Work.Spaces.DzIter r V) z)
            + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k then mixedIntS α i j V z else 0)) := by
    rw [Work.Spaces.HkSq]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun z => MeasureTheory.integral_nonneg (fun θ =>
        Work.Spaces.HkIntegrand_nonneg α k _ z θ)))
      hInt'
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
        (fun z hz => v2_slice_le k hα hV z hz))
  -- ## The majorant side: distribute the outer integral over the summands
  have hInt_le : (∫ z in Work.Spaces.Iz, α ^ 2 *
        ((∑ r ∈ Finset.range (k + 1), mixIntS (Work.Spaces.DzIter r V) z)
          + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              if 1 ≤ i ∧ i + j ≤ k then mixedIntS α i j V z else 0)))
      ≤ α ^ 2 * ((∑ r ∈ Finset.range (k + 1),
            ∫ z in Work.Spaces.Iz, mixIntS (Work.Spaces.DzIter r V) z)
          + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              if 1 ≤ i ∧ i + j ≤ k then
                ∫ z in Work.Spaces.Iz, mixedIntS α i j V z
              else 0)) := by
    rw [MeasureTheory.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg α)
    refine le_trans (integral_add_le_nonneg
      (aemeasurable_finset_sum_apply (fun r _ => hAesm r))
      (aemeasurable_finset_sum_apply
        (fun i _ => aemeasurable_finset_sum_apply (fun j _ => by
          by_cases hc : 1 ≤ i ∧ i + j ≤ k
          · simp only [if_pos hc]
            exact hBesm i j
          · simp only [if_neg hc]
            exact aemeasurable_const)))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
        (fun z _ => Finset.sum_nonneg (fun r _ => hAnnP r z)))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
        (fun z _ => Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by
          by_cases hc : 1 ≤ i ∧ i + j ≤ k
          · simp only [if_pos hc]
            exact hBnnP i j z
          · simp only [if_neg hc]
            exact le_refl 0))))) ?_
    refine add_le_add ?_ ?_
    · exact integral_finset_sum_le (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
        (s := Finset.range (k + 1))
        (f := fun r : ℕ => fun z : ℝ => mixIntS (Work.Spaces.DzIter r V) z)
        (fun r _ => hAesm r)
        (fun r _ => Filter.Eventually.of_forall (fun z => hAnnP r z))
    · refine le_trans (integral_finset_sum_le (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
        (s := Finset.range (k + 1))
        (f := fun i : ℕ => fun z : ℝ => ∑ j ∈ Finset.range (k + 1),
            if 1 ≤ i ∧ i + j ≤ k then mixedIntS α i j V z else 0)
        (fun i _ => aemeasurable_finset_sum_apply (fun j _ => by
          by_cases hc : 1 ≤ i ∧ i + j ≤ k
          · simp only [if_pos hc]
            exact hBesm i j
          · simp only [if_neg hc]
            exact aemeasurable_const))
        (fun i _ => Filter.Eventually.of_forall (fun z => Finset.sum_nonneg (fun j _ => by
          by_cases hc : 1 ≤ i ∧ i + j ≤ k
          · simp only [if_pos hc]
            exact hBnnP i j z
          · simp only [if_neg hc]
            exact le_refl 0)))) ?_
      refine Finset.sum_le_sum (fun i _ => ?_)
      refine le_trans (integral_finset_sum_le (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
        (s := Finset.range (k + 1))
        (f := fun j : ℕ => fun z : ℝ =>
          if 1 ≤ i ∧ i + j ≤ k then mixedIntS α i j V z else 0)
        (fun j _ => by
          by_cases hc : 1 ≤ i ∧ i + j ≤ k
          · simp only [if_pos hc]
            exact hBesm i j
          · simp only [if_neg hc]
            exact aemeasurable_const)
        (fun j _ => by
          by_cases hc : 1 ≤ i ∧ i + j ≤ k
          · simp only [if_pos hc]
            exact Filter.Eventually.of_forall (fun z => hBnnP i j z)
          · simp only [if_neg hc]
            exact Filter.Eventually.of_forall (fun _ => le_refl 0))) ?_
      refine Finset.sum_le_sum (fun j _ => ?_)
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · simp only [if_pos hc]
        exact le_refl _
      · simp only [if_neg hc]
        exact le_of_eq (MeasureTheory.integral_zero ℝ ℝ)
  calc Work.Spaces.HkSq α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ)
      ≤ ∫ z in Work.Spaces.Iz, α ^ 2 *
          ((∑ r ∈ Finset.range (k + 1), mixIntS (Work.Spaces.DzIter r V) z)
            + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k then mixedIntS α i j V z else 0)) := hSq
    _ ≤ α ^ 2 * ((∑ r ∈ Finset.range (k + 1),
            ∫ z in Work.Spaces.Iz, mixIntS (Work.Spaces.DzIter r V) z)
          + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              if 1 ≤ i ∧ i + j ≤ k then
                ∫ z in Work.Spaces.Iz, mixedIntS α i j V z
              else 0)) := hInt_le
    _ = 1 * (α ^ 2 * (∑ r ∈ Finset.range (k + 1),
                  ∫ z in Work.Spaces.Iz, mixIntS (Work.Spaces.DzIter r V) z)
            + α ^ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k then
                  ∫ z in Work.Spaces.Iz, mixedIntS α i j V z
                else 0)) := by ring

end Work.EllipticEst.Core
