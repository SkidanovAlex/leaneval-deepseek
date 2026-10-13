import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS_RegExport.C4.ae_integrableOn_mixed_sq_w_C4
import Submission.Work.FTS_RegExport.C4.HkSqSwap_C4
import Submission.Work.FTS_RegExport.RXA1w.Helpers
import Submission.Work.Spaces.Slots.lintegral_DzIter_le_HkSq_smooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 800000

/-! ## The pointwise domination of a slot by the `ℋ⁴`-integrand

Both kinds of slot occurring in `slot_slice_data` — a mixed slot `D_z^j D_θ^i f` with `1 ≤ i`
and a pure radial slot `D_z^j f` — are dominated, on the open quadrant, by the single
`ℋ⁴`-integrand `HkIntegrand α 4 f`:

* for a mixed slot the angular weight `w_θ = sin(2θ)^{-γ/2}` of `HkIntegrand` is `≥ 1` there
  (`Work.FTS.StrongEps.SupPort.AuxMixSq.mixed_sq_w_le_HkIntegrand`);
* for a pure radial slot the extra factor `sin(2θ)^{-η} ≥ 1` in the matching summand of
  `HkIntegrand` is discarded (`Work.Spaces.Slots.one_le_sin_two_rpow_neg_eta`).

This single pointwise inequality is what makes all three conjuncts of `slot_slice_data` follow
from the two `C⁴` inputs `h4` (smoothness of `f` on the open quadrant) and `hmem`
(honesty of the `ℋ⁴`-norm), together with `Work.FTS_RegExport.C4.HkSqSwap_C4`. -/

/-- A pure radial slot with the radial weight `w` is dominated by the `ℋ⁴`-integrand on the
open quadrant (the angular factor `sin(2θ)^{-η}` of the corresponding summand is `≥ 1`). -/
theorem dzSlot_sq_w_le_HkIntegrand {α : ℝ} {f : ℝ → ℝ → ℝ} {j : ℕ} (hj : j ≤ 4) {s θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (Work.Spaces.DzIter j f s θ) ^ 2 * (Work.Spaces.w s) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 f s θ := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hone : (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    Work.Spaces.Slots.one_le_sin_two_rpow_neg_eta hθ.1 hθ.2
  have hkey := Work.Spaces.sq_le_HkIntegrand_z α 4 f s θ j hj
  have heq : (Work.Spaces.DzIter j f s θ
      * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.DzIter j f s θ) ^ 2 * (Work.Spaces.w s) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    have hs : 0 ≤ Real.sin (2 * θ) := hsin.le
    have hsq : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
        = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
      norm_num
    rw [mul_pow, div_pow, hsq, div_eq_mul_inv, ← Real.rpow_neg hs (Work.Spaces.eta)]
    ring
  calc (Work.Spaces.DzIter j f s θ) ^ 2 * (Work.Spaces.w s) ^ 2
      = (Work.Spaces.DzIter j f s θ) ^ 2 * (Work.Spaces.w s) ^ 2 * 1 := by ring
    _ ≤ (Work.Spaces.DzIter j f s θ) ^ 2 * (Work.Spaces.w s) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        mul_le_mul_of_nonneg_left hone (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = (Work.Spaces.DzIter j f s θ
          * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := heq.symm
    _ ≤ Work.Spaces.HkIntegrand α 4 f s θ := hkey

/-- Every admissible slot `(j,i)` of `slot_slice_data` is dominated by the `ℋ⁴`-integrand on
the open quadrant. -/
theorem slot_sq_w_le_HkIntegrand {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} (j i : ℕ)
    (hadm : (1 ≤ i ∧ i + j ≤ 4) ∨ (i = 0 ∧ j ≤ 4)) {s σ : ℝ}
    (hσ : σ ∈ Set.Ioo 0 (π / 2)) :
    (Work.Spaces.mixed j i f s σ) ^ 2 * (Work.Spaces.w s) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 f s σ := by
  rcases hadm with ⟨hi, hij⟩ | ⟨hi0, hj⟩
  · exact Work.FTS.StrongEps.SupPort.AuxMixSq.mixed_sq_w_le_HkIntegrand hα j i hi hij hσ
  · subst hi0
    simpa only [Work.Spaces.mixed_zero_right] using
      dzSlot_sq_w_le_HkIntegrand (α := α) (f := f) (j := j) hj (s := s) (θ := σ) hσ

/-! ## The main statement -/

theorem slot_slice_data {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) (j i : ℕ)
    (hadm : (1 ≤ i ∧ i + j ≤ 4) ∨ (i = 0 ∧ j ≤ 4)) :
    AEMeasurable
        (fun σ => ∫ s in Work.Spaces.Iz,
          (Work.Spaces.mixed j i f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) ∧
      (∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        MeasureTheory.IntegrableOn
          (fun s => (Work.Spaces.mixed j i f s σ) ^ 2 * (Work.Spaces.w s) ^ 2) Work.Spaces.Iz) ∧
      (∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz,
          (Work.Spaces.mixed j i f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
        ≤ Work.Spaces.HkSq α 4 f := by
  -- The two disjuncts of `hadm` both give `i + j ≤ 4`, which is all the smoothness API needs.
  have hsum : i + j ≤ 4 := by rcases hadm with ⟨_, h⟩ | ⟨h, hj⟩ <;> omega
  -- The angular-slice integrability of the `ℋ⁴`-integrand and the value of its two-fold
  -- integral come from the `C⁴` Tonelli exchange.
  obtain ⟨hswap, hIntHkθ, hAeIntHk⟩ := Work.FTS_RegExport.C4.HkSqSwap_C4 h4 hmem
  -- Joint continuity of the (uncurried) slot integrand on the open quadrant.
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.mixed j i f p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have hmix : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i f p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      Work.FTS.StrongEps.continuousOn_mixed_of_contDiffOn h4 hsum
    have hw : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      Work.FTS_RegExport.C4.continuousOn_w_sq.comp continuousOn_fst (fun p hp => hp.1)
    exact (hmix.pow 2).mul hw
  -- Measurability of the parametrised radial integral, from a.e. strong measurability of the
  -- uncurried integrand and `AEStronglyMeasurable.integral_prod_right'`.
  have hAEM : AEMeasurable (fun σ => ∫ s in Work.Spaces.Iz,
      (Work.Spaces.mixed j i f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have hG : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ =>
        (Work.Spaces.mixed j i f p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      Work.Spaces.aesm_of_continuousOn_Qd _ hcont
    have h2 : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ =>
        (Work.Spaces.mixed j i f p.2 p.1) ^ 2 * (Work.Spaces.w p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iz)) := hG.prod_swap
    have h3 := h2.integral_prod_right'
    exact h3.aemeasurable
  refine ⟨hAEM, ?_, ?_⟩
  · -- A.e. (in the angle) integrability of the radial slice, by domination from the integrable
    -- radial slice of the `ℋ⁴`-integrand.
    filter_upwards [Work.FTS_RegExport.C4.ae_integrableOn_HkIntegrand_slice_C4 h4 hmem,
      Work.FTS_RegExport.C4.ae_mem_Ioo_of_Iθ] with σ hIntσ hσ
    refine MeasureTheory.Integrable.mono' hIntσ
      (Work.FTS_RegExport.C4.aesm_zslice_mixed_sq_w_C4 h4 j i hsum hσ) ?_
    exact Filter.Eventually.of_forall fun s => by
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      exact slot_sq_w_le_HkIntegrand hα j i hadm hσ
  · -- The two-fold bound, by monotonicity of the two iterated integrals against the
    -- `ℋ⁴`-integrand whose two-fold integral is `HkSq α 4 f`.
    have hbound : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        (∫ s in Work.Spaces.Iz,
          (Work.Spaces.mixed j i f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
        ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ := by
      filter_upwards [hAeIntHk, Work.FTS_RegExport.C4.ae_mem_Ioo_of_Iθ] with σ hIntσ hσ
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun s => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hIntσ ?_
      exact Filter.Eventually.of_forall fun s => slot_sq_w_le_HkIntegrand hα j i hadm hσ
    calc ∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz,
          (Work.Spaces.mixed j i f s σ) ^ 2 * (Work.Spaces.w s) ^ 2
        ≤ ∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz,
            Work.Spaces.HkIntegrand α 4 f s σ :=
          MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun σ => integral_nonneg fun s =>
              mul_nonneg (sq_nonneg _) (sq_nonneg _)) hIntHkθ hbound
      _ = Work.Spaces.HkSq α 4 f := hswap

end

end Work.FTS_RegExport.RXT
