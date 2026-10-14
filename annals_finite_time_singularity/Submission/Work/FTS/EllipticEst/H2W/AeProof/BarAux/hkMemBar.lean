import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.H2W.AeProof.BarAux.BarSliceTools
import Submission.Work.FTS.EllipticEst.Honest.I4UpperHonest
import Submission.Work.FTS.EllipticEst.Honest.Yc.HonSliceRightTendstoYc
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.SolutionDelivery.Scaling.Main
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.mixed_mul_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.AeProof.BarAux

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000

/-! ## Two elementary regularity facts for the quotient `u / cos θ` -/

/-- The uncurried quotient `(z,θ) ↦ u z θ / cos θ` is `C^n` on the open quadrant whenever `u`
is: `cos θ` is smooth and nonzero there.  (`Function.uncurry (f / g)` is definitionally
`Function.uncurry f / fun p => g p.2`, whence the `convert`.) -/
private lemma contDiffOn_uncurry_divCos (u : ℝ → ℝ → ℝ) (n : ℕ)
    (hu : ContDiffOn ℝ n (Function.uncurry u) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ n (Function.uncurry (fun z θ => u z θ / Real.cos θ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hh := hu.div (contDiffOn_snd.cos : ContDiffOn ℝ _ (fun p : ℝ × ℝ => Real.cos p.2) _)
    (fun p hp => ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hp.2.1, Real.pi_pos], hp.2.2⟩))
  convert hh using 1
  ext p
  rfl

/-- For `z > 0` the slice integrand `θ ↦ σ θ · (u z θ / cos θ)²` is a.e. strongly measurable on
`Iθ`: off the two endpoints `θ = 0, π/2` (a null set) the slice `u z ·` is `C²` and
`θ ↦ sin(2θ)^{-η}` is continuous. -/
private lemma aestronglyMeasurable_sEta_mul_divCos_sq (u : ℝ → ℝ → ℝ) {z : ℝ} (_hz : 0 < z)
    (hsmz : ContDiffOn ℝ 2 (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2))) :
    AEStronglyMeasurable (fun θ => Work.FTS.EllipticEst.sEta θ * (u z θ / Real.cos θ) ^ 2)
      (volume.restrict Work.Spaces.Iθ) := by
  have hres : volume.restrict Work.Spaces.Iθ
      = volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ))
        (b := Real.pi / 2)).symm
  rw [hres]
  have hcont : ContinuousOn (fun θ : ℝ => u z θ / Real.cos θ) (Set.Ioo 0 (Real.pi / 2)) :=
    hsmz.continuousOn.div Real.continuous_cos.continuousOn
      (fun θ hθ => ne_of_gt (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩))
  exact ((Work.FTS.EllipticEst.Honest.continuousOn_sig_Ioo.mul
    (hcont.pow 2)).aestronglyMeasurable measurableSet_Ioo)

/-- **The `ℋ⁰`-membership of `u / cos θ`** for an `AeData` datum with `HkMem α 0 u` (the first
conjunct of `Work.FTS.EllipticEst.H2W.AeProof.aeBarHkMem`).  All ingredients are *proved*
library lemmas, and `Submission/Work/FTS/EllipticEst/H2W/AeProof/aeBarHkMem.lean` contains the
proved helpers `sliceDivCosSqIntegrable`, `sliceBarLe`, `barHkInt`, `innerEq` (import it, or
reprove them locally).

Route:
* slicewise, for `z > 0`: `Honest.sliceInterp` (fed by `Honest.HkMemSliceSqSigma` for `u` and
  for `pthIter 2 u`) gives the `σ`-integrability and bound of `(∂_θu)²σ`; then
  `Honest.sliceBarSq2` — its limit hypothesis at `π/2` follows from `AeSliceRightTendsto`
  together with the finite derivative limit at `π/2` obtained from the `σ`-square-integrability
  of `∂_θθu` via
  `Work.FTS.EllipticEst.Honest.exists_tendsto_nhdsWithin_Iio_of_integrableOn_deriv` — gives
  the slicewise integrability of `(u z θ/cos θ)²σ`; transfer to
  `HkIntegrand α 0 (u/cos) z θ = w z ^ 2 * ((u/cos)²σ)` on `Iθ` (`barHkInt`-style identity);
* for the outer integral, dominate `∫_θ HkIntegrand α 0 (u/cos) z θ` pointwise in `z` by
  `1010000 * (∫_θ HkIntegrand α 0 u z θ + ∫_θ HkIntegrand α 0 (pthIter 2 u) z θ)`
  (the slicewise bound multiplied by `w z ^ 2`) and use `Integrable.mono'` with the dominating
  function supplied by the two `HkMem` hypotheses; the a.e. strong measurability of the
  dominated function comes from `Honest.aemeasurable_sliceSigmaLin` (applied to
  `fun z θ => u z θ / cos θ`, `C^∞` on the open quadrant) composed with
  `ENNReal.measurable_toReal` and multiplication by `Measurable (fun z => w z ^ 2)`, together
  with `MeasureTheory.integral_eq_lintegral_of_nonneg_ae` for each `z > 0`; at `z = 0`,
  `w 0 = 0` kills both sides. -/
theorem hkMemBar : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G → Work.Spaces.HkMem α 0 u →
      Work.Spaces.HkMem α 0 (fun z θ => u z θ / Real.cos θ) := by
  intro α u G h hmu
  set v : ℝ → ℝ → ℝ := fun z θ => u z θ / Real.cos θ with hv
  refine ⟨?_, ?_⟩
  · -- ## The slicewise integrability
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | h0
    · -- at `z = 0` the radial weight `w` vanishes, hence so does the integrand
      have hw : Work.Spaces.w z = 0 := by
        rw [← h0, Work.Spaces.w]
        norm_num
      refine integrableOn_zero.congr ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      show (0 : ℝ) = Work.Spaces.HkIntegrand α 0 v z θ
      rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq]
      rw [hw]
      ring
    · -- for `z > 0`, divide out the constant `(w z)²`
      have hbase := Work.FTS.EllipticEst.H2W.AeProof.sliceDivCosSqIntegrable α u G h hmu h0
      have h2 := hbase.const_mul ((Work.Spaces.w z) ^ 2)
      refine h2.congr ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      show (Work.Spaces.w z) ^ 2 * ((v z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        = Work.Spaces.HkIntegrand α 0 v z θ
      rw [Work.FTS.EllipticEst.H2W.AeProof.barHkInt α v hθ]
  · -- ## The `z`-integrability, by domination
    -- `Iz` and `(0,∞)` differ by the null set `{0}`, so we may integrate over `(0,∞)`
    have hIzIoi : volume.restrict Work.Spaces.Iz = volume.restrict (Set.Ioi (0 : ℝ)) := by
      rw [Work.Spaces.Iz]
      exact (MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ)))).symm
    -- ## a.e. strong measurability of the dominated function
    have hsmv : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry v)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      intro n
      rw [hv]
      exact contDiffOn_uncurry_divCos u n (h.smooth n)
    have hA := Work.FTS.EllipticEst.Honest.aemeasurable_sliceSigmaLin v hsmv
    rw [hIzIoi] at hA
    have hAt : AEMeasurable
        (fun z => (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ * (v z θ) ^ 2)).toReal)
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      ENNReal.measurable_toReal.comp_aemeasurable hA
    have hw : Measurable (fun z : ℝ => (Work.Spaces.w z) ^ 2) := by
      simp only [Work.Spaces.w]
      fun_prop
    have hg : AEMeasurable (fun z => (Work.Spaces.w z) ^ 2 *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
          (Work.FTS.EllipticEst.sEta θ * (v z θ) ^ 2)).toReal)
        (volume.restrict (Set.Ioi (0 : ℝ))) := hw.aemeasurable.mul hAt
    have haesm_int : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 v z θ) (volume.restrict (Set.Ioi (0 : ℝ))) := by
      have heq : (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 v z θ)
          =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
          (fun z => (Work.Spaces.w z) ^ 2 *
            (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
              (Work.FTS.EllipticEst.sEta θ * (v z θ) ^ 2)).toReal) := by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
        rw [Work.FTS.EllipticEst.H2W.AeProof.innerEq α v z]
        congr 1
        -- `∫_θ (v z θ)² σ = (∫⁻_θ ofReal (σ (v z θ)²)).toReal`
        have haesm_slice : AEStronglyMeasurable
            (fun θ => Work.FTS.EllipticEst.sEta θ * (v z θ) ^ 2)
            (volume.restrict Work.Spaces.Iθ) := by
          rw [hv]
          exact aestronglyMeasurable_sEta_mul_divCos_sq u hz
            (Work.FTS.EllipticEst.Honest.contDiffOn_slice u hz (h.smooth 2))
        have hconv := MeasureTheory.integral_eq_lintegral_of_nonneg_ae
          (μ := volume.restrict Work.Spaces.Iθ)
          (f := fun θ => Work.FTS.EllipticEst.sEta θ * (v z θ) ^ 2)
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
            (fun θ hθ => mul_nonneg (Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ) (sq_nonneg _)))
          haesm_slice
        have hswap : (∫ θ in Work.Spaces.Iθ, (v z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
            = (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (v z θ) ^ 2) := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
          ring
        rw [hswap, hconv]
      exact (hg.congr heq.symm).aestronglyMeasurable
    -- ## the pointwise (in `z`) slice bound
    have hbound : ∀ z ∈ Set.Ioi (0 : ℝ),
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 v z θ)
          ≤ 1010000 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
            + (∫ θ in Work.Spaces.Iθ,
                Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 u) z θ)) := by
      intro z hz
      rw [Work.FTS.EllipticEst.H2W.AeProof.innerEq α v z,
          Work.FTS.EllipticEst.H2W.AeProof.innerEq α u z,
          Work.FTS.EllipticEst.H2W.AeProof.innerEq α (Work.Spaces.pthIter 2 u) z]
      have hsb := Work.FTS.EllipticEst.H2W.AeProof.sliceBarLe α u G h hmu hz
      -- `∂_θθu` is definitionally the `pthIter 2` of `u`
      have heqB : (∫ θ in Work.Spaces.Iθ, deriv (fun t => deriv (fun θ' => u z θ') t) θ ^ 2
            * Work.FTS.EllipticEst.sEta θ)
          = (∫ θ in Work.Spaces.Iθ, Work.Spaces.pthIter 2 u z θ ^ 2
              * Work.FTS.EllipticEst.sEta θ) := rfl
      rw [heqB] at hsb
      have hW : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      refine (mul_le_mul_of_nonneg_left hsb hW).trans (le_of_eq ?_)
      ring
    -- ## the dominating function is integrable
    have hD : MeasureTheory.Integrable (fun z => 1010000 *
        ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
          + (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 u) z θ)))
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
      have h1 : MeasureTheory.IntegrableOn (fun z =>
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
          + (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 u) z θ))
          Work.Spaces.Iz := hmu.2.add h.memAng2.2
      exact (h1.mono_set Set.Ioi_subset_Ici_self).const_mul 1010000
    have hbound_ae : ∀ᵐ z ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        ‖∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 v z θ‖
          ≤ 1010000 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
            + (∫ θ in Work.Spaces.Iθ,
                Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 u) z θ)) := by
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
      rw [Real.norm_of_nonneg ?_]
      · exact hbound z hz
      · rw [Work.FTS.EllipticEst.H2W.AeProof.innerEq α v z]
        exact mul_nonneg (sq_nonneg _) (MeasureTheory.setIntegral_nonneg measurableSet_Icc
          (fun θ hθ => mul_nonneg (sq_nonneg _)
            (Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ)))
    have hf := MeasureTheory.Integrable.mono' hD haesm_int hbound_ae
    rw [MeasureTheory.IntegrableOn, hIzIoi]
    exact hf

end Work.FTS.EllipticEst.H2W.AeProof.BarAux
