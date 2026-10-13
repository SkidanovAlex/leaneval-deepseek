/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Deleg/mixedTruncPairLe` — the per-`(χ_n, ψ_δ)` inequality of the cut-off chain

`Work.FTS.EllipticEst.Deleg.mixedTruncPairLe` : from the 1-D collar bound
`Deleg.CollarBound Cw` derive the per-`(n,δ)` inequality `Deleg.TruncPairLe Cw` of the cut-off
chain for `Deleg.i1Paper_weakMixed`:

`κ·P_tr ≤ D_tr + Tr_tr − 2η·A_tr + Cw·K·Col`

(`P_tr = AeColl.Ptr`, ... the truncated quantities of `AeColl.Defs`).

The proof composes the proved 2-D cut-off identity `I1Wk.truncIdentity` (radial IBP
`truncZIbp2` + angular IBP `truncThetaIbpSep`) with the slicewise collar bound
(`mixedTrunc.sliceCollarLe`, applied a.e. in `z` and integrated against `χ_n w²`).
The three analytic inputs are the pieces

* `mixedTrunc.outerIntegrable` (the four outer-integrability facts of the identity),
* `mixedTrunc.collarAe` (a.e. mixed honesty — the collar energies are honest),
* `mixedTrunc.sliceCollarLe` (the slicewise collar bound).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Deleg.i1Paper_weakMixedDefs
import Submission.Work.FTS.EllipticEst.Deleg.mixedTrunc.QuadBasic
import Submission.Work.FTS.EllipticEst.Deleg.mixedTrunc.sliceCollarLe
import Submission.Work.FTS.EllipticEst.Deleg.mixedTrunc.collarAe
import Submission.Work.FTS.EllipticEst.Deleg.mixedTrunc.outerIntegrable
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.Asm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Deleg

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open Work.FTS.EllipticEst (cut cut_nonneg cut_contDiff cut_le_one)
open Work.FTS.EllipticEst.AeColl (Ptr Atr Dtr Trtr Wtr Col wt sigθ psiD Uz Vz Az
  wt_nonneg sigθ_nonneg_of_mem psiD_nonneg psiD_contDiff psiD_hasCompactSupport
  psiD_tsupport_subset' psiD_tsupport_subset_Ioo
  cut_contDiff_one cut_hasCompactSupport cut_tsupport_subset_Ioi cut_support_subset_Ioi)



/-! ## Elementary nonnegativity -/

/-- `sin(2θ)^{−η} ≥ 0` whenever `0 ≤ θ` and `2θ ≤ π` (division-free form of the
angular-boundary condition, convenient for `linarith`). -/
theorem sigθ_nonneg_of_two_mul_le {θ : ℝ} (h0 : 0 ≤ θ) (hπ : 2 * θ ≤ Real.pi) :
    0 ≤ sigθ θ := by
  rw [Work.FTS.EllipticEst.AeColl.sigθ]
  exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith only [h0]) hπ) _

/-- `4δ ≤ π` from the building convention `4δ ≤ π/2`. -/
theorem four_mul_le_pi_of {δ : ℝ} (hδ2 : 4 * δ ≤ Real.pi / 2) : 4 * δ ≤ Real.pi := by
  have hπ2 : Real.pi / 2 ≤ Real.pi := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    linarith only [Real.pi_pos]
  exact le_trans hδ2 hπ2

/-- `2δ ≤ π` from the building convention `4δ ≤ π/2`. -/
theorem two_mul_le_pi_of {δ : ℝ} (hδ : 0 < δ) (hδ2 : 4 * δ ≤ Real.pi / 2) :
    2 * δ ≤ Real.pi := by
  have h4 : 4 * δ ≤ Real.pi := four_mul_le_pi_of hδ2
  linarith only [h4, hδ]

/-- `0 ≤ π/2 - δ` whenever `2δ ≤ π`. -/
theorem pi_half_sub_nonneg {δ : ℝ} (h2 : 2 * δ ≤ Real.pi) : 0 ≤ Real.pi / 2 - δ := by
  have h : Real.pi / 2 - δ = (Real.pi - 2 * δ) / 2 := by ring
  rw [h]
  exact div_nonneg (by linarith only [h2]) (by norm_num)

/-- `2·(π/2) ≤ π`. -/
theorem two_mul_pi_half_le : 2 * (Real.pi / 2) ≤ Real.pi := by
  rw [show 2 * (Real.pi / 2) = Real.pi by ring]

/-- The `θ`-integral of `σ · (z ∂_z∂_θu)²` over an interval inside `[0,π/2]` is nonnegative. -/
theorem inner_nonneg {f : ℝ → ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hb : 2 * b ≤ Real.pi)
    (z : ℝ) :
    0 ≤ ∫ θ in Set.Ioo a b, sigθ θ * (Vz f z θ) ^ 2 := by
  refine Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.integral_nonneg_of_ae' ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  refine Eventually.of_forall fun θ hθ => ?_
  refine mul_nonneg (sigθ_nonneg_of_two_mul_le (le_trans ha (le_of_lt hθ.1)) ?_) (sq_nonneg _)
  have h1 : 2 * θ < 2 * b := by linarith only [hθ.2]
  linarith only [h1, hb]

/-- `Atr` is nonnegative: it is the integral of a pointwise nonnegative integrand. -/
theorem atr_nonneg (u : ℝ → ℝ → ℝ) (n : ℕ) (δ : ℝ) :
    0 ≤ Atr u n δ := by
  rw [Atr]
  refine Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.integral_nonneg_of_ae' ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun z hz => ?_
  refine mul_nonneg (mul_nonneg (cut_nonneg n z) (wt_nonneg z)) ?_
  refine Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.integral_nonneg_of_ae' ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  refine Eventually.of_forall fun θ hθ => ?_
  exact mul_nonneg (mul_nonneg
    (sigθ_nonneg_of_mem ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) (psiD_nonneg δ θ)) (sq_nonneg _)

/-- `Col` is nonnegative: it is the sum of two integrals of pointwise nonnegative integrands. -/
theorem col_nonneg (u : ℝ → ℝ → ℝ) (n : ℕ) (δ : ℝ) (hδ' : 0 < δ)
    (hδ2 : 4 * δ ≤ Real.pi / 2) :
    0 ≤ Col u n δ := by
  rw [Col]
  refine add_nonneg ?_ ?_
  · refine Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.integral_nonneg_of_ae' ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun z hz => ?_
    exact mul_nonneg (mul_nonneg (cut_nonneg n z) (wt_nonneg z))
      (inner_nonneg (f := u) le_rfl (two_mul_le_pi_of hδ' hδ2) z)
  · refine Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.integral_nonneg_of_ae' ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun z hz => ?_
    exact mul_nonneg (mul_nonneg (cut_nonneg n z) (wt_nonneg z))
      (inner_nonneg (f := u) (pi_half_sub_nonneg (two_mul_le_pi_of hδ' hδ2)) two_mul_pi_half_le z)

/-! ## The `W`-term bound -/

/-- **The `W`-term bound**: the collar hypothesis controls the `ψ_δ''`-moment of `U` slicewise,
and the a.e. mixed honesty makes the collar energies honest. -/
theorem wBound (Cw : ℝ) (hCw : 0 < Cw) (hc : Work.FTS.EllipticEst.Deleg.CollarBound Cw)
    (u : ℝ → ℝ → ℝ) (K : ℝ) (hK : 0 < K)
    (hsm : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hMix : Work.FTS.EllipticEst.Deleg.MixedHon u)
    (hRate : Work.FTS.EllipticEst.Deleg.SliceRate K u)
    (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ2 : 4 * δ ≤ Real.pi / 2) :
    (1 / 2) * |Wtr u n δ| ≤ Cw * K * Col u n δ := by
  rw [Wtr, Col]
  obtain ⟨hslice, hle1, hle2, hInt1, hInt2⟩ :=
    mixedTrunc.collarAe u n δ hδ hδ2 hsm hMix
  -- the a.e. pointwise collar bound (the collar hypothesis, slicewise)
  have hbd : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      |∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ
          * deriv (deriv (psiD δ)) θ * (Uz u z θ) ^ 2|
        ≤ Cw * K * ((∫ θ in Set.Ioo 0 δ, sigθ θ * (Vz u z θ) ^ 2)
          + (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
              sigθ θ * (Vz u z θ) ^ 2)) := by
    filter_upwards [hRate, hslice, ae_restrict_mem measurableSet_Ioi] with z hrate hslice hz
    exact mixedTrunc.sliceCollarLe Cw hc u K z δ hK hδ hδ2 hz
      (contDiffOn_Uz_slice hsm hz) hslice
      (fun θ hθ => deriv_Uz_eq_Vz hsm hz hθ) hrate.1 hrate.2
  -- the dominating function is integrable
  have hg : MeasureTheory.IntegrableOn (fun z => cut n z * wt z
      * (Cw * K * ((∫ θ in Set.Ioo 0 δ, sigθ θ * (Vz u z θ) ^ 2)
          + (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
              sigθ θ * (Vz u z θ) ^ 2)))) (Set.Ioi 0) := by
    refine ((hInt1.add hInt2).const_mul (Cw * K)).congr ?_
    filter_upwards with z
    simp only [Pi.add_apply]
    ring
  -- the dominated function `|G|` is integrable
  have hfint : MeasureTheory.IntegrableOn (fun z => cut n z * wt z
      * |∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ
          * deriv (deriv (psiD δ)) θ * (Uz u z θ) ^ 2|) (Set.Ioi 0) := by
    refine MeasureTheory.Integrable.mono' hg ?_ ?_
    · have haesmG : MeasureTheory.AEStronglyMeasurable
          (fun z => ∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ
              * deriv (deriv (psiD δ)) θ * (Uz u z θ) ^ 2)
          (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
        refine aesm_thetaIntegral_Ioi ?_ measurableSet_Ioo (fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
        have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
          (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
        have h1 : ContinuousOn (fun p : ℝ × ℝ => sigθ p.2)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
          (hsin.rpow_const (fun p hp => Or.inl
            (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
              (by linarith [hp.2.2, Real.pi_pos]))))).congr (fun p _ => rfl)
        have hd2 : Continuous (deriv (deriv (psiD δ))) := by
          have hc := (psiD_contDiff δ).continuous_iteratedDeriv' 2
          simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hc
        have h2 : ContinuousOn (fun p : ℝ × ℝ => deriv (deriv (psiD δ)) p.2)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
          (hd2.comp continuous_snd).continuousOn
        exact (h1.mul h2).mul ((continuousOn_Uz_quad hsm).pow 2)
      have hwtm : Measurable (fun z : ℝ => wt z) := by
        have h1 : Measurable (fun z : ℝ => (1 : ℝ) + z) :=
          (measurable_const : Measurable (fun _ : ℝ => (1 : ℝ))).add measurable_id
        have hz : Measurable (fun z : ℝ => z) := measurable_id
        have h5 : Measurable (fun z : ℝ =>
            (((1 : ℝ) + z) * (1 + z)) / (z * z)
              * ((((1 : ℝ) + z) * (1 + z)) / (z * z))) :=
          ((h1.mul h1).div (hz.mul hz)).mul ((h1.mul h1).div (hz.mul hz))
        rw [show (fun z : ℝ => wt z) = fun z : ℝ =>
            (((1 : ℝ) + z) * (1 + z)) / (z * z)
              * ((((1 : ℝ) + z) * (1 + z)) / (z * z)) from by
          funext z; rw [Work.FTS.EllipticEst.AeColl.wt, Work.Spaces.w]; ring]
        exact h5
      have hcutwt : MeasureTheory.AEStronglyMeasurable (fun z => cut n z * wt z)
          (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
        (((cut_contDiff n).continuous.measurable).mul hwtm).aestronglyMeasurable
      have hGabs : MeasureTheory.AEStronglyMeasurable
          (fun z => |∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ
              * deriv (deriv (psiD δ)) θ * (Uz u z θ) ^ 2|)
          (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
        have hnorm := (haesmG.aemeasurable.norm).aestronglyMeasurable
        simpa only [Real.norm_eq_abs] using hnorm
      exact hcutwt.mul hGabs
    · filter_upwards [hbd] with z hz
      have h1 : ‖cut n z * wt z
          * |∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ
              * deriv (deriv (psiD δ)) θ * (Uz u z θ) ^ 2|‖
          = cut n z * wt z
          * |∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ
              * deriv (deriv (psiD δ)) θ * (Uz u z θ) ^ 2| := by
        simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (cut_nonneg n z),
          abs_of_nonneg (wt_nonneg z), abs_of_nonneg (abs_nonneg _)]
      rw [h1]
      exact mul_le_mul_of_nonneg_left hz (mul_nonneg (cut_nonneg n z) (wt_nonneg z))
  -- the two comparison inequalities for the outer integral
  have hnorm : |∫ z in Set.Ioi 0, cut n z * wt z
        * (∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ
            * deriv (deriv (psiD δ)) θ * (Uz u z θ) ^ 2)|
      ≤ ∫ z in Set.Ioi 0, cut n z * wt z
        * |∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ
            * deriv (deriv (psiD δ)) θ * (Uz u z θ) ^ 2| := by
    have h0 : ‖∫ z in Set.Ioi 0, cut n z * wt z
          * (∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ
              * deriv (deriv (psiD δ)) θ * (Uz u z θ) ^ 2)‖
        ≤ ∫ z in Set.Ioi 0, ‖cut n z * wt z
          * (∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ
              * deriv (deriv (psiD δ)) θ * (Uz u z θ) ^ 2)‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    have h1 : (∫ z in Set.Ioi 0, ‖cut n z * wt z
          * (∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ
              * deriv (deriv (psiD δ)) θ * (Uz u z θ) ^ 2)‖)
        = ∫ z in Set.Ioi 0, cut n z * wt z
          * |∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ
              * deriv (deriv (psiD δ)) θ * (Uz u z θ) ^ 2| := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (cut_nonneg n z),
        abs_of_nonneg (wt_nonneg z), abs_of_nonneg (abs_nonneg _)]
    rw [h1] at h0
    simpa only [Real.norm_eq_abs] using h0
  have hmono : (∫ z in Set.Ioi 0, cut n z * wt z
        * |∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ
            * deriv (deriv (psiD δ)) θ * (Uz u z θ) ^ 2|)
      ≤ ∫ z in Set.Ioi 0, cut n z * wt z
        * (Cw * K * ((∫ θ in Set.Ioo 0 δ, sigθ θ * (Vz u z θ) ^ 2)
            + (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
                sigθ θ * (Vz u z θ) ^ 2))) := by
    refine MeasureTheory.integral_mono_ae hfint hg ?_
    filter_upwards [hbd] with z hz
    exact mul_le_mul_of_nonneg_left hz (mul_nonneg (cut_nonneg n z) (wt_nonneg z))
  -- the dominating integral is `Cw·K·Col`
  have hsplit : (∫ z in Set.Ioi 0, cut n z * wt z
        * (Cw * K * ((∫ θ in Set.Ioo 0 δ, sigθ θ * (Vz u z θ) ^ 2)
            + (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
                sigθ θ * (Vz u z θ) ^ 2))))
      = Cw * K * ((∫ z in Set.Ioi 0, cut n z * wt z
              * (∫ θ in Set.Ioo 0 δ, sigθ θ * (Vz u z θ) ^ 2))
          + ∫ z in Set.Ioi 0, cut n z * wt z
              * (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
                  sigθ θ * (Vz u z θ) ^ 2)) := by
    rw [show (fun z => cut n z * wt z
          * (Cw * K * ((∫ θ in Set.Ioo 0 δ, sigθ θ * (Vz u z θ) ^ 2)
              + (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
                  sigθ θ * (Vz u z θ) ^ 2))))
        = fun z => (Cw * K) * (cut n z * wt z
            * ((∫ θ in Set.Ioo 0 δ, sigθ θ * (Vz u z θ) ^ 2)
              + (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
                  sigθ θ * (Vz u z θ) ^ 2))) from by
      funext z; ring]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [show (fun z => cut n z * wt z
          * ((∫ θ in Set.Ioo 0 δ, sigθ θ * (Vz u z θ) ^ 2)
            + (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
                sigθ θ * (Vz u z θ) ^ 2)))
        = fun z => cut n z * wt z * (∫ θ in Set.Ioo 0 δ, sigθ θ * (Vz u z θ) ^ 2)
            + cut n z * wt z * (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
                sigθ θ * (Vz u z θ) ^ 2) from by
      funext z; ring]
    rw [MeasureTheory.integral_add hInt1 hInt2]
  -- conclusion
  have hCol : Cw * K * Col u n δ
      = Cw * K * ((∫ z in Set.Ioi 0, cut n z * wt z
              * (∫ θ in Set.Ioo 0 δ, sigθ θ * (Vz u z θ) ^ 2))
          + ∫ z in Set.Ioi 0, cut n z * wt z
              * (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
                  sigθ θ * (Vz u z θ) ^ 2)) := rfl
  have h1 : |∫ z in Set.Ioi 0, cut n z * wt z
        * (∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ
            * deriv (deriv (psiD δ)) θ * (Uz u z θ) ^ 2)| ≤ Cw * K * Col u n δ := by
    rw [hCol, ← hsplit]
    exact le_trans hnorm hmono
  rw [hCol] at h1
  have h2δ : 2 * δ ≤ Real.pi := two_mul_le_pi_of hδ hδ2
  have hY0 : 0 ≤ Cw * K * Col u n δ := by
    rw [hCol, ← hsplit]
    refine Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.integral_nonneg_of_ae' ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun z hz => ?_
    have hAB : 0 ≤ (∫ θ in Set.Ioo 0 δ, sigθ θ * (Vz u z θ) ^ 2)
        + (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
            sigθ θ * (Vz u z θ) ^ 2) :=
      add_nonneg (inner_nonneg (f := u) le_rfl h2δ z)
        (inner_nonneg (f := u) (pi_half_sub_nonneg h2δ) two_mul_pi_half_le z)
    exact mul_nonneg (mul_nonneg (cut_nonneg n z) (wt_nonneg z))
      (mul_nonneg (le_of_lt (mul_pos hCw hK)) hAB)
  rw [hCol] at hY0
  linarith only [h1, hY0, abs_nonneg (∫ z in Set.Ioi 0, cut n z * wt z
      * (∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ
          * deriv (deriv (psiD δ)) θ * (Uz u z θ) ^ 2))]

/-! ## The defect term of the truncated angular identity -/

/-- The defect integral of `I1Wk.truncIdentity` at `χ = cut n`, `ψ = psiD δ`. -/
def defTerm (u : ℝ → ℝ → ℝ) (n : ℕ) (δ : ℝ) : ℝ :=
  ∫ z in Set.Ioi 0, cut n z * (Work.Spaces.w z) ^ 2
    * (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * psiD δ θ
          * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ
              - (1 + Work.Spaces.eta) * (z * Work.Spaces.pz u z θ)
                * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(1 : ℝ))) ^ 2)

/-- The defect integral is nonnegative (it is the integral of a pointwise nonnegative
integrand). -/
theorem defTerm_nonneg (u : ℝ → ℝ → ℝ) (n : ℕ) (δ : ℝ) : 0 ≤ defTerm u n δ := by
  rw [defTerm]
  refine Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.integral_nonneg_of_ae' ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun z hz => ?_
  refine mul_nonneg (mul_nonneg (cut_nonneg n z) (sq_nonneg _)) ?_
  refine Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.integral_nonneg_of_ae' ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  refine Eventually.of_forall fun θ hθ => ?_
  have h2θ : 2 * θ ≤ Real.pi := by
    have h := mul_lt_mul_of_pos_left hθ.2 (by norm_num : (0 : ℝ) < 2)
    rw [show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring] at h
    linarith only [h]
  exact mul_nonneg (mul_nonneg (sigθ_nonneg_of_two_mul_le (le_of_lt hθ.1) h2θ)
    (psiD_nonneg δ θ)) (sq_nonneg _)

/-! ## The main theorem -/

theorem mixedTruncPairLe (Cw : ℝ) (hCw : 0 < Cw)
    (hc : Work.FTS.EllipticEst.Deleg.CollarBound Cw) :
    Work.FTS.EllipticEst.Deleg.TruncPairLe Cw := by
  intro α u G hA hU hMix K hKpos hRate n δ hδ hδ2
  have hsm : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hA.smooth
  obtain ⟨ho1, ho2, ho3, ho4⟩ := mixedTrunc.outerIntegrable u n δ hsm hδ hδ2
  have hχ : ContDiff ℝ 1 (cut n) := cut_contDiff_one n
  have hχc : HasCompactSupport (cut n) := cut_hasCompactSupport n
  have hχsupp : tsupport (cut n) ⊆ Set.Ioi (0 : ℝ) := cut_tsupport_subset_Ioi n
  have hχsupp' : Function.support (cut n) ⊆ Set.Ioi (0 : ℝ) := cut_support_subset_Ioi n
  have hχnn : ∀ z, 0 ≤ cut n z := cut_nonneg n
  have hψ : ContDiff ℝ 2 (psiD δ) := psiD_contDiff δ
  have hψc : HasCompactSupport (psiD δ) := psiD_hasCompactSupport δ
  have hψnn : ∀ θ, 0 ≤ psiD δ θ := psiD_nonneg δ
  have h4δ : 4 * δ ≤ Real.pi := four_mul_le_pi_of hδ2
  have h2δ : 2 * δ ≤ Real.pi := two_mul_le_pi_of hδ hδ2
  have h2π : δ < 2 * Real.pi := by linarith only [h2δ, Real.pi_pos]
  have hab : δ / 8 < Real.pi / 2 - δ / 8 := by
    rw [lt_sub_iff_add_lt, show δ / 8 + δ / 8 = δ / 4 by ring]
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 4)]
    rw [show Real.pi / 2 * 4 = 2 * Real.pi by ring]
    exact h2π
  have hψsep : ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < Real.pi / 2
      ∧ tsupport (psiD δ) ⊆ Set.Ioo a b :=
    ⟨δ / 8, Real.pi / 2 - δ / 8, by positivity, hab,
      sub_lt_self _ (by positivity), psiD_tsupport_subset' hδ h4δ⟩
  have hψsep1 : tsupport (psiD δ) ⊆ Set.Ioo 0 (Real.pi / 2) :=
    psiD_tsupport_subset_Ioo hδ h4δ
  have hId := Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.truncIdentity u (cut n) (psiD δ)
    hsm hχ hχc hχsupp hχsupp' hψ hψc hψsep hψsep1 ho1 ho2 ho3 ho4
  have hId' : Dtr u n δ = -Trtr u n δ + 2 * Work.Spaces.eta * Atr u n δ + kap * Ptr u n δ
      + (2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) * defTerm u n δ
      - (1 / 2) * Wtr u n δ := hId
  have hη : (0 : ℝ) ≤ Work.Spaces.eta := by rw [Work.Spaces.eta]; norm_num
  have hDef0 : 0 ≤ (2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) * defTerm u n δ :=
    mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hη) (by linarith only [hη]))
      (defTerm_nonneg u n δ)
  have hWle : (1 / 2) * Wtr u n δ ≤ Cw * K * Col u n δ :=
    le_trans (mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num))
      (wBound Cw hCw hc u K hKpos hsm hMix hRate n δ hδ hδ2)
  linarith only [hId', hDef0, hWle]

end Work.FTS.EllipticEst.Deleg
