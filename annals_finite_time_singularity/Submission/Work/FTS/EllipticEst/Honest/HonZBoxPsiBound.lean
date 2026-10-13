import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.Honest.ZBoxAux
import Submission.Work.FTS.EllipticEst.Honest.two_mul_abs_mul_le_rpow_amgm
import Submission.Work.FTS.EllipticEst.Honest.ZBoxLintegral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option linter.unusedSimpArgs false

theorem HonZBoxPsiBound (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (h : Work.FTS.EllipticEst.Honest.Hon α F Ψ) :
    ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => (∫ u in (z / 2)..z, |Work.Spaces.pzIter 2 Ψ u θ|)
        * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
  intro z hz
  have ha0 : 0 < z / 2 := by linarith
  have hab : z / 2 ≤ z := by linarith
  -- ### the pointwise Young/AM–GM bound
  have hpt : ∀ u ∈ Set.Icc (z / 2) z, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.pzIter 2 Ψ u θ| * |Work.Elliptic.sinCos2 θ|
        ≤ (1 / 2) * ((1 / u ^ 2) * zhbS α Ψ u θ)
          + (1 / 2) * ((1 / (u ^ 2 * (Work.Spaces.w u) ^ 2))
              * ((Work.Elliptic.sinCos2 θ) ^ 2 * zhbT θ)) := by
    intro u hu θ hθ
    have hu0 : 0 < u := lt_of_lt_of_le ha0 hu.1
    have ham := two_mul_abs_mul_le_rpow_amgm (η := Work.Spaces.eta)
      (P := Work.Spaces.pzIter 2 Ψ u θ) (g := |Work.Elliptic.sinCos2 θ|)
      (u := u) (w := Work.Spaces.w u) (s := Real.sin (2 * θ))
      zhb_eta_pos hu0 (zhb_w_pos hu0) (sin_two_nonneg_of_mem_Iθ hθ) (by
        by_cases hs : Real.sin (2 * θ) = 0
        · exact Or.inr (by rw [zhb_sin_two_zero_imp θ hs, abs_zero])
        · exact Or.inl (lt_of_le_of_ne (sin_two_nonneg_of_mem_Iθ hθ) (Ne.symm hs)))
    rw [← zhbSigma, ← zhbT, ← zhb_S_eq α Ψ (u := u) (θ := θ) hθ, zhb_abs_sinCos2 hθ] at ham
    rw [zhb_abs_sinCos2 hθ]
    have h2 : 2 * (|Work.Spaces.pzIter 2 Ψ u θ| * Work.Elliptic.sinCos2 θ)
        ≤ (1 / u ^ 2) * zhbS α Ψ u θ
          + (1 / (u ^ 2 * (Work.Spaces.w u) ^ 2))
              * (Work.Elliptic.sinCos2 θ) ^ 2 * zhbT θ := by
      linarith [ham]
    calc |Work.Spaces.pzIter 2 Ψ u θ| * Work.Elliptic.sinCos2 θ
        = (1 / 2) * (2 * (|Work.Spaces.pzIter 2 Ψ u θ| * Work.Elliptic.sinCos2 θ)) := by ring
      _ ≤ (1 / 2) * ((1 / u ^ 2) * zhbS α Ψ u θ
            + (1 / (u ^ 2 * (Work.Spaces.w u) ^ 2))
                * (Work.Elliptic.sinCos2 θ) ^ 2 * zhbT θ) :=
          mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = (1 / 2) * ((1 / u ^ 2) * zhbS α Ψ u θ)
          + (1 / 2) * ((1 / (u ^ 2 * (Work.Spaces.w u) ^ 2))
              * ((Work.Elliptic.sinCos2 θ) ^ 2 * zhbT θ)) := by ring
  -- ### the box integrand is nonnegative
  have hnn : ∀ u θ : ℝ, 0 ≤ |Work.Spaces.pzIter 2 Ψ u θ| * |Work.Elliptic.sinCos2 θ| :=
    fun u θ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  -- ### slicewise measurability of the box integrand
  have hslice_meas : ∀ θ ∈ Work.Spaces.Iθ,
      AEStronglyMeasurable (fun u => |Work.Spaces.pzIter 2 Ψ u θ| * |Work.Elliptic.sinCos2 θ|)
        (MeasureTheory.volume.restrict (Set.Icc (z / 2) z)) := by
    intro θ hθ
    rcases eq_or_lt_of_le hθ.1 with hθ0 | hθ0
    · subst hθ0
      have hzero : (fun u : ℝ => |Work.Spaces.pzIter 2 Ψ u 0| * |Work.Elliptic.sinCos2 0|)
          = fun _ : ℝ => 0 := by
        funext u
        simp [Work.Elliptic.sinCos2]
      rw [hzero]
      exact aestronglyMeasurable_const
    · rcases eq_or_lt_of_le hθ.2 with hθ1 | hθ1
      · subst hθ1
        have hzero : (fun u : ℝ =>
              |Work.Spaces.pzIter 2 Ψ u (π / 2)| * |Work.Elliptic.sinCos2 (π / 2)|)
            = fun _ : ℝ => 0 := by
          funext u
          simp [Work.Elliptic.sinCos2]
        rw [hzero]
        exact aestronglyMeasurable_const
      · exact ((zhb_slice_cont_Icc h ⟨hθ0, hθ1⟩ ha0).abs.mul continuousOn_const).aestronglyMeasurable
          measurableSet_Icc
  -- ### joint measurability of the (swapped) box integrand
  have hcont_g : ContinuousOn (Function.uncurry (fun u θ => |Work.Spaces.pzIter 2 Ψ u θ|
      * |Work.Elliptic.sinCos2 θ|)) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have h1 : ContinuousOn (Function.uncurry (fun u θ => |Work.Spaces.pzIter 2 Ψ u θ|))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := (zhb_contOn_pzIter2 h).abs
    have h2 : ContinuousOn (Function.uncurry (fun _u θ : ℝ => |Work.Elliptic.sinCos2 θ|))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
      have hc : Continuous (fun p : ℝ × ℝ => |Work.Elliptic.sinCos2 p.2|) := by
        change Continuous (fun p : ℝ × ℝ => |Real.sin p.2 * Real.cos p.2 ^ 2|)
        fun_prop
      exact hc.continuousOn
    exact h1.mul h2
  have haem : AEMeasurable (fun p : ℝ × ℝ => |Work.Spaces.pzIter 2 Ψ p.2 p.1|
        * |Work.Elliptic.sinCos2 p.1|)
      ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
        (MeasureTheory.volume.restrict (Set.Icc (z / 2) z))) := by
    have hbox := (zhb_aesm_box (a := z / 2) (b := z) ha0 hcont_g).aemeasurable
    have hsw := hbox.prod_swap
    have hfun : (fun p : ℝ × ℝ => (Function.uncurry (fun u θ => |Work.Spaces.pzIter 2 Ψ u θ|
          * |Work.Elliptic.sinCos2 θ|)) p.swap)
        = (fun p : ℝ × ℝ => |Work.Spaces.pzIter 2 Ψ p.2 p.1| * |Work.Elliptic.sinCos2 p.1|) := by
      funext p; rfl
    rwa [hfun] at hsw
  -- ### the slicewise bound of the box lemma
  have hslice : ∀ u ∈ Set.Icc (z / 2) z,
      MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (fun θ => ENNReal.ofReal (|Work.Spaces.pzIter 2 Ψ u θ|
          * |Work.Elliptic.sinCos2 θ|)) ≤ ENNReal.ofReal (zhbC α Ψ u) := by
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le ha0 hu.1
    have hSint : IntegrableOn (fun θ => zhbS α Ψ u θ) Work.Spaces.Iθ :=
      zhb_S_int h (by rw [Work.Spaces.Iz]; exact le_of_lt hu0)
    have h1 : MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (fun θ => ENNReal.ofReal (|Work.Spaces.pzIter 2 Ψ u θ| * |Work.Elliptic.sinCos2 θ|))
        ≤ MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iθ)
          (fun θ => ENNReal.ofReal ((1 / 2) * ((1 / u ^ 2) * zhbS α Ψ u θ)
            + (1 / 2) * ((1 / (u ^ 2 * (Work.Spaces.w u) ^ 2))
                * ((Work.Elliptic.sinCos2 θ) ^ 2 * zhbT θ)))) :=
      MeasureTheory.lintegral_mono_ae
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => ENNReal.ofReal_le_ofReal (hpt u hu θ hθ)))
    have hint : Integrable (fun θ => (1 / 2) * ((1 / u ^ 2) * zhbS α Ψ u θ)
        + (1 / 2) * ((1 / (u ^ 2 * (Work.Spaces.w u) ^ 2))
            * ((Work.Elliptic.sinCos2 θ) ^ 2 * zhbT θ)))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (((hSint.const_mul (1 / u ^ 2)).const_mul (1 / 2)).add
        ((zhb_Tint.const_mul (1 / (u ^ 2 * (Work.Spaces.w u) ^ 2))).const_mul (1 / 2)))
    have h2 : MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iθ)
          (fun θ => ENNReal.ofReal ((1 / 2) * ((1 / u ^ 2) * zhbS α Ψ u θ)
            + (1 / 2) * ((1 / (u ^ 2 * (Work.Spaces.w u) ^ 2))
                * ((Work.Elliptic.sinCos2 θ) ^ 2 * zhbT θ))))
        = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, ((1 / 2) * ((1 / u ^ 2) * zhbS α Ψ u θ)
            + (1 / 2) * ((1 / (u ^ 2 * (Work.Spaces.w u) ^ 2))
                * ((Work.Elliptic.sinCos2 θ) ^ 2 * zhbT θ)))) :=
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
          add_nonneg
            (mul_nonneg (by norm_num)
              (mul_nonneg (by positivity) (HkIntegrand_nonneg α 0 (zhbA Ψ) u θ)))
            (mul_nonneg (by norm_num) (mul_nonneg (by positivity)
              (mul_nonneg (sq_nonneg _) (zhb_T_nonneg hθ))))))).symm
    have h3 : (∫ θ in Work.Spaces.Iθ, ((1 / 2) * ((1 / u ^ 2) * zhbS α Ψ u θ)
            + (1 / 2) * ((1 / (u ^ 2 * (Work.Spaces.w u) ^ 2))
                * ((Work.Elliptic.sinCos2 θ) ^ 2 * zhbT θ))))
        = zhbC α Ψ u := by
      rw [MeasureTheory.integral_add
            ((hSint.const_mul (1 / u ^ 2)).const_mul (1 / 2))
            ((zhb_Tint.const_mul (1 / (u ^ 2 * (Work.Spaces.w u) ^ 2))).const_mul (1 / 2)),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      rfl
    exact h1.trans (le_of_eq (h2.trans (congrArg ENNReal.ofReal h3)))
  -- ### the coefficient function is nonnegative on the box
  have hGint0 : IntegrableOn (zhbG α Ψ) Work.Spaces.Iz := h.memA.2
  have hsubIz : Set.Icc (z / 2) z ⊆ Work.Spaces.Iz := by
    intro u hu
    rw [Work.Spaces.Iz]
    exact le_trans (le_of_lt ha0) hu.1
  have hGint : IntegrableOn (zhbG α Ψ) (Set.Icc (z / 2) z) := hGint0.mono_set hsubIz
  have hG0 : ∀ u ∈ Set.Icc (z / 2) z, 0 ≤ zhbG α Ψ u := by
    intro u hu
    exact MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall (fun θ => HkIntegrand_nonneg α 0 (zhbA Ψ) u θ))
  have hK20 : 0 ≤ zhbK2 :=
    MeasureTheory.integral_nonneg_of_ae
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (zhb_T_nonneg hθ)))
  have hc0 : ∀ u ∈ Set.Icc (z / 2) z, 0 ≤ zhbC α Ψ u := by
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le ha0 hu.1
    exact add_nonneg
      (mul_nonneg (by norm_num) (mul_nonneg (by positivity) (hG0 u hu)))
      (mul_nonneg (by norm_num) (mul_nonneg (by positivity) hK20))
  -- ### the coefficient function is integrable on the box
  have hwcont : ContinuousOn (fun u : ℝ => (1 : ℝ) / (u ^ 2 * (Work.Spaces.w u) ^ 2))
      (Set.Icc (z / 2) z) := by
    have hw : ContinuousOn (fun u : ℝ => Work.Spaces.w u) (Set.Icc (z / 2) z) := by
      change ContinuousOn (fun u : ℝ => (1 + u) ^ 2 / u ^ 2) (Set.Icc (z / 2) z)
      exact ((continuousOn_const.add continuousOn_id).pow 2).div (continuousOn_id.pow 2)
        (fun u hu => pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le ha0 hu.1)))
    refine ContinuousOn.div continuousOn_const ((continuousOn_id.pow 2).mul (hw.pow 2)) ?_
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le ha0 hu.1
    exact mul_ne_zero (pow_ne_zero 2 (ne_of_gt hu0)) (pow_ne_zero 2 (ne_of_gt (zhb_w_pos hu0)))
  have hInt1 : Integrable (fun u : ℝ => (1 / u ^ 2) * zhbG α Ψ u)
      (MeasureTheory.volume.restrict (Set.Icc (z / 2) z)) := by
    refine MeasureTheory.Integrable.bdd_mul (c := 4 / z ^ 2) hGint ?_ ?_
    · have hc : ContinuousOn (fun u : ℝ => 1 / u ^ 2) (Set.Icc (z / 2) z) := by
        refine ContinuousOn.div continuousOn_const (continuousOn_id.pow 2) ?_
        intro u hu
        exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le ha0 hu.1))
      exact hc.aestronglyMeasurable measurableSet_Icc
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun u hu => ?_)
      have hu0 : 0 < u := lt_of_lt_of_le ha0 hu.1
      have hnn2 : (0 : ℝ) ≤ 1 / u ^ 2 := div_nonneg zero_le_one (sq_nonneg u)
      rw [Real.norm_eq_abs, abs_of_nonneg hnn2]
      have h3 : (z / 2) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (le_of_lt ha0) hu.1 2
      rw [div_le_div_iff₀ (pow_pos hu0 2) (pow_pos hz 2)]
      nlinarith [h3]
  have hInt2 : Integrable (fun u : ℝ => (1 / (u ^ 2 * (Work.Spaces.w u) ^ 2)) * zhbK2)
      (MeasureTheory.volume.restrict (Set.Icc (z / 2) z)) :=
    MeasureTheory.Integrable.mul_const (ContinuousOn.integrableOn_Icc hwcont) zhbK2
  have hc : IntegrableOn (zhbC α Ψ) (Set.Icc (z / 2) z) :=
    (MeasureTheory.Integrable.const_mul hInt1 (1 / 2)).add
      (MeasureTheory.Integrable.const_mul hInt2 (1 / 2))
  -- ### the box Tonelli lemma
  have hZ := ZBoxLintegral (f := fun u θ => |Work.Spaces.pzIter 2 Ψ u θ|
        * |Work.Elliptic.sinCos2 θ|)
    (c := zhbC α Ψ) (a := z / 2) (b := z) hab hnn hslice_meas haem hslice hc0 hc
  have hfin : MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (fun θ => ENNReal.ofReal (∫ u in (z / 2)..z,
        |Work.Spaces.pzIter 2 Ψ u θ| * |Work.Elliptic.sinCos2 θ|)) < ⊤ :=
    lt_of_le_of_lt hZ ENNReal.ofReal_lt_top
  -- ### measurability of the angular marginal
  have hmeas : AEStronglyMeasurable
      (fun θ => ∫ u in (z / 2)..z, |Work.Spaces.pzIter 2 Ψ u θ| * |Work.Elliptic.sinCos2 θ|)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h1 := haem.aestronglyMeasurable.integral_prod_right'
      (ν := MeasureTheory.volume.restrict (Set.Icc (z / 2) z))
    have key : (fun θ => ∫ u in (z / 2)..z,
          |Work.Spaces.pzIter 2 Ψ u θ| * |Work.Elliptic.sinCos2 θ|)
        = (fun θ => ∫ u in Set.Icc (z / 2) z,
            |Work.Spaces.pzIter 2 Ψ u θ| * |Work.Elliptic.sinCos2 θ|) := by
      funext θ
      rw [intervalIntegral.integral_of_le hab, MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [key]
    exact h1
  -- ### integrability
  have hInt : Integrable
      (fun θ => ∫ u in (z / 2)..z, |Work.Spaces.pzIter 2 Ψ u θ| * |Work.Elliptic.sinCos2 θ|)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine ⟨hmeas, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_norm]
    refine lt_of_le_of_lt ?_ hfin
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (p := fun θ => (0 : ℝ) ≤ ∫ u in (z / 2)..z,
        |Work.Spaces.pzIter 2 Ψ u θ| * |Work.Elliptic.sinCos2 θ|)
      (fun θ _ => intervalIntegral.integral_nonneg_of_forall hab
        (fun u => mul_nonneg (abs_nonneg _) (abs_nonneg _)))] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg hθ]
  -- ### transfer to the requested integrand
  refine IntegrableOn.congr_fun hInt ?_ ?_
  · intro θ hθ
    show (∫ u in (z / 2)..z, |Work.Spaces.pzIter 2 Ψ u θ| * |Work.Elliptic.sinCos2 θ|)
        = (∫ u in (z / 2)..z, |Work.Spaces.pzIter 2 Ψ u θ|) * Work.Elliptic.sinCos2 θ
    rw [zhb_abs_sinCos2 hθ]
    rw [intervalIntegral.integral_congr
      (f := fun u : ℝ => |Work.Spaces.pzIter 2 Ψ u θ| * Work.Elliptic.sinCos2 θ)
      (g := fun u : ℝ => Work.Elliptic.sinCos2 θ * |Work.Spaces.pzIter 2 Ψ u θ|)
      (fun u _ => by ring)]
    rw [intervalIntegral.integral_const_mul]
    ring
  · rw [Work.Spaces.Iθ]
    exact measurableSet_Icc

end Work.FTS.EllipticEst.Honest
