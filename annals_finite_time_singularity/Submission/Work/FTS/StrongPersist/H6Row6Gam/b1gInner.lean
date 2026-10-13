import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.H6Row6Gam.b1gDefs
import Submission.Work.FTS.StrongPersist.H6Row6Gam.gamSliceCS11
import Submission.Work.FTS.StrongPersist.H6Row6Gam.gamSliceSup11

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Row6

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section
/-! ## The pointwise-in-`z` bound on the angular integral -/

theorem b1gInner : ∀ (α : ℝ) (A f : ℝ → ℝ → ℝ) (M : ℝ), α ∈ Set.Ioc 0 1 →
    Work.FTS.EllipticEst.SmoothOpen A → Work.FTS.EllipticEst.SmoothOpen f →
    Work.Spaces.HkMem α 6 A → Work.Spaces.HkMem α 6 f → Work.FTS.Nonlin.Xn α f ≤ M →
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ, |b1gF α A f (z, θ)| ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        ≤ Real.sqrt 3 * M * ((Work.Spaces.w z
              * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z))
            * (Work.Spaces.w z
              * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z))) := by
  intro α A f M hα hA hf h6A h6f hXnM
  obtain ⟨hα0, hα1⟩ := hα
  have hMnn : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hXnM
  have h4f : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hf 4 (by norm_num) h6f
  have hgam1 : Work.Spaces.gam α - 1 = α / 10 :=
    Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.hgam_const
  have hgam_pos : 0 < Work.Spaces.gam α - 1 := by rw [hgam1]; linarith
  have hMXnn : ∀ z : ℝ, 0 ≤ Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z := by
    intro z
    rw [Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX_apply]
    refine add_nonneg (mul_nonneg (by positivity)
        (MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)))
      (mul_nonneg (div_nonneg (by norm_num) hgam_pos.le)
        (MeasureTheory.setIntegral_nonneg measurableSet_Icc
          (fun θ hθ => mul_nonneg
            (Real.rpow_nonneg
              (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.sin_two_nonneg_of_Iθ' hθ) _)
            (sq_nonneg _))))
  have hQznn : ∀ z : ℝ, 0 ≤ Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z := by
    intro z
    rw [Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz_apply]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg
        (Real.rpow_nonneg
          (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.sin_two_nonneg_of_Iθ' hθ) _) (sq_nonneg _))
  have hXpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.DzIter 5 A z θ) ^ 2
        ≤ Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z := by
    intro z θ hz hθ0 hθ1
    rw [Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX_apply]
    exact Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.xSliceAgmon5 α A hα0 hα1 hA h6A
      z θ hz hθ0 hθ1
  have hPz_le : ∀ z : ℝ, 0 < z → b1gPz α f z ≤ 3 * M ^ 2 := by
    intro z hz
    have h1 : b1gPz α f z ≤ 3 * Work.Spaces.HkSq α 4 f := by
      rw [b1gPz_apply]
      exact Work.FTS.StrongPersist.H6Row6Gam.gamSliceSup11 α f hα0 hα1 hf h4f z hz
    have h2 : Work.Spaces.HkSq α 4 f = (Work.Spaces.HkNorm α 4 f) ^ 2 := by
      rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 f)]
    have h3 : (Work.Spaces.HkNorm α 4 f) ^ 2 ≤ M ^ 2 :=
      pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 f) hXnM 2
    linarith [h1, h2.le, h2.ge, h3]
  have hCSθ : ∀ z : ℝ, 0 < z →
      (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (|Work.Spaces.mixed 1 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|))
        ≤ Real.sqrt (b1gPz α f z)
          * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z) := by
    intro z hz
    have h := Work.FTS.StrongPersist.H6Row6Gam.gamSliceCS11 α f hα0 hα1 hf h6f z hz
    simpa only [mul_assoc, b1gPz_apply,
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz_apply] using h
  have hAMall : ∀ z : ℝ,
      (Work.Spaces.w z * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z))
        * (Work.Spaces.w z
          * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z))
      ≤ ((Work.Spaces.w z) ^ 2 * Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z
          + (Work.Spaces.w z) ^ 2
            * Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z) / 2 := by
    intro z
    have ha : (Work.Spaces.w z
        * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)) ^ 2
        = (Work.Spaces.w z) ^ 2
          * Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z := by
      rw [mul_pow, Real.sq_sqrt (hMXnn z)]
    have hb : (Work.Spaces.w z
        * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z)) ^ 2
        = (Work.Spaces.w z) ^ 2
          * Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z := by
      rw [mul_pow, Real.sq_sqrt (hQznn z)]
    nlinarith [sq_nonneg (Work.Spaces.w z
        * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
      - Work.Spaces.w z * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z))]
  have hIz : (Work.Spaces.Iz : Set ℝ) =ᵐ[MeasureTheory.volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm
  rw [MeasureTheory.Measure.restrict_congr_set hIz]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
  have hpt : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |b1gF α A f (z, θ)| ≤ (Work.Spaces.w z) ^ 2
        * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
        * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (|Work.Spaces.mixed 1 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|)) := by
    refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ hθ0 hθ1 => ?_)
    have hθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
    have hσnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
      Real.rpow_nonneg (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.sin_two_nonneg_of_Iθ' hθ) _
    have hX2 : |Work.Spaces.DzIter 5 A z θ|
        ≤ Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (hXpt z θ hz hθ0 hθ1)
    have habsF : |b1gF α A f (z, θ)| = (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * |Work.Spaces.DzIter 5 A z θ|
          * (|Work.Spaces.mixed 1 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|) := by
      simp only [b1gF_apply, Work.FTS.TransportS.leafGam, Work.Spaces.mixed_zero_right]
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (mul_nonneg (sq_nonneg _) hσnn)]
      ring
    rw [habsF]
    have h1 : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * |Work.Spaces.DzIter 5 A z θ|
          * (|Work.Spaces.mixed 1 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|)
        ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
          * (|Work.Spaces.mixed 1 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|) := by
      refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      exact mul_le_mul_of_nonneg_left hX2 (mul_nonneg (sq_nonneg _) hσnn)
    refine h1.trans_eq ?_
    ring
  have hInt_eq : (∫ θ, (Work.Spaces.w z) ^ 2
        * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
        * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (|Work.Spaces.mixed 1 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|))
      ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      = (Work.Spaces.w z) ^ 2
        * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
        * (∫ θ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (|Work.Spaces.mixed 1 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    MeasureTheory.integral_const_mul _ _
  have hWint := Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.integrableOn_gamMixed_slice
    (b := 1) (a := 1) hα0 hf h6f le_rfl (by norm_num) hz
  have hZint := Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.integrableOn_gamMixed_slice
    (b := 5) (a := 1) hα0 hf h6f le_rfl (by norm_num) hz
  have hmaj : MeasureTheory.Integrable (fun θ => (Work.Spaces.w z) ^ 2
        * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
        * (((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 1 1 f z θ) ^ 2
          + (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 5 1 f z θ) ^ 2) / 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (((hWint.add hZint)).div_const 2).const_mul
      ((Work.Spaces.w z) ^ 2
        * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z))
  have hint1 : MeasureTheory.Integrable (fun θ => (Work.Spaces.w z) ^ 2
        * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
        * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (|Work.Spaces.mixed 1 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|)))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
    · exact (Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
          * (|Work.Spaces.mixed 1 1 f p.1 p.2| * |Work.Spaces.mixed 5 1 f p.1 p.2|))
        (contOn_sig_abs11 hf) hz).const_mul
        ((Work.Spaces.w z) ^ 2
          * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z))
    · refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ hθ0 hθ1 => ?_)
      have hθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
      have hσnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
        Real.rpow_nonneg (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.sin_two_nonneg_of_Iθ' hθ) _
      have hc : 0 ≤ (Work.Spaces.w z) ^ 2
          * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z) :=
        mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
      rw [Real.norm_of_nonneg (mul_nonneg hc
        (mul_nonneg hσnn (mul_nonneg (abs_nonneg _) (abs_nonneg _))))]
      have habs : |Work.Spaces.mixed 1 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|
          ≤ ((Work.Spaces.mixed 1 1 f z θ) ^ 2
              + (Work.Spaces.mixed 5 1 f z θ) ^ 2) / 2 := by
        nlinarith [sq_nonneg (|Work.Spaces.mixed 1 1 f z θ| - |Work.Spaces.mixed 5 1 f z θ|),
          sq_abs (Work.Spaces.mixed 1 1 f z θ), sq_abs (Work.Spaces.mixed 5 1 f z θ)]
      have hAM2 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (|Work.Spaces.mixed 1 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|)
          ≤ ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                * (Work.Spaces.mixed 1 1 f z θ) ^ 2
              + (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                * (Work.Spaces.mixed 5 1 f z θ) ^ 2) / 2 := by
        have h := mul_le_mul_of_nonneg_left habs hσnn
        calc (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (|Work.Spaces.mixed 1 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|)
            ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (((Work.Spaces.mixed 1 1 f z θ) ^ 2
                  + (Work.Spaces.mixed 5 1 f z θ) ^ 2) / 2) := h
          _ = ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                  * (Work.Spaces.mixed 1 1 f z θ) ^ 2
                + (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                  * (Work.Spaces.mixed 5 1 f z θ) ^ 2) / 2 := by ring
      exact mul_le_mul_of_nonneg_left hAM2 hc
  calc (∫ θ, |b1gF α A f (z, θ)| ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      ≤ ∫ θ, (Work.Spaces.w z) ^ 2
        * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
        * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (|Work.Spaces.mixed 1 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|))
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        MeasureTheory.integral_mono_ae (b1gSliceInt α A f hα0 hα1 hA hf h6A h6f z hz)
          hint1 hpt
    _ = (Work.Spaces.w z) ^ 2
        * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
        * (∫ θ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (|Work.Spaces.mixed 1 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) := hInt_eq
    _ ≤ (Work.Spaces.w z) ^ 2
        * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
        * (Real.sqrt (b1gPz α f z)
          * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z)) :=
        mul_le_mul_of_nonneg_left (hCSθ z hz) (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))
    _ ≤ Real.sqrt 3 * M
        * ((Work.Spaces.w z
            * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z))
          * (Work.Spaces.w z
            * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z))) := by
        have h2 : Real.sqrt (b1gPz α f z) ≤ Real.sqrt 3 * M := by
          calc Real.sqrt (b1gPz α f z) ≤ Real.sqrt (3 * M ^ 2) :=
                Real.sqrt_le_sqrt (hPz_le z hz)
            _ = Real.sqrt 3 * M := by
                rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_sq_eq_abs,
                  abs_of_nonneg hMnn]
        have h3 : 0 ≤ (Work.Spaces.w z) ^ 2
            * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z) :=
          mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
        calc (Work.Spaces.w z) ^ 2
              * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
              * (Real.sqrt (b1gPz α f z)
                * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z))
            ≤ (Work.Spaces.w z) ^ 2
              * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
              * ((Real.sqrt 3 * M)
                * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z)) := by
              refine mul_le_mul_of_nonneg_left ?_ h3
              exact mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)
          _ = Real.sqrt 3 * M
              * ((Work.Spaces.w z
                  * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z))
                * (Work.Spaces.w z
                  * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z))) := by
              ring
end

end Work.FTS.StrongPersist.H6Row6
