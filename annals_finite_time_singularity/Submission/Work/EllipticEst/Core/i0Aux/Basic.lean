/-
Copyright: work module for the Elgindi finite-time singularity project.

# Bookkeeping for the `i0`-family of the mixed-derivative interpolation

For `u_r = D_z^r V` the slice functions `dIntS u_r`, `ddIntS u_r`, `ttIntS u_r` are the
weighted `L²`-squares of `D_z^{r+1}V`, `D_z^{r+2}V` and `D_z^r∂_θ²V`; hence their `z`-integrals
are bounded by the corresponding summands of the `ℋ^k`-norm (`Work.Spaces.HkSq`).  Also, the
iterates `D_z^r V` vanish at the two angular endpoints, and `∂_θ²` commutes with `D_z^r` on the
open quadrant.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.mixed_comm
import Submission.Work.EllipticEst.Core.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Core.i0Aux

set_option autoImplicit false

/-! ## The weighted square identity -/

/-- The square of `D · (wz / s^{η/2})` equals `D² wz² s^{-η}`; at `s = 0` both sides vanish. -/
theorem mul_div_rpow_sq_eq (D wz s : ℝ) (hs : 0 ≤ s) (hη : Work.Spaces.eta ≠ 0) :
    (D * (wz / s ^ (Work.Spaces.eta / 2))) ^ 2
      = D ^ 2 * wz ^ 2 * s ^ (-(Work.Spaces.eta)) := by
  have hη2 : Work.Spaces.eta / 2 ≠ 0 := by
    intro h
    exact hη (by linarith [h])
  rcases eq_or_lt_of_le hs with h0 | hpos
  · rw [← h0, Real.zero_rpow hη2, Real.zero_rpow (neg_ne_zero.mpr hη)]
    ring
  · have h1 : (s ^ (Work.Spaces.eta / 2)) ^ 2 = s ^ Work.Spaces.eta := by
      rw [← Real.rpow_natCast (s ^ (Work.Spaces.eta / 2)) 2, ← Real.rpow_mul hpos.le]
      norm_num
    rw [mul_pow, div_pow, h1, div_eq_mul_inv, Real.rpow_neg hpos.le]
    ring

/-! ## The angular endpoint values of the iterates -/

/-- Every `D_z`-iterate of a profile vanishing at `θ = 0` still vanishes there. -/
theorem DzIter_zero_theta {V : ℝ → ℝ → ℝ} (h0 : ∀ z : ℝ, V z 0 = 0) (r : ℕ) :
    ∀ z : ℝ, Work.Spaces.DzIter r V z 0 = 0 := by
  induction r with
  | zero => simpa using h0
  | succ r ih =>
      intro z
      have hslice : (fun z' : ℝ => Work.Spaces.DzIter r V z' 0) = fun _ => (0 : ℝ) :=
        funext ih
      show z * Work.Spaces.pz (Work.Spaces.DzIter r V) z 0 = 0
      rw [show Work.Spaces.pz (Work.Spaces.DzIter r V) z 0
          = deriv (fun z' : ℝ => Work.Spaces.DzIter r V z' 0) z from rfl, hslice, deriv_const,
        mul_zero]

/-- Every `D_z`-iterate of a profile vanishing at `θ = π/2` still vanishes there. -/
theorem DzIter_pi_theta {V : ℝ → ℝ → ℝ} (hpi : ∀ z : ℝ, V z (Real.pi / 2) = 0) (r : ℕ) :
    ∀ z : ℝ, Work.Spaces.DzIter r V z (Real.pi / 2) = 0 := by
  induction r with
  | zero => simpa using hpi
  | succ r ih =>
      intro z
      have hslice : (fun z' : ℝ => Work.Spaces.DzIter r V z' (Real.pi / 2)) = fun _ => (0 : ℝ) :=
        funext ih
      show z * Work.Spaces.pz (Work.Spaces.DzIter r V) z (Real.pi / 2) = 0
      rw [show Work.Spaces.pz (Work.Spaces.DzIter r V) z (Real.pi / 2)
          = deriv (fun z' : ℝ => Work.Spaces.DzIter r V z' (Real.pi / 2)) z from rfl, hslice,
        deriv_const, mul_zero]

/-! ## The commutation of `∂_θ²` with the `D_z`-iterates -/

/-- On the open quadrant, `∂_θ² (D_z^r V) = D_z^r (∂_θ² V)`. -/
theorem pthIter2_DzIter_comm {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V)
    {z θ : ℝ} (hz : 0 < z) (hθ1 : 0 < θ) (hθ2 : θ < Real.pi / 2) (r : ℕ) :
    Work.Spaces.pthIter 2 (Work.Spaces.DzIter r V) z θ
      = Work.Spaces.DzIter r (Work.Spaces.pthIter 2 V) z θ := by
  have hsq : ∀ θ' : ℝ, 0 < θ' → θ' < Real.pi / 2 →
      Work.Spaces.pth (Work.Spaces.DzIter r V) z θ'
        = Work.Spaces.DzIter r (Work.Spaces.pth V) z θ' := by
    intro θ' h1 h2
    exact Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
      Work.FTS.EllipticEst.isOpen_Q0 ((Work.FTS.EllipticEst.smoothOpen_iff_forall V).mp hV) r
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, h1, h2⟩)
  have hsq2 : ∀ θ' : ℝ, 0 < θ' → θ' < Real.pi / 2 →
      Work.Spaces.pth (Work.Spaces.DzIter r (Work.Spaces.pth V)) z θ'
        = Work.Spaces.DzIter r (Work.Spaces.pthIter 2 V) z θ' := by
    intro θ' h1 h2
    exact Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
      Work.FTS.EllipticEst.isOpen_Q0
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.pth V)).mp hV.pth) r
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, h1, h2⟩)
  have hloc : (fun θ' : ℝ => Work.Spaces.pth (Work.Spaces.DzIter r V) z θ')
      =ᶠ[𝓝 θ] (fun θ' : ℝ => Work.Spaces.DzIter r (Work.Spaces.pth V) z θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hθ1, hθ2⟩] with θ' hθ'
    exact hsq θ' hθ'.1 hθ'.2
  have hfinal : Work.Spaces.pth (Work.Spaces.DzIter r (Work.Spaces.pth V)) z θ
      = Work.Spaces.DzIter r (Work.Spaces.pthIter 2 V) z θ :=
    hsq2 θ hθ1 hθ2
  calc Work.Spaces.pthIter 2 (Work.Spaces.DzIter r V) z θ
      = deriv (fun θ' : ℝ => Work.Spaces.pth (Work.Spaces.DzIter r V) z θ') θ := rfl
    _ = deriv (fun θ' : ℝ => Work.Spaces.DzIter r (Work.Spaces.pth V) z θ') θ := by
          rw [hloc.deriv_eq]
    _ = Work.Spaces.pth (Work.Spaces.DzIter r (Work.Spaces.pth V)) z θ := rfl
    _ = Work.Spaces.DzIter r (Work.Spaces.pthIter 2 V) z θ := hfinal

/-! ## The three value bounds -/

/-- For `r ≤ k`: `∫_z dIntS (D_z^r V) z ≤ HkSq α k (D_zV)`. -/
theorem dIntS_integral_le_HkSq {k r : ℕ} {α : ℝ} {V : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α k (Work.Spaces.Dz V)) (hr : r ≤ k) :
    (∫ z in Work.Spaces.Iz, dIntS (Work.Spaces.DzIter r V) z)
      ≤ Work.Spaces.HkSq α k (Work.Spaces.Dz V) := by
  have hstep : (∫ z in Work.Spaces.Iz, dIntS (Work.Spaces.DzIter r V) z)
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.Dz (Work.Spaces.DzIter r V) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    rw [dIntS, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    rw [Work.FTS.EllipticEst.thEta,
      mul_div_rpow_sq_eq (Work.Spaces.Dz (Work.Spaces.DzIter r V) z θ) (Work.Spaces.w z)
        (Real.sin (2 * θ)) (Work.FTS.EllipticEst.sin_two_nonneg hθ) Work.Spaces.eta_pos.ne']
    ring
  rw [hstep]
  have hfun : ∀ z θ : ℝ, Work.Spaces.Dz (Work.Spaces.DzIter r V) z θ
      = Work.Spaces.DzIter r (Work.Spaces.Dz V) z θ := by
    intro z θ
    have h2 : Work.Spaces.DzIter (r + 1) V = Work.Spaces.DzIter r (Work.Spaces.Dz V) :=
      Work.Spaces.DzIter_add_right r 1 V
    exact congrFun (congrFun h2 z) θ
  have hcongr : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.Dz (Work.Spaces.DzIter r V) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter r (Work.Spaces.Dz V) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    rw [hfun z θ]
  rw [hcongr]
  exact Work.Spaces.L2Sq_DzIter_le_HkSq α k (Work.Spaces.Dz V) hmem r hr

/-- For `r ≤ k`: `∫_z ddIntS (D_z^r V) z ≤ HkSq α k (D_z²V)`. -/
theorem ddIntS_integral_le_HkSq {k r : ℕ} {α : ℝ} {V : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α k (Work.Spaces.DzIter 2 V)) (hr : r ≤ k) :
    (∫ z in Work.Spaces.Iz, ddIntS (Work.Spaces.DzIter r V) z)
      ≤ Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V) := by
  have hstep : (∫ z in Work.Spaces.Iz, ddIntS (Work.Spaces.DzIter r V) z)
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.Dz (Work.Spaces.Dz (Work.Spaces.DzIter r V)) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    rw [ddIntS, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    rw [Work.FTS.EllipticEst.thEta,
      mul_div_rpow_sq_eq (Work.Spaces.Dz (Work.Spaces.Dz (Work.Spaces.DzIter r V)) z θ)
        (Work.Spaces.w z) (Real.sin (2 * θ))
        (Work.FTS.EllipticEst.sin_two_nonneg hθ) Work.Spaces.eta_pos.ne']
    ring
  rw [hstep]
  have hfun : ∀ z θ : ℝ, Work.Spaces.Dz (Work.Spaces.Dz (Work.Spaces.DzIter r V)) z θ
      = Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) z θ := by
    intro z θ
    have h2 : Work.Spaces.DzIter (r + 2) V = Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) :=
      Work.Spaces.DzIter_add_right r 2 V
    exact congrFun (congrFun h2 z) θ
  have hcongr : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.Dz (Work.Spaces.Dz (Work.Spaces.DzIter r V)) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    rw [hfun z θ]
  rw [hcongr]
  exact Work.Spaces.L2Sq_DzIter_le_HkSq α k (Work.Spaces.DzIter 2 V) hmem r hr

/-- For `r ≤ k`: `∫_z ttIntS (D_z^r V) z ≤ HkSq α k (∂_θ²V)`. -/
theorem ttIntS_integral_le_HkSq {k r : ℕ} {α : ℝ} {V : ℝ → ℝ → ℝ}
    (hV : Work.FTS.EllipticEst.SmoothOpen V)
    (hmem : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 V)) (hr : r ≤ k) :
    (∫ z in Work.Spaces.Iz, ttIntS (Work.Spaces.DzIter r V) z)
      ≤ Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V) := by
  have hstep : (∫ z in Work.Spaces.Iz, ttIntS (Work.Spaces.DzIter r V) z)
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter r (Work.Spaces.pthIter 2 V) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    have hA : (∫ z in Work.Spaces.Iz, ttIntS (Work.Spaces.DzIter r V) z)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pthIter 2 (Work.Spaces.DzIter r V) z θ) ^ 2
              * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      rw [ttIntS, ← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
      simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
      ring
    rw [hA]
    rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl,
      ← MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))]
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl,
      ← MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
          (b := Real.pi / 2))]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    rw [pthIter2_DzIter_comm hV hz hθ.1 hθ.2 r, Work.FTS.EllipticEst.thEta,
      mul_div_rpow_sq_eq (Work.Spaces.DzIter r (Work.Spaces.pthIter 2 V) z θ) (Work.Spaces.w z)
        (Real.sin (2 * θ)) hs.le Work.Spaces.eta_pos.ne']
    try ring
  rw [hstep]
  exact Work.Spaces.L2Sq_DzIter_le_HkSq α k (Work.Spaces.pthIter 2 V) hmem r hr

end Work.EllipticEst.Core.i0Aux
