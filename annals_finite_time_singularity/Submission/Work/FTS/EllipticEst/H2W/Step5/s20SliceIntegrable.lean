import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.Mine.SlotDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.FTS.EllipticEst.H2W.Slot01W.SliceRegular
import Submission.Work.FTS.EllipticEst.H2W.Slot01W.SliceKit
import Submission.Work.FTS.EllipticEst.Mine.FSlotsTwoD
import Submission.Work.FTS.EllipticEst.SrcBnd.GsrcPthTwo
import Submission.Work.FTS.EllipticEst.remov.SourceBound.sliceAesmSq
import Submission.Work.FTS.EllipticEst.mul_w_sin_rpow_sq
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.EllipticEst.H2W.pthIter2_DzIter_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.Step5

open MeasureTheory Set Filter
open scoped Real Topology

set_option maxHeartbeats 1600000

/-! ## Elementary helpers -/

/-- The radial weight `w` is positive for `z > 0`. -/
theorem s20si_w_pos {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z := by
  rw [Work.Spaces.w]
  positivity

/-- If `c * g` is integrable on `Iθ` and `c ≠ 0`, then so is `g`. -/
theorem s20si_integrableOn_of_const_mul {g : ℝ → ℝ} {c : ℝ} (hc : c ≠ 0)
    (h : MeasureTheory.IntegrableOn (fun θ => c * g θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn g Work.Spaces.Iθ :=
  MeasureTheory.IntegrableOn.congr_fun (h.const_mul c⁻¹)
    (fun θ _ => by rw [inv_mul_cancel_left₀ hc]) measurableSet_Icc

/-- The `θ`-measurability of the slices of the iterated `∂_θ`-derivatives of `Ψ`, for positive
order (the order `0` slice is an arbitrary function of `θ`). -/
theorem s20si_measurable_pthIter_succ (n : ℕ) (Ψ : ℝ → ℝ → ℝ) (z : ℝ) :
    Measurable (fun θ : ℝ => Work.Spaces.pthIter (n + 1) Ψ z θ) := by
  have h : Measurable (deriv (fun t : ℝ => Work.Spaces.pthIter n Ψ z t)) := measurable_deriv _
  simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pth] using h

/-- `sig2 γ = sin(2θ)^{2-γ}` is continuous for `γ ≤ 2`. -/
theorem s20si_continuous_sig2 {γ : ℝ} (hγ : γ ≤ 2) :
    Continuous (fun θ : ℝ => Work.FTS.EllipticEst.Mine.sig2 γ θ) := by
  have h : Continuous (fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) (2 - γ)) :=
    (Real.continuous_rpow_const (by linarith)).comp
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  simpa only [Work.FTS.EllipticEst.Mine.sig2] using h

/-- `sig4 γ = sin(2θ)^{4-γ}` is continuous for `γ ≤ 4`. -/
theorem s20si_continuous_sig4 {γ : ℝ} (hγ : γ ≤ 4) :
    Continuous (fun θ : ℝ => Work.FTS.EllipticEst.Mine.sig4 γ θ) := by
  have h : Continuous (fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) (4 - γ)) :=
    (Real.continuous_rpow_const (by linarith)).comp
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  simpa only [Work.FTS.EllipticEst.Mine.sig4] using h

/-! ## The target -/

theorem s20SliceIntegrable :
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      ∀ z : ℝ, 0 < z →
        MeasureTheory.IntegrableOn (fun θ => (Ψ z θ) ^ 2) Work.Spaces.Iθ ∧
        MeasureTheory.IntegrableOn (fun θ => (deriv (fun t => Ψ z t) θ) ^ 2) Work.Spaces.Iθ ∧
        MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (fun t => Ψ z t)) θ) ^ 2 *
          Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ ∧
        MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv (fun t => Ψ z t))) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)) Work.Spaces.Iθ ∧
        MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv (deriv (fun t => Ψ z t)))) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α)) Work.Spaces.Iθ ∧
        MeasureTheory.IntegrableOn (fun θ =>
          (deriv (deriv (fun t => Work.FTS.EllipticEst.Mine.Gsrc α F Ψ z t)) θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
  intro α F Ψ hα hα4 h z hz
  have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
  have hw : 0 < Work.Spaces.w z := s20si_w_pos hz
  have hw2 : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hw)
  have hgam2 : Work.Spaces.gam α ≤ 3 / 2 := by rw [Work.Spaces.gam]; linarith
  -- the three `H²`-memberships of the datum
  have hFmem : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α 2 F z θ) Work.Spaces.Iθ := h.memF.1 z hzI
  have hAmem : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α 2
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) Work.Spaces.Iθ := h.memA.1 z hzI
  have hBmem : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ) Work.Spaces.Iθ :=
    h.memB.1 z hzI
  -- ======================================================================
  -- (1), (2), (3): the low-order slots of the slice, from the equation
  -- ======================================================================
  obtain ⟨-, -, -, -, h1, h2, h3⟩ :=
    Work.FTS.EllipticEst.remov.weakSliceRegular 2 (by norm_num) α F Ψ hα hα4 h z hz
  -- ======================================================================
  -- (4): `(∂_θ³Ψ)² σ₂`
  -- ======================================================================
  have h4 : MeasureTheory.IntegrableOn (fun θ =>
      (deriv (deriv (deriv (fun t => Ψ z t))) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
    have hslot : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.w z) ^ 2 *
        ((Work.Spaces.pthIter 3 Ψ z θ) ^ 2 *
          Work.FTS.EllipticEst.Mine.sig2 (Work.Spaces.gam α) θ)) Work.Spaces.Iθ := by
      refine MeasureTheory.Integrable.mono' hBmem ?_ ?_
      · exact (measurable_const.mul (((s20si_measurable_pthIter_succ 2 Ψ z).pow_const 2).mul
          (s20si_continuous_sig2 (by linarith [Work.Spaces.gam_pos hα])).measurable)).aestronglyMeasurable
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _)
          (Work.FTS.EllipticEst.Mine.sig2_nonneg_of_mem_Iθ hθ)))]
        exact Work.FTS.EllipticEst.Mine.sig2_slot_pointwise α hα (Work.Spaces.gam α) hgam2
          le_rfl (Work.Spaces.pthIter 2 Ψ) z θ hθ
    exact s20si_integrableOn_of_const_mul hw2 hslot
  -- ======================================================================
  -- (5): `(∂_θ⁴Ψ)² σ₄`
  -- ======================================================================
  have h5 : MeasureTheory.IntegrableOn (fun θ =>
      (deriv (deriv (deriv (deriv (fun t => Ψ z t)))) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
    have hslot : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.w z) ^ 2 *
        ((Work.Spaces.pthIter 4 Ψ z θ) ^ 2 *
          Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ)) Work.Spaces.Iθ := by
      refine MeasureTheory.Integrable.mono' (hBmem.const_mul 10) ?_ ?_
      · exact (measurable_const.mul (((s20si_measurable_pthIter_succ 3 Ψ z).pow_const 2).mul
          (s20si_continuous_sig4 (by linarith [Work.Spaces.gam_pos hα])).measurable)).aestronglyMeasurable
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _)
          (Work.FTS.EllipticEst.Mine.sig4_nonneg_of_mem_Iθ hθ)))]
        exact Work.FTS.EllipticEst.Mine.sig4_slot_pointwise α hα (Work.Spaces.gam α) hgam2
          le_rfl (Work.Spaces.pthIter 2 Ψ) z θ hθ
    exact s20si_integrableOn_of_const_mul hw2 hslot
  -- ======================================================================
  -- (6): `(∂_θ² G)² σ₄`, `G = Gsrc α F Ψ`
  -- ======================================================================
  have h6 : MeasureTheory.IntegrableOn (fun θ =>
      (deriv (deriv (fun t => Work.FTS.EllipticEst.Mine.Gsrc α F Ψ z t)) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
    have hFso : Work.FTS.EllipticEst.SmoothOpen F := Work.H2W.smoothOpen_source h
    have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
      Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
    set Maj : ℝ → ℝ := fun θ => 3 * ((10 * Work.Spaces.HkIntegrand α 2 F z θ
      + 10 * α ^ 4 * Work.Spaces.HkIntegrand α 2
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ)
      + (α * (5 + α)) ^ 2 * Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ)
      with hMaj
    have hMajint : MeasureTheory.IntegrableOn Maj Work.Spaces.Iθ := by
      rw [hMaj]
      exact (((hFmem.const_mul 10).add (hAmem.const_mul (10 * α ^ 4))).add
        (hBmem.const_mul ((α * (5 + α)) ^ 2))).const_mul 3
    -- the pointwise domination, a.e. on `Iθ`
    have hbd : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        ‖(deriv (deriv (fun t => Work.FTS.EllipticEst.Mine.Gsrc α F Ψ z t)) θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α)‖
          ≤ (Work.Spaces.w z ^ 2)⁻¹ * Maj θ := by
      filter_upwards [Work.FTS.EllipticEst.remov.SourceBound.ae_mem_Ioo_of_mem_Iθ] with θ hθ
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have hsin : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
      have hσ4 : 0 ≤ Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ :=
        Work.FTS.EllipticEst.Mine.sig4_nonneg_of_mem_Iθ hθI
      have hnn : (0 : ℝ) ≤ (deriv (deriv (fun t => Work.FTS.EllipticEst.Mine.Gsrc α F Ψ z t)) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α) :=
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin.le _)
      rw [Real.norm_of_nonneg hnn]
      -- the expansion of `∂_θ²G`
      have hid := Work.FTS.EllipticEst.SrcBnd.GsrcPthTwo (α := α) hFso hΨso z θ hz hθ
      have hcomm := Work.EllipticEst.H2W.pthIter2_DzIter_comm hΨso 1
        (show ((z, θ) : ℝ × ℝ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) from ⟨hz, hθ⟩)
      -- the three slot bounds
      have b1 : (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter 2 F z θ) ^ 2 *
          Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ)
          ≤ 10 * Work.Spaces.HkIntegrand α 2 F z θ :=
        Work.FTS.EllipticEst.Mine.sig4_slot_pointwise α hα (Work.Spaces.gam α) hgam2 le_rfl
          F z θ hθI
      have b2 : (Work.Spaces.w z) ^ 2 *
          ((Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2 *
            Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ)
          ≤ 10 * Work.Spaces.HkIntegrand α 2
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ :=
        Work.FTS.EllipticEst.Mine.sig4_slot_pointwise α hα (Work.Spaces.gam α) hgam2 le_rfl
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ hθI
      have b3 : (Work.Spaces.w z) ^ 2 *
          ((Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2 *
            Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ)
          ≤ Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ := by
        have hsig : Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ
            ≤ Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)) := by
          rw [Work.FTS.EllipticEst.Mine.sig4]
          exact Real.rpow_le_rpow_of_exponent_ge hsin (Real.sin_le_one _)
            (by rw [Work.Spaces.eta]; linarith)
        have hstep : (Work.Spaces.w z) ^ 2 *
            ((Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2 *
              (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            = (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ *
                (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
          rw [Work.FTS.EllipticEst.mul_w_sin_rpow_sq _ _ hθI]
          ring
        have hcomm' : Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ
            = Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ := hcomm
        rw [hcomm']
        calc (Work.Spaces.w z) ^ 2 *
              ((Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2 *
                Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ)
            ≤ (Work.Spaces.w z) ^ 2 *
              ((Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2 *
                Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hsig (sq_nonneg _)) (sq_nonneg _)
          _ = (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ *
                (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
              hstep
          _ ≤ Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ :=
              Work.Spaces.sq_le_HkIntegrand_z α 2 (Work.Spaces.pthIter 2 Ψ) z θ 1
                (by norm_num)
      -- the squaring
      have hsq : (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ) z θ) ^ 2 *
          Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ
          ≤ 3 * ((Work.Spaces.pthIter 2 F z θ) ^ 2 *
                Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ
              + α ^ 4 * ((Work.Spaces.pthIter 2
                    (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2 *
                  Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ)
              + (α * (5 + α)) ^ 2 *
                  ((Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2 *
                    Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ)) := by
        rw [hid]
        have h3 : (Work.Spaces.pthIter 2 F z θ
              + α ^ 2 * Work.Spaces.pthIter 2
                  (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
              + α * (5 + α) * Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
            ≤ 3 * ((Work.Spaces.pthIter 2 F z θ) ^ 2
              + (α ^ 2 * Work.Spaces.pthIter 2
                  (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
              + (α * (5 + α) * Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2) := by
          nlinarith [sq_nonneg (Work.Spaces.pthIter 2 F z θ
              - α ^ 2 * Work.Spaces.pthIter 2
                  (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ),
            sq_nonneg (α ^ 2 * Work.Spaces.pthIter 2
                  (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
              - α * (5 + α) * Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ),
            sq_nonneg (Work.Spaces.pthIter 2 F z θ
              - α * (5 + α) * Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)]
        calc (Work.Spaces.pthIter 2 F z θ
              + α ^ 2 * Work.Spaces.pthIter 2
                  (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
              + α * (5 + α) * Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2 *
              Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ
            ≤ 3 * ((Work.Spaces.pthIter 2 F z θ) ^ 2
              + (α ^ 2 * Work.Spaces.pthIter 2
                  (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
              + (α * (5 + α) * Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2) *
                Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ :=
              mul_le_mul_of_nonneg_right h3 hσ4
          _ = 3 * ((Work.Spaces.pthIter 2 F z θ) ^ 2 *
                Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ
              + α ^ 4 * ((Work.Spaces.pthIter 2
                    (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2 *
                  Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ)
              + (α * (5 + α)) ^ 2 *
                  ((Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2 *
                    Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ)) := by
              ring
      -- assembly
      have hfinal : (Work.Spaces.w z) ^ 2 *
          ((Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ) z θ) ^ 2 *
            Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ) ≤ Maj θ := by
        rw [hMaj]
        have hstep := mul_le_mul_of_nonneg_left hsq (sq_nonneg (Work.Spaces.w z))
        have hd : (Work.Spaces.w z) ^ 2 * (3 *
              ((Work.Spaces.pthIter 2 F z θ) ^ 2 * Work.FTS.EllipticEst.Mine.sig4
                  (Work.Spaces.gam α) θ
                + α ^ 4 * ((Work.Spaces.pthIter 2
                      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2 *
                    Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ)
                + (α * (5 + α)) ^ 2 *
                    ((Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2 *
                      Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ)))
            = 3 * ((Work.Spaces.w z) ^ 2 *
                  ((Work.Spaces.pthIter 2 F z θ) ^ 2 * Work.FTS.EllipticEst.Mine.sig4
                    (Work.Spaces.gam α) θ)
                + α ^ 4 * ((Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter 2
                      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2 *
                    Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ))
                + (α * (5 + α)) ^ 2 * ((Work.Spaces.w z) ^ 2 *
                    ((Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2 *
                      Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ))) := by
          ring
        rw [hd] at hstep
        have hA : α ^ 4 * ((Work.Spaces.w z) ^ 2 *
              ((Work.Spaces.pthIter 2
                  (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2 *
                Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ))
            ≤ α ^ 4 * (10 * Work.Spaces.HkIntegrand α 2
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) :=
          mul_le_mul_of_nonneg_left b2 (pow_nonneg hα.le 4)
        have hC : (α * (5 + α)) ^ 2 * ((Work.Spaces.w z) ^ 2 *
              ((Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2 *
                Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ))
            ≤ (α * (5 + α)) ^ 2 * Work.Spaces.HkIntegrand α 2
                (Work.Spaces.pthIter 2 Ψ) z θ :=
          mul_le_mul_of_nonneg_left b3 (sq_nonneg _)
        linarith [hstep, b1, hA, hC]
      have hle := mul_le_mul_of_nonneg_left hfinal (inv_nonneg.mpr (sq_nonneg (Work.Spaces.w z)))
      rwa [inv_mul_cancel_left₀ hw2] at hle
    refine MeasureTheory.Integrable.mono' (hMajint.const_mul ((Work.Spaces.w z) ^ 2)⁻¹) ?_ hbd
    exact ((measurable_deriv (deriv (fun t => Work.FTS.EllipticEst.Mine.Gsrc α F Ψ z t))).pow_const 2
      |>.mul (s20si_continuous_sig4 (by linarith [Work.Spaces.gam_pos hα])).measurable).aestronglyMeasurable
  exact ⟨h1, h2, h3, h4, h5, h6⟩

end Work.FTS.EllipticEst.H2W.Step5
