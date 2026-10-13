import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.ClassC.VopGen.Core.truncPoint
import Submission.Work.FTS.EllipticEst.Prop.zIbpTwoD

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.ClassC.VopGen.Core.truncBound` — the per-cut-off inequality of the truncation half

For a logarithmic cut-off family `χ` with `|z·χ_N·χ_N'| ≤ C₀·χ_N` and vanishing off
`[1/(N+1), 2(N+1)]`, the a.e.-slice Agmon inequality for `X = D_z(z²∂_z²Ψ)`, integrated against
`(χ_N)²w²` and radially integrated by parts, gives
`∫_z (χ_N)²·∫_θ(∂_θX)²w²σ ≤ (C₀+2)(∫∫(D_zX)²w²σ + ∫∫X²w²σ + ∫∫Y²w²σ)` for `Y = ∂_θ²(z²∂_z²Ψ)`.
-/

namespace Work.FTS.ClassC.VopGen.Core

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 3200000

open Work.Spaces (HkSq HkMem HkIntegrand HkIntegrand_nonneg w Iz Iθ Dz DzIter pth pz)

local notation "Aof" => Work.FTS.EllipticEst.H2W.Aof

/-- **The per-cut-off inequality.** -/
theorem perNBound {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ)
    (hsl : ∀ᵐ z ∂(volume.restrict Iz),
      (∫ θ in Iθ, (pth (XX Ψ) z θ) ^ 2 * sgm α θ)
        ≤ -(∫ θ in Iθ, XX Ψ z θ * Dz (YY Ψ) z θ * sgm α θ))
    {χ : ℕ → ℝ → ℝ} {C₀ : ℝ} (hC₀pos : 0 < C₀)
    (hχcd : ∀ N : ℕ, ContDiff ℝ Work.Stability.smoothOrder (χ N))
    (hχnn : ∀ N z, 0 ≤ χ N z) (hχle : ∀ N z, χ N z ≤ 1)
    (hχsmall : ∀ (N : ℕ) (z : ℝ), z ≤ 1 / ((N : ℝ) + 1) → χ N z = 0)
    (hχbig : ∀ (N : ℕ) (z : ℝ), 2 * ((N : ℝ) + 1) ≤ z → χ N z = 0)
    (hχbd : ∀ (N : ℕ) (z : ℝ), |z * χ N z * deriv (χ N) z| ≤ C₀ * χ N z) :
    ∀ N : ℕ,
      (∫ z in Iz, (χ N z) ^ 2 * (∫ θ in Iθ, (pth (XX Ψ) z θ) ^ 2 * (w z) ^ 2 * sgm α θ))
        ≤ (C₀ + 2) * ((∫ z in Iz, ∫ θ in Iθ,
              (Dz (XX Ψ) z θ) ^ 2 * (w z) ^ 2 * sgm α θ)
          + (∫ z in Iz, ∫ θ in Iθ, (XX Ψ z θ) ^ 2 * (w z) ^ 2 * sgm α θ)
          + (∫ z in Iz, ∫ θ in Iθ, (YY Ψ z θ) ^ 2 * (w z) ^ 2 * sgm α θ)) := by
  have hα1 : α ≤ 1 := by linarith
  have hC₀ : 0 ≤ C₀ := hC₀pos.le
  have hχm : ∀ N : ℕ, Measurable (χ N) := fun N => (hχcd N).continuous.measurable
  have hAof : Work.FTS.EllipticEst.SmoothOpen (Aof Ψ) :=
    Work.FTS.EllipticEst.Prop.aofSmoothOpen
      (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth)
  have hXX : Work.FTS.EllipticEst.SmoothOpen (XX Ψ) := hAof.Dz
  have hYY : Work.FTS.EllipticEst.SmoothOpen (YY Ψ) := hAof.pth.pth
  obtain ⟨slDX, outDX, prDX, fuDX⟩ := slotFacts_pure hα1 hα hα4 h 2 (by norm_num)
  obtain ⟨slX, outX, prX, fuX⟩ := slotFacts_pure hα1 hα hα4 h 1 (by norm_num)
  obtain ⟨slY, outY, prY, fuY⟩ := slotFacts_ang hα1 hα hα4 h
  have hMaj := outerMajorant hα hα4 h
  have hpairQ := pairOuterIntegrable hα hα4 h
  have slZd := clairautSlice hα hα4 h
  intro N
  have hχd : Differentiable ℝ (χ N) := (hχcd N).differentiable (by simp)
  have hstep : (∫ z in Iz, (χ N z) ^ 2 * (∫ θ in Iθ,
        (pth (XX Ψ) z θ) ^ 2 * (w z) ^ 2 * sgm α θ))
      ≤ -(∫ z in Iz, (χ N z) ^ 2 * (∫ θ in Iθ, (w z) ^ 2
          * (XX Ψ z θ * Dz (YY Ψ) z θ * sgm α θ))) := by
    refine (MeasureTheory.integral_mono_of_nonneg
      (f := fun z => (χ N z) ^ 2 * (∫ θ in Iθ,
        (pth (XX Ψ) z θ) ^ 2 * (w z) ^ 2 * sgm α θ))
      (g := fun z => -((χ N z) ^ 2 * (∫ θ in Iθ, (w z) ^ 2
        * (XX Ψ z θ * Dz (YY Ψ) z θ * sgm α θ)))) ?_ ?_ ?_).trans (le_of_eq ?_)
    · filter_upwards with z
      exact mul_nonneg (sq_nonneg _) (MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
          (by rw [sgm]; exact sigma_nonneg hθ)))
    · refine MeasureTheory.Integrable.mono' hMaj ?_ ?_
      · refine (((hχm N).pow_const 2).aestronglyMeasurable.mul ?_).neg
        exact hpairQ.aestronglyMeasurable
      · filter_upwards [slX, slZd] with z hzX hzZ
        have h1 : |∫ θ in Iθ, (w z) ^ 2 * (XX Ψ z θ * Dz (YY Ψ) z θ * sgm α θ)|
            ≤ ∫ θ in Iθ, (w z) ^ 2 * ((XX Ψ z θ) ^ 2
              + (Dz (YY Ψ) z θ) ^ 2) * sgm α θ := by
          refine le_trans (MeasureTheory.abs_integral_le_integral_abs) ?_
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun θ => abs_nonneg _) ?_ ?_
          · refine MeasureTheory.Integrable.congr (hzX.add hzZ) ?_
            filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ _
            simp only [Pi.add_apply, XX, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
            ring
          · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
            beta_reduce
            have hs : 0 ≤ sgm α θ := by rw [sgm]; exact sigma_nonneg hθ
            rw [abs_mul]
            rw [abs_of_nonneg (sq_nonneg (w z))]
            rw [abs_mul]
            rw [abs_mul]
            rw [abs_of_nonneg hs]
            have hA : 2 * (|XX Ψ z θ| * |Dz (YY Ψ) z θ|)
                ≤ (XX Ψ z θ) ^ 2 + (Dz (YY Ψ) z θ) ^ 2 := by
              nlinarith [sq_nonneg (|XX Ψ z θ| - |Dz (YY Ψ) z θ|), sq_abs (XX Ψ z θ),
                sq_abs (Dz (YY Ψ) z θ)]
            have hxy : 0 ≤ (XX Ψ z θ) ^ 2 + (Dz (YY Ψ) z θ) ^ 2 := by positivity
            calc (w z) ^ 2 * (|XX Ψ z θ| * |Dz (YY Ψ) z θ| * sgm α θ)
                = (w z) ^ 2 * sgm α θ * (|XX Ψ z θ| * |Dz (YY Ψ) z θ|) := by ring
              _ ≤ (w z) ^ 2 * sgm α θ
                    * (((XX Ψ z θ) ^ 2 + (Dz (YY Ψ) z θ) ^ 2) / 2) :=
                    mul_le_mul_of_nonneg_left (by linarith [hA])
                      (mul_nonneg (sq_nonneg _) hs)
              _ ≤ (w z) ^ 2 * ((XX Ψ z θ) ^ 2 + (Dz (YY Ψ) z θ) ^ 2) * sgm α θ := by
                    nlinarith [mul_nonneg (sq_nonneg (w z)) hs, hxy]
        have hM0 : 0 ≤ ∫ θ in Iθ, (w z) ^ 2 * ((XX Ψ z θ) ^ 2
            + (Dz (YY Ψ) z θ) ^ 2) * sgm α θ :=
          MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => by
            have hs : 0 ≤ sgm α θ := by rw [sgm]; exact sigma_nonneg hθ
            exact mul_nonneg (mul_nonneg (sq_nonneg _)
              (add_nonneg (sq_nonneg _) (sq_nonneg _))) hs)
        rw [Real.norm_eq_abs]
        rw [abs_neg]
        rw [abs_mul]
        rw [abs_of_nonneg (sq_nonneg (χ N z))]
        refine (mul_le_mul_of_nonneg_left h1 (sq_nonneg (χ N z))).trans ?_
        exact mul_le_of_le_one_left hM0 (by nlinarith [hχnn N z, hχle N z])
    · filter_upwards [hsl] with z hz
      have h2 : (∫ θ in Iθ, (pth (XX Ψ) z θ) ^ 2 * (w z) ^ 2 * sgm α θ)
          = (w z) ^ 2 * (∫ θ in Iθ, (pth (XX Ψ) z θ) ^ 2 * sgm α θ) := by
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
      have h3 : (∫ θ in Iθ, (w z) ^ 2 * (XX Ψ z θ * Dz (YY Ψ) z θ * sgm α θ))
          = (w z) ^ 2 * (∫ θ in Iθ, XX Ψ z θ * Dz (YY Ψ) z θ * sgm α θ) := by
        rw [← MeasureTheory.integral_const_mul]
      rw [h2, h3]
      have h4 : (w z) ^ 2 * (∫ θ in Iθ, (pth (XX Ψ) z θ) ^ 2 * sgm α θ)
          ≤ (w z) ^ 2 * (-(∫ θ in Iθ, XX Ψ z θ * Dz (YY Ψ) z θ * sgm α θ)) :=
        mul_le_mul_of_nonneg_left hz (sq_nonneg (w z))
      have h5 := mul_le_mul_of_nonneg_left h4 (sq_nonneg (χ N z))
      simp only [mul_neg] at h5
      exact h5
    · exact MeasureTheory.integral_neg _
  have hintZ : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => (χ N p.1) ^ 2 * ((w p.1) ^ 2 * (XX Ψ p.1 p.2
        * Dz (YY Ψ) p.1 p.2 * sgm α p.2))) (Iz ×ˢ Iθ) := by
    refine MeasureTheory.Integrable.mono' (prX.add (clairautSlot hα hα4 h)) ?_ ?_
    · have hwc : ContinuousOn (fun p : ℝ × ℝ => (χ N p.1) ^ 2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
        ((hχcd N).continuous.comp_continuousOn continuousOn_fst).pow 2
      have hwc2 : ContinuousOn (fun p : ℝ × ℝ => (w p.1) ^ 2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
        Work.FTS.ClassC.aslotAux.BslOpPth.continuousOn_w_sq_Q0
      have hXc : ContinuousOn (fun p : ℝ × ℝ => XX Ψ p.1 p.2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
        smoothOpen_continuousOn hXX
      have hDY : ContinuousOn (fun p : ℝ × ℝ => Dz (YY Ψ) p.1 p.2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
        smoothOpen_continuousOn hYY.Dz
      have h4 : ContinuousOn (fun p : ℝ × ℝ => sgm α p.2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
        continuousOn_sgm_Q0 α
      have hcont : ContinuousOn (fun p : ℝ × ℝ => (χ N p.1) ^ 2 * ((w p.1) ^ 2
          * (XX Ψ p.1 p.2 * Dz (YY Ψ) p.1 p.2 * sgm α p.2)))
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
        have h5 := (hwc.mul (hwc2.mul (hXc.mul hDY))).mul h4
        convert h5 using 1
        ext p
        simp only [Pi.mul_apply]
        ring
      have h6 := Work.Spaces.aesm_of_continuousOn_Qd _ hcont
      rwa [prod_restrict_eq_rect] at h6
    · refine MeasureTheory.ae_restrict_of_forall_mem
        (measurableSet_Ici.prod measurableSet_Icc) (fun p hp => ?_)
      have hs : 0 ≤ sgm α p.2 := by rw [sgm]; exact sigma_nonneg hp.2
      have hw : 0 ≤ (w p.1) ^ 2 := sq_nonneg _
      have hχ2 : (χ N p.1) ^ 2 ≤ 1 := by
        nlinarith [hχnn N p.1, hχle N p.1, sq_nonneg (χ N p.1)]
      have h2 : 2 * |XX Ψ p.1 p.2| * |Dz (YY Ψ) p.1 p.2|
          ≤ (XX Ψ p.1 p.2) ^ 2 + (Dz (YY Ψ) p.1 p.2) ^ 2 := by
        have h := sq_nonneg (|XX Ψ p.1 p.2| - |Dz (YY Ψ) p.1 p.2|)
        rw [sub_sq, sq_abs, sq_abs] at h
        nlinarith [h]
      have hmid : |XX Ψ p.1 p.2| * |Dz (YY Ψ) p.1 p.2|
          ≤ ((XX Ψ p.1 p.2) ^ 2 + (Dz (YY Ψ) p.1 p.2) ^ 2) / 2 := by
        linarith [h2]
      have h5 : 0 ≤ (w p.1) ^ 2 * sgm α p.2 := mul_nonneg hw hs
      rw [Real.norm_eq_abs]
      rw [abs_mul]
      rw [abs_mul]
      rw [abs_mul]
      rw [abs_mul]
      rw [abs_of_nonneg (sq_nonneg _)]
      rw [abs_of_nonneg hw]
      rw [abs_of_nonneg hs]
      calc (χ N p.1) ^ 2 * ((w p.1) ^ 2 * (|XX Ψ p.1 p.2|
            * |Dz (YY Ψ) p.1 p.2| * sgm α p.2))
          ≤ 1 * ((w p.1) ^ 2 * (|XX Ψ p.1 p.2| * |Dz (YY Ψ) p.1 p.2| * sgm α p.2)) :=
            mul_le_mul_of_nonneg_right hχ2
              (mul_nonneg hw (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hs))
        _ = (w p.1) ^ 2 * sgm α p.2
              * (|XX Ψ p.1 p.2| * |Dz (YY Ψ) p.1 p.2|) := by ring
        _ ≤ (w p.1) ^ 2 * sgm α p.2
              * (((XX Ψ p.1 p.2) ^ 2 + (Dz (YY Ψ) p.1 p.2) ^ 2) / 2) :=
            mul_le_mul_of_nonneg_left hmid h5
        _ ≤ (XX Ψ p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2
              + (Dz (YY Ψ) p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2 := by
            have ha : 0 ≤ (XX Ψ p.1 p.2) ^ 2 * ((w p.1) ^ 2 * sgm α p.2) :=
              mul_nonneg (sq_nonneg _) h5
            have hb : 0 ≤ (Dz (YY Ψ) p.1 p.2) ^ 2 * ((w p.1) ^ 2 * sgm α p.2) :=
              mul_nonneg (sq_nonneg _) h5
            linarith
  have hFub : (∫ z in Iz, (χ N z) ^ 2 * (∫ θ in Iθ, (w z) ^ 2
        * (XX Ψ z θ * Dz (YY Ψ) z θ * sgm α θ)))
      = ∫ p in Iz ×ˢ Iθ, (w p.1) ^ 2 * ((χ N p.1) ^ 2 * XX Ψ p.1 p.2 * sgm α p.2)
          * Dz (YY Ψ) p.1 p.2 := by
    have h1 : (∫ z in Iz, (χ N z) ^ 2 * (∫ θ in Iθ, (w z) ^ 2
          * (XX Ψ z θ * Dz (YY Ψ) z θ * sgm α θ)))
        = ∫ z in Iz, ∫ θ in Iθ, (χ N z) ^ 2 * ((w z) ^ 2
          * (XX Ψ z θ * Dz (YY Ψ) z θ * sgm α θ)) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      beta_reduce
      have hL : (∫ θ in Iθ, (w z) ^ 2 * (XX Ψ z θ * Dz (YY Ψ) z θ * sgm α θ))
          = (w z) ^ 2 * ∫ θ in Iθ, XX Ψ z θ * Dz (YY Ψ) z θ * sgm α θ :=
        MeasureTheory.integral_const_mul _ _
      have hR : (∫ θ in Iθ, (χ N z) ^ 2
            * ((w z) ^ 2 * (XX Ψ z θ * Dz (YY Ψ) z θ * sgm α θ)))
          = (χ N z) ^ 2 * (w z) ^ 2
            * ∫ θ in Iθ, XX Ψ z θ * Dz (YY Ψ) z θ * sgm α θ := by
        rw [MeasureTheory.integral_const_mul]
        rw [MeasureTheory.integral_const_mul]
        ring
      rw [hL, hR]
      ring
    rw [h1, ← MeasureTheory.setIntegral_prod
      (fun p : ℝ × ℝ => (χ N p.1) ^ 2 * ((w p.1) ^ 2 * (XX Ψ p.1 p.2
        * Dz (YY Ψ) p.1 p.2 * sgm α p.2))) hintZ]
    refine MeasureTheory.setIntegral_congr_fun (measurableSet_Ici.prod measurableSet_Icc)
      (fun p _ => by ring)
  have hint1 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (w p.1) ^ 2
      * ((χ N p.1) ^ 2 * XX Ψ p.1 p.2 * sgm α p.2)
      * (p.1 * deriv (fun z' => YY Ψ z' p.2) p.1)) (Iz ×ˢ Iθ) :=
    MeasureTheory.Integrable.congr hintZ (Filter.Eventually.of_forall fun p => by
      simp only [Dz, pz]; ring)
  have hφ : ∀ᵐ θ ∂(volume.restrict Iθ), ContDiffOn ℝ 1
      (fun z => (χ N z) ^ 2 * XX Ψ z θ * sgm α θ) (Set.Ioi 0) := by
    rw [restrict_Iθ_eq_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have h1 : ContDiffOn ℝ 1 (fun z => (χ N z) ^ 2) (Set.Ioi 0) := by
      have hc : ContDiffOn ℝ 1 (χ N) (Set.Ioi 0) :=
        ((hχcd N).of_le (by simp [Work.Stability.smoothOrder])).contDiffOn
      simpa only [sq] using hc.mul hc
    have h2 : ContDiffOn ℝ 1 (fun z => XX Ψ z θ) (Set.Ioi 0) :=
      (hXX.curry_z hθ).of_le (by simp [Work.Stability.smoothOrder])
    exact (h1.mul h2).mul contDiffOn_const
  have hψ : ∀ᵐ θ ∂(volume.restrict Iθ), ContDiffOn ℝ 1
      (fun z => YY Ψ z θ) (Set.Ioi 0) := by
    rw [restrict_Iθ_eq_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    exact (hYY.curry_z hθ).of_le (by simp [Work.Stability.smoothOrder])
  have hf0 : ∀ᵐ θ ∂(volume.restrict Iθ), Filter.Tendsto
      (fun z => z * (w z) ^ 2 * ((χ N z) ^ 2 * XX Ψ z θ * sgm α θ) * YY Ψ z θ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    filter_upwards with θ
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    have hpos : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
    filter_upwards [nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hpos)] with z hz
    rw [hχsmall N z (le_of_lt hz)]
    ring
  have hf1 : ∀ᵐ θ ∂(volume.restrict Iθ), Filter.Tendsto
      (fun z => z * (w z) ^ 2 * ((χ N z) ^ 2 * XX Ψ z θ * sgm α θ) * YY Ψ z θ)
      Filter.atTop (nhds 0) := by
    filter_upwards with θ
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop (2 * ((N : ℝ) + 1))] with z hz
    rw [hχbig N z hz]
    ring
  have hJint := majIntegrable (F := F) hα hα4 h (C₀ := C₀)
  have hPTe := pointwiseBound (F := F) hα hα4 h (χ := χ N) (C₀ := C₀) hC₀
    (hχnn N) (hχle N) (hχbd N)
  have hint2 := derivFormIntegrable (F := F) hα hα4 h (χ := χ N) (C₀ := C₀) hC₀
    (hχcd N) (hχnn N) (hχle N) (hχbd N)
  have hibp := Work.FTS.EllipticEst.Prop.zIbpTwoD
    (φ := fun z θ => (χ N z) ^ 2 * XX Ψ z θ * sgm α θ) (ψ := YY Ψ)
    hint1 hint2 hφ hψ hf0 hf1
  have hPt : ∀ᵐ p ∂(volume.restrict (Iz ×ˢ Iθ)),
      -((w p.1) ^ 2 * (-(p.1 * deriv (fun z' =>
            (χ N z') ^ 2 * XX Ψ z' p.2 * sgm α p.2) p.1)
          - ((p.1 - 3) / (1 + p.1)) * ((χ N p.1) ^ 2 * XX Ψ p.1 p.2 * sgm α p.2))
        * YY Ψ p.1 p.2)
      ≤ (C₀ + 2) * ((Dz (XX Ψ) p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2
        + ((XX Ψ p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2
          + (YY Ψ p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2)) := by
    filter_upwards [hPTe, ae_mem_Q0_prod] with p hpt hp
    have h1 : (w p.1) ^ 2 * (-(p.1 * deriv (fun z' =>
            (χ N z') ^ 2 * XX Ψ z' p.2 * sgm α p.2) p.1)
          - ((p.1 - 3) / (1 + p.1)) * ((χ N p.1) ^ 2 * XX Ψ p.1 p.2 * sgm α p.2))
        * YY Ψ p.1 p.2
        = (w p.1) ^ 2 * (-(sgm α p.2 * ((2 * (p.1 * χ N p.1 * deriv (χ N) p.1))
              * XX Ψ p.1 p.2 + (χ N p.1) ^ 2 * Dz (XX Ψ) p.1 p.2))
          - ((p.1 - 3) / (1 + p.1)) * ((χ N p.1) ^ 2 * XX Ψ p.1 p.2 * sgm α p.2))
        * YY Ψ p.1 p.2 := by
      rw [deriv_chi_sq_mul_sgm hXX hχd hp.2 hp.1]
      simp only [Dz, pz]
    rw [h1]
    exact le_trans (neg_le_abs _) hpt
  have hQval : (∫ p in Iz ×ˢ Iθ, (C₀ + 2) *
      ((Dz (XX Ψ) p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2
        + ((XX Ψ p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2
          + (YY Ψ p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2)))
      = (C₀ + 2) * ((∫ z in Iz, ∫ θ in Iθ, (Dz (XX Ψ) z θ) ^ 2 * (w z) ^ 2 * sgm α θ)
        + (∫ z in Iz, ∫ θ in Iθ, (XX Ψ z θ) ^ 2 * (w z) ^ 2 * sgm α θ)
        + (∫ z in Iz, ∫ θ in Iθ, (YY Ψ z θ) ^ 2 * (w z) ^ 2 * sgm α θ)) := by
    have prDX' : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ
        => (Dz (XX Ψ) p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2) (Iz ×ˢ Iθ) := by
      simpa only [XX, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using prDX
    have prX' : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ
        => (XX Ψ p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2) (Iz ×ˢ Iθ) := by
      simpa only [XX, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using prX
    have prY' : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ
        => (YY Ψ p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2) (Iz ×ˢ Iθ) := prY
    rw [MeasureTheory.integral_const_mul]
    have hbc : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ
        => (XX Ψ p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2
          + (YY Ψ p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2) (Iz ×ˢ Iθ) :=
      MeasureTheory.Integrable.add prX' prY'
    rw [MeasureTheory.integral_add prDX' hbc]
    rw [MeasureTheory.integral_add prX' prY']
    rw [show (∫ p in Iz ×ˢ Iθ, (Dz (XX Ψ) p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2)
        = ∫ p in Iz ×ˢ Iθ, (DzIter 2 (Aof Ψ) p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2 from by
      refine MeasureTheory.setIntegral_congr_fun (measurableSet_Ici.prod measurableSet_Icc)
        (fun p _ => ?_)
      simp only [XX, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]]
    rw [show (∫ p in Iz ×ˢ Iθ, (XX Ψ p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2)
        = ∫ p in Iz ×ˢ Iθ, (DzIter 1 (Aof Ψ) p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2 from by
      refine MeasureTheory.setIntegral_congr_fun (measurableSet_Ici.prod measurableSet_Icc)
        (fun p _ => ?_)
      simp only [XX, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]]
    rw [show (∫ p in Iz ×ˢ Iθ, (YY Ψ p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2)
        = ∫ p in Iz ×ˢ Iθ, (Work.Spaces.pthIter 2 (Aof Ψ) p.1 p.2) ^ 2
            * (w p.1) ^ 2 * sgm α p.2 from by
      refine MeasureTheory.setIntegral_congr_fun (measurableSet_Ici.prod measurableSet_Icc)
        (fun p _ => ?_)
      simp only [YY]]
    rw [fuDX, fuX, fuY]
    simp only [XX, YY, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
    ring
  calc (∫ z in Iz, (χ N z) ^ 2 * (∫ θ in Iθ,
        (pth (XX Ψ) z θ) ^ 2 * (w z) ^ 2 * sgm α θ))
      ≤ -(∫ z in Iz, (χ N z) ^ 2 * (∫ θ in Iθ, (w z) ^ 2
          * (XX Ψ z θ * Dz (YY Ψ) z θ * sgm α θ))) := hstep
    _ = -(∫ p in Iz ×ˢ Iθ, (w p.1) ^ 2 * ((χ N p.1) ^ 2 * XX Ψ p.1 p.2 * sgm α p.2)
          * Dz (YY Ψ) p.1 p.2) := by rw [hFub]
    _ = -(∫ p in Iz ×ˢ Iθ, (w p.1) ^ 2 * ((χ N p.1) ^ 2 * XX Ψ p.1 p.2 * sgm α p.2)
          * (p.1 * deriv (fun z' => YY Ψ z' p.2) p.1)) := by
        refine congrArg Neg.neg ?_
        refine MeasureTheory.setIntegral_congr_fun (measurableSet_Ici.prod measurableSet_Icc)
          (fun p _ => ?_)
        simp only [Dz, pz]
    _ = -(∫ p in Iz ×ˢ Iθ, (w p.1) ^ 2 * (-(p.1 * deriv (fun z' =>
            (χ N z') ^ 2 * XX Ψ z' p.2 * sgm α p.2) p.1)
          - ((p.1 - 3) / (1 + p.1)) * ((χ N p.1) ^ 2 * XX Ψ p.1 p.2 * sgm α p.2))
        * YY Ψ p.1 p.2) := by rw [hibp]
    _ = ∫ p in Iz ×ˢ Iθ, -((w p.1) ^ 2 * (-(p.1 * deriv (fun z' =>
            (χ N z') ^ 2 * XX Ψ z' p.2 * sgm α p.2) p.1)
          - ((p.1 - 3) / (1 + p.1)) * ((χ N p.1) ^ 2 * XX Ψ p.1 p.2 * sgm α p.2))
        * YY Ψ p.1 p.2) := (MeasureTheory.integral_neg _).symm
    _ ≤ ∫ p in Iz ×ˢ Iθ, (C₀ + 2) *
        ((Dz (XX Ψ) p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2
          + ((XX Ψ p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2
            + (YY Ψ p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2)) :=
        MeasureTheory.integral_mono_ae hint2.neg hJint hPt
    _ = (C₀ + 2) * ((∫ z in Iz, ∫ θ in Iθ, (Dz (XX Ψ) z θ) ^ 2 * (w z) ^ 2 * sgm α θ)
        + (∫ z in Iz, ∫ θ in Iθ, (XX Ψ z θ) ^ 2 * (w z) ^ 2 * sgm α θ)
        + (∫ z in Iz, ∫ θ in Iθ, (YY Ψ z θ) ^ 2 * (w z) ^ 2 * sgm α θ)) := hQval

end

end Work.FTS.ClassC.VopGen.Core
