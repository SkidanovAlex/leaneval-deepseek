import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.H2W.Slot01W.SliceKit
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.EllipticEst.remov.wsMomentId
import Submission.Work.FTS.LocDataExt.Final
import Submission.Work.FTS.LocDataExt.LocG5
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2W.sliceStep4Uniform
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT.Slot11

open MeasureTheory Set Filter
open scoped Real Topology

/-- `1 ≤ w z` for `z > 0`, hence `1 ≤ (w z)²`. -/
private theorem one_le_w_sq {z : ℝ} (hz : 0 < z) : 1 ≤ (Work.Spaces.w z) ^ 2 := by
  have hwpos : 1 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
    nlinarith [hz]
  nlinarith [hwpos]

/-- The elementary square bound for the decomposition of the source's derivative. -/
private theorem sq_sum_le_three {α x y z w : ℝ} :
    (x + α ^ 2 * y + α * (5 + α) * (z + w)) ^ 2
      ≤ 3 * x ^ 2 + 3 * α ^ 4 * y ^ 2 + 6 * (α * (5 + α)) ^ 2 * (z ^ 2 + w ^ 2) := by
  have h1 : (x + α ^ 2 * y + α * (5 + α) * (z + w)) ^ 2
      ≤ 3 * (x ^ 2 + (α ^ 2 * y) ^ 2 + (α * (5 + α) * (z + w)) ^ 2) := by
    nlinarith [sq_nonneg (x - α ^ 2 * y), sq_nonneg (α ^ 2 * y - α * (5 + α) * (z + w)),
      sq_nonneg (x - α * (5 + α) * (z + w))]
  have h2 : (z + w) ^ 2 ≤ 2 * (z ^ 2 + w ^ 2) := by nlinarith [sq_nonneg (z - w)]
  have h3 : (α * (5 + α) * (z + w)) ^ 2 = (α * (5 + α)) ^ 2 * (z + w) ^ 2 := by ring
  have h5 : (α * (5 + α)) ^ 2 * (z + w) ^ 2 ≤ (α * (5 + α)) ^ 2 * (2 * (z ^ 2 + w ^ 2)) :=
    mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  nlinarith [h1, h3, h5]

/-- `(1,1)`-slot of a `SmoothOpen` function is `sin(2θ)` times the angular derivative of its
shifted version `D_z f`. -/
private theorem mixed11_eq_sin_mul_pth {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.mixed 1 1 f z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter 1 f) z θ := by
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have hcd : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ) :=
    (hf.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)).of_le (by
      rw [Work.Stability.smoothOrder]; exact WithTop.coe_le_coe.mpr le_top)
  show Work.Spaces.Dz (Work.Spaces.Dth f) z θ
    = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter 1 f) z θ
  rw [Work.Spaces.Dz_Dth_comm hcd]
  rfl

/-- The shifted slot `(∂_θ(D_z f))² σ₂(γ)` is dominated by a slot of `HkIntegrand α 2 f`. -/
private theorem shiftPth_slot_le {α γ : ℝ} (hα : 0 < α) (hγ2 : γ ≤ 3 / 2)
    (hγg : γ ≤ Work.Spaces.gam α) {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Work.Spaces.pth (Work.Spaces.DzIter 1 f) z θ) ^ 2 * Work.FTS.EllipticEst.Mine.sig2 γ θ
      ≤ Work.Spaces.HkIntegrand α 2 f z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hsp : (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      = (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    have h3 := Real.rpow_add hs (2 : ℝ) (-(Work.Spaces.gam α))
    rw [show (2 : ℝ) + -(Work.Spaces.gam α) = 2 - Work.Spaces.gam α by ring] at h3
    simpa using h3
  have hslot : (Work.Spaces.mixed 1 1 f z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2
        * ((Work.Spaces.pth (Work.Spaces.DzIter 1 f) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) := by
    rw [mixed11_eq_sin_mul_pth hf hz hθ, hsp, mul_pow,
      Work.FTS.EllipticEst.Mine.Wt_sq α z θ hα hθI]
    ring
  have hle : Work.FTS.EllipticEst.Mine.sig2 γ θ ≤ (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) :=
    Real.rpow_le_rpow_of_exponent_ge hs hs1 (by linarith)
  have hnn : 0 ≤ (Work.Spaces.pth (Work.Spaces.DzIter 1 f) z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs.le _)
  calc (Work.Spaces.pth (Work.Spaces.DzIter 1 f) z θ) ^ 2 * Work.FTS.EllipticEst.Mine.sig2 γ θ
      ≤ (Work.Spaces.pth (Work.Spaces.DzIter 1 f) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) :=
        mul_le_mul_of_nonneg_left hle (sq_nonneg _)
    _ = 1 * ((Work.Spaces.pth (Work.Spaces.DzIter 1 f) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) := by ring
    _ ≤ (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pth (Work.Spaces.DzIter 1 f) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) :=
        mul_le_mul_of_nonneg_right (one_le_w_sq hz) hnn
    _ = (Work.Spaces.mixed 1 1 f z θ * Work.Spaces.Wt α z θ) ^ 2 := hslot.symm
    _ ≤ Work.Spaces.HkIntegrand α 2 f z θ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α 2 f z θ 1 1 (by norm_num) (by norm_num)

/-- The source of the shifted slice, written as a sum of the three pieces that are
differentiated by a single `θ`-derivative.  Here `A = z²∂_z²Ψ`. -/
private theorem gsrc_slice_eq {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hSOΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {z t : ℝ} (hz : 0 < z)
    (ht : t ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.FTS.EllipticEst.Mine.Gsrc α (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) z t
      = Work.Spaces.DzIter 1 F z t
        + α ^ 2 * (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z t)
        + α * (5 + α) * ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z t)
            + Work.Spaces.DzIter 1 Ψ z t) := by
  have h1 : Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z t
      = z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z t :=
    (Work.FTS.EllipticEst.H2W.slot11_z_identities hSOΨ).1 z t hz ht.1 ht.2
  have h2 := Work.H2W.MomentAe.zsq_pzIter2_eq hSOΨ hz ht
  rw [show Work.Spaces.Dz Ψ = Work.Spaces.DzIter 1 Ψ from rfl] at h2
  have h3 : z * Work.Spaces.pz (Work.Spaces.DzIter 1 Ψ) z t
      = (z ^ 2 * Work.Spaces.pzIter 2 Ψ z t) + Work.Spaces.DzIter 1 Ψ z t := by
    have h4 : Work.Spaces.DzIter 2 Ψ z t
        = (z ^ 2 * Work.Spaces.pzIter 2 Ψ z t) + Work.Spaces.DzIter 1 Ψ z t := by
      linarith [h2]
    rw [← h4]
    rfl
  simp only [Work.FTS.EllipticEst.Mine.Gsrc]
  rw [← h1, h3]

/-- The `θ`-derivative of the shifted source, decomposed. -/
private theorem gsrc_deriv_eq {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hSOF : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter 1 F))
    (hSOA : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)))
    (hSOA0 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hSOΦ : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter 1 Ψ))
    (hSOΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun t => Work.FTS.EllipticEst.Mine.Gsrc α (Work.Spaces.DzIter 1 F)
        (Work.Spaces.DzIter 1 Ψ) z t) θ
      = deriv (fun t => Work.Spaces.DzIter 1 F z t) θ
        + α ^ 2 * deriv (fun t =>
            Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z t) θ
        + α * (5 + α) * (deriv (fun t => (z ^ 2 * Work.Spaces.pzIter 2 Ψ z t)) θ
            + deriv (fun t => Work.Spaces.DzIter 1 Ψ z t) θ) := by
  have hev : (fun t => Work.FTS.EllipticEst.Mine.Gsrc α (Work.Spaces.DzIter 1 F)
        (Work.Spaces.DzIter 1 Ψ) z t)
      =ᶠ[𝓝 θ] (fun t => Work.Spaces.DzIter 1 F z t
        + α ^ 2 * (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z t)
        + α * (5 + α) * ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z t)
            + Work.Spaces.DzIter 1 Ψ z t)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
    exact gsrc_slice_eq hSOΨ hz ht
  rw [hev.deriv_eq]
  have hdF : DifferentiableAt ℝ (fun t => Work.Spaces.DzIter 1 F z t) θ :=
    differentiableAt_slice_of_smoothOpen hSOF hz hθ
  have hdA : DifferentiableAt ℝ (fun t =>
      Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z t) θ :=
    differentiableAt_slice_of_smoothOpen hSOA hz hθ
  have hdA0 : DifferentiableAt ℝ (fun t => z ^ 2 * Work.Spaces.pzIter 2 Ψ z t) θ :=
    differentiableAt_slice_of_smoothOpen hSOA0 hz hθ
  have hdΦ : DifferentiableAt ℝ (fun t => Work.Spaces.DzIter 1 Ψ z t) θ :=
    differentiableAt_slice_of_smoothOpen hSOΦ hz hθ
  have hd : HasDerivAt (fun t => Work.Spaces.DzIter 1 F z t
        + α ^ 2 * (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z t)
        + α * (5 + α) * ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z t)
            + Work.Spaces.DzIter 1 Ψ z t))
      (deriv (fun t => Work.Spaces.DzIter 1 F z t) θ
        + α ^ 2 * deriv (fun t =>
            Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z t) θ
        + α * (5 + α) * (deriv (fun t => (z ^ 2 * Work.Spaces.pzIter 2 Ψ z t)) θ
            + deriv (fun t => Work.Spaces.DzIter 1 Ψ z t) θ)) θ :=
    ((hdF.hasDerivAt).add ((hdA.hasDerivAt).const_mul (α ^ 2))).add
      (((hdA0.hasDerivAt).add (hdΦ.hasDerivAt)).const_mul (α * (5 + α)))
  rw [hd.deriv]

/-- **Angular-derivative integrability of the source of the shifted slice.** -/
private theorem srcAMine (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => Work.FTS.EllipticEst.Mine.Gsrc α
          (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) z t) θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
  have hγ2 : Work.Spaces.gam α ≤ 3 / 2 := by rw [Work.Spaces.gam]; linarith
  have hSOΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hSOF : Work.FTS.EllipticEst.SmoothOpen F := Work.H2W.smoothOpen_source h
  have hSOΦ : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter 1 Ψ) := hSOΨ.DzIter 1
  have hSOFz : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter 1 F) := hSOF.DzIter 1
  have hSOA0 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.remov.SourceBound.smoothOpen_zsq_mul_pzIter_two hSOΨ
  have hSOA : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) := hSOA0.DzIter 1
  have hWork.FTS.EllipticEst.Mine.sig2_meas : Measurable (fun θ : ℝ => Real.rpow (Real.sin (2 * θ))
      (2 - Work.Spaces.gam α)) := measurable_sig2 hγ2
  -- (1) `(∂_θ(D_z F))² σ₂`
  have hFz : MeasureTheory.IntegrableOn (fun θ =>
      (deriv (fun t => Work.Spaces.DzIter 1 F z t) θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
    refine Integrable.mono' (h.memF.1 z (Set.mem_Ici.mpr hz.le)) ?_ ?_
    · exact ((measurable_deriv (fun t => Work.Spaces.DzIter 1 F z t)).pow_const 2
        |>.mul hWork.FTS.EllipticEst.Mine.sig2_meas).aestronglyMeasurable
    · refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have hnn : 0 ≤ (deriv (fun t => Work.Spaces.DzIter 1 F z t) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α) :=
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Work.Spaces.sin_two_nonneg_of_Iθ hθI) _)
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact shiftPth_slot_le (γ := Work.Spaces.gam α) (f := F) hα hγ2 le_rfl hSOF hz hθ
  -- (2) `(∂_θ(D_z A))² σ₂`
  have hAz : MeasureTheory.IntegrableOn (fun θ =>
      (deriv (fun t =>
          Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z t) θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
    refine Integrable.mono' (h.memA.1 z (Set.mem_Ici.mpr hz.le)) ?_ ?_
    · exact ((measurable_deriv (fun t =>
          Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z t)).pow_const 2
        |>.mul hWork.FTS.EllipticEst.Mine.sig2_meas).aestronglyMeasurable
    · refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have hnn : 0 ≤ (deriv (fun t =>
            Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z t) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α) :=
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Work.Spaces.sin_two_nonneg_of_Iθ hθI) _)
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact shiftPth_slot_le (γ := Work.Spaces.gam α)
        (f := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) hα hγ2 le_rfl hSOA0 hz hθ
  -- (3) `(∂_θ A)² σ₂`
  have hA0 : MeasureTheory.IntegrableOn (fun θ =>
      (deriv (fun t => z ^ 2 * Work.Spaces.pzIter 2 Ψ z t) θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
    refine Integrable.mono' (h.memA.1 z (Set.mem_Ici.mpr hz.le)) ?_ ?_
    · exact ((measurable_deriv (fun t => z ^ 2 * Work.Spaces.pzIter 2 Ψ z t)).pow_const 2
        |>.mul hWork.FTS.EllipticEst.Mine.sig2_meas).aestronglyMeasurable
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
      have hθI : θ ∈ Work.Spaces.Iθ := hθ
      have hnn : 0 ≤ (deriv (fun t => z ^ 2 * Work.Spaces.pzIter 2 Ψ z t) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α) :=
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Work.Spaces.sin_two_nonneg_of_Iθ hθI) _)
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      have hslot := Work.FTS.EllipticEst.Mine.sig2_slot_pointwise α hα (Work.Spaces.gam α)
        hγ2 le_rfl (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ hθI
      calc (deriv (fun t => z ^ 2 * Work.Spaces.pzIter 2 Ψ z t) θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)
          = 1 * ((deriv (fun t => z ^ 2 * Work.Spaces.pzIter 2 Ψ z t) θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)) := by ring
        _ ≤ (Work.Spaces.w z) ^ 2
              * ((deriv (fun t => z ^ 2 * Work.Spaces.pzIter 2 Ψ z t) θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)) :=
            mul_le_mul_of_nonneg_right (one_le_w_sq hz) hnn
        _ = (Work.Spaces.w z) ^ 2
              * ((Work.Spaces.pth (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
                * Work.FTS.EllipticEst.Mine.sig2 (Work.Spaces.gam α) θ) := rfl
        _ ≤ Work.Spaces.HkIntegrand α 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ :=
            hslot
  -- (4) `(∂_θ(D_z Ψ))² σ₂`
  obtain ⟨KP, hKPpos, hKP⟩ := Work.FTS.EllipticEst.Mine.SlicePoincare
  have h2 : (2 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder := by
    rw [Work.Stability.smoothOrder]; exact WithTop.coe_le_coe.mpr le_top
  have hu2 : ContDiffOn ℝ 2 (fun θ => Work.Spaces.DzIter 1 Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    (hSOΦ.curry_θ hz).of_le h2
  have hcont : ContinuousOn (fun θ => Work.Spaces.DzIter 1 Ψ z θ) (Set.Icc 0 (Real.pi / 2)) :=
    (Work.H2W.weakSliceContinuousKit α F Ψ hα hα4 h z hz).2
  have hu0 : (fun θ => Work.Spaces.DzIter 1 Ψ z θ) 0 = 0 :=
    Work.FTS.EllipticEst.TT.DzIter_zero_at_zero Ψ 1 h.zero z
  have hupi : (fun θ => Work.Spaces.DzIter 1 Ψ z θ) (Real.pi / 2) = 0 :=
    Work.FTS.EllipticEst.TT.DzIter_zero_at_pi_half Ψ 1 h.pi_half z
  have hIB : MeasureTheory.IntegrableOn (fun θ =>
      (deriv (fun t => deriv (fun θ' => Work.Spaces.DzIter 1 Ψ z θ') t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := Work.H2W.dzpsi_second_sq h hz
  obtain ⟨hΦint, -, -⟩ := hKP (fun θ => Work.Spaces.DzIter 1 Ψ z θ) hu2 hcont hu0 hupi hIB
  have hΦ : MeasureTheory.IntegrableOn (fun θ =>
      (deriv (fun t => Work.Spaces.DzIter 1 Ψ z t) θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
    refine Integrable.mono' hΦint ?_ ?_
    · exact ((measurable_deriv (fun t => Work.Spaces.DzIter 1 Ψ z t)).pow_const 2
        |>.mul hWork.FTS.EllipticEst.Mine.sig2_meas).aestronglyMeasurable
    · refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have hnn : 0 ≤ (deriv (fun t => Work.Spaces.DzIter 1 Ψ z t) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α) :=
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Work.Spaces.sin_two_nonneg_of_Iθ hθI) _)
      have hle1 := sig2_le_one_of_mem_Iθ hγ2 hθI
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      calc (deriv (fun t => Work.Spaces.DzIter 1 Ψ z t) θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)
          ≤ (deriv (fun t => Work.Spaces.DzIter 1 Ψ z t) θ) ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left hle1 (sq_nonneg _)
        _ = (deriv (fun t => Work.Spaces.DzIter 1 Ψ z t) θ) ^ 2 := mul_one _
  have hmaj : MeasureTheory.IntegrableOn (fun θ =>
      3 * ((deriv (fun t => Work.Spaces.DzIter 1 F z t) θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α))
        + 3 * α ^ 4 * ((deriv (fun t =>
              Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z t) θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α))
        + 6 * (α * (5 + α)) ^ 2
            * (((deriv (fun t => z ^ 2 * Work.Spaces.pzIter 2 Ψ z t) θ) ^ 2
                  * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α))
              + ((deriv (fun t => Work.Spaces.DzIter 1 Ψ z t) θ) ^ 2
                  * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)))) Work.Spaces.Iθ :=
    ((hFz.const_mul 3).add (hAz.const_mul (3 * α ^ 4))).add
      ((hA0.add hΦ).const_mul (6 * (α * (5 + α)) ^ 2))
  refine hmaj.mono' ?_ ?_
  · exact ((measurable_deriv (fun t => Work.FTS.EllipticEst.Mine.Gsrc α (Work.Spaces.DzIter 1 F)
        (Work.Spaces.DzIter 1 Ψ) z t)).pow_const 2 |>.mul hWork.FTS.EllipticEst.Mine.sig2_meas).aestronglyMeasurable
  · refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hσnn : 0 ≤ Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α) :=
      Real.rpow_nonneg (Work.Spaces.sin_two_nonneg_of_Iθ hθI) _
    have hnn : 0 ≤ (deriv (fun t => Work.FTS.EllipticEst.Mine.Gsrc α (Work.Spaces.DzIter 1 F)
        (Work.Spaces.DzIter 1 Ψ) z t) θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α) :=
      mul_nonneg (sq_nonneg _) hσnn
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have hder := gsrc_deriv_eq (α := α) hSOFz hSOA hSOA0 hSOΦ hSOΨ hz hθ
    have hsq : (deriv (fun t => Work.FTS.EllipticEst.Mine.Gsrc α (Work.Spaces.DzIter 1 F)
          (Work.Spaces.DzIter 1 Ψ) z t) θ) ^ 2
        ≤ 3 * (deriv (fun t => Work.Spaces.DzIter 1 F z t) θ) ^ 2
          + 3 * α ^ 4 * (deriv (fun t =>
              Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z t) θ) ^ 2
          + 6 * (α * (5 + α)) ^ 2
              * ((deriv (fun t => z ^ 2 * Work.Spaces.pzIter 2 Ψ z t) θ) ^ 2
                + (deriv (fun t => Work.Spaces.DzIter 1 Ψ z t) θ) ^ 2) := by
      rw [hder]
      exact sq_sum_le_three
    calc (deriv (fun t => Work.FTS.EllipticEst.Mine.Gsrc α (Work.Spaces.DzIter 1 F)
            (Work.Spaces.DzIter 1 Ψ) z t) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)
        ≤ (3 * (deriv (fun t => Work.Spaces.DzIter 1 F z t) θ) ^ 2
            + 3 * α ^ 4 * (deriv (fun t =>
                Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z t) θ) ^ 2
            + 6 * (α * (5 + α)) ^ 2
                * ((deriv (fun t => z ^ 2 * Work.Spaces.pzIter 2 Ψ z t) θ) ^ 2
                  + (deriv (fun t => Work.Spaces.DzIter 1 Ψ z t) θ) ^ 2))
          * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α) :=
          mul_le_mul_of_nonneg_right hsq hσnn
      _ = 3 * ((deriv (fun t => Work.Spaces.DzIter 1 F z t) θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α))
          + 3 * α ^ 4 * ((deriv (fun t =>
                Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z t) θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α))
          + 6 * (α * (5 + α)) ^ 2
              * (((deriv (fun t => z ^ 2 * Work.Spaces.pzIter 2 Ψ z t) θ) ^ 2
                    * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α))
                + ((deriv (fun t => Work.Spaces.DzIter 1 Ψ z t) θ) ^ 2
                    * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α))) := by ring

/-- Absorption arithmetic for the slice Step-4 estimate: given the two Poincaré bounds
`C1 ≤ KP·B`, `C0 ≤ KP·B` and the nonnegativity of `D` and `B`, the lower-order
terms are absorbed into `D + B`. -/
private lemma absorb_arith {C₀ KP D B C1 C0 A : ℝ} (hC₀ : 0 < C₀) (hKP : 0 < KP)
    (hD : 0 ≤ D) (hB : 0 ≤ B) (h1 : C1 ≤ KP * B) (h0 : C0 ≤ KP * B)
    (hstep : A ≤ C₀ * (((D + B) + C1) + C0)) :
    A ≤ (C₀ * (1 + 2 * KP)) * (D + B) := by
  have hKD : 0 ≤ KP * D := mul_nonneg hKP.le hD
  have hkey : (((D + B) + C1) + C0) ≤ (1 + 2 * KP) * (D + B) := by
    nlinarith [hD, hB, hKP, hKD, h1, h0]
  calc A ≤ C₀ * (((D + B) + C1) + C0) := hstep
    _ ≤ C₀ * ((1 + 2 * KP) * (D + B)) := mul_le_mul_of_nonneg_left hkey hC₀.le
    _ = (C₀ * (1 + 2 * KP)) * (D + B) := by ring

/-- The per-`z` form of the shifted slice Step-4 estimate. -/
theorem sliceStep4Shift_z : ∃ K : ℝ, 0 < K ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      ∀ z, 0 < z →
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 3 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α))
        ≤ K * ((∫ θ in Work.Spaces.Iθ,
              (deriv (fun t => Work.FTS.EllipticEst.Mine.Gsrc α (Work.Spaces.DzIter 1 F)
                (Work.Spaces.DzIter 1 Ψ) z t) θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α))
            + (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ)) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.H2W.sliceStep4Uniform
  obtain ⟨KP, hKPpos, hKP⟩ := Work.FTS.EllipticEst.Mine.SlicePoincare
  refine ⟨C₀ * (1 + 2 * KP), by positivity, ?_⟩
  intro α F Ψ hα hα4 h z hz
  -- the exponents `gam α ∈ (1, 3/2]`
  have hγ1 : (1 : ℝ) ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hγ2 : Work.Spaces.gam α ≤ 3 / 2 := by rw [Work.Spaces.gam]; linarith
  -- smoothness of the shifted slice
  have hSOΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hSOu : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter 1 Ψ) := hSOΨ.DzIter 1
  have h3 : (3 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder := by
    rw [Work.Stability.smoothOrder]; exact WithTop.coe_le_coe.mpr le_top
  have h2 : (2 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder := by
    rw [Work.Stability.smoothOrder]; exact WithTop.coe_le_coe.mpr le_top
  have hu3 : ContDiffOn ℝ 3 (fun θ => Work.Spaces.DzIter 1 Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    (hSOu.curry_θ hz).of_le h3
  have hu2 : ContDiffOn ℝ 2 (fun θ => Work.Spaces.DzIter 1 Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    (hSOu.curry_θ hz).of_le h2
  have hcont : ContinuousOn (fun θ => Work.Spaces.DzIter 1 Ψ z θ) (Set.Icc 0 (Real.pi / 2)) :=
    (Work.H2W.weakSliceContinuousKit α F Ψ hα hα4 h z hz).2
  have hu0 : (fun θ => Work.Spaces.DzIter 1 Ψ z θ) 0 = 0 :=
    Work.FTS.EllipticEst.TT.DzIter_zero_at_zero Ψ 1 h.zero z
  have hupi : (fun θ => Work.Spaces.DzIter 1 Ψ z θ) (Real.pi / 2) = 0 :=
    Work.FTS.EllipticEst.TT.DzIter_zero_at_pi_half Ψ 1 h.pi_half z
  -- the slice equation
  have hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.DzIter 1 Ψ z t) θ
        = Work.FTS.EllipticEst.Mine.Gsrc α (Work.Spaces.DzIter 1 F)
            (Work.Spaces.DzIter 1 Ψ) z θ :=
    fun θ hθ => Work.FTS.EllipticEst.Mine.Lzero1_slice_eq_Gsrc
      (Work.FTS.EllipticEst.TT.bslOp_DzIter_eq α F Ψ 1 h.smooth h.eq) hz hθ.1 hθ.2
  -- the five integrability hypotheses of the slice Step-4 estimate
  have hIB : MeasureTheory.IntegrableOn (fun θ =>
      (deriv (fun t => deriv (fun θ' => Work.Spaces.DzIter 1 Ψ z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
    Work.H2W.dzpsi_second_sq h hz
  have hIA : MeasureTheory.IntegrableOn (fun θ =>
      (deriv (deriv (deriv (fun θ' => Work.Spaces.DzIter 1 Ψ z θ'))) θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.TT.Slot11.shiftThirdInt α F Ψ hα hα4 h hz
  have hID : MeasureTheory.IntegrableOn (fun θ =>
      (deriv (fun t => Work.FTS.EllipticEst.Mine.Gsrc α (Work.Spaces.DzIter 1 F)
        (Work.Spaces.DzIter 1 Ψ) z t) θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)) Work.Spaces.Iθ :=
    srcAMine α F Ψ hα hα4 h hz
  obtain ⟨hIC1, hIC0, hbC1, hbC0⟩ :=
    hKP (fun θ => Work.Spaces.DzIter 1 Ψ z θ) hu2 hcont hu0 hupi hIB
  -- the slice Step-4 estimate
  have hstep := hC₀ (Work.Spaces.gam α) (fun θ => Work.Spaces.DzIter 1 Ψ z θ)
    (fun θ => Work.FTS.EllipticEst.Mine.Gsrc α (Work.Spaces.DzIter 1 F)
      (Work.Spaces.DzIter 1 Ψ) z θ)
    hγ1 hγ2 hu3 hcont hu0 hupi hode hIA hIB hIC1 hIC0 hID
  -- nonnegativity of the two resources
  have hBnn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
      (deriv (deriv (fun θ' => Work.Spaces.DzIter 1 Ψ z θ')) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.remov.ws_sEta_nonneg hθ)
  have hDnn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
      (deriv (fun t => Work.FTS.EllipticEst.Mine.Gsrc α (Work.Spaces.DzIter 1 F)
        (Work.Spaces.DzIter 1 Ψ) z t) θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ =>
      mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (Work.Spaces.sin_two_nonneg_of_Iθ hθ) _)
  -- absorption of `∫(u')²` and `∫u²` into `∫(u'')²sEta`
  exact absorb_arith hC₀pos hKPpos hDnn hBnn hbC1 hbC0 hstep

/-- PER-`z` (a.e. in `z`) SLICE STEP-4 ESTIMATE for the SHIFTED slice `u = θ ↦ D_zΨ(z,θ)`.

Setting: `α ∈ (0,1/4]`, `h : EllWeakPos α 2 F Ψ` (the open-quadrant weak class of
`Submission/Work/FTS/EllipticEst/TT/WeakDefs.lean`: equation `bslOp α Ψ = F` on the open
quadrant, Dirichlet values `Ψ z 0 = Ψ z (π/2) = 0`, the two moment conditions, `C^∞` on the open
quadrant, and `HkMem α 2` of `F`, of `z²∂_z²Ψ` and of `∂_θ²Ψ`), and `γ = Work.Spaces.gam α`.

Conclusion, for almost every `z > 0`, with `σ₂(θ) = sin(2θ)^{2-γ} = Real.rpow (Real.sin (2θ)) (2-γ)`
and `sEta θ = sin(2θ)^{-η}`, `η = 99/100`:

  `∫_θ (∂_θ³(D_zΨ)(z,θ))² σ₂ ≤ K · ( ∫_θ (∂_θ g(z,·))² σ₂ + ∫_θ (∂_θ²(D_zΨ)(z,θ))² sEta )`,

where `g = Mine.Gsrc α (D_zF) (D_zΨ)` is the source of the shifted slice: by
`Mine/SlotDefs.lean:Lzero1_slice_eq_Gsrc` applied to the shifted datum
`(D_zF, D_zΨ)` — whose equation `bslOp α (D_zΨ) = D_zF` is
`TT/bslOp_DzIter_eq` — the slice `u` solves `Lzero1 u = g z ·` on `(0,π/2)`.

Route. `u := θ ↦ D_zΨ(z,θ)`.
* `u` is `C^∞` on `(0,π/2)` (`remov/wsAux.ws_contDiffOn_slice` + `SmoothOpen.DzIter`);
* `u 0 = 0 = u (π/2)`: `Ψ · 0` and `Ψ · (π/2)` are *identically* `0` in `z`, so
  `pz Ψ z 0 = deriv (fun z' => Ψ z' 0) z = 0`; and `u` is *continuous on* `[0,π/2]` for every
  `z > 0` by `H2W/weakSliceContinuousKit.lean:weakSliceContinuousKit` (which internally uses the
  moment chain, so the endpoint limit of the slice really is `0`);
* apply the PROVED `Work.H2W.sliceStep4Uniform` (`∃ C > 0, ∀ γ u g, 1 ≤ γ → γ ≤ 3/2 → …`, and
  `gam α ∈ (1, 3/2]`).  Its five integrability hypotheses, at `u`, are:
  `(u''')²σ₂` from `HkMem α 2 (∂_θ²Ψ)` (its `(i,j) = (1,1)` mixed slot is
  `(D_zD_θ(∂_θ²Ψ)·Wt)² = w²·(∂_θ³(D_zΨ))²σ₂` by `H2W/slot11_aux.slot11_sq_eq` + Clairaut);
  `(u'')²sEta` from the `i = 1` pure `D_z`-slot of `HkMem α 2 (∂_θ²Ψ)`
  (`remov/wsAux.ws_slot_slice`, `remov/wsAux.ws_pthIter_two_DzIter`, `H2W/weakSliceContinuousKit.dzpsi_second_sq`);
  `(u')²` and `u²` from `H2W/sliceWirtinger`; and `(∂_θg)²σ₂` from the three source slots
  (see the sibling `FTS/EllipticEst/TT/Slot11/srcBound`) together with the a.e.-in-`z`
  endpoint continuity `Work.FTS.EllipticEst.H2W.slot11_Acont` (PROVED) for the two Poincaré steps;
* absorb `∫(u')²` and `∫u²` into `∫(u'')²sEta` by `H2W/sliceWirtinger` and `1 ≤ sEta` a.e.
  (`remov/wsAux.ws_one_le_sEta`).

The statement is a.e. in `z` because the endpoint continuity of the auxiliary second-order
radial slices is only available a.e. (`H2W/slot11_Acont`). -/
theorem sliceStep4Shift : ∃ K : ℝ, 0 < K ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z →
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 3 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α))
        ≤ K * ((∫ θ in Work.Spaces.Iθ,
              (deriv (fun t => Work.FTS.EllipticEst.Mine.Gsrc α (Work.Spaces.DzIter 1 F)
                (Work.Spaces.DzIter 1 Ψ) z t) θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α))
            + (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ)) := by
  obtain ⟨K, hK, hKz⟩ := sliceStep4Shift_z
  exact ⟨K, hK, fun α F Ψ hα hα4 h =>
    Filter.Eventually.of_forall fun z hz => hKz α F Ψ hα hα4 h z hz⟩

end Work.FTS.EllipticEst.TT.Slot11
