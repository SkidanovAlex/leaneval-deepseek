import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.Final.ReHome.H2W_slot20_bound
import Submission.Work.FTS.EllipticEst.H2W.Ae.aeSigmaSliceLower
import Submission.Work.FTS.EllipticEst.TT.truncAux
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.LocDataExt.Final
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.FTS.EllipticEst.Final.ReHome.M4_S20SrcAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.Step5

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The weighted second angular slot -/

/-- The pointwise integrand `w(z)²·(X(z,θ))²·σ(θ)`: the `σ`-weighted second angular slot of the
*derivative block* `X` (the caller passes `X = ∂_θ²f` or `X = D_z^j D_θ²f`). -/
def s20src_slotFun (X : ℝ → ℝ → ℝ) (σ : ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (Work.Spaces.w z) ^ 2 * ((X z θ) ^ 2 * σ θ)

/-- The `θ`-integral of `s20src_slotFun`: the `σ`-weighted slot of `X` at radius `z`. -/
def s20src_slotZ (X : ℝ → ℝ → ℝ) (σ : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, s20src_slotFun X σ z θ

/-- The `j`-th summand of `pPure`, in the `s20src_slotZ` form. -/
def s20src_pSlot (j : ℕ) (Ψ : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz,
    s20src_slotZ (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ))
      Work.FTS.EllipticEst.sEta z

theorem s20src_slotFun_nonneg {X : ℝ → ℝ → ℝ} {σ : ℝ → ℝ}
    (hσ : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ σ θ) (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ s20src_slotFun X σ z θ :=
  mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (hσ θ hθ))

theorem s20src_slotZ_nonneg {X : ℝ → ℝ → ℝ} {σ : ℝ → ℝ}
    (hσ : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ σ θ) (z : ℝ) :
    0 ≤ s20src_slotZ X σ z := by
  refine integral_nonneg_of_ae ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  exact s20src_slotFun_nonneg hσ z θ hθ

/-! ## The elementary weight facts -/

theorem s20src_sEta_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ :=
  Real.rpow_nonneg (Work.FTS.EllipticEst.Mine.sin_two_nonneg_of_mem_Iθ hθ) _

theorem s20src_eta_div_two_ne_zero : Work.Spaces.eta / 2 ≠ 0 := by
  rw [Work.Spaces.eta]; norm_num

theorem s20src_gam_ne_four (α : ℝ) (hα4 : α ≤ 1 / 4) : (4 : ℝ) - Work.Spaces.gam α ≠ 0 := by
  have hle : Work.Spaces.gam α ≤ 2 := by rw [Work.Spaces.gam]; linarith
  linarith

theorem s20src_sigma4_nonneg (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ :=
  Work.FTS.EllipticEst.Mine.sig4_nonneg_of_mem_Iθ hθ

/-- `σ₄ = sin(2θ)^{4-γ} ≤ sin(2θ)^{-η} = sEta` on the whole closed angular slice. -/
theorem s20src_sigma4_le_sEta (α : ℝ) (hα4 : α ≤ 1 / 4) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ ≤ Work.FTS.EllipticEst.sEta θ := by
  have hgam4 : (4 : ℝ) - Work.Spaces.gam α ≠ 0 := s20src_gam_ne_four α hα4
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · have hz : Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ = 0 := by
      rw [Work.FTS.EllipticEst.Mine.sig4, ← h0, show (2 : ℝ) * 0 = 0 by ring, Real.sin_zero]
      exact Real.zero_rpow hgam4
    rw [hz]
    exact s20src_sEta_nonneg hθ
  · rcases lt_or_eq_of_le hθ.2 with h1 | h1
    · exact Work.FTS.EllipticEst.TT.sig4_le_sEta α hα4 ⟨h0, h1⟩
    · have hz : Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ = 0 := by
        rw [Work.FTS.EllipticEst.Mine.sig4, h1,
          show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
        exact Real.zero_rpow hgam4
      rw [hz]
      exact s20src_sEta_nonneg hθ

/-- `1 ≤ sEta` almost everywhere on the angular slice. -/
theorem s20src_one_le_sEta_ae :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      1 ≤ Work.FTS.EllipticEst.sEta θ := by
  have hIoo : (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) : Measure ℝ)
      = MeasureTheory.volume.restrict Work.Spaces.Iθ :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
  rw [← hIoo]
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
  exact Work.FTS.EllipticEst.TT.one_le_sEta hθ

/-- `σ₄` is continuous on the open angular interval. -/
theorem s20src_continuousOn_sigma4 (α : ℝ) :
    ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hne : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.sin (2 * θ) ≠ 0 := fun θ hθ =>
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos]))
  exact hsin.rpow_const (fun θ hθ => Or.inl (hne θ hθ))


/-! ## A.e. strong measurability and outer integrability of slice integrals -/

/-- The `z`-slice integral of a function continuous on the open quadrant is a.e. strongly
measurable (for `volume.restrict Iz`). -/
theorem s20src_aesm_integral_Qd {H : ℝ → ℝ → ℝ}
    (hH : ContinuousOn (fun p : ℝ × ℝ => H p.1 p.2) Work.FTS.EllipticEst.Q0) :
    MeasureTheory.AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ, H z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
  (Work.Spaces.aesm_of_continuousOn_Qd (fun p : ℝ × ℝ => H p.1 p.2) hH).integral_prod_right'
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)

/-- `w²` is continuous on the open quadrant. -/
theorem s20src_continuousOn_w_sq :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      = fun p : ℝ × ℝ => ((1 + p.1) ^ 2 / p.1 ^ 2) ^ 2 := by
    funext p; rfl
  rw [hfun]
  refine ContinuousOn.pow ?_ 2
  exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2)
    (fun p hp => pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1))

/-- The uncurried integrand `s20src_slotFun X σ` is continuous on the open quadrant as soon as
`X` is smooth there and `σ` is continuous on the open angular interval. -/
theorem s20src_continuousOn_slotFun {X : ℝ → ℝ → ℝ} {σ : ℝ → ℝ}
    (hX : Work.FTS.EllipticEst.SmoothOpen X)
    (hσ : ContinuousOn σ (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (fun p : ℝ × ℝ => s20src_slotFun X σ p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => (X p.1 p.2) ^ 2) Work.FTS.EllipticEst.Q0 :=
    hX.continuousOn.pow 2
  have h2 : ContinuousOn (fun p : ℝ × ℝ => σ p.2) Work.FTS.EllipticEst.Q0 :=
    hσ.comp continuous_snd.continuousOn (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).2)
  exact (s20src_continuousOn_w_sq).mul (h1.mul h2)

/-- A.e. strong measurability of a slot slice, for `z > 0`. -/
theorem s20src_aesm_slotFun {X : ℝ → ℝ → ℝ} {σ : ℝ → ℝ}
    (hX : Work.FTS.EllipticEst.SmoothOpen X)
    (hσ : ContinuousOn σ (Set.Ioo 0 (Real.pi / 2))) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.AEStronglyMeasurable (fun θ => s20src_slotFun X σ z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => s20src_slotFun X σ p.1 p.2)
    (s20src_continuousOn_slotFun hX hσ) hz

/-- **Outer integrability of a weighted `D_z`-summand of `HkMem`.** -/
theorem s20src_integrableOn_zSummand_outer (α : ℝ) (k : ℕ) {A : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.SmoothOpen A) (hmem : Work.Spaces.HkMem α k A)
    (i : ℕ) (hi : i ≤ k) :
    MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.DzIter i A z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iz := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.DzIter i A p.1 p.2
        * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.FTS.EllipticEst.Q0 := (hA.continuousOn_summand i).pow 2
  refine MeasureTheory.Integrable.mono' hmem.2 (s20src_aesm_integral_Qd hcont) ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
  have hmono : (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.DzIter i A z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k A z θ :=
    MeasureTheory.integral_mono_of_nonneg (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun θ : ℝ => (Work.Spaces.DzIter i A z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      (g := fun θ : ℝ => Work.Spaces.HkIntegrand α k A z θ)
      (Filter.Eventually.of_forall fun θ => sq_nonneg _) (hmem.1 z hz)
      (Filter.Eventually.of_forall fun θ => Work.Spaces.sq_le_HkIntegrand_z α k A z θ i hi)
  rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun θ => sq_nonneg _)]
  exact hmono

/-! ## The `L2Sq` form of a slot, and the summands of `pPure` -/

/-- A `sEta`-slot equals the square of the corresponding `w/sin(2θ)^{η/2}`-weighted function. -/
theorem s20src_slotFun_eq_weighted (A : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    s20src_slotFun A Work.FTS.EllipticEst.sEta z θ
      = (A z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  rw [s20src_slotFun, Work.FTS.EllipticEst.mul_w_sin_rpow_sq (A z θ) (Work.Spaces.w z) hθ,
    Work.FTS.EllipticEst.sEta]
  ring

theorem s20src_slotZ_eq_weighted (A : ℝ → ℝ → ℝ) (z : ℝ) :
    s20src_slotZ A Work.FTS.EllipticEst.sEta z
      = ∫ θ in Work.Spaces.Iθ,
          (A z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
  MeasureTheory.integral_congr_ae (by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact s20src_slotFun_eq_weighted A z θ hθ)

theorem s20src_pureSlot_eq (A : ℝ → ℝ → ℝ) :
    Work.Spaces.L2Sq (fun z θ => A z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      = ∫ z in Work.Spaces.Iz, s20src_slotZ A Work.FTS.EllipticEst.sEta z := by
  rw [Work.Spaces.L2Sq]
  exact MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun z => (s20src_slotZ_eq_weighted A z).symm)

theorem s20src_pureSlot_eqDz (j : ℕ) (Ψ : ℝ → ℝ → ℝ) :
    Work.Spaces.L2Sq (fun z θ => Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      = s20src_pSlot j Ψ :=
  s20src_pureSlot_eq (fun z θ => Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ)

theorem s20src_pPure_eq_sum (Ψ : ℝ → ℝ → ℝ) :
    Work.FTS.EllipticEst.H2W.pPure Ψ
      = ∑ j ∈ Finset.range 3, s20src_pSlot j Ψ := by
  rw [Work.FTS.EllipticEst.H2W.pPure]
  exact Finset.sum_congr rfl fun j _ => s20src_pureSlot_eqDz j Ψ

theorem s20src_pPure_eq_three (Ψ : ℝ → ℝ → ℝ) :
    Work.FTS.EllipticEst.H2W.pPure Ψ
      = s20src_pSlot 0 Ψ + s20src_pSlot 1 Ψ + s20src_pSlot 2 Ψ := by
  rw [s20src_pPure_eq_sum]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

theorem s20src_pSlot_nonneg (j : ℕ) (Ψ : ℝ → ℝ → ℝ) : 0 ≤ s20src_pSlot j Ψ :=
  integral_nonneg fun z => s20src_slotZ_nonneg (fun θ hθ => s20src_sEta_nonneg hθ) z

/-! ## The `sEta`-slots of the `D_z^j Ψ` and their honesty -/

/-- The `sEta`-slot integrand of `D_z^j Ψ` equals the weighted `D_z^j`-summand of `∂_θ²Ψ`,
pointwise on the whole angular slice (both sides vanish at the endpoints, and at `z = 0`, where
the commutation of `∂_θ²` with `D_z` is not available). -/
theorem s20src_slotFun_DzIter_comm {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) (j : ℕ) {z : ℝ} (hz : z ∈ Work.Spaces.Iz)
    (θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    s20src_slotFun (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ))
        Work.FTS.EllipticEst.sEta z θ
      = (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 Ψ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  rw [s20src_slotFun_eq_weighted _ z θ hθ]
  congr 1
  have hfac0 : Real.sin (2 * θ) = 0 →
      Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
    intro hs
    rw [hs, Real.zero_rpow s20src_eta_div_two_ne_zero, div_zero]
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · have hw : Work.Spaces.w z = 0 := by rw [← hz0, Work.Spaces.w]; norm_num
    rw [hw, zero_div, mul_zero, mul_zero]
  · rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · have hs : Real.sin (2 * θ) = 0 := by rw [← h0]; simp
      rw [hfac0 hs, mul_zero, mul_zero]
    · rcases lt_or_eq_of_le hθ.2 with h1 | h1
      · have hmem : ((z, θ) : ℝ × ℝ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) :=
          ⟨hzpos, h0, h1⟩
        have hcomm : Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
            = Work.Spaces.DzIter j (Work.Spaces.pthIter 2 Ψ) z θ := by
          simpa only [Function.uncurry] using
            Work.EllipticEst.H2W.pthIter2_DzIter_comm hΨ j hmem
        rw [hcomm]
      · have hs : Real.sin (2 * θ) = 0 := by
          rw [h1, show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
        rw [hfac0 hs, mul_zero, mul_zero]

/-- **The `θ`-slice integrability of the `sEta`-slot of `D_z^j Ψ`, `j ≤ 2`.** -/
theorem s20src_integrableOn_slotFun_sEta_DzIter {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ))
    (j : ℕ) (hj : j ≤ 2) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    MeasureTheory.IntegrableOn
      (fun θ => s20src_slotFun (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ))
        Work.FTS.EllipticEst.sEta z θ)
      Work.Spaces.Iθ := by
  have hBso : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hΨ 2
  have h := Work.FTS.EllipticEst.integrableOn_zSummand α 2 hBso hB j hj hz
  refine h.congr_fun (fun θ hθ => ?_) measurableSet_Icc
  exact (s20src_slotFun_DzIter_comm hΨ j hz θ hθ).symm

/-- **The outer integrability of the `sEta`-slot of `D_z^j Ψ`, `j ≤ 2`.** -/
theorem s20src_integrableOn_slotZ_sEta_DzIter {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ))
    (j : ℕ) (hj : j ≤ 2) :
    MeasureTheory.IntegrableOn
      (fun z => s20src_slotZ (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ))
        Work.FTS.EllipticEst.sEta z)
      Work.Spaces.Iz := by
  have hBso : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hΨ 2
  have h := s20src_integrableOn_zSummand_outer α 2 hBso hB j hj
  refine h.congr ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ici] with z hz
  exact MeasureTheory.integral_congr_ae (by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact (s20src_slotFun_DzIter_comm hΨ j hz θ hθ).symm)

/-! ## The `σ₄`-versions of the `D_z^j Ψ`-slots -/

theorem s20src_slotFun_sigma4_le_sEta (α : ℝ) (hα4 : α ≤ 1 / 4) (X : ℝ → ℝ → ℝ)
    (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    s20src_slotFun X (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ
      ≤ s20src_slotFun X Work.FTS.EllipticEst.sEta z θ :=
  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (s20src_sigma4_le_sEta α hα4 hθ) (sq_nonneg _)) (sq_nonneg _)

/-- The `θ`-slice integrability of the `σ₄`-slot of `D_z^j Ψ`, `j ≤ 2`. -/
theorem s20src_integrableOn_slotFun_sigma4_DzIter {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ))
    (hα4 : α ≤ 1 / 4) (j : ℕ) (hj : j ≤ 2) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    MeasureTheory.IntegrableOn
      (fun θ => s20src_slotFun (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ))
        (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ)
      Work.Spaces.Iθ := by
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · have hz1 : (fun θ => s20src_slotFun (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ))
        (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ) = fun _ => (0 : ℝ) := by
      funext θ
      rw [← hz0, s20src_slotFun, Work.Spaces.w]
      norm_num
    rw [hz1]
    exact integrableOn_zero
  · have hX : Work.FTS.EllipticEst.SmoothOpen
        (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ)) :=
      Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl (hΨ.DzIter j) 2
    refine MeasureTheory.Integrable.mono'
      (s20src_integrableOn_slotFun_sEta_DzIter hΨ hB j hj hz)
      (s20src_aesm_slotFun hX (s20src_continuousOn_sigma4 α) hzpos) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_of_nonneg (s20src_slotFun_nonneg
      (fun θ' hθ' => s20src_sigma4_nonneg α hθ') z θ hθ)]
    exact s20src_slotFun_sigma4_le_sEta α hα4 _ z θ hθ

/-- The outer integrability of the `σ₄`-slot of `D_z^j Ψ`, `j ≤ 2`. -/
theorem s20src_integrableOn_slotZ_sigma4_DzIter {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ))
    (hα4 : α ≤ 1 / 4) (j : ℕ) (hj : j ≤ 2) :
    MeasureTheory.IntegrableOn
      (fun z => s20src_slotZ (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ))
        (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z)
      Work.Spaces.Iz := by
  have hX : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ)) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl (hΨ.DzIter j) 2
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      s20src_slotFun (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ))
        (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) p.1 p.2)
      Work.FTS.EllipticEst.Q0 := s20src_continuousOn_slotFun hX (s20src_continuousOn_sigma4 α)
  refine MeasureTheory.Integrable.mono'
    (s20src_integrableOn_slotZ_sEta_DzIter hΨ hB j hj) (s20src_aesm_integral_Qd hcont) ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ici] with z hz
  rw [Real.norm_of_nonneg (s20src_slotZ_nonneg
    (fun θ' hθ' => s20src_sigma4_nonneg α hθ') z)]
  refine MeasureTheory.integral_mono_of_nonneg
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (f := fun θ => s20src_slotFun (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ))
      (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ)
    (g := fun θ => s20src_slotFun (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ))
      Work.FTS.EllipticEst.sEta z θ) ?_ ?_ ?_
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact s20src_slotFun_nonneg (fun θ' hθ' => s20src_sigma4_nonneg α hθ') z θ hθ
  · exact s20src_integrableOn_slotFun_sEta_DzIter hΨ hB j hj hz
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact s20src_slotFun_sigma4_le_sEta α hα4 _ z θ hθ

/-! ## The `Φ = z²∂_z²Ψ = Az Ψ`-slot -/

/-- The commutation `∂_θ²D_z²Ψ = ∂_θ²(z²∂_z²Ψ) + ∂_θ²(D_zΨ)` on the open quadrant, i.e.
`∂_θ²(Az Ψ) = ∂_θ²(D_z²Ψ) − ∂_θ²(D_zΨ)`. -/
theorem s20src_pthIter2_Az_eq {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ) z θ
      = Work.Spaces.pthIter 2 (Az Ψ) z θ
        + Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ := by
  have hAzso : Work.FTS.EllipticEst.SmoothOpen (Az Ψ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl (hΨ.pzIter 2)
  have h1so : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter 1 Ψ) := hΨ.DzIter 1
  have hEqOn : Set.EqOn (Function.uncurry (Work.Spaces.DzIter 2 Ψ))
      (Function.uncurry (fun z t => Az Ψ z t + 1 * Work.Spaces.DzIter 1 Ψ z t + 0 * Ψ z t))
      Work.FTS.EllipticEst.Q0 := by
    rintro ⟨z', θ'⟩ hp
    obtain ⟨hz', hθ'0, hθ'1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    have h := Work.FTS.EllipticEst.H2W.zsq_pzIter2 hΨ hz' ⟨hθ'0, hθ'1⟩
    have h' : Az Ψ z' θ' + 1 * Work.Spaces.DzIter 1 Ψ z' θ' + 0 * Ψ z' θ'
        = Work.Spaces.DzIter 2 Ψ z' θ' := by linarith [h]
    simpa only [Function.uncurry] using h'.symm
  have hstep1 : Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ) z θ
      = Work.Spaces.pthIter 2
          (fun z t => Az Ψ z t + 1 * Work.Spaces.DzIter 1 Ψ z t + 0 * Ψ z t) z θ := by
    have h1 : Set.EqOn
        (Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter 2 Ψ)))
        (Function.uncurry (Work.Spaces.pth
          (fun z t => Az Ψ z t + 1 * Work.Spaces.DzIter 1 Ψ z t + 0 * Ψ z t)))
        Work.FTS.EllipticEst.Q0 :=
      fun p hp => Work.Spaces.pth_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEqOn hp
    exact Work.Spaces.pth_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 h1
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩)
  have hstep2 : Work.Spaces.pthIter 2
        (fun z t => Az Ψ z t + 1 * Work.Spaces.DzIter 1 Ψ z t + 0 * Ψ z t) z θ
      = Work.Spaces.pthIter 2 (Az Ψ) z θ
        + 1 * Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ
        + 0 * Work.Spaces.pthIter 2 Ψ z θ :=
    Work.FTS.EllipticEst.SrcBnd.pthIter_three_lin hAzso h1so hΨ 1 0 2 z θ hz hθ
  rw [hstep1, hstep2]
  ring

theorem s20src_slotFun_nonneg_sigma4 (α : ℝ) (X : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ s20src_slotFun X (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ :=
  s20src_slotFun_nonneg (fun θ' hθ' => s20src_sigma4_nonneg α hθ') z θ hθ

/-- The slot integrand vanishes identically at `z = 0`. -/
theorem s20src_slotFun_zero_left (X : ℝ → ℝ → ℝ) (σ : ℝ → ℝ) (θ : ℝ) :
    s20src_slotFun X σ 0 θ = 0 := by
  rw [s20src_slotFun, Work.Spaces.w]
  norm_num


theorem s20src_sq_add_three_le (x y z : ℝ) :
    (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)]

/-- **Linearity of the integral of a two-term combination** (the bookkeeping lemma behind all
the `σ₄`-slot comparisons). -/
theorem s20src_integral_two (s : Set ℝ) (f g : ℝ → ℝ) (a b : ℝ)
    (hf : MeasureTheory.IntegrableOn f s) (hg : MeasureTheory.IntegrableOn g s) :
    (∫ x in s, a * f x + b * g x)
      = a * (∫ x in s, f x) + b * (∫ x in s, g x) := by
  rw [MeasureTheory.integral_add (hf.const_mul a) (hg.const_mul b),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

/-- The `θ`-slice integrability of the `σ₄`-slot of `∂_θ²F`, from `HkMem α 2 F` and the
pointwise slot comparison `sig4_slot_pointwise`. -/
theorem s20src_integrableOn_slotFun_sigma4_F {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hFmem : Work.Spaces.HkMem α 2 F)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    MeasureTheory.IntegrableOn
      (fun θ => s20src_slotFun (Work.Spaces.pthIter 2 F)
        (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ)
      Work.Spaces.Iθ := by
  have hgam2 : Work.Spaces.gam α ≤ 3 / 2 := by rw [Work.Spaces.gam]; linarith
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · have hz1 : (fun θ => s20src_slotFun (Work.Spaces.pthIter 2 F)
        (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ) = fun _ => (0 : ℝ) := by
      funext θ
      rw [← hz0]
      exact s20src_slotFun_zero_left _ _ θ
    rw [hz1]
    exact integrableOn_zero
  · have hX : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 F) :=
      Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hF 2
    refine MeasureTheory.Integrable.mono' ((hFmem.1 z hz).const_mul 10)
      (s20src_aesm_slotFun hX (s20src_continuousOn_sigma4 α) hzpos) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_of_nonneg (s20src_slotFun_nonneg_sigma4 α _ z θ hθ)]
    have h := Work.FTS.EllipticEst.Mine.sig4_slot_pointwise α hα (Work.Spaces.gam α) hgam2
      le_rfl F z θ hθ
    simpa only [s20src_slotFun, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero,
      Work.Spaces.pth] using h

/-- **The pointwise comparison for the `Az Ψ`-slot**, on the open quadrant.  The `σ₄`-weighted
second angular slot of `∂_θ²(Az Ψ)` is dominated by twice the two `sEta`-slots of `D_z²Ψ` and
`D_zΨ`. -/
theorem s20src_slotFun_Az_le {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (α : ℝ) (hα4 : α ≤ 1 / 4) {z : ℝ} (hz : 0 < z) (θ : ℝ)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    s20src_slotFun (Work.Spaces.pthIter 2 (Az Ψ))
        (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ
      ≤ 2 * (s20src_slotFun (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ))
              Work.FTS.EllipticEst.sEta z θ
            + s20src_slotFun (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
              Work.FTS.EllipticEst.sEta z θ) := by
  have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hsig : Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ
      ≤ Work.FTS.EllipticEst.sEta θ :=
    s20src_sigma4_le_sEta α hα4 (Set.Ioo_subset_Icc_self hθ)
  have hse : 0 ≤ Work.FTS.EllipticEst.sEta θ :=
    s20src_sEta_nonneg (Set.Ioo_subset_Icc_self hθ)
  have hid := s20src_pthIter2_Az_eq hΨ hz hθ
  obtain ⟨X, Y, Z, hX, hY, hZ, hXY : X = Y - Z⟩ : ∃ X Y Z : ℝ,
      X = Work.Spaces.pthIter 2 (Az Ψ) z θ
      ∧ Y = Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ) z θ
      ∧ Z = Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ
      ∧ X = Y - Z := by
    refine ⟨_, _, _, rfl, rfl, rfl, ?_⟩
    linarith [hid]
  have h2 : (Y - Z) ^ 2 ≤ 2 * (Y ^ 2 + Z ^ 2) := by
    nlinarith [sq_nonneg (Y - Z), sq_nonneg (Y + Z)]
  have h3 : (Work.Spaces.w z) ^ 2 * (X ^ 2 * Work.FTS.EllipticEst.Mine.sig4
        (Work.Spaces.gam α) θ)
      ≤ (Work.Spaces.w z) ^ 2 * (X ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsig (sq_nonneg _)) hw2
  have h4 : (Work.Spaces.w z) ^ 2 * (X ^ 2 * Work.FTS.EllipticEst.sEta θ)
      = (Work.Spaces.w z) ^ 2 * ((Y - Z) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    rw [hXY]
  have h5 : (Work.Spaces.w z) ^ 2 * ((Y - Z) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ (Work.Spaces.w z) ^ 2
        * (2 * (Y ^ 2 + Z ^ 2) * Work.FTS.EllipticEst.sEta θ) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hse) hw2
  have h6 : (Work.Spaces.w z) ^ 2 * (2 * (Y ^ 2 + Z ^ 2) * Work.FTS.EllipticEst.sEta θ)
      = 2 * ((Work.Spaces.w z) ^ 2 * (Y ^ 2 * Work.FTS.EllipticEst.sEta θ)
        + (Work.Spaces.w z) ^ 2 * (Z ^ 2 * Work.FTS.EllipticEst.sEta θ)) := by
    ring
  simp only [s20src_slotFun, hX, hY, hZ] at *
  linarith [h3, h4.le, h5, h6.le]

/-- The slot `θ`-integral vanishes at `z = 0`. -/
theorem s20src_slotZ_zero_left (X : ℝ → ℝ → ℝ) (σ : ℝ → ℝ) :
    s20src_slotZ X σ 0 = 0 := by
  rw [s20src_slotZ,
    show (fun θ => s20src_slotFun X σ 0 θ) = fun _ => (0 : ℝ) from
      funext fun θ => s20src_slotFun_zero_left X σ θ]
  simp

/-- Almost every `z ∈ Iz` is positive. -/
theorem s20src_ae_pos_mem_Iz :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
  rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl,
    MeasureTheory.ae_restrict_iff' measurableSet_Ici]
  filter_upwards [show ∀ᵐ z ∂(MeasureTheory.volume : Measure ℝ), z ≠ 0 from by
      rw [MeasureTheory.ae_iff]
      simpa using (measure_singleton (0 : ℝ))] with z hz hzI
  exact lt_of_le_of_ne hzI (Ne.symm hz)

theorem s20src_integrableOn_slotFun_sigma4_Az {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ))
    (hα4 : α ≤ 1 / 4) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    MeasureTheory.IntegrableOn
      (fun θ => s20src_slotFun (Work.Spaces.pthIter 2 (Az Ψ))
        (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ)
      Work.Spaces.Iθ := by
  have hAzso : Work.FTS.EllipticEst.SmoothOpen (Az Ψ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl (hΨ.pzIter 2)
  have hX : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 (Az Ψ)) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hAzso 2
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · have hz1 : (fun θ => s20src_slotFun (Work.Spaces.pthIter 2 (Az Ψ))
        (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ) = fun _ => (0 : ℝ) := by
      funext θ
      rw [← hz0]
      exact s20src_slotFun_zero_left _ _ θ
    rw [hz1]
    exact integrableOn_zero
  · have h₂ := s20src_integrableOn_slotFun_sEta_DzIter hΨ hB 2 (by norm_num) hz
    have h₁ := s20src_integrableOn_slotFun_sEta_DzIter hΨ hB 1 (by norm_num) hz
    have hmaj : MeasureTheory.IntegrableOn
        (fun θ => 2 * (s20src_slotFun (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ))
              Work.FTS.EllipticEst.sEta z θ
            + s20src_slotFun (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
              Work.FTS.EllipticEst.sEta z θ)) Work.Spaces.Iθ :=
      MeasureTheory.IntegrableOn.congr_fun ((h₂.const_mul 2).add (h₁.const_mul 2))
        (fun θ _ => by simp only [Pi.add_apply]; ring) measurableSet_Icc
    refine MeasureTheory.Integrable.mono' hmaj
      (s20src_aesm_slotFun hX (s20src_continuousOn_sigma4 α) hzpos) ?_
    filter_upwards [Work.FTS.EllipticEst.remov.SourceBound.ae_mem_Ioo_of_mem_Iθ] with θ hθ
    rw [Real.norm_of_nonneg (s20src_slotFun_nonneg_sigma4 α _ z θ (Set.Ioo_subset_Icc_self hθ))]
    exact s20src_slotFun_Az_le hΨ α hα4 hzpos θ hθ

theorem s20src_integrableOn_slotZ_sigma4_Az {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ))
    (hα4 : α ≤ 1 / 4) :
    MeasureTheory.IntegrableOn
      (fun z => s20src_slotZ (Work.Spaces.pthIter 2 (Az Ψ))
        (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z)
      Work.Spaces.Iz := by
  have hAzso : Work.FTS.EllipticEst.SmoothOpen (Az Ψ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl (hΨ.pzIter 2)
  have hX : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 (Az Ψ)) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hAzso 2
  have h₂z := s20src_integrableOn_slotZ_sEta_DzIter hΨ hB 2 (by norm_num)
  have h₁z := s20src_integrableOn_slotZ_sEta_DzIter hΨ hB 1 (by norm_num)
  have hmaj : MeasureTheory.IntegrableOn
      (fun z => 2 * (s20src_slotZ (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ))
            Work.FTS.EllipticEst.sEta z
          + s20src_slotZ (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
            Work.FTS.EllipticEst.sEta z)) Work.Spaces.Iz :=
    MeasureTheory.IntegrableOn.congr_fun ((h₂z.const_mul 2).add (h₁z.const_mul 2))
      (fun z _ => by simp only [Pi.add_apply]; ring) measurableSet_Ici
  refine MeasureTheory.Integrable.mono' hmaj
    (s20src_aesm_integral_Qd (s20src_continuousOn_slotFun hX (s20src_continuousOn_sigma4 α))) ?_
  filter_upwards [s20src_ae_pos_mem_Iz] with z hzpos
  rw [Real.norm_of_nonneg (s20src_slotZ_nonneg (fun θ' hθ' => s20src_sigma4_nonneg α hθ') z)]
  have hθ₂ := s20src_integrableOn_slotFun_sEta_DzIter hΨ hB 2 (by norm_num)
    (Set.mem_Ici.mpr hzpos.le)
  have hθ₁ := s20src_integrableOn_slotFun_sEta_DzIter hΨ hB 1 (by norm_num)
    (Set.mem_Ici.mpr hzpos.le)
  have hmajθ : MeasureTheory.IntegrableOn
      (fun θ => 2 * (s20src_slotFun (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ))
            Work.FTS.EllipticEst.sEta z θ
          + s20src_slotFun (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
            Work.FTS.EllipticEst.sEta z θ)) Work.Spaces.Iθ :=
    MeasureTheory.IntegrableOn.congr_fun ((hθ₂.const_mul 2).add (hθ₁.const_mul 2))
      (fun θ _ => by simp only [Pi.add_apply]; ring) measurableSet_Icc
  have h1 : s20src_slotZ (Work.Spaces.pthIter 2 (Az Ψ))
        (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z
      ≤ ∫ θ in Work.Spaces.Iθ,
          2 * (s20src_slotFun (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ))
              Work.FTS.EllipticEst.sEta z θ
            + s20src_slotFun (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
              Work.FTS.EllipticEst.sEta z θ) :=
    MeasureTheory.integral_mono_of_nonneg
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun θ => s20src_slotFun (Work.Spaces.pthIter 2 (Az Ψ))
        (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ)
      (g := fun θ => 2 * (s20src_slotFun (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ))
          Work.FTS.EllipticEst.sEta z θ
        + s20src_slotFun (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
          Work.FTS.EllipticEst.sEta z θ))
      (by
        filter_upwards [Work.FTS.EllipticEst.remov.SourceBound.ae_mem_Ioo_of_mem_Iθ] with θ hθ
        exact s20src_slotFun_nonneg_sigma4 α _ z θ (Set.Ioo_subset_Icc_self hθ))
      hmajθ
      (by
        filter_upwards [Work.FTS.EllipticEst.remov.SourceBound.ae_mem_Ioo_of_mem_Iθ] with θ hθ
        exact s20src_slotFun_Az_le hΨ α hα4 hzpos θ hθ)
  have h2 : (∫ θ in Work.Spaces.Iθ,
          2 * (s20src_slotFun (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ))
              Work.FTS.EllipticEst.sEta z θ
            + s20src_slotFun (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
              Work.FTS.EllipticEst.sEta z θ))
      = 2 * (s20src_slotZ (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ))
            Work.FTS.EllipticEst.sEta z
          + s20src_slotZ (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
            Work.FTS.EllipticEst.sEta z) := by
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hθ₂ hθ₁]
    rfl
  rw [h2] at h1
  exact h1

/-- **The `σ₄`-slot of `D_z^j Ψ` is bounded by the `j`-th summand of `pPure`.** -/
theorem s20src_slotZ_sigma4_DzIter_le {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ))
    (hα4 : α ≤ 1 / 4) (j : ℕ) (hj : j ≤ 2) :
    (∫ z in Work.Spaces.Iz, s20src_slotZ (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ))
        (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z)
      ≤ s20src_pSlot j Ψ := by
  have hmaj : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ,
        s20src_slotFun (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ))
          Work.FTS.EllipticEst.sEta z θ) Work.Spaces.Iz :=
    s20src_integrableOn_slotZ_sEta_DzIter hΨ hB j hj
  have hpt : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, s20src_slotFun (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ))
          (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ)
        ≤ (∫ θ in Work.Spaces.Iθ, s20src_slotFun (Work.Spaces.pthIter 2
            (Work.Spaces.DzIter j Ψ)) Work.FTS.EllipticEst.sEta z θ) := by
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · rw [← hz0]
      simp only [s20src_slotZ, s20src_slotFun_zero_left]
      simp
    · refine MeasureTheory.integral_mono_of_nonneg
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (f := fun θ => s20src_slotFun (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ))
          (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ)
        (g := fun θ => s20src_slotFun (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ))
          Work.FTS.EllipticEst.sEta z θ) ?_ ?_ ?_
      · filter_upwards [Work.FTS.EllipticEst.remov.SourceBound.ae_mem_Ioo_of_mem_Iθ] with θ hθ
        exact s20src_slotFun_nonneg_sigma4 α _ z θ (Set.Ioo_subset_Icc_self hθ)
      · exact s20src_integrableOn_slotFun_sEta_DzIter hΨ hB j hj hz
      · filter_upwards [Work.FTS.EllipticEst.remov.SourceBound.ae_mem_Ioo_of_mem_Iθ] with θ hθ
        exact s20src_slotFun_sigma4_le_sEta α hα4 _ z θ (Set.Ioo_subset_Icc_self hθ)
  have h := MeasureTheory.integral_mono_of_nonneg
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz =>
      integral_nonneg_of_ae (by
        filter_upwards [Work.FTS.EllipticEst.remov.SourceBound.ae_mem_Ioo_of_mem_Iθ] with θ hθ
        exact s20src_slotFun_nonneg_sigma4 α _ z θ (Set.Ioo_subset_Icc_self hθ)))
    hmaj (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hpt)
  exact h

/-- **The `σ₄`-slot of `Az Ψ` is bounded by twice the `j = 2` and `j = 1` summands of
`pPure`.** -/
theorem s20src_slotZ_sigma4_Az_le {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ))
    (hα4 : α ≤ 1 / 4) :
    (∫ z in Work.Spaces.Iz, s20src_slotZ (Work.Spaces.pthIter 2 (Az Ψ))
        (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z)
      ≤ 2 * (s20src_pSlot 2 Ψ + s20src_pSlot 1 Ψ) := by
  have h₂z := s20src_integrableOn_slotZ_sEta_DzIter hΨ hB 2 (by norm_num)
  have h₁z := s20src_integrableOn_slotZ_sEta_DzIter hΨ hB 1 (by norm_num)
  have hmaj : MeasureTheory.IntegrableOn
      (fun z => 2 * (s20src_slotZ (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ))
            Work.FTS.EllipticEst.sEta z
          + s20src_slotZ (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
            Work.FTS.EllipticEst.sEta z)) Work.Spaces.Iz :=
    MeasureTheory.IntegrableOn.congr_fun ((h₂z.const_mul 2).add (h₁z.const_mul 2))
      (fun z _ => by simp only [Pi.add_apply]; ring) measurableSet_Ici
  have hpt : ∀ z ∈ Work.Spaces.Iz,
      s20src_slotZ (Work.Spaces.pthIter 2 (Az Ψ))
          (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z
        ≤ 2 * (s20src_slotZ (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ))
            Work.FTS.EllipticEst.sEta z
          + s20src_slotZ (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
            Work.FTS.EllipticEst.sEta z) := by
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · rw [← hz0,
        s20src_slotZ_zero_left (Work.Spaces.pthIter 2 (Az Ψ))
          (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)),
        s20src_slotZ_zero_left (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ))
          Work.FTS.EllipticEst.sEta,
        s20src_slotZ_zero_left (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
          Work.FTS.EllipticEst.sEta]
      norm_num
    · have hθ₂ := s20src_integrableOn_slotFun_sEta_DzIter hΨ hB 2 (by norm_num) hz
      have hθ₁ := s20src_integrableOn_slotFun_sEta_DzIter hΨ hB 1 (by norm_num) hz
      have h1 : s20src_slotZ (Work.Spaces.pthIter 2 (Az Ψ))
            (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z
          ≤ ∫ θ in Work.Spaces.Iθ,
              2 * (s20src_slotFun (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ))
                  Work.FTS.EllipticEst.sEta z θ
                + s20src_slotFun (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
                  Work.FTS.EllipticEst.sEta z θ) :=
        MeasureTheory.integral_mono_of_nonneg
          (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
          (f := fun θ => s20src_slotFun (Work.Spaces.pthIter 2 (Az Ψ))
            (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ)
          (g := fun θ => 2 * (s20src_slotFun (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ))
              Work.FTS.EllipticEst.sEta z θ
            + s20src_slotFun (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
              Work.FTS.EllipticEst.sEta z θ))
          (by
            filter_upwards [Work.FTS.EllipticEst.remov.SourceBound.ae_mem_Ioo_of_mem_Iθ]
              with θ hθ
            exact s20src_slotFun_nonneg_sigma4 α _ z θ (Set.Ioo_subset_Icc_self hθ))
          (MeasureTheory.IntegrableOn.congr_fun ((hθ₂.const_mul 2).add (hθ₁.const_mul 2))
            (fun θ _ => by simp only [Pi.add_apply]; ring) measurableSet_Icc)
          (by
            filter_upwards [Work.FTS.EllipticEst.remov.SourceBound.ae_mem_Ioo_of_mem_Iθ]
              with θ hθ
            exact s20src_slotFun_Az_le hΨ α hα4 hzpos θ hθ)
      have h2 : (∫ θ in Work.Spaces.Iθ,
              2 * (s20src_slotFun (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ))
                  Work.FTS.EllipticEst.sEta z θ
                + s20src_slotFun (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
                  Work.FTS.EllipticEst.sEta z θ))
          = 2 * (s20src_slotZ (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ))
                Work.FTS.EllipticEst.sEta z
              + s20src_slotZ (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
                Work.FTS.EllipticEst.sEta z) := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hθ₂ hθ₁]
        rfl
      rw [h2] at h1
      exact h1
  have h := MeasureTheory.integral_mono_of_nonneg
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz =>
      integral_nonneg_of_ae (by
        filter_upwards [Work.FTS.EllipticEst.remov.SourceBound.ae_mem_Ioo_of_mem_Iθ] with θ hθ
        exact s20src_slotFun_nonneg_sigma4 α _ z θ (Set.Ioo_subset_Icc_self hθ)))
    hmaj (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hpt)
  have hsplit : (∫ z in Work.Spaces.Iz, 2 *
        (s20src_slotZ (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ))
            Work.FTS.EllipticEst.sEta z
          + s20src_slotZ (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
            Work.FTS.EllipticEst.sEta z))
      = 2 * (s20src_pSlot 2 Ψ + s20src_pSlot 1 Ψ) := by
    have h1 : (∫ z in Work.Spaces.Iz, 2 * s20src_slotZ (Work.Spaces.pthIter 2
            (Work.Spaces.DzIter 2 Ψ)) Work.FTS.EllipticEst.sEta z
          + 2 * s20src_slotZ (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
            Work.FTS.EllipticEst.sEta z)
        = 2 * (∫ z in Work.Spaces.Iz, s20src_slotZ (Work.Spaces.pthIter 2
              (Work.Spaces.DzIter 2 Ψ)) Work.FTS.EllipticEst.sEta z)
          + 2 * (∫ z in Work.Spaces.Iz, s20src_slotZ (Work.Spaces.pthIter 2
              (Work.Spaces.DzIter 1 Ψ)) Work.FTS.EllipticEst.sEta z) :=
      s20src_integral_two Work.Spaces.Iz _ _ 2 2 h₂z h₁z
    have h2 : (∫ z in Work.Spaces.Iz, 2 *
          (s20src_slotZ (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ))
              Work.FTS.EllipticEst.sEta z
            + s20src_slotZ (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
              Work.FTS.EllipticEst.sEta z))
        = ∫ z in Work.Spaces.Iz, 2 * s20src_slotZ (Work.Spaces.pthIter 2
              (Work.Spaces.DzIter 2 Ψ)) Work.FTS.EllipticEst.sEta z
          + 2 * s20src_slotZ (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
              Work.FTS.EllipticEst.sEta z :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
    rw [h2, h1]
    simp only [s20src_pSlot]
    ring
  have h' : (∫ z in Work.Spaces.Iz, s20src_slotZ (Work.Spaces.pthIter 2 (Az Ψ))
        (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z)
      ≤ ∫ z in Work.Spaces.Iz, 2 * (s20src_slotZ (Work.Spaces.pthIter 2
            (Work.Spaces.DzIter 2 Ψ)) Work.FTS.EllipticEst.sEta z
          + s20src_slotZ (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
            Work.FTS.EllipticEst.sEta z) := h
  rw [hsplit] at h'
  exact h'

/-! ## `s20J2` in the slot form, and the source comparison -/

theorem s20src_s20J2_eq (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) :
    Work.FTS.EllipticEst.H2W.s20J2 α F Ψ
      = ∫ z in Work.Spaces.Iz,
          s20src_slotZ (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ))
            (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z := by
  rw [Work.FTS.EllipticEst.H2W.s20J2]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  exact (MeasureTheory.integral_const_mul ((Work.Spaces.w z) ^ 2)
    (fun θ => (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ) z θ) ^ 2
      * Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ)).symm

/-- **The pointwise source comparison**, on the open quadrant. -/
theorem s20src_slotFun_Gsrc_le {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z : ℝ} (hz : 0 < z) (θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    s20src_slotFun (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ))
        (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ
      ≤ 3 * (s20src_slotFun (Work.Spaces.pthIter 2 F)
              (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ
            + α ^ 4 * s20src_slotFun (Work.Spaces.pthIter 2 (Az Ψ))
              (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ
            + (α * (5 + α)) ^ 2 * s20src_slotFun
              (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
              (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ) := by
  have hσ : 0 ≤ Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ :=
    s20src_sigma4_nonneg α (Set.Ioo_subset_Icc_self hθ)
  have hid := Work.FTS.EllipticEst.SrcBnd.GsrcPthTwo (α := α) hF hΨ z θ hz hθ
  have hsq' : (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ) z θ) ^ 2
      ≤ 3 * ((Work.Spaces.pthIter 2 F z θ) ^ 2
        + α ^ 4 * (Work.Spaces.pthIter 2 (Az Ψ) z θ) ^ 2
        + (α * (5 + α)) ^ 2
          * (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2) := by
    change (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ) z θ) ^ 2
      ≤ 3 * ((Work.Spaces.pthIter 2 F z θ) ^ 2
        + α ^ 4 * (Work.Spaces.pthIter 2
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
        + (α * (5 + α)) ^ 2
          * (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2)
    rw [hid]
    have h3 := s20src_sq_add_three_le (Work.Spaces.pthIter 2 F z θ)
      (α ^ 2 * Work.Spaces.pthIter 2
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ)
      (α * (5 + α) * Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
    nlinarith [h3]
  calc s20src_slotFun (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ))
        (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ
      = (Work.Spaces.w z) ^ 2
        * ((Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ) z θ) ^ 2
          * Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ) := rfl
    _ ≤ (Work.Spaces.w z) ^ 2 * (3 * ((Work.Spaces.pthIter 2 F z θ) ^ 2
          + α ^ 4 * (Work.Spaces.pthIter 2 (Az Ψ) z θ) ^ 2
          + (α * (5 + α)) ^ 2
            * (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2)
        * Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsq' hσ) (sq_nonneg _)
    _ = 3 * (s20src_slotFun (Work.Spaces.pthIter 2 F)
          (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ
        + α ^ 4 * s20src_slotFun (Work.Spaces.pthIter 2 (Az Ψ))
          (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ
        + (α * (5 + α)) ^ 2 * s20src_slotFun
          (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
          (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ) := by
        simp only [s20src_slotFun]; ring

/-- **The `z`-level source comparison**, for `z > 0`. -/
theorem s20src_slotZ_Gsrc_le {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hFmem : Work.Spaces.HkMem α 2 F)
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) {z : ℝ}
    (hz : 0 < z) :
    s20src_slotZ (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ))
        (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z
      ≤ 3 * (s20src_slotZ (Work.Spaces.pthIter 2 F)
              (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z
            + α ^ 4 * s20src_slotZ (Work.Spaces.pthIter 2 (Az Ψ))
              (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z
            + (α * (5 + α)) ^ 2 * s20src_slotZ
              (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
              (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z) := by
  have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
  have hFθ := s20src_integrableOn_slotFun_sigma4_F hα hα4 hF hFmem hzI
  have hAzθ := s20src_integrableOn_slotFun_sigma4_Az hΨ hB hα4 hzI
  have hΛθ := s20src_integrableOn_slotFun_sigma4_DzIter hΨ hB hα4 1 (by norm_num) hzI
  have hmajθ : MeasureTheory.IntegrableOn
      (fun θ => 3 * (s20src_slotFun (Work.Spaces.pthIter 2 F)
            (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ
          + α ^ 4 * s20src_slotFun (Work.Spaces.pthIter 2 (Az Ψ))
            (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ
          + (α * (5 + α)) ^ 2 * s20src_slotFun
            (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
            (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ)) Work.Spaces.Iθ :=
    MeasureTheory.IntegrableOn.congr_fun
      (((hFθ.add (hAzθ.const_mul (α ^ 4))).add
        (hΛθ.const_mul ((α * (5 + α)) ^ 2))).const_mul 3)
      (fun θ _ => by simp only [Pi.add_apply, Pi.mul_apply]; try ring) measurableSet_Icc
  have h1 : s20src_slotZ (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ))
        (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z
      ≤ ∫ θ in Work.Spaces.Iθ, 3 * (s20src_slotFun (Work.Spaces.pthIter 2 F)
            (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ
          + α ^ 4 * s20src_slotFun (Work.Spaces.pthIter 2 (Az Ψ))
            (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ
          + (α * (5 + α)) ^ 2 * s20src_slotFun
            (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
            (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ) :=
    MeasureTheory.integral_mono_of_nonneg
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun θ => s20src_slotFun (Work.Spaces.pthIter 2
          (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ))
        (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ)
      (g := fun θ => 3 * (s20src_slotFun (Work.Spaces.pthIter 2 F)
          (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ
        + α ^ 4 * s20src_slotFun (Work.Spaces.pthIter 2 (Az Ψ))
          (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ
        + (α * (5 + α)) ^ 2 * s20src_slotFun
          (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
          (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ))
      (by
        filter_upwards [Work.FTS.EllipticEst.remov.SourceBound.ae_mem_Ioo_of_mem_Iθ] with θ hθ
        exact s20src_slotFun_nonneg_sigma4 α _ z θ (Set.Ioo_subset_Icc_self hθ))
      hmajθ
      (by
        filter_upwards [Work.FTS.EllipticEst.remov.SourceBound.ae_mem_Ioo_of_mem_Iθ] with θ hθ
        exact s20src_slotFun_Gsrc_le hα hα4 hF hΨ hz θ hθ)
  have hI12 : MeasureTheory.IntegrableOn
      (fun θ => s20src_slotFun (Work.Spaces.pthIter 2 F)
          (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ
        + α ^ 4 * s20src_slotFun (Work.Spaces.pthIter 2 (Az Ψ))
          (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ) Work.Spaces.Iθ :=
    hFθ.add (hAzθ.const_mul (α ^ 4))
  have hI3 : MeasureTheory.IntegrableOn
      (fun θ => (α * (5 + α)) ^ 2 * s20src_slotFun
          (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
          (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ) Work.Spaces.Iθ :=
    hΛθ.const_mul ((α * (5 + α)) ^ 2)
  have h2 : (∫ θ in Work.Spaces.Iθ, 3 * (s20src_slotFun (Work.Spaces.pthIter 2 F)
          (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ
        + α ^ 4 * s20src_slotFun (Work.Spaces.pthIter 2 (Az Ψ))
          (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ
        + (α * (5 + α)) ^ 2 * s20src_slotFun
          (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
          (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ))
      = 3 * (s20src_slotZ (Work.Spaces.pthIter 2 F)
            (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z
          + α ^ 4 * s20src_slotZ (Work.Spaces.pthIter 2 (Az Ψ))
            (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z
          + (α * (5 + α)) ^ 2 * s20src_slotZ
            (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
            (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z) := by
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add hI12 hI3,
      MeasureTheory.integral_add hFθ (hAzθ.const_mul (α ^ 4)),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    rfl
  rw [h2] at h1
  exact h1
end Work.FTS.EllipticEst.H2W.Step5
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.aeSliceAesm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## The measurability engine

Every one of the six `z`-functions in the statement is the `θ`-marginal of a function which is
*continuous on the open quadrant* `Q0 = (0,∞) × (0,π/2)`, against the product measure
`volume|_{(0,∞)} × volume|_{Iθ}`.  Such a function is a.e. strongly measurable for `nuFts`
(it is continuous, hence Borel measurable, on an open set of full `nuFts`-measure), and Fubini's
measurability theorem for the partial integral then gives the claim for the marginal, on the
first factor `volume|_{(0,∞)}`. -/


/-- The squared weight `w(z)²` is continuous on `(0,∞)`. -/
private theorem continuousOn_w_sq_prv :
    ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := by
    funext z; simp only [Work.Spaces.w]
  rw [hfun]
  refine (ContinuousOn.div ?_ ?_ ?_).pow 2
  · fun_prop
  · fun_prop
  · intro z hz; exact pow_ne_zero 2 (ne_of_gt hz)




end

end Work.FTS.EllipticEst.TT
end
